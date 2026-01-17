#!/usr/bin/env python3
"""
Solve quantifier-free real polynomial constraints using SMT solvers (Z3/Yices).

Intended to run inside a docker image that provides the solver binaries
(`z3`, `yices-smt2`), but it can also run on-host if those binaries exist.

Input JSON schema matches `scripts/cad_dreal_solve.py` and Lean's
`SemiAlgebraic.Computational.RealConstraints.IR`.
"""

from __future__ import annotations

import argparse
import json
import subprocess
import time
from dataclasses import dataclass
from decimal import Decimal
from fractions import Fraction
from pathlib import Path
from typing import Any, Iterable


def _expect_dict(x: Any, ctx: str) -> dict:
    if not isinstance(x, dict):
        raise ValueError(f"{ctx}: expected object")
    return x


def _expect_list(x: Any, ctx: str) -> list:
    if not isinstance(x, list):
        raise ValueError(f"{ctx}: expected array")
    return x


def _expect_str(x: Any, ctx: str) -> str:
    if not isinstance(x, str):
        raise ValueError(f"{ctx}: expected string")
    return x


def _expect_num(x: Any, ctx: str) -> Decimal:
    if isinstance(x, Decimal):
        return x
    if isinstance(x, (int, float)):
        return Decimal(str(x))
    raise ValueError(f"{ctx}: expected number")


def _smt_symbol(name: str) -> str:
    # Our JSON var names are simple; still, reject anything that would lead to
    # solver injection or invalid SMT-LIB.
    if not name or any(c.isspace() for c in name) or any(c in "()\";" for c in name):
        raise ValueError(f"invalid SMT symbol: {name!r}")
    return name


def _smt_num(d: Decimal) -> str:
    # SMT-LIB accepts decimal numerals; keep this as a canonical string.
    s = format(d, "f") if d == d.to_integral() else str(d.normalize())
    # Normalize things like "-0" and "-0.0".
    if s.startswith("-0") and Decimal(s) == 0:
        s = "0"
    if s.startswith("-"):
        return f"(- {s[1:]})"
    return s


def _pow_as_mul(base: str, exp: int) -> str:
    if exp < 0:
        raise ValueError("pow exp must be nonnegative")
    if exp == 0:
        return "1"
    if exp == 1:
        return base
    return f"(* {' '.join([base] * exp)})"


def smt_of_expr(node: dict, var_names: set[str]) -> str:
    node = _expect_dict(node, "expr")
    kind = _expect_str(node.get("kind", None), "expr.kind")

    if kind == "var":
        name = _smt_symbol(_expect_str(node.get("name", None), "expr.var.name"))
        if name not in var_names:
            raise ValueError(f"expr.var: unknown variable '{name}'")
        return name

    if kind == "const":
        return _smt_num(_expect_num(node.get("value", None), "expr.const.value"))

    if kind == "add":
        xs = _expect_list(node.get("children", None), "expr.add.children")
        if not xs:
            return "0"
        return f"(+ {' '.join([smt_of_expr(ch, var_names) for ch in xs])})"

    if kind == "mul":
        xs = _expect_list(node.get("children", None), "expr.mul.children")
        if not xs:
            return "1"
        return f"(* {' '.join([smt_of_expr(ch, var_names) for ch in xs])})"

    if kind == "neg":
        ch = node.get("child", None)
        return f"(- {smt_of_expr(ch, var_names)})"

    if kind == "pow":
        base = smt_of_expr(node.get("base", None), var_names)
        exp = node.get("exp", None)
        if not isinstance(exp, int) or exp < 0:
            raise ValueError("expr.pow.exp: expected nonnegative integer")
        return _pow_as_mul(base, exp)

    raise ValueError(f"expr: unsupported kind '{kind}'")


def smt_of_formula(node: dict, var_names: set[str]) -> str:
    node = _expect_dict(node, "formula")
    kind = _expect_str(node.get("kind", None), "formula.kind")

    if kind == "and":
        xs = _expect_list(node.get("children", None), "formula.and.children")
        if not xs:
            return "true"
        return f"(and {' '.join([smt_of_formula(ch, var_names) for ch in xs])})"

    if kind == "or":
        xs = _expect_list(node.get("children", None), "formula.or.children")
        if not xs:
            return "false"
        return f"(or {' '.join([smt_of_formula(ch, var_names) for ch in xs])})"

    if kind == "not":
        ch = node.get("child", None)
        return f"(not {smt_of_formula(ch, var_names)})"

    if kind == "cmp":
        op = _expect_str(node.get("op", None), "formula.cmp.op")
        lhs = smt_of_expr(node.get("lhs", None), var_names)
        rhs = smt_of_expr(node.get("rhs", None), var_names)
        if op == "<":
            return f"(< {lhs} {rhs})"
        if op == "<=":
            return f"(<= {lhs} {rhs})"
        if op in ("=", "=="):
            return f"(= {lhs} {rhs})"
        if op == ">=":
            return f"(>= {lhs} {rhs})"
        if op == ">":
            return f"(> {lhs} {rhs})"
        raise ValueError(f"formula.cmp.op: unsupported op '{op}'")

    raise ValueError(f"formula: unsupported kind '{kind}'")


def _tokenize_sexp(s: str) -> list[str]:
    tokens: list[str] = []
    i = 0
    while i < len(s):
        c = s[i]
        if c.isspace():
            i += 1
            continue
        if c in ("(", ")"):
            tokens.append(c)
            i += 1
            continue
        j = i
        while j < len(s) and (not s[j].isspace()) and s[j] not in ("(", ")"):
            j += 1
        tokens.append(s[i:j])
        i = j
    return tokens


def _parse_sexp(tokens: list[str]) -> Any:
    def parse_at(pos: int) -> tuple[Any, int]:
        if pos >= len(tokens):
            raise ValueError("unexpected end of tokens")
        if tokens[pos] == "(":
            out: list[Any] = []
            pos += 1
            while True:
                if pos >= len(tokens):
                    raise ValueError("missing ')'")
                if tokens[pos] == ")":
                    return out, pos + 1
                item, pos = parse_at(pos)
                out.append(item)
        if tokens[pos] == ")":
            raise ValueError("unexpected ')'")
        return tokens[pos], pos + 1

    node, end = parse_at(0)
    if end != len(tokens):
        raise ValueError("trailing tokens after S-expression")
    return node


def _fraction_of_atom(tok: str) -> Fraction:
    if "/" in tok and tok.count("/") == 1:
        a, b = tok.split("/", 1)
        return Fraction(int(a), int(b))
    return Fraction(Decimal(tok))


def _fraction_of_term(term: Any) -> Fraction:
    if isinstance(term, str):
        if term == "true":
            return Fraction(1)
        if term == "false":
            return Fraction(0)
        return _fraction_of_atom(term)
    if not isinstance(term, list) or not term:
        raise ValueError("invalid numeric term")
    head = term[0]
    args = term[1:]
    if head == "/":
        if len(args) != 2:
            raise ValueError("(/ a b) expects 2 args")
        return _fraction_of_term(args[0]) / _fraction_of_term(args[1])
    if head == "-":
        if len(args) == 1:
            return -_fraction_of_term(args[0])
        if len(args) >= 2:
            acc = _fraction_of_term(args[0])
            for a in args[1:]:
                acc -= _fraction_of_term(a)
            return acc
    if head == "+":
        acc = Fraction(0)
        for a in args:
            acc += _fraction_of_term(a)
        return acc
    if head == "*":
        acc = Fraction(1)
        for a in args:
            acc *= _fraction_of_term(a)
        return acc
    raise ValueError(f"unsupported numeric term head: {head!r}")


@dataclass(frozen=True)
class SolveResult:
    status: str
    model: dict[str, dict[str, Any]] | None


def _solver_cmd(solver: str) -> list[str]:
    if solver == "z3":
        return ["z3", "-in", "-smt2"]
    if solver == "yices":
        return ["yices-smt2"]
    raise ValueError(f"unknown solver {solver!r}")


def _build_smt2(problem: dict, vars_: list[dict], var_names: set[str], include_values: bool) -> str:
    formula = smt_of_formula(problem.get("formula", None), var_names)
    decls = "\n".join([f"(declare-fun {n} () Real)" for n in sorted(var_names)])
    bounds: list[str] = []
    for v in vars_:
        name = _smt_symbol(_expect_str(v.get("name", None), "vars[i].name"))
        lo = _smt_num(_expect_num(v.get("lo", None), f"vars[{name}].lo"))
        hi = _smt_num(_expect_num(v.get("hi", None), f"vars[{name}].hi"))
        bounds.append(f"(>= {name} {lo})")
        bounds.append(f"(<= {name} {hi})")
    bounds_smt = "(and " + " ".join(bounds) + ")" if bounds else "true"
    get_value = ""
    if include_values and var_names:
        get_value = "(get-value (" + " ".join(sorted(var_names)) + "))"

    return "\n".join(
        [
            "(set-logic QF_NRA)",
            decls,
            f"(assert {bounds_smt})",
            f"(assert {formula})",
            "(check-sat)",
            get_value,
            "(exit)",
            "",
        ]
    )


def solve(problem: dict, solver: str) -> SolveResult:
    problem = _expect_dict(problem, "problem")
    vars_ = _expect_list(problem.get("vars", None), "problem.vars")
    var_names = set()
    for i, v in enumerate(vars_):
        v = _expect_dict(v, f"vars[{i}]")
        name = _smt_symbol(_expect_str(v.get("name", None), f"vars[{i}].name"))
        var_names.add(name)

    smt2_check = _build_smt2(problem, vars_, var_names, include_values=False)
    t0 = time.time()
    try:
        out = subprocess.run(
            _solver_cmd(solver),
            input=smt2_check,
            text=True,
            capture_output=True,
            check=False,
        )
    except FileNotFoundError as e:
        return SolveResult(
            status="error",
            model=None,
        )

    if out.returncode != 0:
        raise RuntimeError(f"solver failed (exit={out.returncode}): {out.stderr.strip()}")

    lines = [ln.strip() for ln in out.stdout.splitlines() if ln.strip()]
    if not lines:
        raise RuntimeError("solver produced no output")
    status = lines[0]
    if status not in ("sat", "unsat", "unknown"):
        raise RuntimeError(f"unexpected solver status: {status!r}")

    if status != "sat" or not var_names:
        return SolveResult(status=status, model=None)

    # Second pass: query model values only when `sat`.
    smt2_values = _build_smt2(problem, vars_, var_names, include_values=True)
    out2 = subprocess.run(
        _solver_cmd(solver),
        input=smt2_values,
        text=True,
        capture_output=True,
        check=False,
    )
    if out2.returncode != 0:
        raise RuntimeError(f"solver failed (exit={out2.returncode}): {out2.stderr.strip()}")

    lines2 = [ln.strip() for ln in out2.stdout.splitlines() if ln.strip()]
    if not lines2:
        raise RuntimeError("solver produced no output")
    status2 = lines2[0]
    if status2 != "sat":
        raise RuntimeError(f"unexpected solver status on model query: {status2!r}")

    # Everything after the first line should be the get-value response.
    sexp_txt = "\n".join(lines2[1:]).strip()
    tokens = _tokenize_sexp(sexp_txt)
    sexp = _parse_sexp(tokens)
    if not isinstance(sexp, list):
        raise RuntimeError("get-value response is not a list")

    model: dict[str, dict[str, Any]] = {}
    for entry in sexp:
        if (
            not isinstance(entry, list)
            or len(entry) != 2
            or not isinstance(entry[0], str)
        ):
            raise RuntimeError("malformed get-value entry")
        name = entry[0]
        if name not in var_names:
            continue
        frac = _fraction_of_term(entry[1])
        exact = f"{frac.numerator}/{frac.denominator}" if frac.denominator != 1 else str(frac.numerator)
        mid = float(frac.numerator / frac.denominator)
        model[name] = {"lb": mid, "ub": mid, "mid": mid, "exact": exact}

    return SolveResult(status=status, model=model)


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("--in", dest="in_path", required=True)
    ap.add_argument("--solver", choices=["z3", "yices"], required=True)
    args = ap.parse_args()

    in_path = Path(args.in_path)
    raw = in_path.read_text()
    problem = json.loads(raw, parse_float=Decimal)

    t0 = time.time()
    try:
        res = solve(problem, args.solver)
        out: dict[str, Any] = {
            "backend": args.solver,
            "status": res.status,
            "elapsed_ms": int(1000 * (time.time() - t0)),
            "model": res.model,
        }
    except Exception as e:
        out = {
            "backend": args.solver,
            "status": "error",
            "message": f"{type(e).__name__}: {e}",
            "elapsed_ms": int(1000 * (time.time() - t0)),
            "model": None,
        }

    print(json.dumps(out))


if __name__ == "__main__":
    main()
