#!/usr/bin/env python3
"""
Solve quantifier-free real constraints using dReal (via the dReal Python API).

Intended to run inside the `dreal/dreal4` Docker image, but also works on-host
if `pip install dreal` is available.

Input JSON (minimal):
{
  "vars": [ { "name": "x", "lo": 0.0, "hi": 1.0 }, ... ],
  "formula": { ... }   // see `parse_formula`
  "config": { "precision": 0.001 }
}

Expression nodes:
  {"kind":"var","name":"x"}
  {"kind":"const","value": 1.0}
  {"kind":"add","children":[E1,E2,...]}
  {"kind":"mul","children":[E1,E2,...]}
  {"kind":"neg","child":E}
  {"kind":"pow","base":E,"exp":2}

Formula nodes:
  {"kind":"and","children":[F1,F2,...]}
  {"kind":"or","children":[F1,F2,...]}
  {"kind":"not","child":F}
  {"kind":"cmp","op":"<=","lhs":E,"rhs":E}   # op in {"<","<=","=","==",">=",">"}
"""

import argparse
import json
import time
from pathlib import Path


def _expect_dict(x, ctx):
    if not isinstance(x, dict):
        raise ValueError(f"{ctx}: expected object")
    return x


def _expect_list(x, ctx):
    if not isinstance(x, list):
        raise ValueError(f"{ctx}: expected array")
    return x


def _expect_str(x, ctx):
    if not isinstance(x, str):
        raise ValueError(f"{ctx}: expected string")
    return x


def _expect_num(x, ctx):
    if not isinstance(x, (int, float)):
        raise ValueError(f"{ctx}: expected number")
    return float(x)


def parse_expr(node, var_map):
    node = _expect_dict(node, "expr")
    kind = _expect_str(node.get("kind", None), "expr.kind")

    if kind == "var":
        name = _expect_str(node.get("name", None), "expr.var.name")
        if name not in var_map:
            raise ValueError(f"expr.var: unknown variable '{name}'")
        return var_map[name]

    if kind == "const":
        return _expect_num(node.get("value", None), "expr.const.value")

    if kind == "add":
        xs = _expect_list(node.get("children", None), "expr.add.children")
        if not xs:
            return 0.0
        acc = 0.0
        for ch in xs:
            acc = acc + parse_expr(ch, var_map)
        return acc

    if kind == "mul":
        xs = _expect_list(node.get("children", None), "expr.mul.children")
        if not xs:
            return 1.0
        acc = 1.0
        for ch in xs:
            acc = acc * parse_expr(ch, var_map)
        return acc

    if kind == "neg":
        ch = node.get("child", None)
        return -parse_expr(ch, var_map)

    if kind == "pow":
        base = parse_expr(node.get("base", None), var_map)
        exp = node.get("exp", None)
        if not isinstance(exp, int) or exp < 0:
            raise ValueError("expr.pow.exp: expected nonnegative integer")
        return base ** exp

    raise ValueError(f"expr: unsupported kind '{kind}'")


def parse_formula(node, var_map):
    node = _expect_dict(node, "formula")
    kind = _expect_str(node.get("kind", None), "formula.kind")

    if kind == "and":
        xs = _expect_list(node.get("children", None), "formula.and.children")
        if not xs:
            from dreal import True_ as DTrue

            return DTrue()
        from dreal import And

        return And(*[parse_formula(ch, var_map) for ch in xs])

    if kind == "or":
        xs = _expect_list(node.get("children", None), "formula.or.children")
        if not xs:
            from dreal import False_ as DFalse

            return DFalse()
        from dreal import Or

        return Or(*[parse_formula(ch, var_map) for ch in xs])

    if kind == "not":
        ch = node.get("child", None)
        from dreal import Not

        return Not(parse_formula(ch, var_map))

    if kind == "cmp":
        op = _expect_str(node.get("op", None), "formula.cmp.op")
        lhs = parse_expr(node.get("lhs", None), var_map)
        rhs = parse_expr(node.get("rhs", None), var_map)
        if op == "<":
            return lhs < rhs
        if op == "<=":
            return lhs <= rhs
        if op in ("=", "=="):
            return lhs == rhs
        if op == ">=":
            return lhs >= rhs
        if op == ">":
            return lhs > rhs
        raise ValueError(f"formula.cmp.op: unsupported op '{op}'")

    raise ValueError(f"formula: unsupported kind '{kind}'")


def solve(problem):
    problem = _expect_dict(problem, "problem")
    vars_ = _expect_list(problem.get("vars", None), "problem.vars")

    # Build dReal variables.
    from dreal import Variable

    var_map = {}
    bounds = []
    for i, v in enumerate(vars_):
        v = _expect_dict(v, f"vars[{i}]")
        name = _expect_str(v.get("name", None), f"vars[{i}].name")
        lo = _expect_num(v.get("lo", None), f"vars[{i}].lo")
        hi = _expect_num(v.get("hi", None), f"vars[{i}].hi")
        if lo > hi:
            raise ValueError(f"vars[{i}]: lo > hi")
        x = Variable(name)
        var_map[name] = x
        bounds.append((name, x, lo, hi))

    # Config.
    prec = 1e-3
    cfg_in = problem.get("config", {})
    if isinstance(cfg_in, dict) and "precision" in cfg_in:
        prec = float(cfg_in["precision"])

    from dreal import And, Config, CheckSatisfiability

    cfg = Config()
    cfg.precision = float(prec)

    dom = And(*[And(x >= lo, x <= hi) for (_, x, lo, hi) in bounds]) if bounds else None
    phi = parse_formula(problem.get("formula", None), var_map)
    query = And(dom, phi) if dom is not None else phi

    t0 = time.time()
    try:
        res = CheckSatisfiability(query, cfg)
    except Exception as e:
        return {
            "status": "error",
            "backend": "dreal4",
            "precision": float(prec),
            "message": f"dreal exception: {type(e).__name__}: {e}",
            "elapsed_ms": int(1000 * (time.time() - t0)),
        }

    out = {
        "backend": "dreal4",
        "precision": float(prec),
        "elapsed_ms": int(1000 * (time.time() - t0)),
    }
    if res is None:
        out["status"] = "unsat"
        out["model"] = None
        return out

    model = {}
    for name, x, _, _ in bounds:
        iv = res[x]
        model[name] = {"lb": float(iv.lb()), "ub": float(iv.ub()), "mid": float(iv.mid())}
    out["status"] = "sat"
    out["model"] = model
    return out


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--in", dest="inp", required=True, help="Input problem JSON.")
    ap.add_argument("--out", dest="out", default="", help="Optional output path (writes JSON).")
    args = ap.parse_args()

    problem = json.loads(Path(args.inp).read_text(encoding="utf-8"))
    result = solve(problem)
    out_s = json.dumps(result, indent=2, sort_keys=True) + "\n"

    # JSON to stdout (for Lean wrapper parsing).
    print(out_s, end="")

    if args.out:
        Path(args.out).parent.mkdir(parents=True, exist_ok=True)
        Path(args.out).write_text(out_s, encoding="utf-8")


if __name__ == "__main__":
    main()
