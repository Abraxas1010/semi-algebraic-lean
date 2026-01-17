// SemiAlgebraic declaration data for UMAP visualizations
// Generated from SemiAlgebraic.* modules

const semialgebraicProofsData = {
  items: [
    // Computational/RealConstraints/IR.lean - Core types
    { name: "VarDecl", kind: "structure", family: "Core/IR", pos: { x: 0.15, y: 0.75, z: 0.2 } },
    { name: "Expr", kind: "inductive", family: "Core/IR", pos: { x: 0.18, y: 0.72, z: 0.25 } },
    { name: "CmpOp", kind: "inductive", family: "Core/IR", pos: { x: 0.12, y: 0.78, z: 0.18 } },
    { name: "Formula", kind: "inductive", family: "Core/IR", pos: { x: 0.20, y: 0.70, z: 0.22 } },
    { name: "Problem", kind: "structure", family: "Core/IR", pos: { x: 0.22, y: 0.68, z: 0.28 } },
    { name: "Env", kind: "abbrev", family: "Core/IR", pos: { x: 0.16, y: 0.80, z: 0.15 } },
    { name: "Expr.eval", kind: "def", family: "Core/IR", pos: { x: 0.25, y: 0.65, z: 0.30 } },
    { name: "Formula.eval", kind: "def", family: "Core/IR", pos: { x: 0.28, y: 0.62, z: 0.32 } },
    { name: "VarDecl.ofJson", kind: "def", family: "Core/IR", pos: { x: 0.10, y: 0.82, z: 0.12 } },
    { name: "Expr.ofJson", kind: "def", family: "Core/IR", pos: { x: 0.13, y: 0.85, z: 0.10 } },
    { name: "Formula.ofJson", kind: "def", family: "Core/IR", pos: { x: 0.08, y: 0.88, z: 0.08 } },
    { name: "Problem.ofJson", kind: "def", family: "Core/IR", pos: { x: 0.06, y: 0.90, z: 0.05 } },
    { name: "Problem.parseString", kind: "def", family: "Core/IR", pos: { x: 0.04, y: 0.92, z: 0.03 } },

    // Computational/RealConstraints/Cert.lean - SAT verification
    { name: "checkBounds", kind: "def", family: "SAT/Cert", pos: { x: 0.45, y: 0.55, z: 0.50 } },
    { name: "checkSatWitness", kind: "def", family: "SAT/Cert", pos: { x: 0.48, y: 0.52, z: 0.55 } },
    { name: "envOfJsonObj", kind: "def", family: "SAT/Cert", pos: { x: 0.42, y: 0.58, z: 0.45 } },
    { name: "jsonOfFloat", kind: "def", family: "SAT/Cert", pos: { x: 0.40, y: 0.60, z: 0.42 } },

    // Computational/RealConstraints/Unsat.lean - UNSAT patterns
    { name: "UnsatReason", kind: "inductive", family: "UNSAT/Pattern", pos: { x: 0.70, y: 0.35, z: 0.65 } },
    { name: "tryCertify", kind: "def", family: "UNSAT/Pattern", pos: { x: 0.75, y: 0.30, z: 0.70 } },
    { name: "verifyReason", kind: "def", family: "UNSAT/Pattern", pos: { x: 0.78, y: 0.28, z: 0.72 } },
    { name: "UnsatReason.toJson", kind: "def", family: "UNSAT/Pattern", pos: { x: 0.72, y: 0.38, z: 0.62 } },
    { name: "UnsatReason.ofJson", kind: "def", family: "UNSAT/Pattern", pos: { x: 0.68, y: 0.40, z: 0.60 } },

    // Computational/RealConstraints/UnsatInterval.lean - Interval trees
    { name: "Tri", kind: "inductive", family: "UNSAT/Interval", pos: { x: 0.82, y: 0.20, z: 0.80 } },
    { name: "Interval", kind: "structure", family: "UNSAT/Interval", pos: { x: 0.85, y: 0.18, z: 0.82 } },
    { name: "CertTree", kind: "inductive", family: "UNSAT/Interval", pos: { x: 0.88, y: 0.15, z: 0.85 } },
    { name: "RatIR.Expr", kind: "inductive", family: "UNSAT/Interval", pos: { x: 0.80, y: 0.22, z: 0.78 } },
    { name: "RatIR.Formula", kind: "inductive", family: "UNSAT/Interval", pos: { x: 0.78, y: 0.25, z: 0.75 } },
    { name: "RatIR.Problem", kind: "structure", family: "UNSAT/Interval", pos: { x: 0.76, y: 0.28, z: 0.73 } },
    { name: "Interval.evalExpr", kind: "def", family: "UNSAT/Interval", pos: { x: 0.90, y: 0.12, z: 0.88 } },
    { name: "Formula.evalTri", kind: "def", family: "UNSAT/Interval", pos: { x: 0.92, y: 0.10, z: 0.90 } },
    { name: "tryCertify", kind: "def", family: "UNSAT/Interval", pos: { x: 0.95, y: 0.08, z: 0.92 } },
    { name: "verify", kind: "def", family: "UNSAT/Interval", pos: { x: 0.93, y: 0.05, z: 0.95 } },
    { name: "CertTree.toJson", kind: "def", family: "UNSAT/Interval", pos: { x: 0.86, y: 0.16, z: 0.84 } },
    { name: "CertTree.ofJson", kind: "def", family: "UNSAT/Interval", pos: { x: 0.84, y: 0.19, z: 0.81 } },

    // Computational/RealConstraints/RatCheck.lean - Exact checking
    { name: "RatEnv", kind: "abbrev", family: "SAT/Exact", pos: { x: 0.55, y: 0.45, z: 0.55 } },
    { name: "ratOfJson", kind: "def", family: "SAT/Exact", pos: { x: 0.58, y: 0.42, z: 0.58 } },
    { name: "envOfJsonObj", kind: "def", family: "SAT/Exact", pos: { x: 0.52, y: 0.48, z: 0.52 } },
    { name: "checkSatWitnessExact", kind: "def", family: "SAT/Exact", pos: { x: 0.60, y: 0.40, z: 0.60 } },

    // Util/JCS.lean - JSON Canonicalization
    { name: "utf16Units", kind: "def", family: "Util/JCS", pos: { x: 0.30, y: 0.85, z: 0.35 } },
    { name: "compareUtf16", kind: "def", family: "Util/JCS", pos: { x: 0.32, y: 0.82, z: 0.38 } },
    { name: "renderString", kind: "def", family: "Util/JCS", pos: { x: 0.35, y: 0.80, z: 0.40 } },
    { name: "renderJsonNumber", kind: "def", family: "Util/JCS", pos: { x: 0.38, y: 0.78, z: 0.42 } },
    { name: "canonicalString", kind: "def", family: "Util/JCS", pos: { x: 0.40, y: 0.75, z: 0.45 } },

    // Util/SHA.lean - SHA-256
    { name: "SHA256.rotr", kind: "def", family: "Util/SHA", pos: { x: 0.25, y: 0.90, z: 0.30 } },
    { name: "SHA256.k", kind: "def", family: "Util/SHA", pos: { x: 0.22, y: 0.92, z: 0.28 } },
    { name: "SHA256.h0", kind: "def", family: "Util/SHA", pos: { x: 0.20, y: 0.94, z: 0.25 } },
    { name: "SHA256.pad", kind: "def", family: "Util/SHA", pos: { x: 0.28, y: 0.88, z: 0.32 } },
    { name: "SHA256.processChunk", kind: "def", family: "Util/SHA", pos: { x: 0.30, y: 0.86, z: 0.35 } },
    { name: "sha256Bytes", kind: "def", family: "Util/SHA", pos: { x: 0.32, y: 0.84, z: 0.38 } },
    { name: "sha256Hex", kind: "def", family: "Util/SHA", pos: { x: 0.35, y: 0.82, z: 0.40 } },
    { name: "sha256HexOfStringIO", kind: "def", family: "Util/SHA", pos: { x: 0.38, y: 0.80, z: 0.42 } },
    { name: "sha256HexOfFileIO", kind: "def", family: "Util/SHA", pos: { x: 0.40, y: 0.78, z: 0.45 } },

    // CLI/SolveMain.lean
    { name: "SolveMain.main", kind: "def", family: "CLI", pos: { x: 0.50, y: 0.15, z: 0.50 } },
    { name: "runDRealDocker", kind: "def", family: "CLI", pos: { x: 0.48, y: 0.18, z: 0.48 } },
    { name: "runSMTDocker", kind: "def", family: "CLI", pos: { x: 0.52, y: 0.12, z: 0.52 } },

    // CLI/CertifyMain.lean
    { name: "CertifyMain.main", kind: "def", family: "CLI", pos: { x: 0.55, y: 0.10, z: 0.55 } },
    { name: "witnessEnvOfModel", kind: "def", family: "CLI", pos: { x: 0.58, y: 0.08, z: 0.58 } },

    // CLI/VerifyMain.lean
    { name: "VerifyMain.main", kind: "def", family: "CLI", pos: { x: 0.62, y: 0.05, z: 0.62 } },
  ],
  edges: [
    // IR dependencies
    [4, 0], [4, 1], [4, 3], // Problem uses VarDecl, Expr, Formula
    [3, 1], [3, 2], // Formula uses Expr, CmpOp
    [7, 6], // Formula.eval uses Expr.eval
    [11, 9], [11, 10], // Problem.ofJson uses VarDecl/Expr/Formula.ofJson

    // Cert depends on IR
    [14, 4], [15, 4], // checkSatWitness uses Problem

    // Unsat depends on IR
    [19, 4], [20, 18], // tryCertify/verifyReason use Problem, UnsatReason

    // UnsatInterval depends on IR
    [31, 4], [32, 25], // tryCertify/verify use Problem, CertTree

    // RatCheck depends on UnsatInterval
    [38, 27], // checkSatWitnessExact uses RatIR

    // JCS standalone
    [44, 40], [44, 41], [44, 42], [44, 43], // canonicalString uses helpers

    // SHA standalone
    [52, 49], [52, 50], [53, 52], // sha256Hex uses sha256Bytes

    // CLI uses everything
    [55, 4], [55, 6], // SolveMain uses Problem, Expr.eval
    [59, 4], [59, 15], [59, 19], [59, 31], [59, 44], [59, 53], // CertifyMain uses many
    [61, 4], [61, 15], [61, 20], [61, 32], [61, 38], // VerifyMain uses many
  ]
};

// Module family colors matching Apoth3osis palette
const familyColors = {
  'Core/IR': '#3b82f6',        // blue-500
  'SAT/Cert': '#10b981',       // emerald-500
  'SAT/Exact': '#22d3d3',      // cyan
  'UNSAT/Pattern': '#f59e0b',  // amber-500
  'UNSAT/Interval': '#ef4444', // red-500
  'Util/JCS': '#8b5cf6',       // violet-500
  'Util/SHA': '#a855f7',       // purple-500
  'CLI': '#ec4899',            // pink-500
};
