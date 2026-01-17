/-!
# SemiAlgebraic

Verified constraint solving for quantifier-free real polynomial constraints.

## Core Modules

- `SemiAlgebraic.Computational.RealConstraints.IR`: Expression and formula AST with JSON parsing
- `SemiAlgebraic.Computational.RealConstraints.Cert`: SAT witness certificates and verification
- `SemiAlgebraic.Computational.RealConstraints.Unsat`: Restricted UNSAT pattern checker
- `SemiAlgebraic.Computational.RealConstraints.UnsatInterval`: Interval partition UNSAT certificates
- `SemiAlgebraic.Computational.RealConstraints.RatCheck`: Exact rational witness checking

## Utility Modules

- `SemiAlgebraic.Util.JCS`: RFC 8785 JSON Canonicalization Scheme
- `SemiAlgebraic.Util.SHA`: Pure Lean SHA-256 implementation

## CLI Executables

- `cad_solve`: dReal/Z3/Yices-backed solver bridge
- `cad_certify`: Produces verified certificates for SAT/UNSAT
- `cad_verify`: Offline certificate verifier
-/

import SemiAlgebraic.Computational.RealConstraints.IR
import SemiAlgebraic.Computational.RealConstraints.Cert
import SemiAlgebraic.Computational.RealConstraints.Unsat
import SemiAlgebraic.Computational.RealConstraints.UnsatInterval
import SemiAlgebraic.Computational.RealConstraints.RatCheck
import SemiAlgebraic.Util.JCS
import SemiAlgebraic.Util.SHA
import SemiAlgebraic.CLI.SolveMain
import SemiAlgebraic.CLI.CertifyMain
import SemiAlgebraic.CLI.VerifyMain
