import Lake
open Lake DSL

package «SemiAlgebraic» where

require mathlib from git
  "https://github.com/leanprover-community/mathlib4" @ "v4.24.0"

-- Pin auxiliary libraries for reproducibility (matching Mathlib v4.24.0).
require batteries from git
  "https://github.com/leanprover-community/batteries" @ "8da40b72fece29b7d3fe3d768bac4c8910ce9bee"

@[default_target]
lean_lib «SemiAlgebraic» where

-- Executables for constraint solving and verification
lean_exe cad_solve where
  root := `SemiAlgebraic.CLI.SolveMain

lean_exe cad_certify where
  root := `SemiAlgebraic.CLI.CertifyMain

lean_exe cad_verify where
  root := `SemiAlgebraic.CLI.VerifyMain
