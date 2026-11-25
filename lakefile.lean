import Lake
open Lake DSL

package «RHFormalization» where

-- PNT+ (local branch rh-von-koch) supplies von Koch; Mathlib comes transitively at PNT+'s pin.
require PrimeNumberTheoremAnd from "../PrimeNumberTheoremAnd"

@[default_target]
lean_lib RHFormalization where
