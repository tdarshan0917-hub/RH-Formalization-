import Lake
open Lake DSL

package «RHFormalization» where

-- PNT+ fork, branch rh-von-koch (von Koch's theorem); Mathlib comes transitively at PNT+'s pin.
require PrimeNumberTheoremAnd from git
  "https://github.com/tdarshan0917-hub/PrimeNumberTheoremAnd.git" @ "3bec220c090bee68d0a13d46c934aecd32d02abb"

@[default_target]
lean_lib RHFormalization where
