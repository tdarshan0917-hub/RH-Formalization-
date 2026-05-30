import Mathlib
import RHFormalization.AppendixESharedCanonicalPackage

open Complex

#check Nat.Prime
#check Nat.factors
#check Nat.factorization
#check ArithmeticFunction.vonMangoldt
#check vonMangoldt
#check Real.log
#check Complex.exp
#check Complex.sqrt
#check ENat
#check Finset.sum
#check tsum
#check Summable

-- Candidate finite prime-power package shape:
#check fun (R : ℝ) (s : ℂ) =>
  ∑ n in Finset.range 10, (n : ℂ)

