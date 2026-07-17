import Mathlib.NumberTheory.LSeries.Dirichlet
import Mathlib.NumberTheory.VonMangoldt

/-!
# RHFormalization.PrimePowerSumConvergence
**Prime-side brick 1: convergence.** The von Mangoldt L-series
`L ↗Λ s = ∑' n, Λ(n)/n^s` converges for `Re s > 1` (Mathlib).
This file restates that summability in a form usable by the prime-power package,
and records the `−ζ'/ζ` identity. No `sorry`.
-/

set_option autoImplicit false

namespace RHFormalization

open ArithmeticFunction Complex

/-- The von Mangoldt L-series is summable for `Re s > 1` (Mathlib floor). -/
theorem vonMangoldt_LSeriesSummable {s : ℂ} (hs : 1 < s.re) :
    LSeriesSummable (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) s :=
  ArithmeticFunction.LSeriesSummable_vonMangoldt hs

/-- Termwise: the `n`-th L-series term of `Λ` is `Λ(n) / n^s` for `n ≠ 0`. -/
theorem vonMangoldt_term_eq {s : ℂ} {n : ℕ} (hn : n ≠ 0) :
    LSeries.term (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) s n
      = (ArithmeticFunction.vonMangoldt n : ℂ) / (n : ℂ) ^ s := by
  rw [LSeries.term_of_ne_zero hn]

/-- The von Mangoldt L-series equals `−ζ'/ζ` for `Re s > 1` (Mathlib floor). -/
theorem vonMangoldt_LSeries_eq_logDeriv_zeta {s : ℂ} (hs : 1 < s.re) :
    LSeries (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) s
      = - deriv riemannZeta s / riemannZeta s :=
  ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div hs

#print axioms vonMangoldt_LSeriesSummable
#print axioms vonMangoldt_LSeries_eq_logDeriv_zeta

end RHFormalization
