import Mathlib
import RHFormalization.AdmissibleGalerkinStage
set_option autoImplicit false
open ArithmeticFunction Finset Real

namespace RHFormalization

/-- **S1 — Chebyshev bound on the unweighted von Mangoldt partial sum.**
The sum `∑_{k ≤ e^{admR n}} Λ(k)` equals Mathlib's Chebyshev `ψ` at `e^{admR n}`
(same index set `Ioc 0 ⌊·⌋₊`, same `Λ`), hence is `≤ (log 4 + 4)·e^{admR n}`
by `Chebyshev.psi_le_const_mul_self`. This is the O(x) input feeding the Abel
transfer on the parabola strip. -/
theorem vonMangoldt_partialSum_le
    (n : ℕ) :
    ∑ k ∈ Finset.Ioc 0 ⌊Real.exp (admR n)⌋₊, (vonMangoldt k : ℝ)
      ≤ (Real.log 4 + 4) * Real.exp (admR n) := by
  -- the repo sum IS Chebyshev.psi at e^{admR n}, definitionally
  have hpsi : ∑ k ∈ Finset.Ioc 0 ⌊Real.exp (admR n)⌋₊, (vonMangoldt k : ℝ)
      = Chebyshev.psi (Real.exp (admR n)) := rfl
  rw [hpsi]
  exact Chebyshev.psi_le_const_mul_self (le_of_lt (Real.exp_pos _))

#print axioms vonMangoldt_partialSum_le

end RHFormalization
