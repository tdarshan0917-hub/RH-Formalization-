import RHFormalization.SeamCoreForm
import RHFormalization.DecodedWindowCorrectionBound
import Mathlib

/-!
# SeamCoreFactoredForm — P2-4b: seamCore over the common prefactor

ROUTE CARD
1. Target: EXACT identity
   `seamCore n s = invSqrtFactor s * (seamArithmeticSum n s − seamMainTerm n s)`
   — the prime exponential sum vs. the D.OP.1 main term, common (2w)⁻¹
   prefactor extracted. Pure algebra over kernel_eq_prefactor_mul_exp +
   the compensatorM definition. No bound asserted.
2. Raw B on Ω? NO. B−M bare Prop? NO.
3. Consumer: P2-4c (ε control of the bracket via D.BFF) →
   correctedResidual_locbdd_of_seamCore → provider → HtailExists.
-/

set_option autoImplicit false

namespace RHFormalization

noncomputable section

open Complex
open scoped BigOperators

/-- The seam's arithmetic side: prime-power exponential sum at cutoff. -/
def seamArithmeticSum (n : ℕ) (s : ℂ) : ℂ :=
  ∑ q ∈ activePrimePowerPairsCenterBelow (admR n),
    q.weightC * Complex.exp (-(Complex.sqrt (s + (1/4:ℂ))) * (q.center : ℝ))

/-- The seam's main term: the D.OP.1 compensator bracket. -/
def seamMainTerm (n : ℕ) (s : ℂ) : ℂ :=
  Complex.exp (((1/2:ℂ) - Complex.sqrt (s + (1/4:ℂ))) * (admR n : ℝ))
    / ((1/2:ℂ) - Complex.sqrt (s + (1/4:ℂ)))

/-- **P2-4b: the factored seam identity.** -/
theorem seamCore_eq_prefactor_mul_bracket (n : ℕ) (s : ℂ) :
    seamCore n s
      = invSqrtFactor s * (seamArithmeticSum n s - seamMainTerm n s) := by
  unfold seamCore seamArithmeticSum seamMainTerm compensatorM
    finiteCanonicalPrimePowerPackage
  have hker : ∀ q ∈ activePrimePowerPairsCenterBelow (admR n),
      q.weightC * shiftedLaplaceHeatKernelC q.center s
        = invSqrtFactor s
          * (q.weightC
            * Complex.exp (-(Complex.sqrt (s + (1/4:ℂ))) * (q.center : ℝ))) := by
    intro q _
    rw [kernel_eq_prefactor_mul_exp q.center s]
    ring
  rw [Finset.sum_congr rfl hker, ← Finset.mul_sum]
  first
    | (unfold invSqrtFactor; ring)
    | ring
    | (rw [mul_sub]; unfold invSqrtFactor; ring)
    | (rw [mul_sub]; ring)

#print axioms seamArithmeticSum
#print axioms seamMainTerm
#print axioms seamCore_eq_prefactor_mul_bracket

end

end RHFormalization
