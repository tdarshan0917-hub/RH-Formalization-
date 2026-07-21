import RHFormalization.PerSpikeTailBound
import Mathlib

/-!
# BTailSummedBound — C3: the summed B-tail integrand bound

ROUTE CARD
1. Target: define `bTailMass n := Σ_{q active} ‖w(q)‖·e^{−a_q/2}` and prove
   ‖galBIntegrand n s t‖ ≤ bTailMass n · e^{−Re(s)t}/√(4πt) for t > 0.
   Triangle inequality over the finite spike set + C2 per term.
   Per-spike: ‖w(q)‖·e^{−a_q/2} = (Λ(q)/√q)·q^{−1/2} = Λ(q)/q — the
   SUMMABLE weight; bTailMass grows only like Mertens (~ admR n).
2. Consumer: C4 (t-integrated B-tail bound on Re s > 0, explicit growth)
   → the cancellation confrontation with mainTermIntegral's tail.
3. Raw B on Ω? NO — Re s > 0 integrand bound. hstar hypothesis? NONE.
-/

set_option autoImplicit false

namespace RHFormalization

noncomputable section

open Complex MeasureTheory Set
open scoped BigOperators

/-- The tail mass: spike weights with the AM–GM center decay. -/
def bTailMass (n : ℕ) : ℝ :=
  ∑ q ∈ activePrimePowerPairsCenterBelow (admR n),
    ‖q.weightC‖ * Real.exp (-(q.center / 2))

theorem bTailMass_nonneg (n : ℕ) : 0 ≤ bTailMass n := by
  unfold bTailMass
  apply Finset.sum_nonneg
  intro q _
  positivity

/-- **C3: the summed B-tail integrand bound** (t > 0, every s, every n). -/
theorem galBIntegrand_norm_le_tailMass (n : ℕ) (s : ℂ) (t : ℝ) (ht : 0 < t) :
    ‖galBIntegrand n s t‖
      ≤ bTailMass n * (Real.exp (-s.re * t) * (1 / Real.sqrt (4 * Real.pi * t))) := by
  unfold galBIntegrand bTailMass
  calc ‖∑ q ∈ activePrimePowerPairsCenterBelow (admR n),
        q.weightC * shiftedHeatIntegrand q.center s t‖
      ≤ ∑ q ∈ activePrimePowerPairsCenterBelow (admR n),
          ‖q.weightC * shiftedHeatIntegrand q.center s t‖ :=
        norm_sum_le _ _
    _ ≤ ∑ q ∈ activePrimePowerPairsCenterBelow (admR n),
          ‖q.weightC‖ * Real.exp (-(q.center / 2))
            * (Real.exp (-s.re * t) * (1 / Real.sqrt (4 * Real.pi * t))) := by
        apply Finset.sum_le_sum
        intro q _
        rw [norm_mul]
        have hC2 := shiftedHeatIntegrand_norm_le_center_decay
          q.center (center_nonneg q) s t ht
        have hw : (0:ℝ) ≤ ‖q.weightC‖ := norm_nonneg _
        calc ‖q.weightC‖ * ‖shiftedHeatIntegrand q.center s t‖
            ≤ ‖q.weightC‖ * (Real.exp (-s.re * t) * Real.exp (-(q.center / 2))
                * (1 / Real.sqrt (4 * Real.pi * t))) :=
              mul_le_mul_of_nonneg_left hC2 hw
          _ = ‖q.weightC‖ * Real.exp (-(q.center / 2))
                * (Real.exp (-s.re * t) * (1 / Real.sqrt (4 * Real.pi * t))) := by
              ring
    _ = (∑ q ∈ activePrimePowerPairsCenterBelow (admR n),
          ‖q.weightC‖ * Real.exp (-(q.center / 2)))
        * (Real.exp (-s.re * t) * (1 / Real.sqrt (4 * Real.pi * t))) := by
        rw [← Finset.sum_mul]

#print axioms bTailMass
#print axioms bTailMass_nonneg
#print axioms galBIntegrand_norm_le_tailMass

end

end RHFormalization
