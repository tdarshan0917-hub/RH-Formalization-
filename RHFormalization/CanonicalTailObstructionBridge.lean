import RHFormalization.CanonicalRcanTailReduction
import RHFormalization.GalerkinStieltjesRep
import RHFormalization.GalerkinFTailBound
import RHFormalization.BTailSummedBound
import RHFormalization.DMRSectorTimeSplit
import Mathlib

set_option autoImplicit false

namespace RHFormalization

noncomputable section

open Complex MeasureTheory

/-!
# CanonicalTailObstructionBridge — STEP 1: the obstruction IS the compensated B-tail
Exact identities on RHP(0). No estimates; the raw B-tail is never bounded here.
Consumer: STEP 2 window/bulk decomposition of Bcorr − galBTail.
-/

/-- The prime-side large-time tail (raw; never bounded directly). -/
noncomputable def galBTail (n : ℕ) (s : ℂ) : ℂ :=
  ∫ t in Set.Ioi spikeT0, galBIntegrand n s t

/-- B-integrand tail integrability: per-atom heat integrability restricted. -/
theorem galBIntegrand_integrableOn_tail (n : ℕ) (s : ℂ) (hs : 0 < s.re) :
    IntegrableOn (fun t => galBIntegrand n s t) (Set.Ioi spikeT0) := by
  unfold galBIntegrand
  apply integrable_finsetSum
  intro q hq
  exact ((shiftedHeatIntegrand_integrableOn q.center s hs).mono_set
    (Set.Ioi_subset_Ioi (le_of_lt spikeT0_pos))).const_mul _

/-- F-integrand tail integrability, by addition of banked QRes and B facts. -/
theorem galFIntegrand_integrableOn_tail (n : ℕ) (s : ℂ) (hs : 0 < s.re) :
    IntegrableOn (fun t => galFIntegrand n s t) (Set.Ioi spikeT0) := by
  have h := (galQRes_integrableOn_tail n s hs).add
    (galBIntegrand_integrableOn_tail n s hs)
  refine h.congr_fun (fun t _ => ?_) measurableSet_Ioi
  simp only [Pi.add_apply]
  unfold galQResIntegrand
  ring

/-- **STEP 1 ENDPOINT: the obstruction is the compensated B-tail** (exact). -/
theorem canonicalTailObstruction_eq_Bcorr_sub_Btail
    (n : ℕ) (s : ℂ) (hs : 0 < s.re) :
    canonicalTailObstruction n s = Bcorr n s - galBTail n s := by
  unfold canonicalTailObstruction
  rw [galTail_eq_Ftail_sub_Btail n s hs, ← galFTailClosed_eq_integral n s hs]
  have hBT : galBTail n s
      = canonicalPackageTail (activePrimePowerPairsCenterBelow (admR n)) spikeT0 s := by
    unfold galBTail canonicalPackageTail galBIntegrand
    have hint : ∀ q ∈ activePrimePowerPairsCenterBelow (admR n),
        IntegrableOn (fun t : ℝ => q.weightC * shiftedHeatIntegrand q.center s t)
          (Set.Ioi spikeT0) := by
      intro q hq
      exact ((shiftedHeatIntegrand_integrableOn q.center s hs).mono_set
        (Set.Ioi_subset_Ioi (le_of_lt spikeT0_pos))).const_mul _
    rw [MeasureTheory.integral_finsetSum _ hint]
    refine Finset.sum_congr rfl fun q hq => ?_
    rw [MeasureTheory.integral_const_mul]
    unfold kernelTailPart
    rfl
  linear_combination hBT

#print axioms galBTail
#print axioms galTail_eq_Ftail_sub_Btail
#print axioms canonicalTailObstruction_eq_Bcorr_sub_Btail

end

end RHFormalization
