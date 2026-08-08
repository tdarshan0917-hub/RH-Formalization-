import RHFormalization.ObstructionToRH
import RHFormalization.CompensatorDensityKernelForm
import RHFormalization.CanonicalTailObstructionBridge
import Mathlib

set_option autoImplicit false

namespace RHFormalization

noncomputable section

open Complex MeasureTheory

/-!
# ObstructionPairedForm — the strip object, exactly

On Re s > 0:
  obstruction = BcorrWin + pole + shortDensityGap + pairedTailGap,
  pairedTailGap := ∫₀^R e^{u/2}·Ktail(u,t₀,s)du − galBTail n s
— density vs point masses of ONE smoothed kernel. Exact; no estimates.
Every subsequent lemma is a sublemma of bounding these four terms on
strip compacts. (BcorrWin: banked. pole: elementary. The two gaps: the
live mathematics.)
-/

/-- The tail-kernel density leg. -/
noncomputable def tailDensityLeg (n : ℕ) (s : ℂ) : ℂ :=
  ∫ u in (0:ℝ)..(admR n),
    Complex.exp ((u:ℂ)/2) * kernelTailPart u spikeT0 s

/-- **THE STRIP OBJECT**: density minus point masses of the tail kernel. -/
noncomputable def pairedTailGap (n : ℕ) (s : ℂ) : ℂ :=
  tailDensityLeg n s - galBTail n s

/-- The short-kernel density gap (full-kernel leg minus tail leg). -/
noncomputable def shortDensityGap (n : ℕ) (s : ℂ) : ℂ :=
  (∫ u in (0:ℝ)..(admR n),
    Complex.exp ((u:ℂ)/2) * shiftedLaplaceHeatKernelC u s)
  - tailDensityLeg n s

/-- **THE PAIRED FORM** (exact, Re s > 0). -/
theorem obstruction_eq_paired_form (n : ℕ) (s : ℂ) (hs : 0 < s.re) :
    canonicalTailObstruction n s
      = BcorrWin n s + compensatorPole s
        + shortDensityGap n s + pairedTailGap n s := by
  have hsΩ : s ∈ Ω := by
    have h := halfplane_subset_Omega s.re hs {s}
      (fun t ht => by rw [Set.mem_singleton_iff] at ht; rw [ht])
    exact h (Set.mem_singleton s)
  rw [canonicalTailObstruction_eq_Bcorr_sub_Btail n s hs]
  unfold Bcorr
  rw [compensatorM_eq_densityKernelIntegral_add_pole n hsΩ]
  unfold shortDensityGap pairedTailGap
  ring

#print axioms tailDensityLeg
#print axioms pairedTailGap
#print axioms obstruction_eq_paired_form

end

end RHFormalization
