-- SENTINEL: dmr-rstage-halfplane-bound-v1
import RHFormalization.DMRBTailHalfplaneBound
import RHFormalization.GalerkinTailSplit
import RHFormalization.GalerkinHeadNormalFamily
import RHFormalization.GalerkinFTailBound
import Mathlib

/-! # Step 2b: R_stage uniformly bounded on half-plane compacts (hypothesis-free).
`R = head + (Ftail − Btail)` with head (banked normal family), Ftail (banked),
Btail (step 2a). The overlap leg of D.MR.2 for the concrete stage. -/

set_option autoImplicit false

namespace RHFormalization

noncomputable section

open Complex MeasureTheory Set
open scoped BigOperators Classical

/-- Half-plane sets sit inside Ω. -/
theorem halfplane_subset_Omega (σ : ℝ) (hσ : 0 < σ) (K : Set ℂ)
    (hKσ : ∀ s ∈ K, σ ≤ s.re) : K ⊆ Ω := by
  intro s hs
  rw [mem_Omega_iff]
  intro ⟨_, hre⟩
  have := hKσ s hs
  linarith

/-- The B-integrand tail integral IS the canonical package tail. -/
theorem galB_tail_eq_canonicalPackageTail (n : ℕ) (s : ℂ) (hs : 0 < s.re) :
    (∫ t in Ioi spikeT0, galBIntegrand n s t)
      = canonicalPackageTail (activePrimePowerPairsCenterBelow (admR n))
          spikeT0 s := by
  unfold galBIntegrand canonicalPackageTail kernelTailPart
  rw [integral_finset_sum]
  · refine Finset.sum_congr rfl (fun q _ => ?_)
    rw [integral_const_mul]
  · intro q _
    exact ((shiftedHeatIntegrand_integrableOn q.center s hs).mono_set
      (Ioi_subset_Ioi spikeT0_pos.le)).const_mul _

/-- B-integrand tail integrability. -/
theorem galB_tail_integrableOn (n : ℕ) (s : ℂ) (hs : 0 < s.re) :
    IntegrableOn (fun t : ℝ => galBIntegrand n s t) (Ioi spikeT0) volume := by
  unfold galBIntegrand
  apply integrable_finset_sum
  intro q _
  exact ((shiftedHeatIntegrand_integrableOn q.center s hs).mono_set
    (Ioi_subset_Ioi spikeT0_pos.le)).const_mul _

/-- The R-tail splits: `galTail = Ftail − Btail`. -/
theorem galTail_eq_Ftail_sub_Btail (n : ℕ) (s : ℂ) (hs : 0 < s.re) :
    galTail n s
      = (∫ t in Ioi spikeT0, galFIntegrand n s t)
        - canonicalPackageTail (activePrimePowerPairsCenterBelow (admR n))
            spikeT0 s := by
  have hB := galB_tail_integrableOn n s hs
  have hQ := galQRes_integrableOn_tail n s hs
  have hFeq : (fun t : ℝ => galFIntegrand n s t)
      = fun t : ℝ => galQResIntegrand n s t + galBIntegrand n s t := by
    funext t
    unfold galQResIntegrand
    ring
  have hF : IntegrableOn (fun t : ℝ => galFIntegrand n s t)
      (Ioi spikeT0) volume := by
    rw [hFeq]
    exact hQ.add hB
  unfold galTail galQResIntegrand
  rw [integral_sub hF hB, galB_tail_eq_canonicalPackageTail n s hs]

/-- **STEP 2b: R_stage bounded on half-plane compacts, uniform in n.** -/
theorem R_stage_uniform_bound_on_halfplane (σ : ℝ) (hσ : 0 < σ)
    (K : Set ℂ) (hK : IsCompact K) (hne : K.Nonempty)
    (hKσ : ∀ s ∈ K, σ ≤ s.re) :
    ∃ C : ℝ, ∀ n : ℕ, ∀ s ∈ K,
      ‖galerkinStagePackage.R_stage (admissibleGalerkinStageSeq n) s‖ ≤ C := by
  have hKO : K ⊆ Ω := halfplane_subset_Omega σ hσ K hKσ
  obtain ⟨_, Chead, hChead0, hChead⟩ := galHead_normal_family K hK hne
  obtain ⟨CF, hCF0, hCF⟩ := galF_tail_uniform_bound K hK hKO hne
  obtain ⟨CB, hCB⟩ := canonicalPackageTail_uniform_bound_on_halfplane
    σ hσ spikeT0 spikeT0_pos K hKσ
  refine ⟨Chead + CF + CB, fun n s hs => ?_⟩
  have hs0 : (0:ℝ) < s.re := lt_of_lt_of_le hσ (hKσ s hs)
  rw [R_stage_eq_head_add_tail n s hs0,
    galTail_eq_Ftail_sub_Btail n s hs0]
  calc ‖galHead n s
        + ((∫ t in Ioi spikeT0, galFIntegrand n s t)
            - canonicalPackageTail
                (activePrimePowerPairsCenterBelow (admR n)) spikeT0 s)‖
      ≤ ‖galHead n s‖
        + ‖(∫ t in Ioi spikeT0, galFIntegrand n s t)
            - canonicalPackageTail
                (activePrimePowerPairsCenterBelow (admR n)) spikeT0 s‖ :=
        norm_add_le _ _
    _ ≤ ‖galHead n s‖
        + (‖∫ t in Ioi spikeT0, galFIntegrand n s t‖
            + ‖canonicalPackageTail
                (activePrimePowerPairsCenterBelow (admR n)) spikeT0 s‖) := by
        have := norm_sub_le
          (∫ t in Ioi spikeT0, galFIntegrand n s t)
          (canonicalPackageTail
            (activePrimePowerPairsCenterBelow (admR n)) spikeT0 s)
        linarith
    _ ≤ Chead + (CF + CB) := by
        have h1 := hChead n s hs
        have h2 := hCF n s hs hs0
        have h3 := hCB n s hs
        linarith
    _ = Chead + CF + CB := by ring

#print axioms galB_tail_eq_canonicalPackageTail
#print axioms galTail_eq_Ftail_sub_Btail
#print axioms R_stage_uniform_bound_on_halfplane

end

end RHFormalization
