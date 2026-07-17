import RHFormalization.GalerkinTailSplit
import RHFormalization.GalerkinFStageCompactBound
import RHFormalization.AdmissibleEigenvalueFloor
import RHFormalization.DTailUniformBound
import RHFormalization.DTailPerturbedTraceDomination
import RHFormalization.GalerkinFConvergence
import Mathlib

/-!
# GalerkinFTailBound — the F-sector of the tail `∫_{t₀}^∞`, uniformly in `n`

ROUTE CARD
1. Target: `‖∫ t in Ioi spikeT0, galFIntegrand n s t‖ ≤ C(K)` for `s ∈ K ⊆ Ω`
   compact, uniform in `n`.
2. Objects: `integral_cexp_neg_mul_Ioi_shift` (banked, GalerkinTailSplit) evaluates
   the tail in CLOSED FORM to the resolvent sum; `dTail_uniform_bound` (banked)
   bounds that sum; its `h_fk` slot is filled by `h_fk_perturbed_galerkin` (banked).
3. Raw B on Ω? NO. 4. R = F − raw B? NO. 5. True outright.
6. Manuscript: D.LOC-TAIL / D.TAIL-DENSITY (p179–180).
7. Consumer: `galTail` bound; thence `R_stage` local boundedness (D.MR.2).

DEFEQ NOTE. `h_fk_perturbed_galerkin` is stated with `galerkinLam`; `admPerturbedLam`
is defined with `galerkinFreeMu`. These are definitionally equal, so `exact` closes
`hfk_adm` — but `linarith` sees two distinct atoms. Always restate at
`admPerturbedLam` first (`hfk_adm`), then reason.

POSITIVITY NOTE. `positivity` cannot see `0 < admL n` (opaque application).
Use `admL_pos n` + `div_nonneg`/`linarith` explicitly.
-/

set_option autoImplicit false

namespace RHFormalization

open Complex MeasureTheory
open scoped BigOperators

/-- The perturbed eigenvalues are nonnegative. -/
theorem admPerturbedLam_nonneg (n : ℕ) (i : Fin (admN n)) :
    (0:ℝ) ≤ admPerturbedLam n i :=
  le_trans (admFreeEig_nonneg n i) (admFreeEig_le_admPerturbedLam n i)

/-- The shifted eigenvalues are nonnegative. -/
theorem admShiftedLam_nonneg' (n : ℕ) (i : Fin (admN n)) :
    (0:ℝ) ≤ admPerturbedLam n i + SupVConst := by
  have h1 := admPerturbedLam_nonneg n i
  have h2 := SupVConst_nonneg_adm
  linarith

/-- `h_fk`, restated at `admPerturbedLam` so downstream atoms match. -/
theorem hfk_adm (n : ℕ) (t : ℝ) (ht : 0 < t) :
    (1 / (2 * admL n)) * (∑ i : Fin (admN n), Real.exp (-t * admPerturbedLam n i))
      ≤ freeHeatDiagonal t := by
  have hL : 0 < admL n := admL_pos n
  exact h_fk_perturbed_galerkin (N := admN n)
    (activePrimePowerCodesCenterBelow (admR n)) (admL n) t hL ht
    (galerkinVC_isHermitian (N := admN n) 1
      (activePrimePowerCodesCenterBelow (admR n)) ppWeightReal (admL n))

/-- `h_fk` at the shifted eigenvalues (`SupVConst ≥ 0` shrinks each exponential). -/
theorem hfk_adm_shifted (n : ℕ) (t : ℝ) (ht : 0 < t) :
    (1 / (2 * admL n)) * (∑ i : Fin (admN n),
        Real.exp (-t * (admPerturbedLam n i + SupVConst)))
      ≤ freeHeatDiagonal t := by
  have hL : 0 < admL n := admL_pos n
  have hpre : (0:ℝ) ≤ 1 / (2 * admL n) := by
    apply div_nonneg zero_le_one; linarith
  refine le_trans ?_ (hfk_adm n t ht)
  refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun i _ => ?_)) hpre
  apply Real.exp_le_exp.mpr
  have h2 := SupVConst_nonneg_adm
  nlinarith [ht.le]

/-- **CLOSED-FORM EVALUATION OF THE F-TAIL.** On RHP(0). -/
theorem galF_tail_eq_resolvent_sum (n : ℕ) (s : ℂ) (hs : 0 < s.re) :
    (∫ t in Set.Ioi spikeT0, galFIntegrand n s t)
      = admDensityC n * ∑ i : Fin (admN n),
          Complex.exp (-(s + ((admPerturbedLam n i + SupVConst : ℝ) : ℂ)) * (spikeT0:ℂ))
            / (s + ((admPerturbedLam n i + SupVConst : ℝ) : ℂ)) := by
  have hre : ∀ i : Fin (admN n),
      0 < (s + ((admPerturbedLam n i + SupVConst : ℝ) : ℂ)).re := by
    intro i
    rw [Complex.add_re, Complex.ofReal_re]
    have := admShiftedLam_nonneg' n i; linarith
  have hint : ∀ i : Fin (admN n),
      IntegrableOn
        (fun t : ℝ => Complex.exp (-(s + ((admPerturbedLam n i + SupVConst : ℝ) : ℂ)) * (t:ℂ)))
        (Set.Ioi spikeT0) := fun i =>
    (galF_summand_integrableOn n s hs i).mono_set (Set.Ioi_subset_Ioi spikeT0_pos.le)
  unfold galFIntegrand
  rw [integral_const_mul]
  congr 1
  rw [integral_finsetSum Finset.univ (fun i _ => hint i)]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  exact integral_cexp_neg_mul_Ioi_shift (hre i) spikeT0

/-- Orientation bridge: `e^{-(s+λ)t₀} = e^{-t₀(s+λ)}`. -/
theorem resolvent_sum_orientation (n : ℕ) (s : ℂ) :
    (∑ i : Fin (admN n),
        Complex.exp (-(s + ((admPerturbedLam n i + SupVConst : ℝ) : ℂ)) * (spikeT0:ℂ))
          / (s + ((admPerturbedLam n i + SupVConst : ℝ) : ℂ)))
      = ∑ i : Fin (admN n),
        Complex.exp (-(spikeT0 : ℂ) * (s + ((admPerturbedLam n i + SupVConst : ℝ) : ℂ)))
          / (s + ((admPerturbedLam n i + SupVConst : ℝ) : ℂ)) := by
  refine Finset.sum_congr rfl (fun i _ => ?_)
  congr 2
  ring

/-- **THE F-TAIL BOUND. Uniform in `n`, on any Ω-compact.** -/
theorem galF_tail_uniform_bound
    (K : Set ℂ) (hK : IsCompact K) (hKO : K ⊆ Ω) (hne : K.Nonempty) :
    ∃ Ctail : ℝ, 0 ≤ Ctail ∧ ∀ (n : ℕ), ∀ s ∈ K, 0 < s.re →
      ‖∫ t in Set.Ioi spikeT0, galFIntegrand n s t‖ ≤ Ctail := by
  have hT : (0:ℝ) < spikeT0 := spikeT0_pos
  obtain ⟨delta, hdelta, hgapK⟩ := exists_uniform_lower_bound_on_compact K hK hKO
  obtain ⟨s0, hs0, hmax⟩ := hK.exists_isMaxOn hne
    (Complex.continuous_re.abs.continuousOn)
  set M : ℝ := |s0.re| with hMdef
  have hMK : ∀ s ∈ K, |s.re| ≤ M := fun s hs => hmax hs
  refine ⟨Real.exp (spikeT0 * M) * ((1 / delta) * freeHeatDiagonal spikeT0), ?_, ?_⟩
  · have h1 : (0:ℝ) < 1 / delta := by positivity
    have h2 : (0:ℝ) ≤ freeHeatDiagonal spikeT0 := freeHeatDiagonal_nonneg _
    positivity
  · intro n s hs hsre
    have hL : 0 < admL n := admL_pos n
    have hgap : ∀ i : Fin (admN n),
        delta ≤ ‖s + ((admPerturbedLam n i + SupVConst : ℝ) : ℂ)‖ := fun i =>
      hgapK s hs _ (admShiftedLam_nonneg' n i)
    have hdt := dTail_uniform_bound spikeT0 (admL n) hT.le hL s
      (fun i => admPerturbedLam n i + SupVConst)
      (admShiftedLam_nonneg' n) delta M hdelta hgap (hMK s hs)
      (hfk_adm_shifted n spikeT0 hT)
    rw [galF_tail_eq_resolvent_sum n s hsre, norm_mul, resolvent_sum_orientation n s]
    have hdc : ‖admDensityC n‖ = 1 / (2 * admL n) := by
      unfold admDensityC
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by
        apply div_nonneg zero_le_one; linarith)]
    rw [hdc]
    exact hdt

#print axioms admPerturbedLam_nonneg
#print axioms admShiftedLam_nonneg'
#print axioms hfk_adm
#print axioms hfk_adm_shifted
#print axioms galF_tail_eq_resolvent_sum
#print axioms resolvent_sum_orientation
#print axioms galF_tail_uniform_bound

end RHFormalization
