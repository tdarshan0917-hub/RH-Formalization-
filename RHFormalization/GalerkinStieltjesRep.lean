import RHFormalization.GalerkinFSideLaplace
import RHFormalization.GalerkinBSideLaplace
import Mathlib

/-!
# RHFormalization.GalerkinStieltjesRep

**THE GENUINE GALERKIN STIELTJES REPRESENTATION.**
`R_stage = F_stage − B_stage` on the genuine perturbed operator at the
admissible net, as a single Laplace integral on `re s > 0`. Unconditional.
-/

set_option autoImplicit false

namespace RHFormalization

open Complex MeasureTheory Set
open scoped BigOperators

noncomputable def galFIntegrand (n : ℕ) (s : ℂ) (t : ℝ) : ℂ :=
  admDensityC n * ∑ i : Fin (admN n),
    Complex.exp (-(s + ((admPerturbedLam n i + SupVConst : ℝ) : ℂ)) * (t:ℂ))

noncomputable def galBIntegrand (n : ℕ) (s : ℂ) (t : ℝ) : ℂ :=
  ∑ q ∈ activePrimePowerPairsCenterBelow (admR n),
    q.weightC * shiftedHeatIntegrand q.center s t

noncomputable def galQResIntegrand (n : ℕ) (s : ℂ) (t : ℝ) : ℂ :=
  galFIntegrand n s t - galBIntegrand n s t

lemma galF_summand_integrableOn (n : ℕ) (s : ℂ) (hs : 0 < s.re) (i : Fin (admN n)) :
    IntegrableOn
      (fun t : ℝ => Complex.exp (-(s + ((admPerturbedLam n i + SupVConst : ℝ) : ℂ)) * (t:ℂ)))
      (Ioi 0) volume := by
  have hnn := admShiftedLam_nonneg n i
  set c : ℝ := (s + ((admPerturbedLam n i + SupVConst : ℝ) : ℂ)).re with hc
  have hcpos : 0 < c := by
    rw [hc, Complex.add_re, Complex.ofReal_re]; linarith
  have hmajor : IntegrableOn (fun t : ℝ => Real.exp (-(c * t))) (Ioi 0) volume := by
    first
      | simpa [neg_mul] using (exp_neg_integrableOn_Ioi (0:ℝ) hcpos)
      | simpa [neg_mul] using (integrableOn_Ioi_exp_neg_mul (0:ℝ) hcpos)
      | exact (exp_neg_integrableOn_Ioi (0:ℝ) hcpos)
      | · have h := (integrableOn_Ioi_comp_mul_left_iff
            (fun x : ℝ => Real.exp (-x)) (0:ℝ) hcpos).mpr
          simp only [mul_zero] at h
          simpa [neg_mul] using h (exp_neg_integrableOn_Ioi (0:ℝ) one_pos)
  have hmeas : AEStronglyMeasurable
      (fun t : ℝ => Complex.exp (-(s + ((admPerturbedLam n i + SupVConst : ℝ) : ℂ)) * (t:ℂ)))
      (volume.restrict (Ioi 0)) := by
    apply Measurable.aestronglyMeasurable; fun_prop
  refine hmajor.mono' hmeas ?_
  filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with t _
  rw [Complex.norm_exp]
  apply le_of_eq
  congr 1
  rw [hc]
  simp [Complex.mul_re, Complex.neg_re, Complex.neg_im]
  ring

lemma galF_integrand_integrableOn (n : ℕ) (s : ℂ) (hs : 0 < s.re) :
    IntegrableOn (fun t : ℝ => galFIntegrand n s t) (Ioi 0) volume := by
  unfold galFIntegrand
  refine MeasureTheory.Integrable.const_mul ?_ (admDensityC n)
  first
    | exact MeasureTheory.integrable_finset_sum Finset.univ
        (fun i _ => galF_summand_integrableOn n s hs i)
    | exact integrable_finset_sum Finset.univ
        (fun i _ => galF_summand_integrableOn n s hs i)
    | exact MeasureTheory.integrable_finset_sum' Finset.univ
        (fun i _ => galF_summand_integrableOn n s hs i)

lemma galB_integrand_integrableOn (n : ℕ) (s : ℂ) (hs : 0 < s.re) :
    IntegrableOn (fun t : ℝ => galBIntegrand n s t) (Ioi 0) volume := by
  unfold galBIntegrand
  first
    | exact MeasureTheory.integrable_finset_sum (activePrimePowerPairsCenterBelow (admR n))
        (fun q _ => (shiftedHeatIntegrand_integrableOn q.center s hs).const_mul q.weightC)
    | exact integrable_finset_sum (activePrimePowerPairsCenterBelow (admR n))
        (fun q _ => (shiftedHeatIntegrand_integrableOn q.center s hs).const_mul q.weightC)
    | exact MeasureTheory.integrable_finset_sum' (activePrimePowerPairsCenterBelow (admR n))
        (fun q _ => (shiftedHeatIntegrand_integrableOn q.center s hs).const_mul q.weightC)

/-- **THE GENUINE GALERKIN STIELTJES REPRESENTATION.** -/
theorem galerkin_R_stage_eq_laplace (n : ℕ) (s : ℂ) (hs : 0 < s.re) :
    galerkinStagePackage.R_stage (admissibleGalerkinStageSeq n) s
      = ∫ t in Ioi (0:ℝ), galQResIntegrand n s t := by
  have hR : galerkinStagePackage.R_stage (admissibleGalerkinStageSeq n) s
      = galerkinStagePackage.F_stage (admissibleGalerkinStageSeq n) s
        - galerkinStagePackage.B_stage (admissibleGalerkinStageSeq n) s := rfl
  have hsplit : (∫ t in Ioi (0:ℝ), galQResIntegrand n s t)
      = (∫ t in Ioi (0:ℝ), galFIntegrand n s t)
        - (∫ t in Ioi (0:ℝ), galBIntegrand n s t) :=
    MeasureTheory.integral_sub
      (galF_integrand_integrableOn n s hs) (galB_integrand_integrableOn n s hs)
  rw [hR, galerkin_F_stage_eq_laplace_heatTrace n s hs,
      galerkin_B_stage_eq_laplace n s hs, hsplit]
  congr 1
  unfold galFIntegrand
  first
    | rw [MeasureTheory.integral_const_mul]
    | simp [MeasureTheory.integral_const_mul]
    | rfl

#print axioms galF_summand_integrableOn
#print axioms galerkin_R_stage_eq_laplace

end RHFormalization
