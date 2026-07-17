import RHFormalization.GalerkinHeadIntegralBound
import RHFormalization.GalerkinStieltjesRep
import RHFormalization.DA2LaplaceResolvent
import RHFormalization.AdmissibleRStageHolo
import Mathlib

/-!
# GalerkinTailSplit — the `t₀`-split of the genuine Stieltjes representation

ROUTE CARD
1. Target: on RHP(0), `R_stage n s = head n s + tail n s` where
   `head n s = ∫ t in Ioc 0 spikeT0, galQResIntegrand n s t`  (bounded on ALL of ℂ, banked)
   `tail n s = ∫ t in Ioi spikeT0, galQResIntegrand n s t`.
2. Objects: `galerkin_R_stage_eq_laplace` (banked), `Set.Ioc_union_Ioi_eq_Ioi`,
   `setIntegral_union`, `integral_exp_mul_complex_Ioi` (Mathlib, general lower limit).
3. Raw B on Ω? NO. 4. R = F − raw B? NO — genuine `R_stage`. 5. True outright.
6. Manuscript: D.KEY-FORM, the truncated transform.
7. Consumer: head-holomorphy by subtraction (`head = R_stage − tail`), then
   `DBFFO3ParabolaDepthHstar` from the banked head bound.

ASYMMETRY (the point of the split). The HEAD needs no half-plane but has a
`t^{-1/2}` singularity at `0`, so it is hard to differentiate under the integral.
The TAIL needs `Re s > 0` but evaluates in CLOSED FORM, hence is manifestly
holomorphic. So: prove the split on RHP(0); get head-holomorphy on Ω by
subtraction from the banked `R_stage` holomorphy; and use the banked head bound,
which holds on every compact of `ℂ` at any parabola depth.
-/

set_option autoImplicit false

namespace RHFormalization

open Complex MeasureTheory
open scoped BigOperators

/-- **Shifted Laplace evaluator.** `∫_{t₀}^∞ e^{-a t} dt = e^{-a t₀}/a` for `Re a > 0`. -/
theorem integral_cexp_neg_mul_Ioi_shift {a : ℂ} (ha : 0 < a.re) (c : ℝ) :
    (∫ t in Set.Ioi c, Complex.exp (-a * (t:ℂ)))
      = Complex.exp (-a * (c:ℂ)) / a := by
  have hneg : (-a).re < 0 := by rw [Complex.neg_re]; linarith
  have h := integral_exp_mul_complex_Ioi (a := -a) hneg c
  rw [show (fun t : ℝ => Complex.exp (-a * (t:ℂ)))
        = (fun x : ℝ => Complex.exp ((-a) * (x:ℂ))) from rfl]
  rw [h]
  have ha0 : a ≠ 0 := by
    intro h0; rw [h0] at ha; simp at ha
  field_simp

/-- The head of the Stieltjes integral. Bounded on every compact of `ℂ` (banked). -/
noncomputable def galHead (n : ℕ) (s : ℂ) : ℂ :=
  ∫ t in Set.Ioc (0:ℝ) spikeT0, galQResIntegrand n s t

/-- The tail of the Stieltjes integral. -/
noncomputable def galTail (n : ℕ) (s : ℂ) : ℂ :=
  ∫ t in Set.Ioi spikeT0, galQResIntegrand n s t

/-- Tail integrability on the right half-plane. -/
theorem galQRes_integrableOn_tail (n : ℕ) (s : ℂ) (hs : 0 < s.re) :
    IntegrableOn (fun t : ℝ => galQResIntegrand n s t) (Set.Ioi spikeT0) := by
  have hfull : IntegrableOn (fun t : ℝ => galQResIntegrand n s t) (Set.Ioi 0) := by
    unfold galQResIntegrand
    exact (galF_integrand_integrableOn n s hs).sub (galB_integrand_integrableOn n s hs)
  exact hfull.mono_set (Set.Ioi_subset_Ioi spikeT0_pos.le)

/-- The additive split of the Stieltjes integral at `t₀ = spikeT0`. -/
theorem galQRes_integral_split (n : ℕ) (s : ℂ) (hs : 0 < s.re) :
    (∫ t in Set.Ioi (0:ℝ), galQResIntegrand n s t)
      = galHead n s + galTail n s := by
  have hT : (0:ℝ) < spikeT0 := spikeT0_pos
  have h1 : IntegrableOn (fun t : ℝ => galQResIntegrand n s t) (Set.Ioc 0 spikeT0) :=
    galQRes_integrableOn_head n s
  have h2 : IntegrableOn (fun t : ℝ => galQResIntegrand n s t) (Set.Ioi spikeT0) :=
    galQRes_integrableOn_tail n s hs
  unfold galHead galTail
  rw [← Set.Ioc_union_Ioi_eq_Ioi hT.le]
  rw [MeasureTheory.setIntegral_union _ measurableSet_Ioi h1 h2]
  exact Set.Ioc_disjoint_Ioi_same

/-- **THE `t₀`-SPLIT IDENTITY.** On the right half-plane,
`R_stage = head + tail`. -/
theorem R_stage_eq_head_add_tail (n : ℕ) (s : ℂ) (hs : 0 < s.re) :
    galerkinStagePackage.R_stage (admissibleGalerkinStageSeq n) s
      = galHead n s + galTail n s := by
  rw [galerkin_R_stage_eq_laplace n s hs]
  exact galQRes_integral_split n s hs

/-- **HEAD = R_stage − TAIL on RHP(0).** The form used to transport
head-holomorphy from the banked `R_stage` holomorphy. -/
theorem galHead_eq_R_stage_sub_tail (n : ℕ) (s : ℂ) (hs : 0 < s.re) :
    galHead n s
      = galerkinStagePackage.R_stage (admissibleGalerkinStageSeq n) s - galTail n s := by
  rw [R_stage_eq_head_add_tail n s hs]; ring

#print axioms integral_cexp_neg_mul_Ioi_shift
#print axioms galQRes_integrableOn_tail
#print axioms galQRes_integral_split
#print axioms R_stage_eq_head_add_tail
#print axioms galHead_eq_R_stage_sub_tail

end RHFormalization
