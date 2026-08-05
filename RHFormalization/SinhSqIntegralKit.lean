import Mathlib

/-!
# SinhSqIntegralKit — P2-B1: closed sinh² integrals

ROUTE CARD
1. Target: FTC closed forms `∫ sinh(κx)² dx` and `∫ sinh(κ(L−x))² dx` on
   intervals — the two pieces of the split-at-a squared-Green diagonal
   integral `∫₀^L G(x,a)² dx`. Clone of the banked antiderivative-kit
   pattern (SinhSinAntiderivKit / CoshCosineCoefficient).
2. Raw B on Ω? NO. B−M bare Prop? NO — calculus only.
3. Consumer: P2-B2 `greenSq_diagonal_closed`: the closed hyperbolic form of
   `∫₀^L dirichletGreen L κ x a ^ 2 dx`, whose large-L limit is the
   `e^{−2κa}` continuum structure the combined density−osc profile must
   match (Phase-2 go/no-go).
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace RHFormalization

open Real

/-- Antiderivative of `sinh(κx)²`: `(sinh(κx)·cosh(κx)/κ − x)/2`. -/
noncomputable def sinhSqAntideriv (κ : ℝ) (x : ℝ) : ℝ :=
  (Real.sinh (κ * x) * Real.cosh (κ * x) / κ - x) / 2

/-- `d/dx sinhSqAntideriv = sinh(κx)²`. -/
theorem hasDerivAt_sinhSqAntideriv (κ : ℝ) (hκ : κ ≠ 0) (x : ℝ) :
    HasDerivAt (sinhSqAntideriv κ) (Real.sinh (κ * x) ^ 2) x := by
  have hkx : HasDerivAt (fun x : ℝ => κ * x) κ x := by
    simpa using (hasDerivAt_id x).const_mul κ
  have hsinh : HasDerivAt (fun x : ℝ => Real.sinh (κ * x))
      (Real.cosh (κ * x) * κ) x := (Real.hasDerivAt_sinh _).comp x hkx
  have hcosh : HasDerivAt (fun x : ℝ => Real.cosh (κ * x))
      (Real.sinh (κ * x) * κ) x := (Real.hasDerivAt_cosh _).comp x hkx
  have hmul := hsinh.mul hcosh
  have hdivk := hmul.div_const κ
  have hid : HasDerivAt (fun x : ℝ => x) 1 x := hasDerivAt_id x
  have hsub := hdivk.sub hid
  have hfin := hsub.div_const 2
  unfold sinhSqAntideriv
  convert hfin using 1
  have hpyth : Real.cosh (κ * x) ^ 2 = 1 + Real.sinh (κ * x) ^ 2 := by
    have := Real.cosh_sq (κ * x)
    first
      | linarith
      | (rw [Real.cosh_sq]; ring)
      | nlinarith [Real.cosh_sq (κ * x)]
  field_simp
  nlinarith [hpyth]

/-- Antiderivative of `sinh(κ(L−x))²`: `−(sinh·cosh/κ)(κ(L−x))/2 − x/2`. -/
noncomputable def sinhSqRevAntideriv (κ L : ℝ) (x : ℝ) : ℝ :=
  (-(Real.sinh (κ * (L - x)) * Real.cosh (κ * (L - x)) / κ) - x) / 2

/-- `d/dx sinhSqRevAntideriv = sinh(κ(L−x))²`. -/
theorem hasDerivAt_sinhSqRevAntideriv (κ L : ℝ) (hκ : κ ≠ 0) (x : ℝ) :
    HasDerivAt (sinhSqRevAntideriv κ L) (Real.sinh (κ * (L - x)) ^ 2) x := by
  have hu : HasDerivAt (fun x : ℝ => κ * (L - x)) (-κ) x := by
    simpa using ((hasDerivAt_const x L).sub (hasDerivAt_id x)).const_mul κ
  have hsinh : HasDerivAt (fun x : ℝ => Real.sinh (κ * (L - x)))
      (Real.cosh (κ * (L - x)) * (-κ)) x := (Real.hasDerivAt_sinh _).comp x hu
  have hcosh : HasDerivAt (fun x : ℝ => Real.cosh (κ * (L - x)))
      (Real.sinh (κ * (L - x)) * (-κ)) x := (Real.hasDerivAt_cosh _).comp x hu
  have hmul := hsinh.mul hcosh
  have hdivk := hmul.div_const κ
  have hneg := hdivk.neg
  have hid : HasDerivAt (fun x : ℝ => x) 1 x := hasDerivAt_id x
  have hsub := hneg.sub hid
  have hfin := hsub.div_const 2
  unfold sinhSqRevAntideriv
  convert hfin using 1
  have hpyth : Real.cosh (κ * (L - x)) ^ 2 = 1 + Real.sinh (κ * (L - x)) ^ 2 := by
    have := Real.cosh_sq (κ * (L - x))
    first
      | linarith
      | (rw [Real.cosh_sq]; ring)
      | nlinarith [Real.cosh_sq (κ * (L - x))]
  field_simp
  nlinarith [hpyth]

/-- FTC: `∫ sinh(κx)²` on `[u,v]`. -/
theorem integral_sinh_sq (κ u v : ℝ) (hκ : κ ≠ 0) :
    (∫ x in u..v, Real.sinh (κ * x) ^ 2)
      = sinhSqAntideriv κ v - sinhSqAntideriv κ u := by
  have hderiv : ∀ x ∈ Set.uIcc u v,
      HasDerivAt (sinhSqAntideriv κ) (Real.sinh (κ * x) ^ 2) x :=
    fun x _ => hasDerivAt_sinhSqAntideriv κ hκ x
  have hint : IntervalIntegrable (fun x => Real.sinh (κ * x) ^ 2)
      MeasureTheory.volume u v := by
    apply Continuous.intervalIntegrable
    continuity
  exact intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint

/-- FTC: `∫ sinh(κ(L−x))²` on `[u,v]`. -/
theorem integral_sinhRev_sq (κ L u v : ℝ) (hκ : κ ≠ 0) :
    (∫ x in u..v, Real.sinh (κ * (L - x)) ^ 2)
      = sinhSqRevAntideriv κ L v - sinhSqRevAntideriv κ L u := by
  have hderiv : ∀ x ∈ Set.uIcc u v,
      HasDerivAt (sinhSqRevAntideriv κ L) (Real.sinh (κ * (L - x)) ^ 2) x :=
    fun x _ => hasDerivAt_sinhSqRevAntideriv κ L hκ x
  have hint : IntervalIntegrable (fun x => Real.sinh (κ * (L - x)) ^ 2)
      MeasureTheory.volume u v := by
    apply Continuous.intervalIntegrable
    continuity
  exact intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint

#print axioms hasDerivAt_sinhSqAntideriv
#print axioms hasDerivAt_sinhSqRevAntideriv
#print axioms integral_sinh_sq
#print axioms integral_sinhRev_sq

end RHFormalization
