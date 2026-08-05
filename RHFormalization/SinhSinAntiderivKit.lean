import Mathlib

/-!
# SinhSinAntiderivKit — P2-A1: the sinh·sin antiderivatives

ROUTE CARD
1. Target: closed antiderivatives + FTC interval integrals for
   `sinh(κx)·sin(bx)` and `sinh(κ(L−x))·sin(bx)` — the two pieces of the
   split-at-y Green-coefficient integral. Exact clone of the banked
   `CoshCosineCoefficient` pattern (D.LOC-1 stone).
2. Raw B on Ω? NO. B−M bare Prop? NO — calculus only.
3. Consumer: P2-A2 `greenSineCoefficient`:
   `∫₀^L dirichletGreen L κ x y · sin(mπx/L) dx = sin(mπy/L)/(κ²+λ_m)` —
   the spectral-expansion identity joining the two D.LOC-1 stones, feeding
   the combined density−osc continuum match (Phase 2 go/no-go).
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace RHFormalization

open Real

/-- Antiderivative of `sinh(κx)·sin(bx)`. -/
noncomputable def sinhSinAntideriv (κ b : ℝ) (x : ℝ) : ℝ :=
  (κ * Real.cosh (κ * x) * Real.sin (b * x)
     - b * Real.sinh (κ * x) * Real.cos (b * x)) / (κ^2 + b^2)

/-- `d/dx sinhSinAntideriv = sinh(κx)·sin(bx)`. -/
theorem hasDerivAt_sinhSinAntideriv (κ b : ℝ) (hden : κ^2 + b^2 ≠ 0) (x : ℝ) :
    HasDerivAt (sinhSinAntideriv κ b)
      (Real.sinh (κ * x) * Real.sin (b * x)) x := by
  have hkx : HasDerivAt (fun x : ℝ => κ * x) κ x := by
    simpa using (hasDerivAt_id x).const_mul κ
  have hbx : HasDerivAt (fun x : ℝ => b * x) b x := by
    simpa using (hasDerivAt_id x).const_mul b
  have hcosh : HasDerivAt (fun x : ℝ => Real.cosh (κ * x))
      (Real.sinh (κ * x) * κ) x := (Real.hasDerivAt_cosh _).comp x hkx
  have hsinh : HasDerivAt (fun x : ℝ => Real.sinh (κ * x))
      (Real.cosh (κ * x) * κ) x := (Real.hasDerivAt_sinh _).comp x hkx
  have hcos : HasDerivAt (fun x : ℝ => Real.cos (b * x))
      (-Real.sin (b * x) * b) x := (Real.hasDerivAt_cos _).comp x hbx
  have hsin : HasDerivAt (fun x : ℝ => Real.sin (b * x))
      (Real.cos (b * x) * b) x := (Real.hasDerivAt_sin _).comp x hbx
  have h1 := (hcosh.const_mul κ).mul hsin
  have h2 := (hsinh.const_mul b).mul hcos
  have hfin := (h1.sub h2).div_const (κ^2 + b^2)
  unfold sinhSinAntideriv
  convert hfin using 1
  field_simp
  ring

/-- Antiderivative of `sinh(κ(L−x))·sin(bx)`. -/
noncomputable def sinhSinRevAntideriv (κ b L : ℝ) (x : ℝ) : ℝ :=
  (-κ * Real.cosh (κ * (L - x)) * Real.sin (b * x)
     - b * Real.sinh (κ * (L - x)) * Real.cos (b * x)) / (κ^2 + b^2)

/-- `d/dx sinhSinRevAntideriv = sinh(κ(L−x))·sin(bx)`. -/
theorem hasDerivAt_sinhSinRevAntideriv (κ b L : ℝ) (hden : κ^2 + b^2 ≠ 0)
    (x : ℝ) :
    HasDerivAt (sinhSinRevAntideriv κ b L)
      (Real.sinh (κ * (L - x)) * Real.sin (b * x)) x := by
  have hu : HasDerivAt (fun x : ℝ => κ * (L - x)) (-κ) x := by
    simpa using ((hasDerivAt_const x L).sub (hasDerivAt_id x)).const_mul κ
  have hbx : HasDerivAt (fun x : ℝ => b * x) b x := by
    simpa using (hasDerivAt_id x).const_mul b
  have hcosh : HasDerivAt (fun x : ℝ => Real.cosh (κ * (L - x)))
      (Real.sinh (κ * (L - x)) * (-κ)) x := (Real.hasDerivAt_cosh _).comp x hu
  have hsinh : HasDerivAt (fun x : ℝ => Real.sinh (κ * (L - x)))
      (Real.cosh (κ * (L - x)) * (-κ)) x := (Real.hasDerivAt_sinh _).comp x hu
  have hcos : HasDerivAt (fun x : ℝ => Real.cos (b * x))
      (-Real.sin (b * x) * b) x := (Real.hasDerivAt_cos _).comp x hbx
  have hsin : HasDerivAt (fun x : ℝ => Real.sin (b * x))
      (Real.cos (b * x) * b) x := (Real.hasDerivAt_sin _).comp x hbx
  have h1 := (hcosh.const_mul (-κ)).mul hsin
  have h2 := (hsinh.const_mul b).mul hcos
  have hfin := (h1.sub h2).div_const (κ^2 + b^2)
  unfold sinhSinRevAntideriv
  convert hfin using 1
  field_simp
  ring

/-- FTC on `[u,v]` for `sinh(κx)·sin(bx)`. -/
theorem integral_sinh_mul_sin (κ b u v : ℝ) (hden : κ^2 + b^2 ≠ 0) :
    (∫ x in u..v, Real.sinh (κ * x) * Real.sin (b * x))
      = sinhSinAntideriv κ b v - sinhSinAntideriv κ b u := by
  have hderiv : ∀ x ∈ Set.uIcc u v,
      HasDerivAt (sinhSinAntideriv κ b)
        (Real.sinh (κ * x) * Real.sin (b * x)) x :=
    fun x _ => hasDerivAt_sinhSinAntideriv κ b hden x
  have hint : IntervalIntegrable
      (fun x => Real.sinh (κ * x) * Real.sin (b * x))
      MeasureTheory.volume u v := by
    apply Continuous.intervalIntegrable
    continuity
  exact intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint

/-- FTC on `[u,v]` for `sinh(κ(L−x))·sin(bx)`. -/
theorem integral_sinhRev_mul_sin (κ b L u v : ℝ) (hden : κ^2 + b^2 ≠ 0) :
    (∫ x in u..v, Real.sinh (κ * (L - x)) * Real.sin (b * x))
      = sinhSinRevAntideriv κ b L v - sinhSinRevAntideriv κ b L u := by
  have hderiv : ∀ x ∈ Set.uIcc u v,
      HasDerivAt (sinhSinRevAntideriv κ b L)
        (Real.sinh (κ * (L - x)) * Real.sin (b * x)) x :=
    fun x _ => hasDerivAt_sinhSinRevAntideriv κ b L hden x
  have hint : IntervalIntegrable
      (fun x => Real.sinh (κ * (L - x)) * Real.sin (b * x))
      MeasureTheory.volume u v := by
    apply Continuous.intervalIntegrable
    continuity
  exact intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint

#print axioms hasDerivAt_sinhSinAntideriv
#print axioms hasDerivAt_sinhSinRevAntideriv
#print axioms integral_sinh_mul_sin
#print axioms integral_sinhRev_mul_sin

end RHFormalization
