-- SENTINEL: CCCOEF-v2
import Mathlib

/-!
# CoshCosineCoefficient — the COSINE coefficient of cosh (brick 2a.1)

  ∫₀^L cosh(κ(L−x))·cos(bx) dx = κ·sinh(κL)/(κ²+b²)

for b = mπ/L (so sin(bL)=0, cos(bL)=(−1)^m — but the cos(bL) terms cancel
in this coefficient, which is why it is the RIGHT one; the sine version
carries a parity-dependent numerator and does NOT give the classical
cosine series).

Antiderivative:
  F(x) = (−κ·cosh(κ(L−x))·sin(bx) + b·sinh(κ(L−x))·cos(bx)) / (κ²+b²)
  F'(x) = cosh(κ(L−x))·cos(bx)

Check at x with u = κ(L−x), so d/dx cosh u = −κ sinh u, d/dx sinh u = −κ cosh u:
  F' = [−κ(−κ sinh u)sin(bx) − κ cosh u·b cos(bx)
        + b(−κ cosh u)cos(bx) − b sinh u·b sin(bx)]/(κ²+b²)   ← WRONG SIGNS
Corrected below by direct differentiation; the sign pattern is fixed so
that the cross terms cancel and (κ²+b²)cosh u cos(bx) survives.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace RHFormalization

open Real

/-- Antiderivative for the cosine coefficient. -/
noncomputable def coshCosAntideriv (κ b L : ℝ) (x : ℝ) : ℝ :=
  (-κ * Real.sinh (κ * (L - x)) * Real.cos (b * x)
     + b * Real.cosh (κ * (L - x)) * Real.sin (b * x)) / (κ^2 + b^2)

/-- **THE DERIVATIVE** — `F' = cosh(κ(L−x))·cos(bx)`. -/
theorem hasDerivAt_coshCosAntideriv (κ b L : ℝ) (hden : κ^2 + b^2 ≠ 0) (x : ℝ) :
    HasDerivAt (coshCosAntideriv κ b L)
      (Real.cosh (κ * (L - x)) * Real.cos (b * x)) x := by
  have hu : HasDerivAt (fun x : ℝ => κ * (L - x)) (-κ) x := by
    simpa using ((hasDerivAt_const x L).sub (hasDerivAt_id x)).const_mul κ
  have hcosh : HasDerivAt (fun x : ℝ => Real.cosh (κ * (L - x)))
      (Real.sinh (κ * (L - x)) * (-κ)) x := (Real.hasDerivAt_cosh _).comp x hu
  have hsinh : HasDerivAt (fun x : ℝ => Real.sinh (κ * (L - x)))
      (Real.cosh (κ * (L - x)) * (-κ)) x := (Real.hasDerivAt_sinh _).comp x hu
  have hbx : HasDerivAt (fun x : ℝ => b * x) b x := by
    simpa using (hasDerivAt_id x).const_mul b
  have hcos : HasDerivAt (fun x : ℝ => Real.cos (b * x))
      (-Real.sin (b * x) * b) x := (Real.hasDerivAt_cos _).comp x hbx
  have hsin : HasDerivAt (fun x : ℝ => Real.sin (b * x))
      (Real.cos (b * x) * b) x := (Real.hasDerivAt_sin _).comp x hbx
  have h1 := (hsinh.const_mul (-κ)).mul hcos
  have h2 := (hcosh.const_mul b).mul hsin
  have hfin := (h1.add h2).div_const (κ^2 + b^2)
  unfold coshCosAntideriv
  convert hfin using 1
  field_simp
  ring

/-- **THE COSINE COEFFICIENT INTEGRAL.** -/
theorem integral_cosh_mul_cos (κ b L : ℝ) (hden : κ^2 + b^2 ≠ 0) :
    (∫ x in (0:ℝ)..L, Real.cosh (κ * (L - x)) * Real.cos (b * x))
      = coshCosAntideriv κ b L L - coshCosAntideriv κ b L 0 := by
  have hderiv : ∀ x ∈ Set.uIcc (0:ℝ) L,
      HasDerivAt (coshCosAntideriv κ b L)
        (Real.cosh (κ * (L - x)) * Real.cos (b * x)) x :=
    fun x _ => hasDerivAt_coshCosAntideriv κ b L hden x
  have hint : IntervalIntegrable
      (fun x => Real.cosh (κ * (L - x)) * Real.cos (b * x))
      MeasureTheory.volume 0 L := by
    apply Continuous.intervalIntegrable
    continuity
  exact intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint

/-- **CLOSED FORM at `b = mπ/L`**: `sin(bL) = 0` kills the boundary terms
and the coefficient is `κ·sinh(κL)/(κ²+b²)`. -/
theorem integral_cosh_mul_cos_at_mode (κ L : ℝ) (m : ℕ) (hm : m ≠ 0)
    (hL : 0 < L) (hden : κ^2 + ((m:ℝ) * Real.pi / L)^2 ≠ 0) :
    (∫ x in (0:ℝ)..L,
        Real.cosh (κ * (L - x)) * Real.cos (((m:ℝ) * Real.pi / L) * x))
      = κ * Real.sinh (κ * L) / (κ^2 + ((m:ℝ) * Real.pi / L)^2) := by
  rw [integral_cosh_mul_cos κ ((m:ℝ) * Real.pi / L) L hden]
  unfold coshCosAntideriv
  have hsinL : Real.sin (((m:ℝ) * Real.pi / L) * L) = 0 := by
    have : ((m:ℝ) * Real.pi / L) * L = (m:ℝ) * Real.pi := by
      field_simp
    rw [this]
    exact Real.sin_nat_mul_pi m
  have hcosh0 : Real.cosh (κ * (L - L)) = 1 := by
    simp
  have hsinh0 : Real.sinh (κ * (L - L)) = 0 := by
    simp
  have hcos0 : Real.cos (((m:ℝ) * Real.pi / L) * 0) = 1 := by simp
  have hsin0 : Real.sin (((m:ℝ) * Real.pi / L) * 0) = 0 := by simp
  have hLL : L - 0 = L := by ring
  rw [hsinL, hcosh0, hsinh0, hcos0, hsin0, hLL]
  field_simp
  ring

#print axioms hasDerivAt_coshCosAntideriv
#print axioms integral_cosh_mul_cos
#print axioms integral_cosh_mul_cos_at_mode

end RHFormalization
