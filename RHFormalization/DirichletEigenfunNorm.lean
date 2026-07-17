import RHFormalization.DirichletEigenfunInner
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# RHFormalization.DirichletEigenfunNorm
**Brick 3, stone 3.** Diagonal L² norm `∫₀ᴸ sin²(nπx/L) = L/2` (n ≥ 1, L > 0),
proved by FTC with antiderivative `x/2 − sin(2cx)/(4c)`.
-/

set_option autoImplicit false

namespace RHFormalization

noncomputable section

open Real intervalIntegral
open scoped Real

/-- The diagonal integral `∫₀ᴸ sin²(nπx/L) dx = L/2` for `n ≥ 1`, `L > 0`. -/
theorem integral_dirichletEigenfun_sq (n : ℕ) (L : ℝ) (hL : 0 < L) (hn : 1 ≤ n) :
    ∫ x in (0:ℝ)..L, dirichletEigenfun n L x ^ 2 = L / 2 := by
  have hLne : L ≠ 0 := ne_of_gt hL
  set c : ℝ := (n : ℝ) * Real.pi / L with hc_def
  have hcpos : 0 < c := by rw [hc_def]; positivity
  have hcne : c ≠ 0 := ne_of_gt hcpos
  -- integrand: φₙ² = sin²(cx) = 1/2 - cos(2cx)/2
  have hrw : ∀ x : ℝ,
      dirichletEigenfun n L x ^ 2 = 1/2 - Real.cos (2 * c * x) / 2 := by
    intro x
    unfold dirichletEigenfun
    rw [Real.sin_sq_eq_half_sub]
    rw [hc_def]
    congr 2
    ring
  simp_rw [hrw]
  -- antiderivative F x = x/2 - sin(2cx)/(4c), F' = 1/2 - cos(2cx)/2
  have hderiv : ∀ x ∈ Set.uIcc (0:ℝ) L,
      HasDerivAt (fun x => x/2 - Real.sin (2*c*x) / (4*c))
        (1/2 - Real.cos (2*c*x) / 2) x := by
    intro x _
    have h2cx : HasDerivAt (fun x : ℝ => 2*c*x) (2*c) x := by
      simpa using (hasDerivAt_id x).const_mul (2*c)
    have hsin : HasDerivAt (fun x => Real.sin (2*c*x)) (Real.cos (2*c*x) * (2*c)) x :=
      h2cx.sin
    have hlin : HasDerivAt (fun x : ℝ => x/2) (1/2) x := by
      simpa using (hasDerivAt_id x).div_const 2
    have hfull := hlin.sub (hsin.div_const (4*c))
    have hrwd : (1:ℝ)/2 - Real.cos (2*c*x) * (2*c) / (4*c)
        = 1/2 - Real.cos (2*c*x) / 2 := by
      field_simp; ring
    rwa [hrwd] at hfull
  have hint : IntervalIntegrable (fun x => 1/2 - Real.cos (2*c*x)/2)
      MeasureTheory.volume 0 L :=
    (by fun_prop : Continuous (fun x => 1/2 - Real.cos (2*c*x)/2)).intervalIntegrable 0 L
  rw [integral_eq_sub_of_hasDerivAt hderiv hint]
  -- evaluate: (L/2 - sin(2cL)/(4c)) - (0/2 - sin 0/(4c))
  have h2cL : 2 * c * L = 2 * ((n:ℝ) * Real.pi) := by rw [hc_def]; field_simp
  have hsin2cL : Real.sin (2 * c * L) = 0 := by
    rw [h2cL, show 2 * ((n:ℝ)*Real.pi) = (((2*n:ℕ)):ℝ)*Real.pi by push_cast; ring]
    exact Real.sin_nat_mul_pi (2*n)
  rw [hsin2cL]
  simp

#print axioms integral_dirichletEigenfun_sq

end

end RHFormalization
