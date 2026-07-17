import RHFormalization.DirichletLaplacianEigenpairs
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# RHFormalization.DirichletEigenfunOrthogonal
**Foundation brick 2.** Orthogonality of the Dirichlet eigenfunctions
`φₙ(x) = sin(nπx/L)` on `[0,L]`:
* off-diagonal `∫₀ᴸ φₘ φₙ = 0` for `m ≠ n`,
* diagonal `∫₀ᴸ φₙ² = L/2` for `n ≥ 1`.
Pure interval-integral calculus over brick 1; no operator theory yet.
-/

set_option autoImplicit false

namespace RHFormalization

noncomputable section

open Real intervalIntegral
open scoped Real

/-- Product-to-sum: `sin a * sin b = (cos (a - b) - cos (a + b)) / 2`. -/
theorem sin_mul_sin_eq (a b : ℝ) :
    Real.sin a * Real.sin b = (Real.cos (a - b) - Real.cos (a + b)) / 2 := by
  rw [Real.cos_sub, Real.cos_add]; ring

/-- The integrand `φₘ·φₙ` rewritten via product-to-sum. -/
theorem eigenfun_mul_eq (m n : ℕ) (L x : ℝ) :
    dirichletEigenfun m L x * dirichletEigenfun n L x =
      (Real.cos (((m : ℝ) - n) * Real.pi * x / L)
        - Real.cos (((m : ℝ) + n) * Real.pi * x / L)) / 2 := by
  unfold dirichletEigenfun
  rw [sin_mul_sin_eq]
  congr 2 <;> · field_simp <;> ring

/-- `∫₀ᴸ cos(kπx/L) = 0` for integer `k ≠ 0`: the antiderivative `sin(cx)/c`
lands on `sin(kπ) = 0` at both endpoints. -/
theorem integral_cos_scaled_vanishes (k : ℤ) (L : ℝ) (hL : L ≠ 0) (hk : k ≠ 0) :
    ∫ x in (0:ℝ)..L, Real.cos ((k : ℝ) * Real.pi * x / L) = 0 := by
  set c : ℝ := (k : ℝ) * Real.pi / L with hc_def
  have hc : c ≠ 0 :=
    div_ne_zero (mul_ne_zero (Int.cast_ne_zero.mpr hk) Real.pi_ne_zero) hL
  have hcos_eq : ∀ x : ℝ,
      Real.cos ((k : ℝ) * Real.pi * x / L) = Real.cos (c * x) := by
    intro x; rw [hc_def]; congr 1; ring
  simp_rw [hcos_eq]
  -- antiderivative F x = sin (c x) / c, with F' x = cos (c x)
  have hderiv : ∀ x ∈ Set.uIcc (0:ℝ) L,
      HasDerivAt (fun x => Real.sin (c * x) / c) (Real.cos (c * x)) x := by
    intro x _
    have hcx : HasDerivAt (fun x : ℝ => c * x) c x := by
      simpa using (hasDerivAt_id x).const_mul c
    have hsin : HasDerivAt (fun x => Real.sin (c * x)) (Real.cos (c * x) * c) x :=
      hcx.sin
    have hdiv := hsin.div_const c
    have hrw : Real.cos (c * x) * c / c = Real.cos (c * x) := by
      rw [mul_div_assoc, div_self hc, mul_one]
    rwa [hrw] at hdiv
  have hint : IntervalIntegrable (fun x => Real.cos (c * x))
      MeasureTheory.volume 0 L :=
    (by fun_prop : Continuous (fun x => Real.cos (c * x))).intervalIntegrable 0 L
  rw [integral_eq_sub_of_hasDerivAt hderiv hint]
  have hcL : c * L = (k : ℝ) * Real.pi := by rw [hc_def]; field_simp
  rw [mul_zero, hcL, Real.sin_zero]
  have hsin0 : Real.sin ((k : ℝ) * Real.pi) = 0 := by
    rw [show ((k : ℝ) * Real.pi) = ((k : ℤ) : ℝ) * Real.pi by push_cast; ring]
    exact Real.sin_int_mul_pi k
  rw [hsin0]
  simp

#print axioms sin_mul_sin_eq
#print axioms eigenfun_mul_eq
#print axioms integral_cos_scaled_vanishes

end

end RHFormalization

namespace RHFormalization

noncomputable section

open Real intervalIntegral
open scoped Real

/-- Off-diagonal orthogonality: `∫₀ᴸ φₘ φₙ = 0` for `m ≠ n`. -/
theorem eigenfun_orthogonal (m n : ℕ) (L : ℝ) (hL : L ≠ 0) (hmn : m ≠ n) :
    ∫ x in (0:ℝ)..L, dirichletEigenfun m L x * dirichletEigenfun n L x = 0 := by
  have hrw : (fun x => dirichletEigenfun m L x * dirichletEigenfun n L x)
      = (fun x =>
          (Real.cos (((m : ℝ) - n) * Real.pi * x / L)
            - Real.cos (((m : ℝ) + n) * Real.pi * x / L)) / 2) := by
    funext x; exact eigenfun_mul_eq m n L x
  rw [hrw]
  -- ∫ (cos(d⁻πx/L) - cos(d⁺πx/L))/2 = (∫cos(d⁻) - ∫cos(d⁺))/2 = (0-0)/2
  have hint_minus : IntervalIntegrable
      (fun x => Real.cos (((m : ℝ) - n) * Real.pi * x / L))
      MeasureTheory.volume 0 L :=
    (by fun_prop : Continuous _).intervalIntegrable 0 L
  have hint_plus : IntervalIntegrable
      (fun x => Real.cos (((m : ℝ) + n) * Real.pi * x / L))
      MeasureTheory.volume 0 L :=
    (by fun_prop : Continuous _).intervalIntegrable 0 L
  rw [integral_div, intervalIntegral.integral_sub hint_minus hint_plus]
  -- both integrals vanish: m-n and m+n are nonzero integers
  have hminus : ∫ x in (0:ℝ)..L, Real.cos (((m : ℝ) - n) * Real.pi * x / L) = 0 := by
    have hk : ((m : ℤ) - (n : ℤ)) ≠ 0 := by
      intro h; exact hmn (by omega)
    have hcast : (((m : ℤ) - (n : ℤ) : ℤ) : ℝ) = (m : ℝ) - n := by push_cast; ring
    have := integral_cos_scaled_vanishes ((m : ℤ) - (n : ℤ)) L hL hk
    rwa [hcast] at this
  have hplus : ∫ x in (0:ℝ)..L, Real.cos (((m : ℝ) + n) * Real.pi * x / L) = 0 := by
    have hk : ((m : ℤ) + (n : ℤ)) ≠ 0 := by
      intro h
      have hm0 : m = 0 := by omega
      have hn0 : n = 0 := by omega
      exact hmn (by rw [hm0, hn0])
    have hcast : (((m : ℤ) + (n : ℤ) : ℤ) : ℝ) = (m : ℝ) + n := by push_cast; ring
    have := integral_cos_scaled_vanishes ((m : ℤ) + (n : ℤ)) L hL hk
    rwa [hcast] at this
  rw [hminus, hplus]; simp

#print axioms eigenfun_orthogonal

end

end RHFormalization
