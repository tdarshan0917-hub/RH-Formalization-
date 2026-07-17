import RHFormalization.DirichletEigenfunNorm

/-!
# RHFormalization.DirichletEigenfunONB
**Brick 3, stone 4.** The normalized Dirichlet eigenfunctions `√(2/L)·sin((n+1)πx/L)`
form an orthonormal family in L²[0,L]. Indexed `n ↦ (n+1)` to skip the zero vector.
-/

set_option autoImplicit false

namespace RHFormalization

noncomputable section

open MeasureTheory Real
open scoped Real

/-- Normalized Dirichlet eigenfunction in L²[0,L], `n ↦ √(2/L)·sin((n+1)πx/L)`. -/
noncomputable def dirichletONB (L : ℝ) (n : ℕ) : (ℝ →₂[intervalMeasure L] ℝ) :=
  Real.sqrt (2 / L) • eigenLp (n + 1) L

/-- `(√(2/L))² = 2/L` for `L > 0`. -/
theorem sqrt_two_div_L_sq (L : ℝ) (hL : 0 < L) :
    Real.sqrt (2 / L) * Real.sqrt (2 / L) = 2 / L :=
  Real.mul_self_sqrt (by positivity)

/-- The normalized Dirichlet eigenfunctions form an orthonormal family in L²[0,L]. -/
theorem dirichletONB_orthonormal (L : ℝ) (hL : 0 < L) :
    Orthonormal ℝ (dirichletONB L) := by
  rw [orthonormal_iff_ite]
  intro i j
  unfold dirichletONB
  rw [real_inner_smul_left, real_inner_smul_right,
      inner_eigenLp_eq_intervalIntegral _ _ L (le_of_lt hL)]
  by_cases h : i = j
  · subst h
    rw [if_pos rfl]
    have hsq : (∫ x in (0:ℝ)..L,
          dirichletEigenfun (i+1) L x * dirichletEigenfun (i+1) L x)
        = ∫ x in (0:ℝ)..L, dirichletEigenfun (i+1) L x ^ 2 := by
      simp_rw [← pow_two]
    rw [hsq, integral_dirichletEigenfun_sq (i+1) L hL (by omega),
        ← mul_assoc, sqrt_two_div_L_sq L hL]
    field_simp
  · rw [if_neg h,
        eigenfun_orthogonal (i+1) (j+1) L (ne_of_gt hL) (by omega)]
    ring

#print axioms dirichletONB_orthonormal

end

end RHFormalization
