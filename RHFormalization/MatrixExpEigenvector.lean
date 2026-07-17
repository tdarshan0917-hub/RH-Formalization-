import RHFormalization.GalerkinDuhamelUniformBound
import Mathlib

/-!
# Matrix exp preserves eigenvectors — BRICK 8a-ii (crux lemma)
SENTINEL: exp-eigenvector-v4

ROUTE CARD
1. `matrix_exp_mulVec_eigenvector`: `mulVec M v = c • v` implies
   `mulVec (exp M) v = exp c • v`, via CLM-through-tsum.
2. v4 pin fixes: `Matrix.smul_mulVec` (Mul.lean:800) for the smul law;
   `NormedSpace.exp_eq_tsum (𝕂 := ℂ)` with the scalar field EXPLICIT
   (the CharZero ?𝕂 failure was field ambiguity).
-/

set_option autoImplicit false

namespace RHFormalization

noncomputable section

open scoped BigOperators

attribute [local instance] Matrix.linftyOpNormedAddCommGroup
  Matrix.linftyOpNormedSpace Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {N : ℕ}

/-- `A ↦ mulVec A v` as a linear map in the matrix argument. -/
def mulVecByL (v : Fin N → ℂ) :
    Matrix (Fin N) (Fin N) ℂ →ₗ[ℂ] (Fin N → ℂ) where
  toFun A := Matrix.mulVec A v
  map_add' A B := Matrix.add_mulVec A B v
  map_smul' c A := by
    first
      | exact Matrix.smul_mulVec c A v
      | exact Matrix.smul_mulVec (a := c) (A := A) (b := v)
      | (funext j
         simp [Matrix.mulVec, Matrix.dotProduct, Finset.mul_sum, mul_assoc])

/-- Powers act by powers on an eigenvector. -/
theorem pow_mulVec_eigenvector (M : Matrix (Fin N) (Fin N) ℂ)
    (v : Fin N → ℂ) (c : ℂ) (h : Matrix.mulVec M v = c • v) (k : ℕ) :
    Matrix.mulVec (M ^ k) v = (c ^ k) • v := by
  induction k with
  | zero => simp [Matrix.one_mulVec]
  | succ k ih =>
    rw [pow_succ, ← Matrix.mulVec_mulVec, h]
    rw [Matrix.mulVec_smul, ih, smul_smul, pow_succ]
    ring_nf

/-- **BRICK 8a-ii CRUX: matrix exp preserves eigenvectors.** -/
theorem matrix_exp_mulVec_eigenvector (M : Matrix (Fin N) (Fin N) ℂ)
    (v : Fin N → ℂ) (c : ℂ) (h : Matrix.mulVec M v = c • v) :
    Matrix.mulVec (NormedSpace.exp M) v = (NormedSpace.exp c) • v := by
  classical
  set φ : Matrix (Fin N) (Fin N) ℂ →L[ℂ] (Fin N → ℂ) :=
    (mulVecByL (N := N) v).toContinuousLinearMap with hφ
  have hφ_apply : ∀ A : Matrix (Fin N) (Fin N) ℂ,
      φ A = Matrix.mulVec A v := by
    intro A; rfl
  have hsumM : Summable (fun k : ℕ =>
      ((Nat.factorial k : ℂ))⁻¹ • M ^ k) :=
    NormedSpace.expSeries_summable' (𝕂 := ℂ) M
  have hsumc : Summable (fun k : ℕ =>
      ((Nat.factorial k : ℂ))⁻¹ * c ^ k) := by
    have h' : Summable (fun k : ℕ =>
        ((Nat.factorial k : ℂ))⁻¹ • c ^ k) :=
      NormedSpace.expSeries_summable' (𝕂 := ℂ) c
    simpa [smul_eq_mul] using h'
  have hexpM : NormedSpace.exp M
      = ∑' k : ℕ, ((Nat.factorial k : ℂ))⁻¹ • M ^ k :=
    congrFun (NormedSpace.exp_eq_tsum (𝕂 := ℂ)) M
  have hstep : φ (NormedSpace.exp M)
      = ∑' k : ℕ, φ (((Nat.factorial k : ℂ))⁻¹ • M ^ k) := by
    rw [hexpM]
    exact φ.map_tsum hsumM
  have hterm : ∀ k : ℕ, φ (((Nat.factorial k : ℂ))⁻¹ • M ^ k)
      = (((Nat.factorial k : ℂ))⁻¹ * c ^ k) • v := by
    intro k
    rw [map_smul, hφ_apply, pow_mulVec_eigenvector M v c h k, smul_smul]
  have hcollect : (∑' k : ℕ, φ (((Nat.factorial k : ℂ))⁻¹ • M ^ k))
      = (∑' k : ℕ, ((Nat.factorial k : ℂ))⁻¹ * c ^ k) • v := by
    rw [tsum_congr hterm]
    first
      | exact tsum_smul_const hsumc v
      | exact hsumc.tsum_smul_const v
  have hexpc : (∑' k : ℕ, ((Nat.factorial k : ℂ))⁻¹ * c ^ k)
      = NormedSpace.exp c := by
    have h2 : NormedSpace.exp c
        = ∑' k : ℕ, ((Nat.factorial k : ℂ))⁻¹ • c ^ k :=
      congrFun (NormedSpace.exp_eq_tsum (𝕂 := ℂ)) c
    rw [h2]
    exact (tsum_congr fun k => by rw [smul_eq_mul]).symm
  calc Matrix.mulVec (NormedSpace.exp M) v
      = φ (NormedSpace.exp M) := (hφ_apply _).symm
    _ = (∑' k : ℕ, ((Nat.factorial k : ℂ))⁻¹ * c ^ k) • v := by
        rw [hstep, hcollect]
    _ = (NormedSpace.exp c) • v := by rw [hexpc]

#print axioms mulVecByL
#print axioms pow_mulVec_eigenvector
#print axioms matrix_exp_mulVec_eigenvector

end

end RHFormalization
