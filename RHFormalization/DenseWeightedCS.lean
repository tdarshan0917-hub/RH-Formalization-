import RHFormalization.DensePerturbedEnergy
import Mathlib

/-!
# DenseWeightedCS — B(i)-8c inst.1: the quadratic-form Cauchy–Schwarz core

For a real symmetric PSD matrix A:
  (u ⬝ᵥ A *ᵥ v)² ≤ (u ⬝ᵥ A *ᵥ u)·(v ⬝ᵥ A *ᵥ v)
by the discriminant of t ↦ (t•u+v)ᵀA(t•u+v) ≥ 0 (`discrim_le_zero`).
No matrix square root anywhere. inst.2 instantiates v := A⁻¹y to get
(u ⬝ᵥ y)² ≤ (uᵀAu)(yᵀA⁻¹y), inst.3 does the Re/Im recombination
against denseCenteredTrace.
-/

set_option autoImplicit false

namespace RHFormalization

noncomputable section

open Matrix

variable {N : ℕ}

/-- Entry symmetry gives the cross-term swap. -/
theorem dotProduct_mulVec_symm (A : Matrix (Fin N) (Fin N) ℝ)
    (hA : ∀ i j, A i j = A j i) (u v : Fin N → ℝ) :
    u ⬝ᵥ A *ᵥ v = v ⬝ᵥ A *ᵥ u := by
  simp only [dotProduct, mulVec, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
  rw [hA j i]
  ring

/-- PSD quadratic form is pointwise nonneg (real, star-trivial form). -/
theorem quadForm_nonneg {A : Matrix (Fin N) (Fin N) ℝ}
    (hA : A.PosSemidef) (x : Fin N → ℝ) :
    0 ≤ x ⬝ᵥ A *ᵥ x := by
  have h := hA.dotProduct_mulVec_nonneg x
  have hx : star x = x := by
    funext i; exact star_trivial (x i)
  rwa [hx] at h

/-- **8c core: quadratic-form Cauchy–Schwarz** (discriminant route). -/
theorem quadForm_cauchy_schwarz {A : Matrix (Fin N) (Fin N) ℝ}
    (hA : A.PosSemidef) (hsym : ∀ i j, A i j = A j i) (u v : Fin N → ℝ) :
    (u ⬝ᵥ A *ᵥ v) ^ 2 ≤ (u ⬝ᵥ A *ᵥ u) * (v ⬝ᵥ A *ᵥ v) := by
  set a := u ⬝ᵥ A *ᵥ u with ha
  set b := 2 * (u ⬝ᵥ A *ᵥ v) with hb
  set c := v ⬝ᵥ A *ᵥ v with hc
  have hexpand : ∀ t : ℝ,
      (t • u + v) ⬝ᵥ A *ᵥ (t • u + v) = a * (t * t) + b * t + c := by
    intro t
    have hAv : A *ᵥ (t • u + v) = t • (A *ᵥ u) + A *ᵥ v := by
      rw [mulVec_add, mulVec_smul]
    rw [hAv]
    simp only [add_dotProduct, dotProduct_add, smul_dotProduct, dotProduct_smul,
      smul_eq_mul]
    have hcross : v ⬝ᵥ A *ᵥ u = u ⬝ᵥ A *ᵥ v :=
      dotProduct_mulVec_symm A hsym v u
    rw [hcross, ha, hb, hc]
    ring
  have hq : ∀ t : ℝ, 0 ≤ a * (t * t) + b * t + c := by
    intro t
    rw [← hexpand t]
    exact quadForm_nonneg hA _
  have hdisc := discrim_le_zero hq
  unfold discrim at hdisc
  rw [hb] at hdisc
  nlinarith [hdisc]


/-! ## inst.2: CS against the inverse — `(u ⬝ᵥ y)² ≤ (uᵀAu)·(yᵀA⁻¹y)` for PosDef A -/

/-- **8c inverse form**: instantiate the core at `v := A⁻¹ *ᵥ y`. -/
theorem quadForm_cauchy_schwarz_inv {A : Matrix (Fin N) (Fin N) ℝ}
    (hA : A.PosDef) (hsym : ∀ i j, A i j = A j i) (u y : Fin N → ℝ) :
    (u ⬝ᵥ y) ^ 2 ≤ (u ⬝ᵥ A *ᵥ u) * (y ⬝ᵥ A⁻¹ *ᵥ y) := by
  have hdet : IsUnit A.det := (Matrix.isUnit_iff_isUnit_det A).mp hA.isUnit
  have hAAinv : A * A⁻¹ = 1 := Matrix.mul_nonsing_inv A hdet
  have hcore := quadForm_cauchy_schwarz hA.posSemidef hsym u (A⁻¹ *ᵥ y)
  have hmid : A *ᵥ (A⁻¹ *ᵥ y) = y := by
    rw [Matrix.mulVec_mulVec, hAAinv, Matrix.one_mulVec]
  rw [hmid] at hcore
  have hswap : (A⁻¹ *ᵥ y) ⬝ᵥ y = y ⬝ᵥ A⁻¹ *ᵥ y := dotProduct_comm _ _
  calc (u ⬝ᵥ y) ^ 2 ≤ (u ⬝ᵥ A *ᵥ u) * ((A⁻¹ *ᵥ y) ⬝ᵥ y) := hcore
    _ = (u ⬝ᵥ A *ᵥ u) * (y ⬝ᵥ A⁻¹ *ᵥ y) := by rw [hswap]


/-! ## inst.3a: diagonal trace simplifications (GPT-signed separate bank) -/

/-- `Tr(M·diag(d)) = Σ M_ii·d_i`. -/
theorem trace_mul_diagonal (M : Matrix (Fin N) (Fin N) ℝ) (d : Fin N → ℝ) :
    (M * Matrix.diagonal d).trace = ∑ i, M i i * d i := by
  rw [Matrix.trace]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [Matrix.diag_apply, Matrix.mul_diagonal]

/-- **The signed diagonal-only fact**: `Tr(diag(d)·A·diag(d)) = Σ A_ii·d_i²` —
off-diagonal entries of `A` never enter the dual factor. -/
theorem trace_diag_mul_A_mul_diag (d : Fin N → ℝ) (A : Matrix (Fin N) (Fin N) ℝ) :
    (Matrix.diagonal d * A * Matrix.diagonal d).trace = ∑ i, A i i * d i ^ 2 := by
  rw [trace_mul_diagonal]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [Matrix.diagonal_mul]
  ring

/-- `Tr(Cᵀ·diag(d)) = Tr(diag(d)·C)` (both are `Σ d_i·C_ii`). -/
theorem trace_transpose_mul_diagonal_eq (C : Matrix (Fin N) (Fin N) ℝ) (d : Fin N → ℝ) :
    (Cᵀ * Matrix.diagonal d).trace = (Matrix.diagonal d * C).trace := by
  rw [trace_mul_diagonal, trace_diagonal_mul]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [Matrix.transpose_apply]
  ring

/-! ## inst.3b: weighted matrix/Frobenius Cauchy–Schwarz (GPT-signed target) -/

/-- **B(i)-8c inst.3b**: `Tr(DC)² ≤ Tr(DAD)·Tr(CᵀA⁻¹C)` for `D = diagonal d`,
real `C`, PosDef symmetric real `A`. Square-root-free: positivity of
`Tr((C − t·AD)ᵀ A⁻¹ (C − t·AD))` for all real `t` + `discrim_le_zero`. -/
theorem trace_diag_cauchy_schwarz (d : Fin N → ℝ)
    (C A : Matrix (Fin N) (Fin N) ℝ) (hA : A.PosDef) (hsym : Aᵀ = A) :
    ((Matrix.diagonal d * C).trace) ^ 2
      ≤ (Matrix.diagonal d * A * Matrix.diagonal d).trace
          * (Cᵀ * A⁻¹ * C).trace := by
  have hdet : IsUnit A.det := (Matrix.isUnit_iff_isUnit_det A).mp hA.isUnit
  have hAAinv : A * A⁻¹ = 1 := Matrix.mul_nonsing_inv A hdet
  have hAinvA : A⁻¹ * A = 1 := Matrix.nonsing_inv_mul A hdet
  have hpsd : ∀ M : Matrix (Fin N) (Fin N) ℝ, 0 ≤ (Mᵀ * A⁻¹ * M).trace := by
    intro M
    have hinv : (A⁻¹).PosSemidef := (Matrix.PosDef.inv hA).posSemidef
    have h1 : (Mᴴ * A⁻¹ * M).PosSemidef := hinv.conjTranspose_mul_mul_same M
    rw [Matrix.conjTranspose_eq_transpose_of_trivial] at h1
    exact h1.trace_nonneg
  have hcol1 : Cᵀ * A⁻¹ * (A * Matrix.diagonal d) = Cᵀ * Matrix.diagonal d := by
    rw [← mul_assoc, mul_assoc Cᵀ A⁻¹ A, hAinvA, mul_one]
  have hM : ∀ t : ℝ,
      (C - t • (A * Matrix.diagonal d))ᵀ * A⁻¹ * (C - t • (A * Matrix.diagonal d))
        = Cᵀ * A⁻¹ * C - t • (Cᵀ * Matrix.diagonal d)
            - t • (Matrix.diagonal d * C)
            + (t * t) • (Matrix.diagonal d * A * Matrix.diagonal d) := by
    intro t
    have hT : (C - t • (A * Matrix.diagonal d))ᵀ * A⁻¹
        = Cᵀ * A⁻¹ - t • Matrix.diagonal d := by
      rw [Matrix.transpose_sub, Matrix.transpose_smul, Matrix.transpose_mul,
          Matrix.diagonal_transpose, hsym, sub_mul, smul_mul_assoc, mul_assoc,
          hAAinv, mul_one]
    rw [hT]
    simp only [sub_mul, mul_sub, smul_mul_assoc, mul_smul_comm, smul_smul,
      smul_sub]
    rw [hcol1, ← mul_assoc (Matrix.diagonal d) A (Matrix.diagonal d)]
    abel
  have hquad : ∀ t : ℝ,
      0 ≤ (Matrix.diagonal d * A * Matrix.diagonal d).trace * (t * t)
          + (-(2 * (Matrix.diagonal d * C).trace)) * t
          + (Cᵀ * A⁻¹ * C).trace := by
    intro t
    have h0 := hpsd (C - t • (A * Matrix.diagonal d))
    rw [hM t] at h0
    simp only [Matrix.trace_add, Matrix.trace_sub, Matrix.trace_smul,
      smul_eq_mul] at h0
    rw [trace_transpose_mul_diagonal_eq] at h0
    nlinarith [h0]
  have hdisc := discrim_le_zero hquad
  simp only [discrim] at hdisc
  nlinarith [hdisc]

#print axioms dotProduct_mulVec_symm
#print axioms quadForm_nonneg
#print axioms quadForm_cauchy_schwarz
#print axioms quadForm_cauchy_schwarz_inv
#print axioms trace_diagonal_mul
#print axioms trace_mul_diagonal
#print axioms trace_diag_mul_A_mul_diag
#print axioms trace_transpose_mul_diagonal_eq
#print axioms trace_diag_cauchy_schwarz

end

end RHFormalization
