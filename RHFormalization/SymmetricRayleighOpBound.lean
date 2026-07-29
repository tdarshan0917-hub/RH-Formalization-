-- SENTINEL: RAYOP-v3
import RHFormalization.CompactSpectralGap
import Mathlib

/-!
# SymmetricRayleighOpBound — the CV mechanism (input 3 of 4)

CONSUMER: the `hVop` hypothesis of `norm_split_remainder_trace_le` (ZWIRE),
instantiated at V via the banked `galerkinV_form_le_supV` + `galerkinTrial_normSq`
(which together give ⟨a,Va⟩ ≤ SupVConst·‖a‖², N-free: SupVConst is a fixed tsum).

  T symmetric,  −C‖x‖² ≤ ⟨x,Tx⟩ ≤ C‖x‖²   ⟹   ‖Tx‖ ≤ C‖x‖

Proof: eigenvectors give |λᵢ| ≤ C; Parseval in the eigenbasis.
-/

set_option autoImplicit false

namespace RHFormalization

noncomputable section

open Complex Module

variable {N : ℕ}

/-- Eigenvalues are bounded when the Rayleigh quotient is two-sided bounded. -/
theorem abs_eigenvalue_le_of_rayleigh
    {T : EuclideanSpace ℂ (Fin N) →ₗ[ℂ] EuclideanSpace ℂ (Fin N)}
    (hT : T.IsSymmetric) (C : ℝ)
    (hray : ∀ x : EuclideanSpace ℂ (Fin N),
      |RCLike.re (inner ℂ x (T x))| ≤ C * ‖x‖ ^ 2)
    (i : Fin N) :
    |hT.eigenvalues (perturbedOp_finrank (N := N)) i| ≤ C := by
  set b := hT.eigenvectorBasis (perturbedOp_finrank (N := N)) with hb
  have hev := hT.hasEigenvector_eigenvectorBasis (perturbedOp_finrank (N := N)) i
  have hTx : T (b i) = (hT.eigenvalues (perturbedOp_finrank (N := N)) i : ℂ) • b i := by
    have := hev.1
    rwa [Module.End.mem_eigenspace_iff] at this
  have hnorm : ‖b i‖ = 1 := b.orthonormal.1 i
  have hinner : inner ℂ (b i) (T (b i))
      = (hT.eigenvalues (perturbedOp_finrank (N := N)) i : ℂ) := by
    rw [hTx, inner_smul_right]
    have : inner ℂ (b i) (b i) = (1 : ℂ) := by
      rw [inner_self_eq_norm_sq_to_K, hnorm]
      norm_num
    rw [this, mul_one]
  have h := hray (b i)
  rw [hinner, hnorm] at h
  simpa using h

/-- **Input 3 mechanism: Rayleigh bound ⟹ operator bound.** -/
theorem norm_le_of_rayleigh_bound
    {T : EuclideanSpace ℂ (Fin N) →ₗ[ℂ] EuclideanSpace ℂ (Fin N)}
    (hT : T.IsSymmetric) (C : ℝ) (hC : 0 ≤ C)
    (hray : ∀ x : EuclideanSpace ℂ (Fin N),
      |RCLike.re (inner ℂ x (T x))| ≤ C * ‖x‖ ^ 2)
    (x : EuclideanSpace ℂ (Fin N)) :
    ‖T x‖ ≤ C * ‖x‖ := by
  set b := hT.eigenvectorBasis (perturbedOp_finrank (N := N)) with hb
  set lam := hT.eigenvalues (perturbedOp_finrank (N := N)) with hlam
  have hrepr : ∀ i, b.repr (T x) i = (lam i : ℂ) * b.repr x i := by
    intro i
    have hei : T (b i) = (lam i : ℂ) • b i := by
      have := (hT.hasEigenvector_eigenvectorBasis
        (perturbedOp_finrank (N := N)) i).1
      rwa [Module.End.mem_eigenspace_iff] at this
    have h1 : b.repr (T x) i = inner ℂ (b i) (T x) := b.repr_apply_apply _ i
    have h2 : b.repr x i = inner ℂ (b i) x := b.repr_apply_apply _ i
    rw [h1, h2, ← hT (b i) x, hei, inner_smul_left, Complex.conj_ofReal]
  have hnx : ‖x‖ = ‖b.repr x‖ := (b.repr.norm_map x).symm
  have hnT : ‖T x‖ = ‖b.repr (T x)‖ := (b.repr.norm_map _).symm
  rw [hnx, hnT]
  have hsq1 : ‖b.repr (T x)‖ = Real.sqrt (∑ i, ‖b.repr (T x) i‖ ^ 2) := by
    first
      | exact EuclideanSpace.norm_eq _
      | exact PiLp.norm_eq_of_L2 _ _
  have hsq2 : ‖b.repr x‖ = Real.sqrt (∑ i, ‖b.repr x i‖ ^ 2) := by
    first
      | exact EuclideanSpace.norm_eq _
      | exact PiLp.norm_eq_of_L2 _ _
  rw [hsq1, hsq2]
  have hterm : ∀ i : Fin N, ‖b.repr (T x) i‖ ^ 2 ≤ C ^ 2 * ‖b.repr x i‖ ^ 2 := by
    intro i
    rw [hrepr i, norm_mul, mul_pow]
    have h1 : ‖(lam i : ℂ)‖ ≤ C := by
      rw [Complex.norm_real, Real.norm_eq_abs]
      exact abs_eigenvalue_le_of_rayleigh hT C hray i
    have h2 : (0:ℝ) ≤ ‖(lam i : ℂ)‖ := norm_nonneg _
    have hsq : ‖(lam i : ℂ)‖ ^ 2 ≤ C ^ 2 := by
      rw [pow_two, pow_two]
      exact mul_le_mul h1 h1 h2 hC
    exact mul_le_mul_of_nonneg_right hsq (sq_nonneg _)
  have hsum : (∑ i, ‖b.repr (T x) i‖ ^ 2) ≤ C ^ 2 * ∑ i, ‖b.repr x i‖ ^ 2 := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum (fun i _ => hterm i)
  calc Real.sqrt (∑ i, ‖b.repr (T x) i‖ ^ 2)
      ≤ Real.sqrt (C ^ 2 * ∑ i, ‖b.repr x i‖ ^ 2) := Real.sqrt_le_sqrt hsum
    _ = C * Real.sqrt (∑ i, ‖b.repr x i‖ ^ 2) := by
        rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hC]

#print axioms abs_eigenvalue_le_of_rayleigh
#print axioms norm_le_of_rayleigh_bound

end

end RHFormalization
