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

#print axioms dotProduct_mulVec_symm
#print axioms quadForm_nonneg
#print axioms quadForm_cauchy_schwarz

end

end RHFormalization
