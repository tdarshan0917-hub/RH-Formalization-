import RHFormalization.BumpMatrixElementCosForm
import RHFormalization.CosBumpIntegralBound
import RHFormalization.PrimePotentialBumpSplit

/-!
# Brick 2, stone 5.5: entrywise uniform bound `|V_{mn}| ≤ ∑_q |w(q)|·bumpMass(q)`.
Chains Stone 2 (per-bump split), 3a (cosine form), 3b-0 (cosine bound) by triangle
inequality. Makes V's boundedness usable on the Galerkin matrix.
-/

set_option autoImplicit false

namespace RHFormalization
noncomputable section
open Real MeasureTheory
open scoped Real BigOperators

/-- **Stone 5.5a**: `|B_{mn}(q)| ≤ bumpMass(q)`, uniformly in `m,n`. -/
theorem abs_bumpMatrixElement_le_bumpMass
    (δ : ℝ) (hδ : 0 < δ) (q : ℕ) (L : ℝ) (hL : 0 ≤ L) (m n : ℕ) :
    |bumpMatrixElement δ q L m n| ≤ bumpMass δ q L := by
  rw [bumpMatrixElement_eq_cos]
  calc |(1/2) * cosBumpIntegral δ q L ((m : ℝ) - n)
          - (1/2) * cosBumpIntegral δ q L ((m : ℝ) + n)|
      ≤ |(1/2) * cosBumpIntegral δ q L ((m : ℝ) - n)|
          + |(1/2) * cosBumpIntegral δ q L ((m : ℝ) + n)| := abs_sub _ _
    _ = (1/2) * |cosBumpIntegral δ q L ((m : ℝ) - n)|
          + (1/2) * |cosBumpIntegral δ q L ((m : ℝ) + n)| := by
        rw [abs_mul, abs_mul]; norm_num
    _ ≤ (1/2) * bumpMass δ q L + (1/2) * bumpMass δ q L := by
        apply add_le_add
        · apply mul_le_mul_of_nonneg_left
            (abs_cosBumpIntegral_le_bumpMass δ hδ q L hL _) (by norm_num)
        · apply mul_le_mul_of_nonneg_left
            (abs_cosBumpIntegral_le_bumpMass δ hδ q L hL _) (by norm_num)
    _ = bumpMass δ q L := by ring

/-- **Stone 5.5**: `|V_{mn}| ≤ ∑_q |w(q)|·bumpMass(q)`, uniformly in `m,n`. -/
theorem abs_VmatrixElement_le
    (δ : ℝ) (hδ : 0 < δ) (qs : Finset ℕ) (w : ℕ → ℝ) (L : ℝ) (hL : 0 ≤ L) (m n : ℕ) :
    |VmatrixElement δ qs w L m n| ≤ ∑ q ∈ qs, |w q| * bumpMass δ q L := by
  rw [VmatrixElement_eq_sum_bumps]
  calc |∑ q ∈ qs, w q * bumpMatrixElement δ q L m n|
      ≤ ∑ q ∈ qs, |w q * bumpMatrixElement δ q L m n| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ q ∈ qs, |w q| * bumpMass δ q L := by
        apply Finset.sum_le_sum
        intro q _
        rw [abs_mul]
        apply mul_le_mul_of_nonneg_left
          (abs_bumpMatrixElement_le_bumpMass δ hδ q L hL m n) (abs_nonneg _)

#print axioms abs_bumpMatrixElement_le_bumpMass
#print axioms abs_VmatrixElement_le
end
end RHFormalization
