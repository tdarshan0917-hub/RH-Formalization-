import RHFormalization.DenseTraceCS
import RHFormalization.DenseFreeDualBound
import RHFormalization.DensePerturbedEnergy
import Mathlib

/-!
# DenseTraceUniformBound — B(i)-8d: uniform energy ⇒ compact trace bound

Uniform `denseQV` hypothesis + 8b compact `S^V` bound + 3c(ii) CS
⇒ `‖denseCenteredTrace‖` bounded on compacts, uniformly in n.
Sqrt-free: squared bound first, then `x² ≤ B ⇒ x ≤ max 1 B`.
-/

set_option autoImplicit false

namespace RHFormalization

noncomputable section

/-- Elementary sqrt-free extraction: `0 ≤ x` and `x² ≤ B` give `x ≤ max 1 B`. -/
theorem le_max_one_of_sq_le {x B : ℝ} (hx : 0 ≤ x) (h : x ^ 2 ≤ B) :
    x ≤ max 1 B := by
  rcases le_or_gt x 1 with hx1 | hx1
  · exact le_trans hx1 (le_max_left _ _)
  · have hxx : x ≤ x ^ 2 := by nlinarith
    exact le_trans (le_trans hxx h) (le_max_right _ _)

/-- **B(i)-8d**: a uniform bound on the perturbed energy forces the centered
trace to be bounded on every compact `K ⊆ Ω`, uniformly in `n`. -/
theorem denseCenteredTrace_bounded_on_compact
    {a : ℝ} (ha : 0 < a) {CQ : ℝ} (hQ : ∀ n : ℕ, denseQV n a ≤ CQ)
    (K : Set ℂ) (hK : IsCompact K) (hKΩ : K ⊆ Ω) :
    ∃ CT : ℝ, ∀ n : ℕ, ∀ s ∈ K, ‖denseCenteredTrace n s‖ ≤ CT := by
  obtain ⟨CS, hCS, hSV⟩ := denseSVReal_dnorm_bounded_on_compact K hK hKΩ ha
  refine ⟨max 1 (4 * CQ * CS), fun n s hs => ?_⟩
  have hQn : 0 ≤ denseQV n a := denseQV_nonneg n ha
  have h1 : ‖denseCenteredTrace n s‖ ^ 2
      ≤ 4 * denseQV n a * denseSVReal n a (denseDnorm n s) :=
    denseCenteredTrace_sq_le n ha s
  have h2 : 4 * denseQV n a * denseSVReal n a (denseDnorm n s)
      ≤ 4 * CQ * CS := by
    have hSVn := hSV n s hs
    have hQCQ := hQ n
    nlinarith
  exact le_max_one_of_sq_le (norm_nonneg _) (le_trans h1 h2)

#print axioms le_max_one_of_sq_le
#print axioms denseCenteredTrace_bounded_on_compact

end

end RHFormalization
