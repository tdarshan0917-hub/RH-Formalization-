import RHFormalization.DenseTraceUniformBound
import RHFormalization.DenseBridgeIdentity
import RHFormalization.DenseSealEndpoint
import Mathlib

/-!
# DenseSealB8 — B(i)-8e/8f: uniform energy ⇒ hP_dense ⇒ RH

8e: uniform `denseQV` bound + B7 bridge identity + bounded remainder
⇒ the exact `hP_dense` predicate Stage A consumes.
8f: composition with `RH_from_pairedTransform_only_dense` — the Stage B(i)
capstone.
-/

set_option autoImplicit false

namespace RHFormalization

noncomputable section

/-- **B(i)-8e**: a uniform bound on the perturbed energy yields the exact
`hP_dense` compact-local boundedness predicate. -/
theorem hP_dense_of_denseQV_uniform
    {a : ℝ} (ha : 0 < a) (hQ : ∃ CQ : ℝ, ∀ n : ℕ, denseQV n a ≤ CQ) :
    ∀ K : Set ℂ, IsCompact K → K ⊆ Ω →
      ∃ Cp : ℝ, ∀ n, ∀ s ∈ K,
        ‖(2:ℂ) * denseFreePairedTransform n s - compensatorM n s‖ ≤ Cp := by
  obtain ⟨CQ, hCQ⟩ := hQ
  intro K hK hKΩ
  obtain ⟨CT, hCT⟩ := denseCenteredTrace_bounded_on_compact ha hCQ K hK hKΩ
  obtain ⟨M, hM⟩ := denseRemainder_bounded_on_compact K hK hKΩ
  refine ⟨CT + M, fun n s hs => ?_⟩
  rw [denseBridge_identity' n (hKΩ hs)]
  calc ‖denseCenteredTrace n s + denseRemainder n s‖
      ≤ ‖denseCenteredTrace n s‖ + ‖denseRemainder n s‖ := norm_add_le _ _
    _ ≤ CT + M := add_le_add (hCT n s hs) (hM n s hs)

/-- **B(i)-8f — STAGE B(i) CAPSTONE**: a uniform bound on the explicit
finite-dimensional perturbed energy `denseQV` implies the Riemann
Hypothesis. Composition of 8e with the Stage A endpoint. -/
theorem RH_of_denseQV_uniform
    (a : ℝ) (ha : 0 < a) (hQ : ∃ CQ : ℝ, ∀ n : ℕ, denseQV n a ≤ CQ) :
    RiemannHypothesis :=
  RH_from_pairedTransform_only_dense (hP_dense_of_denseQV_uniform ha hQ)

#print axioms hP_dense_of_denseQV_uniform
#print axioms RH_of_denseQV_uniform

end

end RHFormalization
