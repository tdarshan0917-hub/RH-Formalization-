-- SENTINEL: ZBOUND-v1
import RHFormalization.EuclideanDiagTracePairing
import RHFormalization.AdaptivePairedResolventSplit
import Mathlib

/-!
# RemainderTraceZBound — stone 3b-ii

CONSUMER: `hr` of `seam_bdd_of_parts` (SEAMASM) → `h_ctail_le_of_seam_bdd`
(B2CONN) → GATE → RH.

Z := Tr(R_D · V · R_H · T), the remainder of the banked B2 split
`paired_resolvent_split`. Bound:

    ‖Z‖ ≤ (Σ ‖(s+μᵢ)⁻¹‖) · CV · δ⁻¹ · CT

N-FREE: dimension enters nowhere; the free-resolvent mass is the convergent
p-series (banked `summable_inv_nsq_add_one` + `galerkinLam_growth`).
Measured 6.4976e-2 → 6.5024e-2 for N = 8→128.

REMAINING after this brick: CV (Euclidean op bound for V, from the banked
form bound `galerkinV_form_le_supV`) and CT (T is an L² contraction).
-/

set_option autoImplicit false

namespace RHFormalization

noncomputable section

open Complex

variable {N : ℕ}

/-- **Stone 3b-ii: the remainder trace bound.** -/
theorem norm_remainder_trace_le
    (μ : Fin N → ℝ) {V : Matrix (Fin N) (Fin N) ℂ} (hV : V.IsHermitian)
    (s : ℂ) {δ : ℝ} (hδ : 0 < δ)
    (hlowP : ∀ i, δ ≤ ‖s + ((perturbedEigenvalues μ hV i : ℝ) : ℂ)‖)
    (Vop Top : EuclideanSpace ℂ (Fin N) →ₗ[ℂ] EuclideanSpace ℂ (Fin N))
    (CV CT Cm : ℝ) (hCV : 0 ≤ CV) (hCT : 0 ≤ CT)
    (hVop : ∀ x, ‖Vop x‖ ≤ CV * ‖x‖)
    (hTop : ∀ x, ‖Top x‖ ≤ CT * ‖x‖)
    (hmass : (∑ i, ‖(s + ((μ i : ℝ) : ℂ))⁻¹‖) ≤ Cm) (hCm : 0 ≤ Cm) :
    ‖LinearMap.trace ℂ (EuclideanSpace ℂ (Fin N))
        (freeResolventOpE μ s * (Vop * (perturbedResolventOp μ hV s * Top)))‖
      ≤ Cm * (CV * (δ⁻¹ * CT)) := by
  classical
  set X := Vop * (perturbedResolventOp μ hV s * Top) with hX
  set C : ℝ := CV * (δ⁻¹ * CT) with hCdef
  have hC0 : 0 ≤ C := by
    rw [hCdef]; positivity
  have hXbd : ∀ x : EuclideanSpace ℂ (Fin N), ‖X x‖ ≤ C * ‖x‖ := by
    intro x
    have h1 : ‖X x‖ ≤ CV * ‖perturbedResolventOp μ hV s (Top x)‖ := by
      rw [hX]; exact hVop _
    have h2 : ‖perturbedResolventOp μ hV s (Top x)‖ ≤ δ⁻¹ * ‖Top x‖ :=
      perturbedResolventOp_norm_le μ hV s hδ hlowP _
    have h3 : ‖Top x‖ ≤ CT * ‖x‖ := hTop x
    have hδ0 : (0:ℝ) ≤ δ⁻¹ := by positivity
    calc ‖X x‖ ≤ CV * ‖perturbedResolventOp μ hV s (Top x)‖ := h1
      _ ≤ CV * (δ⁻¹ * ‖Top x‖) := mul_le_mul_of_nonneg_left h2 hCV
      _ ≤ CV * (δ⁻¹ * (CT * ‖x‖)) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left h3 hδ0) hCV
      _ = C * ‖x‖ := by rw [hCdef]; ring
  have hswap : LinearMap.trace ℂ (EuclideanSpace ℂ (Fin N))
      (freeResolventOpE μ s * X)
      = LinearMap.trace ℂ (EuclideanSpace ℂ (Fin N))
          (X * freeResolventOpE μ s) :=
    LinearMap.trace_mul_comm ℂ _ _
  rw [hX] at hswap ⊢
  rw [hswap]
  have hpair := norm_trace_mul_diag_le (N := N) (sONB N)
      (freeResolventOpE μ s) X (fun i => (s + ((μ i : ℝ) : ℂ))⁻¹)
      (fun i => freeResolventOpE_apply_ONB μ s i) C hC0 hXbd
  refine le_trans hpair ?_
  exact mul_le_mul_of_nonneg_right hmass hC0

#print axioms norm_remainder_trace_le

end

end RHFormalization
