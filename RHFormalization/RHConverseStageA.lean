import RHFormalization.DenseSealEndpoint
import RHFormalization.DBFFStarObject
import RHFormalization.PolylogEndpoint
import Mathlib

/-!
# RHConverseStageA — RHC-1: hP_dense follows from a uniform bound on the star object

`starObject n s = Σ_{k ≤ √(n+2)} Λ(k) k^{-ρ} − (Y^{1-ρ}−1)/(1−ρ) − 1/(1−ρ)`, `ρ = ½ + √(s+¼)`.
* `compensatedB_locbdd_of_starObject_locbdd`: star-object bound ⇒ compensated-B bound
  (kernel prefactor bounded via `sqrtRe_min`).
* `hPdense_of_compensatedB_locbdd`: compensated-B bound ⇒ hP_dense (window and defect terms are
  unconditionally bounded: `BcorrWinDense_uniform_bound`, `denseGalerkinTransformDefect_loc_bdd`).
* `hPdense_of_starObject_locbdd` (RHC-1). Under RH the star object is bounded (von Koch + Abel
  summation; RHC-2/RHC-3), so this is the first leg of `hP_dense ↔ RH`.
-/

set_option autoImplicit false

namespace RHFormalization

noncomputable section

/-- Compensated-B bound ⇒ hP_dense. -/
theorem hPdense_of_compensatedB_locbdd
    (h : ∀ K : Set ℂ, IsCompact K → K ⊆ Ω →
        ∃ C : ℝ, ∀ n, ∀ s ∈ K, ‖compensatedBFamily n s‖ ≤ C) :
    ∀ K : Set ℂ, IsCompact K → K ⊆ Ω →
        ∃ Cp : ℝ, ∀ n, ∀ s ∈ K,
          ‖(2:ℂ) * denseFreePairedTransform n s - compensatorM n s‖ ≤ Cp := by
  intro K hK hKΩ
  obtain ⟨C, hC⟩ := h K hK hKΩ
  obtain ⟨Cw, hWK⟩ := BcorrWinDense_uniform_bound K hK hKΩ
  obtain ⟨Cd, hDK⟩ := denseGalerkinTransformDefect_loc_bdd K hKΩ hK
  refine ⟨C + 2 * Cw + 2 * Cd, fun n s hs => ?_⟩
  have hlock := denseFreePairedTransform_route_lock n s
  have hid : (2:ℂ) * denseFreePairedTransform n s - compensatorM n s
      = (compensatedBFamily n s - 2 * BcorrWinDense n s)
        + 2 * denseGalerkinTransformDefect n s := by
    unfold compensatedBFamily
    linear_combination (2:ℂ) * hlock
  rw [hid]
  have e2 : ‖(2:ℂ)‖ = 2 := by norm_num
  have t1 := norm_add_le (compensatedBFamily n s - 2 * BcorrWinDense n s)
    (2 * denseGalerkinTransformDefect n s)
  have t2 := norm_sub_le (compensatedBFamily n s) (2 * BcorrWinDense n s)
  rw [norm_mul, e2] at t1 t2
  linarith [hC n s hs, hWK n s hs, hDK n s hs]

/-- Star-object bound ⇒ compensated-B bound. -/
theorem compensatedB_locbdd_of_starObject_locbdd
    (hstar : ∀ K : Set ℂ, IsCompact K → K ⊆ Ω →
        ∃ C : ℝ, ∀ n, ∀ s ∈ K, ‖starObject n s‖ ≤ C) :
    ∀ K : Set ℂ, IsCompact K → K ⊆ Ω →
        ∃ C : ℝ, ∀ n, ∀ s ∈ K, ‖compensatedBFamily n s‖ ≤ C := by
  intro K hK hKΩ
  obtain ⟨c, hc0, hc⟩ := sqrtRe_min K hK hKΩ
  obtain ⟨Cs, hCs⟩ := hstar K hK hKΩ
  have hker : ∀ s ∈ K, ‖(1:ℂ) / (2 * Complex.sqrt (s + (1/4:ℂ)))‖ ≤ (2 * c)⁻¹ := by
    intro s hs
    have hw : c ≤ ‖Complex.sqrt (s + (1/4:ℂ))‖ := by
      refine le_trans (hc s hs) ?_
      first
        | exact Complex.re_le_norm _
        | exact Complex.re_le_abs _
        | exact le_trans (le_abs_self _) (Complex.abs_re_le_norm _)
    have e2 : ‖(2:ℂ)‖ = 2 := by norm_num
    rw [norm_div, norm_one, norm_mul, e2, ← one_div]
    exact one_div_le_one_div_of_le (by positivity) (by linarith)
  refine ⟨(2 * c)⁻¹ * Cs, fun n s hs => ?_⟩
  exact compensated_B_bounded_of_starObject_bounded K hKΩ (2 * c) (by positivity) hker Cs
    hCs n s hs

/-- **RHC-1 — a uniformly bounded star object gives hP_dense.** -/
theorem hPdense_of_starObject_locbdd
    (hstar : ∀ K : Set ℂ, IsCompact K → K ⊆ Ω →
        ∃ C : ℝ, ∀ n, ∀ s ∈ K, ‖starObject n s‖ ≤ C) :
    ∀ K : Set ℂ, IsCompact K → K ⊆ Ω →
        ∃ Cp : ℝ, ∀ n, ∀ s ∈ K,
          ‖(2:ℂ) * denseFreePairedTransform n s - compensatorM n s‖ ≤ Cp :=
  hPdense_of_compensatedB_locbdd (compensatedB_locbdd_of_starObject_locbdd hstar)

#print axioms hPdense_of_compensatedB_locbdd
#print axioms compensatedB_locbdd_of_starObject_locbdd
#print axioms hPdense_of_starObject_locbdd

end

end RHFormalization
