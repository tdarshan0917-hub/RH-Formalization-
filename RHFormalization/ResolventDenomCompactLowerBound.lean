-- SENTINEL: L0a-resolvent-denom-lower-v4
import RHFormalization.ResolventTraceHolo
import Mathlib

/-!
# L0a — Compact-uniform denominator floor on Ω
`resolventDenom_lower_bound`: ∀ K ⋐ Ω, ∃ c > 0, ∀ s ∈ K, ∀ ξ : ℝ,
c·(1+ξ²) ≤ ‖s + 1/4 + ξ²‖. Shared by L0c (Ω-analyticity of the continuum
cosine-resolvent integral) and L1 (per-spike Riemann-sum comparison).
v4: explicit rw instantiation (denom_eq_add_real s ξ — bare rw grabbed the
z₀ atom); hcancel rewritten forward inside hstep instead of ← in goal.
-/

set_option autoImplicit false

namespace RHFormalization

noncomputable section

/-- Cast shape: the denominator as a single real shift of `s`. -/
theorem denom_eq_add_real (s : ℂ) (ξ : ℝ) :
    s + (1/4 : ℂ) + (ξ : ℂ)^2 = s + (((1/4 + ξ^2 : ℝ)) : ℂ) := by
  push_cast
  ring

/-- On Ω the resolvent denominator never vanishes (poles live on the cut). -/
theorem denom_ne_zero_of_mem_Omega {s : ℂ} (hs : s ∈ Ω) (ξ : ℝ) :
    s + (1/4 : ℂ) + (ξ : ℂ)^2 ≠ 0 := by
  rw [denom_eq_add_real]
  exact add_real_ne_zero_of_mem_Omega hs (by positivity)

/-- **L0a — the compact-uniform denominator floor on Ω.** -/
theorem resolventDenom_lower_bound (K : Set ℂ) (hK : IsCompact K) (hKΩ : K ⊆ Ω) :
    ∃ c : ℝ, 0 < c ∧ ∀ s ∈ K, ∀ ξ : ℝ,
      c * (1 + ξ^2) ≤ ‖s + (1/4 : ℂ) + (ξ : ℂ)^2‖ := by
  rcases K.eq_empty_or_nonempty with hKe | ⟨s₀, hs₀⟩
  · refine ⟨1, one_pos, ?_⟩
    intro s hs
    rw [hKe] at hs
    simp at hs
  obtain ⟨M, hM⟩ := hK.exists_bound_of_continuousOn continuousOn_id
  have hM0 : (0:ℝ) ≤ M := le_trans (norm_nonneg s₀) (hM s₀ hs₀)
  have hden_pos : (0:ℝ) < 1 + 2*(M+1) := by linarith
  have hTcomp : IsCompact (K ×ˢ Set.Icc (-(1 + 2*(M+1))) (1 + 2*(M+1))) :=
    hK.prod isCompact_Icc
  have hTne : (K ×ˢ Set.Icc (-(1 + 2*(M+1))) (1 + 2*(M+1))).Nonempty :=
    ⟨(s₀, 0), Set.mk_mem_prod hs₀ (Set.mem_Icc.mpr ⟨by linarith, by linarith⟩)⟩
  have hFc : ContinuousOn (fun p : ℂ × ℝ => ‖p.1 + (1/4 : ℂ) + ((p.2 : ℂ))^2‖)
      (K ×ˢ Set.Icc (-(1 + 2*(M+1))) (1 + 2*(M+1))) := by
    apply Continuous.continuousOn
    apply Continuous.norm
    exact (continuous_fst.add continuous_const).add
      ((Complex.continuous_ofReal.comp continuous_snd).pow 2)
  obtain ⟨⟨z₀, ξ₀⟩, hp₀T, hminOn⟩ := hTcomp.exists_isMinOn hTne hFc
  have hmin : ∀ p ∈ K ×ˢ Set.Icc (-(1 + 2*(M+1))) (1 + 2*(M+1)),
      ‖z₀ + (1/4 : ℂ) + (ξ₀ : ℂ)^2‖ ≤ ‖p.1 + (1/4 : ℂ) + ((p.2 : ℂ))^2‖ :=
    fun p hp => isMinOn_iff.mp hminOn p hp
  have hz₀K : z₀ ∈ K := (Set.mem_prod.mp hp₀T).1
  have hc₁ : (0:ℝ) < ‖z₀ + (1/4 : ℂ) + (ξ₀ : ℂ)^2‖ :=
    norm_pos_iff.mpr (denom_ne_zero_of_mem_Omega (hKΩ hz₀K) ξ₀)
  refine ⟨min (1/4) (‖z₀ + (1/4 : ℂ) + (ξ₀ : ℂ)^2‖ / (1 + 2*(M+1))),
    lt_min (by norm_num) (div_pos hc₁ hden_pos), ?_⟩
  intro s hs ξ
  have hsM : ‖s‖ ≤ M := hM s hs
  have hc14 : min (1/4) (‖z₀ + (1/4 : ℂ) + (ξ₀ : ℂ)^2‖ / (1 + 2*(M+1))) ≤ 1/4 :=
    min_le_left _ _
  by_cases hnear : ξ^2 ≤ 2*(M+1)
  · -- NEAR: inside the compact window, the minimum applies
    have habs : |ξ| ≤ 1 + 2*(M+1) := by
      nlinarith [sq_abs ξ, sq_nonneg (|ξ| - 1), abs_nonneg ξ]
    have hmemT : (s, ξ) ∈ K ×ˢ Set.Icc (-(1 + 2*(M+1))) (1 + 2*(M+1)) :=
      Set.mk_mem_prod hs (Set.mem_Icc.mpr (abs_le.mp habs))
    have hge := hmin (s, ξ) hmemT
    have hxi : 1 + ξ^2 ≤ 1 + 2*(M+1) := by linarith
    have hstep : min (1/4) (‖z₀ + (1/4 : ℂ) + (ξ₀ : ℂ)^2‖ / (1 + 2*(M+1))) * (1 + ξ^2)
        ≤ (‖z₀ + (1/4 : ℂ) + (ξ₀ : ℂ)^2‖ / (1 + 2*(M+1))) * (1 + 2*(M+1)) := by
      apply mul_le_mul (min_le_right _ _) hxi (by positivity)
      positivity
    rw [div_mul_cancel₀ _ (ne_of_gt hden_pos)] at hstep
    exact le_trans hstep hge
  · -- FAR: triangle inequality; ξ² dominates M
    push_neg at hnear
    rw [denom_eq_add_real s ξ]
    have htri := norm_add_le (s + (((1/4 + ξ^2 : ℝ)) : ℂ)) (-s)
    have hshape : s + (((1/4 + ξ^2 : ℝ)) : ℂ) + (-s) = (((1/4 + ξ^2 : ℝ)) : ℂ) := by
      ring
    rw [hshape, norm_neg] at htri
    have hwn : ‖(((1/4 + ξ^2 : ℝ)) : ℂ)‖ = 1/4 + ξ^2 := by
      rw [Complex.norm_real, Real.norm_eq_abs]
      exact abs_of_nonneg (by positivity)
    rw [hwn] at htri
    have hkey : min (1/4) (‖z₀ + (1/4 : ℂ) + (ξ₀ : ℂ)^2‖ / (1 + 2*(M+1))) * (1 + ξ^2)
        ≤ (1/4) * (1 + ξ^2) :=
      mul_le_mul_of_nonneg_right hc14 (by positivity)
    linarith

/-- Companion in the form L1 consumes: the resolvent term is uniformly
`≤ (1/c)/(1+ξ²)` on every Ω-compact. -/
theorem resolventTerm_upper_bound (K : Set ℂ) (hK : IsCompact K) (hKΩ : K ⊆ Ω) :
    ∃ c : ℝ, 0 < c ∧ ∀ s ∈ K, ∀ ξ : ℝ,
      ‖1 / (s + (1/4 : ℂ) + (ξ : ℂ)^2)‖ ≤ 1 / (c * (1 + ξ^2)) := by
  obtain ⟨c, hc, hbound⟩ := resolventDenom_lower_bound K hK hKΩ
  refine ⟨c, hc, ?_⟩
  intro s hs ξ
  rw [norm_div, norm_one]
  exact one_div_le_one_div_of_le (by positivity) (hbound s hs ξ)

#print axioms denom_eq_add_real
#print axioms denom_ne_zero_of_mem_Omega
#print axioms resolventDenom_lower_bound
#print axioms resolventTerm_upper_bound

end

end RHFormalization
