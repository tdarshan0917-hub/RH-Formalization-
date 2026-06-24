import RHFormalization.CorrectedResolventPayload
import RHFormalization.ConcreteResolventConvergence
import RHFormalization.ResolventLocalBound
import RHFormalization.ResolventTraceHolo
import RHFormalization.EigenvalueGrowthSummable
import RHFormalization.MontelUniqueLimit
import Mathlib

namespace RHFormalization
noncomputable section
open Complex Set Topology Filter

private def cLam : ℕ → ℝ := fun n => ((n : ℝ) * Real.pi) ^ 2
private theorem cLam_nonneg (n : ℕ) : 0 ≤ cLam n := by unfold cLam; positivity

private theorem spectralResolventPartial_eq (a : DFiniteStage) (s : ℂ) :
    spectralResolventPartial a s
      = Finset.sum (Finset.range (resolventIndices a).card)
          (fun k => (s + (cLam k : ℂ))⁻¹) := by
  unfold spectralResolventPartial cLam; rfl

private def wEnv (s : ℂ) : ℝ := max |s.im| (max s.re 0)

private theorem wEnv_continuous : Continuous wEnv := by
  unfold wEnv
  exact (continuous_abs.comp Complex.continuous_im).max
    ((Complex.continuous_re).max continuous_const)

private theorem wEnv_pos_of_mem_Omega {s : ℂ} (hs : s ∈ Ω) : 0 < wEnv s := by
  rw [Omega_eq_slitPlane] at hs
  rcases hs with hre | him
  · exact lt_of_lt_of_le (lt_of_lt_of_le hre (le_max_left _ _)) (le_max_right _ _)
  · exact lt_of_lt_of_le (abs_pos.mpr him) (le_max_left _ _)

private theorem norm_add_real_ge_wEnv (s : ℂ) {lam : ℝ} (hlam : 0 ≤ lam) :
    wEnv s ≤ ‖s + (lam : ℂ)‖ := by
  unfold wEnv
  have him : |s.im| ≤ ‖s + (lam : ℂ)‖ := by
    have h1 : |(s + (lam : ℂ)).im| ≤ ‖s + (lam : ℂ)‖ := abs_im_le_norm _
    simpa [Complex.add_im, Complex.ofReal_im] using h1
  have hre : s.re ≤ ‖s + (lam : ℂ)‖ := by
    have h2 : (s + (lam : ℂ)).re ≤ ‖s + (lam : ℂ)‖ := re_le_norm _
    simp only [Complex.add_re, Complex.ofReal_re] at h2
    linarith
  exact max_le him (max_le hre (norm_nonneg _))

private theorem re_ge_neg_norm (s : ℂ) : -‖s‖ ≤ s.re := by
  have := abs_re_le_norm s; rw [abs_le] at this; linarith [this.1]

theorem correctedResolvent_F_bound :
  ∀ K : Set ℂ, IsCompact K → K ⊆ Ω →
      ∃ CF : ℝ, 0 ≤ CF ∧
          ∀ a : DFiniteStage, ∀ s : ℂ, s ∈ K →
              ‖spectralResolventPartial a s‖ ≤ CF := by
  intro K hK hKOmega
  rcases K.eq_empty_or_nonempty with hKe | hKne
  · exact ⟨0, le_refl 0, fun a s hs => absurd (hKe ▸ hs) (Set.notMem_empty s)⟩
  obtain ⟨s1, hs1K, hs1max⟩ :=
    hK.exists_isMaxOn hKne (continuous_norm.continuousOn (s := K))
  have hsR0 : ∀ s ∈ K, ‖s‖ ≤ ‖s1‖ := isMaxOn_iff.mp hs1max
  have hR0pos : 0 ≤ ‖s1‖ := norm_nonneg _
  obtain ⟨s0, hs0K, hs0min⟩ :=
    hK.exists_isMinOn hKne (wEnv_continuous.continuousOn (s := K))
  have hdmin : ∀ s ∈ K, wEnv s0 ≤ wEnv s := isMinOn_iff.mp hs0min
  have hdpos : 0 < wEnv s0 := wEnv_pos_of_mem_Omega (hKOmega hs0K)
  have hCKpos0 : 0 ≤ (2 * (1 + ‖s1‖)) / wEnv s0 + 2 := by positivity
  have hCK2_0 : (2 : ℝ) ≤ (2 * (1 + ‖s1‖)) / wEnv s0 + 2 := by
    have h : 0 ≤ (2 * (1 + ‖s1‖)) / wEnv s0 := by positivity
    linarith
  have hCKd0 : 2 * (1 + ‖s1‖) ≤ ((2 * (1 + ‖s1‖)) / wEnv s0 + 2) * wEnv s0 := by
    have he : (2 * (1 + ‖s1‖)) / wEnv s0 * wEnv s0 = 2 * (1 + ‖s1‖) := by
      field_simp
    nlinarith [hdpos, he, hR0pos]
  set R0 := ‖s1‖ with hR0def
  set dlt := wEnv s0 with hdltdef
  set CK := (2 * (1 + R0)) / dlt + 2 with hCK
  have hCKpos : 0 ≤ CK := hCKpos0
  have hCK2 : (2 : ℝ) ≤ CK := hCK2_0
  have hCKd : 2 * (1 + R0) ≤ CK * dlt := hCKd0
  have husummable : Summable (fun n => CK * (1 + cLam n)⁻¹) :=
    concrete_summable_resolvent.mul_left CK
  refine ⟨∑' n, CK * (1 + cLam n)⁻¹,
    tsum_nonneg (fun n => by have := cLam_nonneg n; positivity), ?_⟩
  intro a s hs
  rw [spectralResolventPartial_eq]
  have hperterm : ∀ k, ‖(s + (cLam k : ℂ))⁻¹‖ ≤ CK * (1 + cLam k)⁻¹ := by
    intro k
    have hsk_ne : s + (cLam k : ℂ) ≠ 0 :=
      add_real_ne_zero_of_mem_Omega (hKOmega hs) (cLam_nonneg k)
    have hnorm_pos : 0 < ‖s + (cLam k : ℂ)‖ := norm_pos_iff.mpr hsk_ne
    have hdbd : dlt ≤ ‖s + (cLam k : ℂ)‖ :=
      le_trans (hdmin s hs) (norm_add_real_ge_wEnv s (cLam_nonneg k))
    have hrebd : cLam k - R0 ≤ ‖s + (cLam k : ℂ)‖ := by
      have h2 : (s + (cLam k : ℂ)).re ≤ ‖s + (cLam k : ℂ)‖ := re_le_norm _
      simp only [Complex.add_re, Complex.ofReal_re] at h2
      have hneg := re_ge_neg_norm s
      have hsR0' := hsR0 s hs
      linarith
    have hL0 : (0 : ℝ) ≤ cLam k := cLam_nonneg k
    have hden_pos : (0 : ℝ) < 1 + cLam k := by linarith
    have hkey : (1 + cLam k) ≤ CK * ‖s + (cLam k : ℂ)‖ := by
      by_cases hk : cLam k < 1 + 2 * R0
      · have hstep : CK * dlt ≤ CK * ‖s + (cLam k : ℂ)‖ :=
          mul_le_mul_of_nonneg_left hdbd hCKpos
        nlinarith [hstep, hCKd, hk, hR0pos]
      · have hkge : 1 + 2 * R0 ≤ cLam k := not_lt.mp hk
        have hstep : 2 * ‖s + (cLam k : ℂ)‖ ≤ CK * ‖s + (cLam k : ℂ)‖ :=
          mul_le_mul_of_nonneg_right hCK2 (norm_nonneg _)
        nlinarith [hstep, hrebd, hkge, hR0pos]
    rw [norm_inv]
    rw [inv_le_iff_one_le_mul₀ hnorm_pos]
    calc (1 : ℝ) = (1 + cLam k)⁻¹ * (1 + cLam k) := by
          field_simp
      _ ≤ (1 + cLam k)⁻¹ * (CK * ‖s + (cLam k : ℂ)‖) :=
          mul_le_mul_of_nonneg_left hkey (by positivity)
      _ = CK * (1 + cLam k)⁻¹ * ‖s + (cLam k : ℂ)‖ := by ring
  calc ‖Finset.sum (Finset.range (resolventIndices a).card)
          (fun k => (s + (cLam k : ℂ))⁻¹)‖
      ≤ Finset.sum (Finset.range (resolventIndices a).card)
          (fun k => ‖(s + (cLam k : ℂ))⁻¹‖) := norm_sum_le _ _
    _ ≤ Finset.sum (Finset.range (resolventIndices a).card)
          (fun k => CK * (1 + cLam k)⁻¹) :=
        Finset.sum_le_sum (fun k _ => hperterm k)
    _ ≤ ∑' n, CK * (1 + cLam n)⁻¹ :=
        husummable.sum_le_tsum _ (fun k _ => by have := cLam_nonneg k; positivity)


/-- Per-term resolvent majorant on a compact `K ⊆ Ω`: the extractable form of the
inner estimate already proven inside `correctedResolvent_F_bound`. Returns a constant
`CK` (depending on `K`), the summability of `CK·(1+lam)⁻¹`, and the per-term bound. -/
theorem resolvent_term_bound_on_compact
    (K : Set ℂ) (hK : IsCompact K) (hKOmega : K ⊆ Ω) :
    ∃ CK : ℝ, 0 ≤ CK ∧
      Summable (fun n => CK * (1 + cLam n)⁻¹) ∧
      ∀ k : ℕ, ∀ s : ℂ, s ∈ K →
        ‖(s + (cLam k : ℂ))⁻¹‖ ≤ CK * (1 + cLam k)⁻¹ := by
  rcases K.eq_empty_or_nonempty with hKe | hKne
  · exact ⟨0, le_refl 0, concrete_summable_resolvent.mul_left 0,
      fun k s hs => absurd (hKe ▸ hs) (Set.notMem_empty s)⟩
  obtain ⟨s1, hs1K, hs1max⟩ :=
    hK.exists_isMaxOn hKne (continuous_norm.continuousOn (s := K))
  have hsR0 : ∀ s ∈ K, ‖s‖ ≤ ‖s1‖ := isMaxOn_iff.mp hs1max
  have hR0pos : 0 ≤ ‖s1‖ := norm_nonneg _
  obtain ⟨s0, hs0K, hs0min⟩ :=
    hK.exists_isMinOn hKne (wEnv_continuous.continuousOn (s := K))
  have hdmin : ∀ s ∈ K, wEnv s0 ≤ wEnv s := isMinOn_iff.mp hs0min
  have hdpos : 0 < wEnv s0 := wEnv_pos_of_mem_Omega (hKOmega hs0K)
  have hCKpos0 : 0 ≤ (2 * (1 + ‖s1‖)) / wEnv s0 + 2 := by positivity
  have hCK2_0 : (2 : ℝ) ≤ (2 * (1 + ‖s1‖)) / wEnv s0 + 2 := by
    have h : 0 ≤ (2 * (1 + ‖s1‖)) / wEnv s0 := by positivity
    linarith
  have hCKd0 : 2 * (1 + ‖s1‖) ≤ ((2 * (1 + ‖s1‖)) / wEnv s0 + 2) * wEnv s0 := by
    have he : (2 * (1 + ‖s1‖)) / wEnv s0 * wEnv s0 = 2 * (1 + ‖s1‖) := by field_simp
    nlinarith [hdpos, he, hR0pos]
  set R0 := ‖s1‖ with hR0def
  set dlt := wEnv s0 with hdltdef
  set CK := (2 * (1 + R0)) / dlt + 2 with hCK
  have hCKpos : 0 ≤ CK := hCKpos0
  have hCK2 : (2 : ℝ) ≤ CK := hCK2_0
  have hCKd : 2 * (1 + R0) ≤ CK * dlt := hCKd0
  have husummable : Summable (fun n => CK * (1 + cLam n)⁻¹) :=
    concrete_summable_resolvent.mul_left CK
  refine ⟨CK, hCKpos, husummable, ?_⟩
  intro k s hs
  have hsk_ne : s + (cLam k : ℂ) ≠ 0 :=
    add_real_ne_zero_of_mem_Omega (hKOmega hs) (cLam_nonneg k)
  have hnorm_pos : 0 < ‖s + (cLam k : ℂ)‖ := norm_pos_iff.mpr hsk_ne
  have hdbd : dlt ≤ ‖s + (cLam k : ℂ)‖ :=
    le_trans (hdmin s hs) (norm_add_real_ge_wEnv s (cLam_nonneg k))
  have hrebd : cLam k - R0 ≤ ‖s + (cLam k : ℂ)‖ := by
    have h2 : (s + (cLam k : ℂ)).re ≤ ‖s + (cLam k : ℂ)‖ := re_le_norm _
    simp only [Complex.add_re, Complex.ofReal_re] at h2
    have hneg := re_ge_neg_norm s
    have hsR0' := hsR0 s hs
    linarith
  have hL0 : (0 : ℝ) ≤ cLam k := cLam_nonneg k
  have hden_pos : (0 : ℝ) < 1 + cLam k := by linarith
  have hkey : (1 + cLam k) ≤ CK * ‖s + (cLam k : ℂ)‖ := by
    by_cases hk : cLam k < 1 + 2 * R0
    · have hstep : CK * dlt ≤ CK * ‖s + (cLam k : ℂ)‖ :=
        mul_le_mul_of_nonneg_left hdbd hCKpos
      nlinarith [hstep, hCKd, hk, hR0pos]
    · have hkge : 1 + 2 * R0 ≤ cLam k := not_lt.mp hk
      have hstep : 2 * ‖s + (cLam k : ℂ)‖ ≤ CK * ‖s + (cLam k : ℂ)‖ :=
        mul_le_mul_of_nonneg_right hCK2 (norm_nonneg _)
      nlinarith [hstep, hrebd, hkge, hR0pos]
  rw [norm_inv]
  rw [inv_le_iff_one_le_mul₀ hnorm_pos]
  calc (1 : ℝ) = (1 + cLam k)⁻¹ * (1 + cLam k) := by field_simp
    _ ≤ (1 + cLam k)⁻¹ * (CK * ‖s + (cLam k : ℂ)‖) :=
        mul_le_mul_of_nonneg_left hkey (by positivity)
    _ = CK * (1 + cLam k)⁻¹ * ‖s + (cLam k : ℂ)‖ := by ring

end
end RHFormalization
