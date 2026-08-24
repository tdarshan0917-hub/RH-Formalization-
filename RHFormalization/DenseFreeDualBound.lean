import RHFormalization.DensePerturbedEnergy
import RHFormalization.SpectralWeightSumExport
import RHFormalization.DenseBridgeIdentity
import Mathlib

/-!
# DenseFreeDualBound — B(i)-8a: compact bound on the free dual factor S⁰

At the live dual vector `d_k(s) = ‖(s+¼+λ_k)⁻¹‖`:
  S⁰_n(a, d(s)) = (1/2L)·Σ_k (λ_k+a)·‖(s+¼+λ_k)⁻¹‖²  ≤  max(1,a)/(4c₀²)
on every compact K ⊆ Ω, where c₀ is the resolvent-denominator floor
(`resolventDenom_lower_bound`, at ξ = √λ_k) and the B3 ladder
`sum_inv_one_add_galerkinLam_le` supplies Σ(1+λ_k)⁻¹ ≤ L/2, cancelling
the 1/(2L). No V, no Q, no Cauchy–Schwarz (GPT 8a scope).
-/

set_option autoImplicit false

namespace RHFormalization

noncomputable section

open Complex

/-- The live dual vector: norms of the resolvent diagonal. -/
noncomputable def denseDnorm (n : ℕ) (s : ℂ) (k : Fin (denseN n)) : ℝ :=
  ‖(1 / (s + (1/4:ℂ) + ((galerkinLam (denseL n) (k : ℕ) : ℝ) : ℂ)))‖

/-- Pointwise floor transfer: on the floor hypothesis, each dual entry obeys
`d_k(s) ≤ 1/(c₀(1+λ_k))`. -/
theorem denseDnorm_le (n : ℕ) {c₀ : ℝ} (hc₀ : 0 < c₀) {K : Set ℂ}
    (hfl : ∀ s ∈ K, ∀ ξ : ℝ, c₀ * (1 + ξ^2) ≤ ‖s + (1/4 : ℂ) + (ξ : ℂ)^2‖)
    {s : ℂ} (hs : s ∈ K) (k : Fin (denseN n)) :
    denseDnorm n s k
      ≤ 1 / (c₀ * (1 + galerkinLam (denseL n) (k : ℕ))) := by
  set lam := galerkinLam (denseL n) (k : ℕ) with hlamdef
  have hlam : (0:ℝ) ≤ lam := galerkinLam_nonneg _ _
  have hsq : Real.sqrt lam ^ 2 = lam := Real.sq_sqrt hlam
  have h := hfl s hs (Real.sqrt lam)
  rw [show ((Real.sqrt lam : ℝ) : ℂ)^2 = ((lam : ℝ) : ℂ) from by
    rw [← Complex.ofReal_pow, hsq], hsq] at h
  have hden : (0:ℝ) < c₀ * (1 + lam) := by positivity
  have hnorm : c₀ * (1 + lam) ≤ ‖s + (1/4:ℂ) + ((lam : ℝ) : ℂ)‖ := h
  unfold denseDnorm
  rw [norm_div, norm_one]
  rw [← hlamdef]
  exact one_div_le_one_div_of_le hden hnorm

/-- **B(i)-8a**: compact-uniform bound on the free dual factor at the live
dual vector — the `L/2` ladder cancels the `1/(2L)` prefactor. -/
theorem denseS0_dnorm_bounded_on_compact
    (K : Set ℂ) (hK : IsCompact K) (hKΩ : K ⊆ Ω) (a : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, ∀ s ∈ K,
      denseS0 n a (denseDnorm n s) ≤ C := by
  obtain ⟨c₀, hc₀, hfl⟩ := resolventDenom_lower_bound K hK hKΩ
  refine ⟨max 1 a / (4 * c₀^2), by positivity, ?_⟩
  intro n s hs
  have hL0 : (0:ℝ) < denseL n := denseL_pos n
  have h2L : (0:ℝ) < 2 * denseL n := by linarith
  have hpre : (0:ℝ) ≤ 1 / (2 * denseL n) := le_of_lt (one_div_pos.mpr h2L)
  -- per-k: (λ+a)·d² ≤ (max 1 a / c₀²)·(1+λ)⁻¹
  have hterm : ∀ k : Fin (denseN n),
      (galerkinLam (denseL n) (k : ℕ) + a) * denseDnorm n s k ^ 2
        ≤ (max 1 a / c₀^2) * (1 + galerkinLam (denseL n) (k : ℕ))⁻¹ := by
    intro k
    set lam := galerkinLam (denseL n) (k : ℕ) with hlamdef
    have hlam : (0:ℝ) ≤ lam := galerkinLam_nonneg _ _
    have h1l : (0:ℝ) < 1 + lam := by linarith
    have hd0 : (0:ℝ) ≤ denseDnorm n s k := norm_nonneg _
    have hdk := denseDnorm_le n hc₀ hfl hs k
    rw [← hlamdef] at hdk
    have hsq : denseDnorm n s k ^ 2 ≤ (1 / (c₀ * (1 + lam)))^2 := by
      exact pow_le_pow_left₀ hd0 hdk 2
    have hlam_a : lam + a ≤ max 1 a * (1 + lam) := by
      have h1 : a ≤ max 1 a := le_max_right _ _
      have h2 : (1:ℝ) ≤ max 1 a := le_max_left _ _
      nlinarith
    have hlam_a0 : (0:ℝ) ≤ lam + a ∨ lam + a ≤ 0 := le_total 0 _
    rcases hlam_a0 with hpos | hneg
    · calc (lam + a) * denseDnorm n s k ^ 2
          ≤ (lam + a) * (1 / (c₀ * (1 + lam)))^2 :=
            mul_le_mul_of_nonneg_left hsq hpos
        _ ≤ (max 1 a * (1 + lam)) * (1 / (c₀ * (1 + lam)))^2 :=
            mul_le_mul_of_nonneg_right hlam_a (by positivity)
        _ = (max 1 a / c₀^2) * (1 + lam)⁻¹ := by
            field_simp
    · calc (lam + a) * denseDnorm n s k ^ 2
          ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hneg (sq_nonneg _)
        _ ≤ (max 1 a / c₀^2) * (1 + lam)⁻¹ := by positivity
  -- sum, ladder, cancel
  have hsum : ∑ k : Fin (denseN n),
      (galerkinLam (denseL n) (k : ℕ) + a) * denseDnorm n s k ^ 2
        ≤ (max 1 a / c₀^2) * (denseL n / 2) := by
    calc ∑ k : Fin (denseN n),
        (galerkinLam (denseL n) (k : ℕ) + a) * denseDnorm n s k ^ 2
        ≤ ∑ k : Fin (denseN n),
            (max 1 a / c₀^2) * (1 + galerkinLam (denseL n) (k : ℕ))⁻¹ :=
          Finset.sum_le_sum (fun k _ => hterm k)
      _ = (max 1 a / c₀^2) * ∑ k : Fin (denseN n),
            ((1:ℝ) + galerkinLam (denseL n) (k : ℕ))⁻¹ := by
          rw [Finset.mul_sum]
      _ ≤ (max 1 a / c₀^2) * (denseL n / 2) :=
          mul_le_mul_of_nonneg_left
            (sum_inv_one_add_galerkinLam_le (denseN n) (denseL n) hL0)
            (by positivity)
  unfold denseS0
  calc (1 / (2 * denseL n)) * ∑ k : Fin (denseN n),
        (galerkinLam (denseL n) (k : ℕ) + a) * denseDnorm n s k ^ 2
      ≤ (1 / (2 * denseL n)) * ((max 1 a / c₀^2) * (denseL n / 2)) :=
        mul_le_mul_of_nonneg_left hsum hpre
    _ = max 1 a / (4 * c₀^2) := by
        field_simp
        ring


/-! ## 8b: compact-uniform bound on the perturbed dual factor S^V -/

/-- The potential rate is uniformly bounded: `ε_n ≤ 24(log4+4)`. -/
theorem denseVrate_le_const (n : ℕ) :
    denseVrate n ≤ 24 * (Real.log 4 + 4) := by
  unfold denseVrate
  have hB : (0:ℝ) ≤ 24 * (Real.log 4 + 4) := by
    have := Real.log_nonneg (show (1:ℝ) ≤ 4 by norm_num)
    nlinarith
  have hx : (1:ℝ) ≤ (n:ℝ) + 2 := by
    have := Nat.cast_nonneg (α := ℝ) n; linarith
  have hr : ((n:ℝ)+2) ^ (-(1:ℝ)/8) ≤ 1 := by
    calc ((n:ℝ)+2) ^ (-(1:ℝ)/8)
        ≤ ((1:ℝ)) ^ (-(1:ℝ)/8) := by
          apply Real.rpow_le_rpow_of_nonpos (by norm_num) hx
          norm_num
      _ = 1 := Real.one_rpow _
  calc 24 * (Real.log 4 + 4) * ((n:ℝ)+2) ^ (-(1:ℝ)/8)
      ≤ 24 * (Real.log 4 + 4) * 1 := mul_le_mul_of_nonneg_left hr hB
    _ = 24 * (Real.log 4 + 4) := mul_one _

/-- **B(i)-8b**: compact-uniform bound on `S^V` at the live dual vector. -/
theorem denseSVReal_dnorm_bounded_on_compact
    (K : Set ℂ) (hK : IsCompact K) (hKΩ : K ⊆ Ω) {a : ℝ} (ha : 0 < a) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, ∀ s ∈ K,
      denseSVReal n a (denseDnorm n s) ≤ C := by
  obtain ⟨C₀, hC₀, hS0⟩ := denseS0_dnorm_bounded_on_compact K hK hKΩ a
  refine ⟨(1 + 24 * (Real.log 4 + 4) / a) * C₀, by positivity, ?_⟩
  intro n s hs
  have h1 := denseSVReal_le n ha (denseDnorm n s)
  have hS0n : 0 ≤ denseS0 n a (denseDnorm n s) :=
    denseS0_nonneg n ha.le _
  have hrate : denseVrate n / a ≤ 24 * (Real.log 4 + 4) / a :=
    div_le_div_of_nonneg_right (denseVrate_le_const n) ha.le
  calc denseSVReal n a (denseDnorm n s)
      ≤ (1 + denseVrate n / a) * denseS0 n a (denseDnorm n s) := h1
    _ ≤ (1 + 24 * (Real.log 4 + 4) / a) * denseS0 n a (denseDnorm n s) := by
        apply mul_le_mul_of_nonneg_right _ hS0n
        linarith
    _ ≤ (1 + 24 * (Real.log 4 + 4) / a) * C₀ := by
        apply mul_le_mul_of_nonneg_left (hS0 n s hs)
        have := Real.log_nonneg (show (1:ℝ) ≤ 4 by norm_num)
        positivity

#print axioms denseDnorm
#print axioms denseDnorm_le
#print axioms denseS0_dnorm_bounded_on_compact
#print axioms denseVrate_le_const
#print axioms denseSVReal_dnorm_bounded_on_compact

end

end RHFormalization
