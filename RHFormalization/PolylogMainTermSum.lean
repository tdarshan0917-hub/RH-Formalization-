import RHFormalization.PolylogMainTermShift
import Mathlib

/-!
# PolylogMainTermSum — PL-4b-ii-3: the shifted main term is uniformly close

For `0 ≤ σ ≤ Re ρ`, `δ ≥ 0`, `ρ ≠ 1`, `ρ + δ ≠ 1`, and every `M`:
`‖Σ_{1 ≤ k < M} (mainIncr(1−ρ) k · (k+1)^{−δ} − mainIncr(1−ρ−δ) k)‖ ≤ 1`.
Each term is at most `k^{−δ} − (k+1)^{−δ}` (PL-4b-ii-2 with `k^{−σ} ≤ 1`), and those
differences telescope to `1 − M^{−δ} ≤ 1`.
-/

set_option autoImplicit false

namespace RHFormalization

noncomputable section

open scoped BigOperators

/-- Telescoping of `k^{−δ} − (k+1)^{−δ}` over `1 ≤ k < M`. -/
theorem sum_Ico_rpow_neg_telescope (δ : ℝ) {M : ℕ} (hM : 1 ≤ M) :
    ∑ k ∈ Finset.Ico 1 M, (((k:ℝ)) ^ (-δ) - ((k:ℝ) + 1) ^ (-δ)) = 1 - ((M:ℝ)) ^ (-δ) := by
  induction M, hM using Nat.le_induction with
  | base => simp
  | succ M hM ih =>
    rw [Finset.sum_Ico_succ_top hM, ih]
    push_cast
    ring

/-- **PL-4b-ii-3**: uniform bound on the summed main-term shift error. -/
theorem mainIncr_shift_sum_le {ρ : ℂ} {σ δ : ℝ} (hσ : 0 ≤ σ) (hσρ : σ ≤ ρ.re) (hδ : 0 ≤ δ)
    (hρ : ρ ≠ 1) (hρδ : ρ + (δ:ℂ) ≠ 1) (M : ℕ) :
    ‖∑ k ∈ Finset.Ico 1 M,
        (mainIncr (1 - ρ) k * ((((k:ℝ) + 1) ^ (-δ) : ℝ) : ℂ)
          - mainIncr (1 - (ρ + (δ:ℂ))) k)‖ ≤ 1 := by
  rcases Nat.eq_zero_or_pos M with h0 | hpos
  · subst h0
    simp
  have hM : 1 ≤ M := hpos
  have hterm : ∀ k ∈ Finset.Ico 1 M,
      ‖mainIncr (1 - ρ) k * ((((k:ℝ) + 1) ^ (-δ) : ℝ) : ℂ) - mainIncr (1 - (ρ + (δ:ℂ))) k‖
        ≤ ((k:ℝ)) ^ (-δ) - ((k:ℝ) + 1) ^ (-δ) := by
    intro k hk
    have hk1 : 1 ≤ k := (Finset.mem_Ico.mp hk).1
    have hkR : (1:ℝ) ≤ (k:ℝ) := by exact_mod_cast hk1
    have hkpos : (0:ℝ) < (k:ℝ) := by linarith
    have hdiff : 0 ≤ ((k:ℝ)) ^ (-δ) - ((k:ℝ) + 1) ^ (-δ) := by
      have := Real.rpow_le_rpow_of_nonpos hkpos (by linarith : (k:ℝ) ≤ (k:ℝ) + 1)
        (by linarith : -δ ≤ 0)
      linarith
    have hσle : ((k:ℝ)) ^ (-σ) ≤ 1 := by
      have h := Real.rpow_le_rpow_of_exponent_le hkR (by linarith : -σ ≤ 0)
      rwa [Real.rpow_zero] at h
    calc _ ≤ ((k:ℝ)) ^ (-σ) * (((k:ℝ)) ^ (-δ) - ((k:ℝ) + 1) ^ (-δ)) :=
          mainIncr_shift_norm_le hσ hσρ hδ hρ hρδ hk1
      _ ≤ ((k:ℝ)) ^ (-δ) - ((k:ℝ) + 1) ^ (-δ) := mul_le_of_le_one_left hdiff hσle
  calc _ ≤ ∑ k ∈ Finset.Ico 1 M,
        ‖mainIncr (1 - ρ) k * ((((k:ℝ) + 1) ^ (-δ) : ℝ) : ℂ) - mainIncr (1 - (ρ + (δ:ℂ))) k‖ :=
        norm_sum_le _ _
    _ ≤ ∑ k ∈ Finset.Ico 1 M, (((k:ℝ)) ^ (-δ) - ((k:ℝ) + 1) ^ (-δ)) :=
        Finset.sum_le_sum hterm
    _ = 1 - ((M:ℝ)) ^ (-δ) := sum_Ico_rpow_neg_telescope δ hM
    _ ≤ 1 := by
        have := Real.rpow_nonneg (Nat.cast_nonneg M : (0:ℝ) ≤ (M:ℝ)) (-δ)
        linarith

#print axioms sum_Ico_rpow_neg_telescope
#print axioms mainIncr_shift_sum_le

end

end RHFormalization
