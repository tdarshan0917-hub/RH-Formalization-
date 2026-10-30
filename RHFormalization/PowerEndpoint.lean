import RHFormalization.PowerShiftTheorem
import RHFormalization.PolylogEndpoint
import Mathlib

/-!
# PowerEndpoint — PE-2: RH from `M^ε` growth of the prime discrepancy, for every ε > 0

If for every `ε > 0` and every compact `L` in the half-plane `Re ρ > ½` the discrepancy
satisfies `‖vmDiscrepancy (m+1) ρ‖ ≤ C_{ε,L} (m+1)^ε`, then RH. Same route as PL-5b-ii,
with PE-1 in place of PL-5a: `ε = c/8`, shifts `δ = c/2` or `c/4`.
-/

set_option autoImplicit false

namespace RHFormalization

noncomputable section

open scoped BigOperators

/-- One shift with power growth: PE-1 at `ρ = ρ_s − δ` bounds the discrepancy at `ρ_s`. -/
theorem vmDiscrepancy_bound_via_shift_pow {K : Set ℂ} (hKO : K ⊆ Ω) {c δ ε C Kδ : ℝ}
    (hcK : ∀ s ∈ K, c ≤ (Complex.sqrt (s + (1/4:ℂ))).re) (hδc : δ ≤ c)
    (hKδ : ∀ ρ : ℂ, 0 ≤ ρ.re → ρ ≠ 1 → ρ + (δ:ℂ) ≠ 1 →
      (∀ m : ℕ, ‖vmDiscrepancy (m + 1) ρ‖ ≤ C * ((m:ℝ) + 1) ^ ε) →
      ∀ M : ℕ, 1 ≤ M → ‖vmDiscrepancy M (ρ + (δ:ℂ))‖ ≤ Kδ)
    (hD : ∀ s ∈ K, shiftPt δ s ≠ 1 → ∀ m : ℕ,
      ‖vmDiscrepancy (m + 1) (shiftPt δ s)‖ ≤ C * ((m:ℝ) + 1) ^ ε)
    {s : ℂ} (hs : s ∈ K) (hne : shiftPt δ s ≠ 1) {M : ℕ} (hM : 1 ≤ M) :
    ‖vmDiscrepancy M (Complex.sqrt (s + (1/4:ℂ)) + (1/2:ℂ))‖ ≤ Kδ := by
  have hsum : shiftPt δ s + (δ:ℂ) = Complex.sqrt (s + (1/4:ℂ)) + (1/2:ℂ) := by
    unfold shiftPt; ring
  have hρs : Complex.sqrt (s + (1/4:ℂ)) + (1/2:ℂ) ≠ 1 := by
    intro h
    exact sqrt_ne_half (hKO hs) (by linear_combination h)
  have hre : 0 ≤ (shiftPt δ s).re := by
    rw [shiftPt_re]
    have h1 := hcK s hs
    linarith
  have h := hKδ (shiftPt δ s) hre hne (by rw [hsum]; exact hρs) (hD s hs hne) M hM
  rwa [hsum] at h

/-- **PE-2 — the ε-power endpoint.** RH from `C_ε·M^ε` growth (every ε > 0) of the
von Mangoldt discrepancy on compact subsets of the half-plane `Re ρ > ½`. -/
theorem RH_from_vmDiscrepancy_power
    (hpow : ∀ ε : ℝ, 0 < ε → ∀ L : Set ℂ, IsCompact L → L ⊆ {ρ : ℂ | (1/2:ℝ) < ρ.re} →
      ∃ C : ℝ, ∀ ρ ∈ L, ρ ≠ 1 → ∀ m : ℕ,
        ‖vmDiscrepancy (m + 1) ρ‖ ≤ C * ((m:ℝ) + 1) ^ ε) :
    RiemannHypothesis := by
  apply RH_from_vmDiscrepancy_bdd
  intro K hK hKO
  obtain ⟨c, hc, hcK⟩ := sqrtRe_min K hK hKO
  have hsq := sqrtShift_continuousOn K hKO
  have hcont : ∀ δ : ℝ, ContinuousOn (shiftPt δ) K := fun δ => by
    unfold shiftPt
    exact (hsq.add continuousOn_const).sub continuousOn_const
  have hL : IsCompact (shiftPt (c/2) '' K ∪ shiftPt (c/4) '' K) :=
    (hK.image_of_continuousOn (hcont (c/2))).union (hK.image_of_continuousOn (hcont (c/4)))
  have hLsub : shiftPt (c/2) '' K ∪ shiftPt (c/4) '' K ⊆ {ρ : ℂ | (1/2:ℝ) < ρ.re} := by
    rintro x (⟨s, hs, rfl⟩ | ⟨s, hs, rfl⟩)
    · show (1/2:ℝ) < (shiftPt (c/2) s).re
      rw [shiftPt_re]
      have h1 := hcK s hs
      linarith
    · show (1/2:ℝ) < (shiftPt (c/4) s).re
      rw [shiftPt_re]
      have h1 := hcK s hs
      linarith
  obtain ⟨C, hCε⟩ := hpow (c/8) (by linarith) _ hL hLsub
  have hC' : (0:ℝ) ≤ max C 0 := le_max_right _ _
  have hD : ∀ δ : ℝ, (δ = c/2 ∨ δ = c/4) → ∀ s ∈ K, shiftPt δ s ≠ 1 → ∀ m : ℕ,
      ‖vmDiscrepancy (m + 1) (shiftPt δ s)‖ ≤ max C 0 * ((m:ℝ) + 1) ^ (c/8) := by
    intro δ hδ s hs hne m
    have hmem : shiftPt δ s ∈ shiftPt (c/2) '' K ∪ shiftPt (c/4) '' K := by
      rcases hδ with rfl | rfl
      · exact Or.inl ⟨s, hs, rfl⟩
      · exact Or.inr ⟨s, hs, rfl⟩
    have hp0 : 0 ≤ ((m:ℝ) + 1) ^ (c/8) := Real.rpow_nonneg (by positivity) _
    exact le_trans (hCε _ hmem hne m) (mul_le_mul_of_nonneg_right (le_max_left C 0) hp0)
  obtain ⟨K1, hK1⟩ := shifted_vmDiscrepancy_uniform_pow
    (div_pos hc (by norm_num : (0:ℝ) < 2)) (by linarith : c/8 ≤ c/2/2) hC'
  obtain ⟨K2, hK2⟩ := shifted_vmDiscrepancy_uniform_pow
    (div_pos hc (by norm_num : (0:ℝ) < 4)) (by linarith : c/8 ≤ c/4/2) hC'
  refine ⟨max K1 K2, fun M hM s hs => ?_⟩
  by_cases h1 : shiftPt (c/2) s = 1
  · have h2 : shiftPt (c/4) s ≠ 1 := by
      intro h2
      have hx : ((c/2:ℝ):ℂ) = ((c/4:ℝ):ℂ) := by
        unfold shiftPt at h1 h2
        linear_combination h2 - h1
      have hx' : c/2 = c/4 := Complex.ofReal_injective hx
      linarith
    exact le_trans (vmDiscrepancy_bound_via_shift_pow hKO hcK (by linarith) hK2
      (hD (c/4) (Or.inr rfl)) hs h2 (by omega)) (le_max_right _ _)
  · exact le_trans (vmDiscrepancy_bound_via_shift_pow hKO hcK (by linarith) hK1
      (hD (c/2) (Or.inl rfl)) hs h1 (by omega)) (le_max_left _ _)

#print axioms RH_from_vmDiscrepancy_power

end

end RHFormalization
