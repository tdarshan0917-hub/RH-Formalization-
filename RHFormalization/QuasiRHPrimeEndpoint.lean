import RHFormalization.QuasiRHMontelEndpoint
import RHFormalization.PolylogEndpoint
import Mathlib

/-!
# QuasiRHPrimeEndpoint — QR-6c: quasi-RH from the prime discrepancy

`quasiRH_from_vmDiscrepancy_halfplane`: if the von Mangoldt discrepancy
`Σ_{k≤M} Λ(k) k^{−ρ} − (M^{1−ρ}−1)/(1−ρ)` is bounded, uniformly in `M ≥ 2`, on every
compact subset of the half-plane `Re ρ > ½ + θ`, then every nontrivial zero satisfies
`|Re ρ − ½| ≤ θ`. At θ = 0 this is the RH endpoint `RH_from_vmDiscrepancy_bdd`.
Route: PL-5b-i square-stage bridge on `Ω_θ`, then QR-6b.
-/

set_option autoImplicit false

namespace RHFormalization

noncomputable section

/-- QR-6c-i: discrepancy at `ρ_s` bounded on `Ω_θ`-compacts ⟹ `QuasiRH θ`. -/
theorem quasiRH_from_vmDiscrepancy_bdd (θ : ℝ) (hθ : 0 ≤ θ)
    (h : ∀ K : Set ℂ, IsCompact K → K ⊆ OmegaTheta θ →
      ∃ B : ℝ, ∀ M : ℕ, 2 ≤ M → ∀ s ∈ K,
        ‖vmDiscrepancy M (Complex.sqrt (s + (1/4:ℂ)) + (1/2:ℂ))‖ ≤ B) :
    QuasiRH θ := by
  refine quasiRH_from_compensatedB_locbdd_subseq θ hθ (fun M : ℕ => (M + 2) ^ 2 - 2)
    squareStage_strictMono ?_
  intro K hK hKO
  have hKΩ : K ⊆ Ω := hKO.trans (OmegaTheta_subset_Omega θ)
  obtain ⟨B, hB⟩ := h K hK hKO
  obtain ⟨c, hc, hcK⟩ := kernelDenom_min K hK hKΩ
  obtain ⟨e, he, heK⟩ := halfDenom_min K hK hKΩ
  refine ⟨1 / c * (B + 1 / e), fun M s hs => ?_⟩
  show ‖compensatedBFamily ((M + 2) ^ 2 - 2) s‖ ≤ 1 / c * (B + 1 / e)
  rw [compensatedBFamily_square_stage (M + 2) (by omega) (hKΩ hs), norm_mul]
  have hker : ‖(1:ℂ) / (2 * Complex.sqrt (s + (1/4:ℂ)))‖ ≤ 1 / c := by
    rw [norm_div, norm_one]
    exact one_div_le_one_div_of_le hc (hcK s hs)
  have hfix : ‖(1:ℂ) / ((1/2:ℂ) - Complex.sqrt (s + (1/4:ℂ)))‖ ≤ 1 / e := by
    rw [norm_div, norm_one]
    exact one_div_le_one_div_of_le he (heK s hs)
  have hsum : ‖vmDiscrepancy (M + 2) (Complex.sqrt (s + (1/4:ℂ)) + (1/2:ℂ))
        - 1 / ((1/2:ℂ) - Complex.sqrt (s + (1/4:ℂ)))‖ ≤ B + 1 / e :=
    le_trans (norm_sub_le _ _) (add_le_add (hB (M + 2) (by omega) s hs) hfix)
  exact mul_le_mul hker hsum (norm_nonneg _) (one_div_pos.mpr hc).le

/-- **QR-6c — quasi-RH from the prime discrepancy.** Bounded von Mangoldt discrepancy on
compacts of `Re ρ > ½ + θ` ⟹ every nontrivial zero lies within θ of the critical line. -/
theorem quasiRH_from_vmDiscrepancy_halfplane (θ : ℝ) (hθ : 0 ≤ θ)
    (h : ∀ L : Set ℂ, IsCompact L → L ⊆ {ρ : ℂ | (1/2:ℝ) + θ < ρ.re} →
      ∃ B : ℝ, ∀ M : ℕ, 2 ≤ M → ∀ ρ ∈ L, ‖vmDiscrepancy M ρ‖ ≤ B) :
    QuasiRH θ := by
  apply quasiRH_from_vmDiscrepancy_bdd θ hθ
  intro K hK hKO
  have hKΩ : K ⊆ Ω := hKO.trans (OmegaTheta_subset_Omega θ)
  have hcont : ContinuousOn (fun s : ℂ => Complex.sqrt (s + (1/4:ℂ)) + (1/2:ℂ)) K :=
    (sqrtShift_continuousOn K hKΩ).add continuousOn_const
  have hsubL : (fun s : ℂ => Complex.sqrt (s + (1/4:ℂ)) + (1/2:ℂ)) '' K
      ⊆ {ρ : ℂ | (1/2:ℝ) + θ < ρ.re} := by
    rintro x ⟨s, hs, rfl⟩
    show (1/2:ℝ) + θ < (Complex.sqrt (s + (1/4:ℂ)) + (1/2:ℂ)).re
    have h1 := (hKO hs).2
    rw [Complex.add_re]
    have h12 : ((1/2:ℂ)).re = (1/2:ℝ) := by norm_num
    rw [h12]
    linarith
  obtain ⟨B, hB⟩ := h _ (hK.image_of_continuousOn hcont) hsubL
  exact ⟨B, fun M hM s hs => hB M hM _ ⟨s, hs, rfl⟩⟩

#print axioms quasiRH_from_vmDiscrepancy_bdd
#print axioms quasiRH_from_vmDiscrepancy_halfplane

end

end RHFormalization
