import RHFormalization.MontelOnOpen
import RHFormalization.QuasiRHFlatTerminus
import RHFormalization.CompensatedBSubseqEndpoint
import Mathlib

/-!
# QuasiRHMontelEndpoint — QR-6b: the decisive endpoint on Ω_θ

`quasiRH_from_compensatedB_locbdd_subseq`: local boundedness of the compensated operator
family on compacts of `Ω_θ`, along any strictly increasing stage sequence, gives
`QuasiRH θ`. Same argument as PL-6a with Montel on `Ω_θ` (QR-6a) and the quasi-RH flat
terminus (QR-5). The overlap `Re s > 1` lies in `Ω_θ` for θ ≤ 1 (`Re s > θ²` suffices);
for θ > 1 `QuasiRH θ` is automatic since nontrivial zeros have `0 < Re ρ < 1`.
-/

set_option autoImplicit false

namespace RHFormalization

noncomputable section

open Complex Filter
open scoped Topology

/-- The half-plane `Re s > θ²` lies in `Ω_θ`. -/
theorem rightHalfPlane_subset_OmegaTheta (θ : ℝ) (hθ : 0 ≤ θ) :
    RightHalfPlane (θ ^ 2) ⊆ OmegaTheta θ := by
  intro s hs
  have hs' : θ ^ 2 < s.re := hs
  refine ⟨?_, ?_⟩
  · rw [mem_Omega_iff]
    rintro ⟨_, hre⟩
    nlinarith [sq_nonneg θ]
  · have hsq : (Complex.sqrt (s + (1/4:ℂ))) ^ 2 = s + (1/4:ℂ) := by
      unfold Complex.sqrt
      exact Complex.cpow_nat_inv_pow _ (by norm_num)
    have hre : ((Complex.sqrt (s + (1/4:ℂ))) ^ 2).re = s.re + 1/4 := by
      rw [hsq, Complex.add_re]
      norm_num
    rw [sq, Complex.mul_re] at hre
    have ha := sqrt_re_nonneg (s + (1/4:ℂ))
    nlinarith [mul_self_nonneg (Complex.sqrt (s + (1/4:ℂ))).im]

/-- For θ > 1, `QuasiRH θ` holds trivially (nontrivial zeros lie in the strip). -/
theorem quasiRH_of_gt_one {θ : ℝ} (hθ : 1 < θ) : QuasiRH θ := by
  intro ρ hρ
  obtain ⟨_, h0, h1⟩ := hρ
  rw [abs_le]
  constructor <;> linarith

/-- **QR-6b**: local boundedness of the compensated family on `Ω_θ`-compacts along any
strictly increasing stage sequence ⟹ `QuasiRH θ`. -/
theorem quasiRH_from_compensatedB_locbdd_subseq (θ : ℝ) (hθ : 0 ≤ θ)
    (σ : ℕ → ℕ) (hσ : StrictMono σ)
    (h_loc_bdd : ∀ K : Set ℂ, IsCompact K → K ⊆ OmegaTheta θ →
        ∃ C : ℝ, ∀ M, ∀ s ∈ K, ‖compensatedBFamily (σ M) s‖ ≤ C) :
    QuasiRH θ := by
  rcases le_or_gt θ 1 with hθ1 | hθ1
  swap
  · exact quasiRH_of_gt_one hθ1
  have hsub := OmegaTheta_subset_Omega θ
  obtain ⟨ψ, hψ, g, hg_holo, hg_conv⟩ := montel_extraction_open (isOpen_OmegaTheta θ)
    (fun M => compensatedBFamily (σ M))
    (fun M => (compensatedBFamily_holo (σ M)).mono hsub) h_loc_bdd id
  have hσψ : StrictMono (fun n => σ (ψ n)) := hσ.comp hψ
  have hover : ∀ s ∈ RightHalfPlane (1 : ℝ), g s = galerkinBcanLimitData.Bcan s := by
    intro s hs
    have hs1 : (1:ℝ) < s.re := hs
    have hsθ : s ∈ OmegaTheta θ := rightHalfPlane_subset_OmegaTheta θ hθ (by
      show θ ^ 2 < s.re
      nlinarith)
    have h1 : Tendsto (fun n => compensatedBFamily (σ (ψ n)) s) atTop (𝓝 (g s)) := by
      rw [Metric.tendsto_nhds]
      intro ε hε
      have h := hg_conv {s} isCompact_singleton (Set.singleton_subset_iff.mpr hsθ) ε hε
      filter_upwards [h] with n hn
      first
        | exact hn s rfl
        | exact hn s (Set.mem_singleton s)
    have hB : Tendsto (fun n => galerkinStagePackage.B_stage
          (admissibleGalerkinStageSeq (σ (ψ n))) s)
        atTop (𝓝 (galerkinBcanLimitData.Bcan s)) :=
      (admissible_hB s hs).comp hσψ.tendsto_atTop
    have hM : Tendsto (fun n => compensatorM (σ (ψ n)) s) atTop (𝓝 (0:ℂ)) :=
      (compensatorM_overlap0 hs).comp hσψ.tendsto_atTop
    have h2 : Tendsto (fun n => compensatedBFamily (σ (ψ n)) s)
        atTop (𝓝 (galerkinBcanLimitData.Bcan s)) := by
      have := hB.sub hM
      simpa [compensatedBFamily] using this
    exact tendsto_nhds_unique h1 h2
  refine quasiRH_from_holomorphic_remainder θ hθ (fun s => FHadmFree s - g s) ?_ ?_
  · first
      | exact (FHadmFree_holo.mono hsub).sub hg_holo
      | exact AnalyticOn.sub (FHadmFree_holo.mono hsub) hg_holo
  · intro s hs
    have h := hover s hs
    show FHadmFree s = galerkinBcanLimitData.Bcan s + (FHadmFree s - g s)
    rw [← h]
    ring

#print axioms rightHalfPlane_subset_OmegaTheta
#print axioms quasiRH_from_compensatedB_locbdd_subseq

end

end RHFormalization
