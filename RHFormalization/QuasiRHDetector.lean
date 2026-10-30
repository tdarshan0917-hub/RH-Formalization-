import RHFormalization.QuasiRHIdentity
import RHFormalization.PuncturedIdentityLocalCore
import RHFormalization.HalfPlaneGeometry
import Mathlib

/-!
# QuasiRHDetector — QR-4: the θ-detector theorem

Abstract form of the contradiction in `RH_from_manuscript_content`, on `Ω_θ` instead of Ω.
Data: `F` (operator side) and `G` (remainder + archimedean part) holomorphic on `Ω_θ`,
`Z` (zero-pole package) meromorphic on `Ω_θ`, the split `F = G − Z` on a right half-plane,
and a genuine pole of `Z` at `−ρ(1−ρ)` for every zero off the θ-strip. Conclusion:
`QuasiRH θ`. The split spreads from the overlap to the pole by QR-3; holomorphy of `F, G`
at the pole contradicts the pole of `Z` (`local_order_obstruction`).
-/

set_option autoImplicit false

namespace RHFormalization

noncomputable section

open Filter Topology

/-- The overlap `Re s > σ` meets `Ω_θ`. -/
theorem rightHalfPlane_inter_OmegaTheta_nonempty (σ θ : ℝ) (hθ : 0 ≤ θ) :
    (RightHalfPlane σ ∩ OmegaTheta θ).Nonempty := by
  set R : ℝ := |σ| + θ + 1 with hR
  have hR1 : 1 ≤ R := by rw [hR]; linarith [abs_nonneg σ]
  have hσR : σ < R ^ 2 - 1/4 := by
    have := le_abs_self σ
    nlinarith [mul_nonneg (sub_nonneg.mpr hR1) (sub_nonneg.mpr hR1)]
  have hre : ((R:ℂ) ^ 2 - (1/4:ℂ)).re = R ^ 2 - 1/4 := by
    rw [sqQ_re]
    simp only [Complex.ofReal_re, Complex.ofReal_im]
    ring
  refine ⟨(R:ℂ) ^ 2 - (1/4:ℂ), ?_, ?_⟩
  · show σ < ((R:ℂ) ^ 2 - (1/4:ℂ)).re
    rw [hre]
    exact hσR
  · rw [OmegaTheta_eq_image θ hθ]
    refine ⟨(R:ℂ), ⟨?_, ?_⟩, rfl⟩
    · simp only [Complex.ofReal_re]
      rw [hR]; linarith [abs_nonneg σ]
    · rw [mem_Omega_iff]
      rintro ⟨_, hle⟩
      rw [hre] at hle
      nlinarith

/-- **QR-4 — the θ-detector.** -/
theorem quasiRH_of_detector (ZF : ZetaZeroFacts) {θ σ : ℝ} (hθ : 0 ≤ θ)
    (F G Z : ℂ → ℂ)
    (hF : HolomorphicOnC F (OmegaTheta θ))
    (hG : HolomorphicOnC G (OmegaTheta θ))
    (hZ : MeromorphicOnC Z (OmegaTheta θ))
    (hsplit : ∀ s ∈ RightHalfPlane σ, F s = G s - Z s)
    (hpole : ∀ ρ : ℂ, IsNontrivialZetaZero ρ → θ < |ρ.re - 1/2| →
      meromorphicOrderAt Z (polePoint ρ) < 0) :
    QuasiRH θ := by
  intro ρ hρ
  by_contra hcon
  push_neg at hcon
  have hs0 := polePoint_mem_OmegaTheta_of_offStrip ZF hρ hθ hcon
  have hUo := isOpen_OmegaTheta θ
  have hVo : IsOpen (RightHalfPlane σ ∩ OmegaTheta θ) :=
    (isOpen_RightHalfPlane σ).inter hUo
  have hVne := rightHalfPlane_inter_OmegaTheta_nonempty σ θ hθ
  have hFm : MeromorphicOnC F (OmegaTheta θ) :=
    fun z hz => (hF.analyticAt (hUo.mem_nhds hz)).meromorphicAt
  have hGm : MeromorphicOnC G (OmegaTheta θ) :=
    fun z hz => (hG.analyticAt (hUo.mem_nhds hz)).meromorphicAt
  have hGZm : MeromorphicOnC (fun s => G s - Z s) (OmegaTheta θ) := by
    first
      | exact hGm.sub hZ
      | (intro z hz; exact (hGm z hz).sub (hZ z hz))
  have hEq : Set.EqOn F (fun s => G s - Z s) (RightHalfPlane σ ∩ OmegaTheta θ) :=
    fun s hs => hsplit s hs.1
  have hpunct := punctured_identity_OmegaTheta θ hθ F (fun s => G s - Z s)
    (RightHalfPlane σ ∩ OmegaTheta θ) (polePoint ρ) hVo hVne Set.inter_subset_right
    hs0 hFm hGZm hEq
  exact local_order_obstruction_from_punctured_holomorphic_balance F G Z (polePoint ρ)
    hpunct (hF.analyticAt (hUo.mem_nhds hs0)) (hG.analyticAt (hUo.mem_nhds hs0))
    (hpole ρ hρ hcon)

#print axioms rightHalfPlane_inter_OmegaTheta_nonempty
#print axioms quasiRH_of_detector

end

end RHFormalization
