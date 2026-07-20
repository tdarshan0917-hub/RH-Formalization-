import RHFormalization.GalOmegaCoreCompactUniform
import RHFormalization.DecodedFlatTerminus

/-!
# HtailFrontier — THE FRONTIER, FROZEN IN THE KERNEL (Case B, 2026-07-19)

The entire remaining mathematics: an Ω-holomorphic extension of the
arithmetic tail limit. Given it, RH follows from banked theorems only.
-/

set_option autoImplicit false

namespace RHFormalization

noncomputable section

open Complex

/-- **THE FRONTIER PROP.** -/
def HtailExists : Prop :=
  ∃ Htail : ℂ → ℂ, HolomorphicOnC Htail Ω ∧
    ∀ s ∈ RightHalfPlane (1 : ℝ),
      Htail s = galerkinBcanLimitData.Bcan s - shortPackageLimit spikeT0 s

/-- **RH from the frontier**: with Htail in hand, RHcand := g − Htail closes
both flat-terminus inputs from banked theorems. -/
theorem RH_from_Htail (h : HtailExists) : RiemannHypothesis := by
  obtain ⟨Htail, hH_holo, hH_over⟩ := h
  obtain ⟨g, hg_holo, hg_over, _⟩ := galOmegaCore_compact_uniform
  refine RH_from_holomorphic_remainder (fun s => g s - Htail s) ?_ ?_
  · intro z hz
    exact (hg_holo z hz).sub (hH_holo z hz)
  · intro s hs
    have h1 := hg_over s hs
    have h2 := hH_over s hs
    unfold galOmegaCoreLimit at h1
    simp only []
    rw [h1, h2]
    ring

#print axioms RH_from_Htail

end

end RHFormalization
