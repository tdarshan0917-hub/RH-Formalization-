-- SENTINEL: ADAPT-v1
import RHFormalization.AdaptiveDefectHolo
import RHFormalization.AdaptiveDefectOverlapZero
import RHFormalization.AscoliLocBddBridge
import RHFormalization.DCanRemFromMontel
import RHFormalization.MontelSubsequenceAssembly
import Mathlib

/-!
# THE GATE ADAPTER: eps0 from loc_bdd alone

`adaptiveGalerkinTransformDefect_eps0_of_loc_bdd`: the all-Ω compact-uniform
vanishing of the defect, from ONE input — the coarse n-uniform local bound.

Assembly (everything else banked this session or prior):
  holo    = adaptiveGalerkinTransformDefect_holo           (banked)
  overlap = adaptiveGalerkinTransformDefect_overlap0       (banked; RH := 0)
  Ascoli  = ascoliExtraction_of_loc_bdd                    (banked bridge)
  Montel  = holomorphicMontelConvergence_from_ascoli       (banked)

After this file, the defect gate ≡ loc_bdd.
-/

set_option autoImplicit false

namespace RHFormalization

noncomputable section

open Filter

/-- The zero function is Ω-holomorphic. -/
theorem zero_holo_Omega : HolomorphicOnC (fun _ : ℂ => (0 : ℂ)) Ω :=
  fun z hz => analyticAt_const.analyticWithinAt

/-- **eps0 ⟸ loc_bdd** — the defect gate collapsed to one input. -/
theorem adaptiveGalerkinTransformDefect_eps0_of_loc_bdd (c : ℝ)
    (h_loc_bdd : ∀ K : Set ℂ, IsCompact K → K ⊆ Ω →
        ∃ C : ℝ, ∀ n, ∀ s ∈ K,
          ‖adaptiveGalerkinTransformDefect c n s‖ ≤ C) :
    ∀ K : Set ℂ, IsCompact K → K ⊆ Ω → ∀ ε : ℝ, 0 < ε →
      ∀ᶠ n in atTop, ∀ s : ℂ, s ∈ K →
        dist (adaptiveGalerkinTransformDefect c n s) 0 < ε := by
  have hAscoli : AscoliExtraction
      (fun n s => adaptiveGalerkinTransformDefect c n s) :=
    ascoliExtraction_of_loc_bdd _ h_loc_bdd
  have hMontel : HolomorphicMontelConvergence
      (fun n s => adaptiveGalerkinTransformDefect c n s)
      (fun _ => (0 : ℂ)) :=
    holomorphicMontelConvergence_from_ascoli zero_holo_Omega hAscoli
  have hholo : ∀ n, HolomorphicOnC
      (fun s => adaptiveGalerkinTransformDefect c n s) Ω :=
    fun n => adaptiveGalerkinTransformDefect_holo c n
  have hoverlap : ∃ U : Set ℂ, IsOpen U ∧ U.Nonempty ∧ U ⊆ Ω ∧
      ∀ s ∈ U, Tendsto (fun n => adaptiveGalerkinTransformDefect c n s)
        atTop (nhds ((fun _ : ℂ => (0:ℂ)) s)) := by
    obtain ⟨U, hopen, hne, hsub, hconv⟩ :=
      adaptiveGalerkinTransformDefect_overlap0 c
    exact ⟨U, hopen, hne, hsub, hconv⟩
  exact hMontel hholo h_loc_bdd hoverlap

#print axioms zero_holo_Omega
#print axioms adaptiveGalerkinTransformDefect_eps0_of_loc_bdd

end

end RHFormalization
