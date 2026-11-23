import RHFormalization.VonKochToStageA
import Mathlib

/-!
# StageAEquivalence — RHC-4: the Stage A hypothesis is equivalent to RH

`HPdense`: the dense paired transform minus compensator is bounded on Ω-compacts, uniformly in stage.
`VonKochBound`: `|ψ(t) − t| ≤ C t^{1/2+δ/2}` for every `δ > 0` (von Koch 1901: RH ⇒ this).
* `RH_of_HPdense`        — Stage A endpoint.
* `HPdense_of_vonKoch`   — RHC-1, RHC-2a/b/c.
* `RH_of_vonKochBound`   — the easy classical direction, certified through the operator.
* `HPdense_iff_RH`       — `HPdense ↔ RH`, given von Koch's theorem `RH → VonKochBound` (RHC-3).
-/

set_option autoImplicit false

namespace RHFormalization

noncomputable section

/-- The Stage A hypothesis as a proposition. -/
def HPdense : Prop :=
  ∀ K : Set ℂ, IsCompact K → K ⊆ Ω →
    ∃ Cp : ℝ, ∀ n, ∀ s ∈ K,
      ‖(2:ℂ) * denseFreePairedTransform n s - compensatorM n s‖ ≤ Cp

/-- von Koch-type bound on the Chebyshev function. -/
def VonKochBound : Prop :=
  ∀ δ : ℝ, 0 < δ → ∃ C : ℝ, 0 ≤ C ∧
    ∀ t : ℝ, 1 ≤ t → |Chebyshev.psi t - t| ≤ C * t ^ (1/2 + δ/2)

theorem RH_of_HPdense (h : HPdense) : RiemannHypothesis :=
  RH_from_pairedTransform_only_dense h

theorem HPdense_of_vonKochBound (h : VonKochBound) : HPdense :=
  hPdense_of_vonKoch h

theorem RH_of_vonKochBound (h : VonKochBound) : RiemannHypothesis :=
  RH_of_vonKoch h

/-- **RHC-4 — the Stage A hypothesis is equivalent to RH**, given von Koch's theorem. -/
theorem HPdense_iff_RH (vonKoch : RiemannHypothesis → VonKochBound) :
    HPdense ↔ RiemannHypothesis :=
  ⟨RH_of_HPdense, fun hRH => HPdense_of_vonKochBound (vonKoch hRH)⟩

/-- With von Koch's theorem and RH, the Stage A hypothesis holds. -/
theorem HPdense_holds (vonKoch : RiemannHypothesis → VonKochBound)
    (hRH : RiemannHypothesis) : HPdense :=
  (HPdense_iff_RH vonKoch).mpr hRH

#print axioms HPdense_iff_RH
#print axioms HPdense_holds
#print axioms RH_of_vonKochBound

end

end RHFormalization
