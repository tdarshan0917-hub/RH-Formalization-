import RHFormalization.AscoliRelativelyCompactBoxed
import Mathlib

/-!
# Discharge of the boxed Ascoli obligation — reduced to ONE classical image-compactness gap

`AscoliRelCompactObligation` (pointwise-bounded + equicontinuous ⟹ `IsCompact (closure (range G))`)
is reduced here to the single classical fact `ToFunImageCompact`: the evaluation image
`toFun '' range G` is compact in the product topology. Everything else (Tychonoff product of
balls, the final `isCompact_of_equicontinuous` application) is discharged.

## The remaining named gap `ToFunImageCompact`
Standard Arzelà–Ascoli image-compactness on the NON-compact domain `↥Ω`. The Mathlib recipe:
`EquicontinuousOn.isClosed_range_pi_of_uniformOnFun'` (Ascoli.lean:374) gives closedness of the
pointwise-restricted range FROM closedness of the `UniformOnFun`-range; combined with the compact
product `Set.pi univ (closedBall 0 (M ·))` (Tychonoff, ℂ ProperSpace) via `of_isClosed_subset`,
this yields `IsCompact (toFun '' range G)`. The upstream input is
`IsClosed (range (UniformOnFun.ofFun {K|IsCompact K} ∘ (coe ∘ G)))` — a dedicated
`UniformOnFun`-topology development. NO RH content.
-/

namespace RHFormalization
open Filter Topology Complex Metric Set

/-- **Named classical gap.** The evaluation image of a pointwise-bounded equicontinuous family
on `↥Ω` is compact in the product topology. (Standard Arzelà–Ascoli image-compactness; NOT
RH-specific. See `isClosed_range_pi_of_uniformOnFun'` recipe above.) -/
def ToFunImageCompact : Prop :=
  ∀ (G : ℕ → C(Ω, ℂ)) (M : (Ω : Set ℂ) → ℝ),
    (∀ x : (Ω : Set ℂ), ∀ n, G n x ∈ closedBall (0 : ℂ) (M x)) →
    Equicontinuous ((↑) : (Set.range G) → (Ω : Set ℂ) → ℂ) →
    IsCompact (ContinuousMap.toFun '' (Set.range G))

/-- **Boxed obligation reduced to the single image-compactness gap.** All wiring discharged;
only `ToFunImageCompact` (classical, non-RH) remains. -/
theorem ascoliRelCompactObligation_of_toFunImageCompact
    (hImg : ToFunImageCompact) : AscoliRelCompactObligation := by
  intro G M hbd hequi
  -- range G compact via Ascoli (496) from the image-compactness gap + equicontinuity
  have hrange : IsCompact (Set.range G) :=
    ArzelaAscoli.isCompact_of_equicontinuous (Set.range G) (hImg G M hbd hequi) hequi
  -- closure of a compact set is compact
  exact hrange.closure

#print axioms ascoliRelCompactObligation_of_toFunImageCompact

end RHFormalization
