import RHFormalization.AscoliRelativelyCompactReduction
import Mathlib

/-!
# BOXED: the one remaining standard Montel/Ascoli obligation

Everything in the holomorphic-Montel cone is banked EXCEPT this single standard
Arzelà–Ascoli relative-compactness fact. It is NOT RH-specific mathematics — it is the
classical statement "a pointwise-bounded equicontinuous family of continuous maps on an
open subset of ℂ is relatively compact in the topology of locally uniform convergence."

## Status
- `ascoliRelativelyCompact_of_pointwiseCompact_equicontinuous` is banked, reducing
  `AscoliRelativelyCompact` to: `IsCompact (toFun '' range G)` + `Equicontinuous`.
- Both inputs reduce to local boundedness of the family:
    equicontinuity from banked `uniformEquicontinuousOn_ball_of_bounded_holo`;
    pointwise-compactness from this BOXED lemma (Tychonoff + closure-image agreement).

## Why boxed
Pointwise-compactness of `toFun '' range G` needs the closure-image-agreement on the
NON-COMPACT domain `↥Ω`. Mathlib has the pieces (`isCompact_of_equicontinuous`,
`Equicontinuous.closure'`, `isCompact_univ_pi`, `isCompact_closedBall`,
`isUniformEmbedding_toUniformOnFunIsCompact`, the `arzela_ascoli` BCF template at
`Mathlib/Topology/ContinuousMap/Bounded/ArzelaAscoli.lean:109`) but not the exact package
for `C(↥Ω, ℂ)` with non-compact domain. Contained Mathlib-style development for a dedicated
session — standard infrastructure, NO RH content.
-/

namespace RHFormalization
open Filter Topology Complex Metric Set

/-- **BOXED Montel obligation.** Pointwise-bounded + equicontinuous family on `↥Ω` has
relatively compact range in `C(↥Ω, ℂ)`. (Standard Arzelà–Ascoli; NOT RH-specific.) -/
def AscoliRelCompactObligation : Prop :=
  ∀ (G : ℕ → C(Ω, ℂ)) (M : (Ω : Set ℂ) → ℝ),
    (∀ x : (Ω : Set ℂ), ∀ n, G n x ∈ closedBall (0 : ℂ) (M x)) →
    Equicontinuous ((↑) : (Set.range G) → (Ω : Set ℂ) → ℂ) →
    IsCompact (closure (Set.range G))

/-- From the boxed obligation, `AscoliRelativelyCompact` holds. (Reduction wiring; only the
boxed obligation is unproven.) -/
theorem ascoliRelativelyCompact_of_obligation
    (hOblig : AscoliRelCompactObligation)
    (G : ℕ → C(Ω, ℂ)) (M : (Ω : Set ℂ) → ℝ)
    (hbd : ∀ x : (Ω : Set ℂ), ∀ n, G n x ∈ closedBall (0 : ℂ) (M x))
    (hequi : Equicontinuous ((↑) : (Set.range G) → (Ω : Set ℂ) → ℂ)) :
    AscoliRelativelyCompact G :=
  ⟨closure (Set.range G), hOblig G M hbd hequi,
    fun n => subset_closure (Set.mem_range_self n)⟩

#print axioms ascoliRelativelyCompact_of_obligation

end RHFormalization
