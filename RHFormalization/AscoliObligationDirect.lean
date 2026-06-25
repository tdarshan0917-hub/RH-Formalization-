import RHFormalization.AscoliRelativelyCompactBoxed
import Mathlib

/-!
# Direct discharge of AscoliRelCompactObligation (closure-compact, the TRUE Ascoli statement)

`ToFunImageCompact` (raw-image compactness) was too strong / false (constant family 1/(n+1):
pointwise-bounded, equicontinuous, raw range NOT compact — only the CLOSURE is). The correct
target is `AscoliRelCompactObligation`: `IsCompact (closure (range G))`, exactly what
Arzelà–Ascoli gives. Proved directly via `ArzelaAscoli.isCompact_closure_of_isClosedEmbedding`,
closed embedding from `isUniformEmbedding_toUniformOnFunIsCompact` + closed range
(`range_toUniformOnFunIsCompact` = {Continuous}, `UniformOnFun.isClosed_setOf_continuous`).
NO RH content.
-/

namespace RHFormalization
open Filter Topology Complex Metric Set

/-- The closed embedding for `C(↥Ω,ℂ)` into uniform-convergence-on-compacts, from the uniform
embedding plus closedness of its range (`{f | Continuous f}`). Codomain type is inferred. -/
theorem isClosedEmbedding_toUOFC_Omega :
    IsClosedEmbedding
      (ContinuousMap.toUniformOnFunIsCompact :
        C(Ω, ℂ) → UniformOnFun (Ω : Set ℂ) ℂ {K | IsCompact K}) := by
  have hemb := ContinuousMap.isUniformEmbedding_toUniformOnFunIsCompact
      (α := (Ω : Set ℂ)) (β := ℂ) |>.isEmbedding
  -- ↥Ω is locally compact ⟹ weakly locally compact ⟹ compactly coherent ⟹ IsCoherentWith {compacts}
  haveI : LocallyCompactSpace (Ω : Set ℂ) := isOpen_Omega.locallyCompactSpace
  have hclosed : IsClosed (Set.range
      (ContinuousMap.toUniformOnFunIsCompact :
        C(Ω, ℂ) → UniformOnFun (Ω : Set ℂ) ℂ {K | IsCompact K})) := by
    rw [ContinuousMap.range_toUniformOnFunIsCompact]
    exact UniformOnFun.isClosed_setOf_continuous CompactlyCoherentSpace.isCoherentWith
  exact ⟨hemb, hclosed⟩

/-- **AscoliRelCompactObligation, proved directly.** Pointwise-bounded + equicontinuous family on
`↥Ω` has compact closure in `C(↥Ω,ℂ)`. -/
theorem ascoliRelCompactObligation_direct : AscoliRelCompactObligation := by
  intro G M hbd hequi
  set Fcoe : C(Ω, ℂ) → ((Ω : Set ℂ) → ℂ) := fun f => (f : (Ω : Set ℂ) → ℂ) with hFcoe
  have hScompact : ∀ K ∈ {K : Set (Ω : Set ℂ) | IsCompact K}, IsCompact K := fun K hK => hK
  have hclemb : IsClosedEmbedding
      (UniformOnFun.ofFun {K : Set (Ω : Set ℂ) | IsCompact K} ∘ Fcoe) :=
    isClosedEmbedding_toUOFC_Omega
  have heqcontOn : ∀ K ∈ {K : Set (Ω : Set ℂ) | IsCompact K},
      EquicontinuousOn (Fcoe ∘ ((↑) : (Set.range G) → C(Ω, ℂ))) K := by
    intro K _hK
    exact (hequi.equicontinuousOn K)
  have hptC : ∀ K ∈ {K : Set (Ω : Set ℂ) | IsCompact K}, ∀ x ∈ K,
      ∃ Q, IsCompact Q ∧ ∀ i ∈ (Set.range G), Fcoe i x ∈ Q := by
    intro K _hK x _hx
    refine ⟨closedBall (0 : ℂ) (M x), isCompact_closedBall _ _, ?_⟩
    rintro i ⟨n, rfl⟩
    exact hbd x n
  have hclosure : IsCompact (closure (Set.range G)) :=
    ArzelaAscoli.isCompact_closure_of_isClosedEmbedding
      hScompact hclemb heqcontOn hptC
  exact hclosure

#print axioms ascoliRelCompactObligation_direct

end RHFormalization
