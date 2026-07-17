import RHFormalization.AscoliRelativelyCompactBoxed
import Mathlib

set_option autoImplicit false

namespace RHFormalization
noncomputable section
open Filter Topology Complex Metric Set

theorem ascoliRelCompactObligation_proof : AscoliRelCompactObligation := by
  intro G M hbd hequi
  -- box-set of bundled maps pointwise in closedBall, closed
  have hboxset_closed :
      IsClosed {h : C((Ω : Set ℂ), ℂ) | ∀ y, h y ∈ Metric.closedBall (0:ℂ) (M y)} := by
    have heq : {h : C((Ω : Set ℂ), ℂ) | ∀ y, h y ∈ Metric.closedBall (0:ℂ) (M y)}
        = ⋂ y, {h : C((Ω : Set ℂ), ℂ) | h y ∈ Metric.closedBall (0:ℂ) (M y)} := by
      ext h; simp [Set.mem_iInter]
    rw [heq]
    exact isClosed_iInter (fun y =>
      isClosed_closedBall.preimage (continuous_eval_const y))
  have hsub_box : Set.range G
      ⊆ {h : C((Ω : Set ℂ), ℂ) | ∀ y, h y ∈ Metric.closedBall (0:ℂ) (M y)} := by
    rintro h ⟨n, rfl⟩ y; exact hbd y n
  have hclos_box : closure (Set.range G)
      ⊆ {h : C((Ω : Set ℂ), ℂ) | ∀ y, h y ∈ Metric.closedBall (0:ℂ) (M y)} :=
    closure_minimal hsub_box hboxset_closed
  refine ArzelaAscoli.isCompact_of_equicontinuous (closure (Set.range G)) ?_ ?_
  · -- IsCompact (toFun '' closure(range G)): closed subset of compact pi-box
    have hbox : IsCompact (Set.univ.pi (fun x : (Ω : Set ℂ) => Metric.closedBall (0 : ℂ) (M x))) :=
      isCompact_univ_pi (fun x => isCompact_closedBall _ _)
    have hsub : (ContinuousMap.toFun '' (closure (Set.range G)))
        ⊆ Set.univ.pi (fun x : (Ω : Set ℂ) => Metric.closedBall (0 : ℂ) (M x)) := by
      rintro f ⟨g, hg, rfl⟩ x _
      exact hclos_box hg x
    -- image closed: toFun '' (closed set), toFun is an isometry/embedding on C(Ω,ℂ) compact-open;
    -- closure(range G) closed ⟹ image closed. Use IsClosedEmbedding of DFunLike.coe.
    have hemb : IsClosedEmbedding (DFunLike.coe : C((Ω : Set ℂ), ℂ) → ((Ω : Set ℂ) → ℂ)) := by
      apply Isometry.isClosedEmbedding
      intro f g
      rfl
    have himgcl : IsClosed (ContinuousMap.toFun '' (closure (Set.range G))) :=
      hemb.isClosedMap _ isClosed_closure
    exact hbox.of_isClosed_subset himgcl hsub
  · -- Equicontinuous on closure(range G), via indexed closure' (matches hequi's shape)
    have h1 : Equicontinuous ((fun h : C((Ω : Set ℂ), ℂ) => (h : (Ω : Set ℂ) → ℂ)) ∘ ((↑) : (Set.range G) → C((Ω : Set ℂ), ℂ))) := hequi
    have h2 := Equicontinuous.closure' (A := Set.range G)
      (u := (fun h : C((Ω : Set ℂ), ℂ) => (h : (Ω : Set ℂ) → ℂ))) h1 (by continuity)
    exact h2

#print axioms ascoliRelCompactObligation_proof

end
end RHFormalization
