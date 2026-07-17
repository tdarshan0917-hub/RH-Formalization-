import RHFormalization.DBFFStarDirichletOffParabolaBound

/-!
# DBFFStarOffParabolaBound

ROUTE CARD
1. Target: off-parabola half of O3 / `hstar`.
2. Object: `starObject`, split into `starDirichletPartial - starMainPart`.
3. Raw B on Ω? NO.
4. R = F − raw B forced? NO.
5. True outright from banked Dirichlet partial and main-part bounds.
6. Manuscript: D.OP-BOUND / D.OP.2 / off-parabola O3.
7. Consumer: parabola-depth reduction for the remaining O3 proof.

This file proves that on any compact set `K ⊆ Ω` where

  Re sqrt(s+1/4) ≥ 1/2 + δ

uniformly, the discrete Stieltjes error `starObject` is uniformly bounded
over all stages. Thus O3 remains only at parabola-depth compacts.
-/

set_option autoImplicit false

namespace RHFormalization

noncomputable section

open Complex

open scoped Topology BigOperators

/--
Full off-parabola bound for `starObject`.

This combines:
* `starDirichletPartial_bounded_off_parabola`;
* `starMainPart_norm_le_off_parabola`;
* `starObject_bounded_of_parts_bounded`.
-/
theorem starObject_bounded_off_parabola
    (K : Set ℂ) (hKO : K ⊆ Ω)
    {δ : ℝ} (hδ : 0 < δ)
    (hoff : ∀ s ∈ K,
      (1 / 2 : ℝ) + δ ≤ (Complex.sqrt (s + (1/4 : ℂ))).re) :
    ∃ Cstar : ℝ,
      ∀ n : ℕ, ∀ s ∈ K, ‖starObject n s‖ ≤ Cstar := by
  obtain ⟨Cdir, hdir⟩ :=
    starDirichletPartial_bounded_off_parabola
      K (δ := δ) hδ hoff

  refine ⟨Cdir + 3 / δ, ?_⟩

  exact
    starObject_bounded_of_parts_bounded
      K
      Cdir
      (3 / δ)
      hdir
      (by
        intro n s hs
        exact
          starMainPart_norm_le_off_parabola
            hδ
            n
            (s := s)
            (hKO hs)
            (hoff s hs))

#print axioms starObject_bounded_off_parabola

end

end RHFormalization
