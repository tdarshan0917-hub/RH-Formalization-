import RHFormalization.DBFFO2Order2SandwichTerm
import RHFormalization.AdmissibleResidualUniform

/-!
# DBFFO2DensityNormalizedOrder2Anchor

ROUTE CARD
1. Target: O2 density-normalized order-2 anchor along the admissible net.
2. Object: `SecondResolventResidual`, the already-banked density-normalized
   second-resolvent / order-2 residual in the admissible F-stage split.
3. Raw B on Ω? NO.
4. R = F − raw B forced? NO.
5. True outright from banked `SecondResolventResidual_uniform_bound` and
   `SecondResolventResidual_epsN`.
6. Manuscript: D.KEY-FORM-TRACE / D.UNIFORM-SHORT-RESIDUAL order-2 anchor.
7. Consumer: corrected-bulk/O1–O3 assembly; this file gives the named O2
   order-2 density-normalized bound.

This file does not reprove the mass algebra. It records that the exact
density-normalized order-2 estimate demanded by O2 is already available in the
admissible residual layer:

  ‖SecondResolventResidual n s‖ ≤ C_K / (n+2),

hence it vanishes uniformly on Ω-compacts.
-/

set_option autoImplicit false

namespace RHFormalization

noncomputable section

open Complex Filter

open scoped Topology BigOperators

/--
O2 order-2 anchor, compact-uniform form.

This is the D.KEY-FORM-TRACE order-2 estimate after the admissible
density normalization.
-/
theorem DBFFO2_order2_anchor_uniform_bound
    (K : Set ℂ) (hK : IsCompact K) (hKO : K ⊆ Ω) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, ∀ s ∈ K,
      ‖SecondResolventResidual n s‖ ≤ C / ((n : ℝ) + 2) :=
  SecondResolventResidual_uniform_bound K hK hKO

/--
O2 order-2 anchor, eps-N form.

This is the form consumed by later corrected-bulk/error assembly.
-/
theorem DBFFO2_order2_anchor_epsN
    (K : Set ℂ) (hK : IsCompact K) (hKO : K ⊆ Ω) :
    ∀ ε : ℝ, 0 < ε →
      ∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n → ∀ s ∈ K,
        ‖SecondResolventResidual n s‖ ≤ ε :=
  SecondResolventResidual_epsN K hK hKO

/--
Filter-form version of the O2 order-2 anchor.
-/
theorem DBFFO2_order2_anchor_eventually
    (K : Set ℂ) (hK : IsCompact K) (hKO : K ⊆ Ω) :
    ∀ ε : ℝ, 0 < ε →
      ∀ᶠ n in atTop, ∀ s ∈ K,
        ‖SecondResolventResidual n s‖ ≤ ε := by
  intro ε hε
  obtain ⟨N₀, hN₀⟩ :=
    DBFFO2_order2_anchor_epsN K hK hKO ε hε
  exact Filter.eventually_atTop.2 ⟨N₀, hN₀⟩

#print axioms DBFFO2_order2_anchor_uniform_bound
#print axioms DBFFO2_order2_anchor_epsN
#print axioms DBFFO2_order2_anchor_eventually

end

end RHFormalization
