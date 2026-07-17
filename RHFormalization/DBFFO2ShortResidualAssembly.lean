import RHFormalization.DBFFO2DensityNormalizedOrder2Anchor
import RHFormalization.AdmissibleFirstOrderVanish

/-!
# DBFFO2ShortResidualAssembly

ROUTE CARD
1. Target: O2 short-residual assembly.
2. Object: first-order window plus density-normalized second-resolvent residual.
3. Raw B on Ω? NO.
4. R = F − raw B forced? NO.
5. True outright from banked `FirstOrderWindow_epsN` and
   `DBFFO2_order2_anchor_epsN`.
6. Manuscript: D.KEY-FORM-TRACE / D.UNIFORM-SHORT-RESIDUAL.
7. Consumer: corrected-bulk/D.OP-BOUND assembly.

This file packages the O2 short-residual estimate under the DBFF/O2 route.

The two inputs are already banked:
  * first-order window vanishes on Ω-compacts;
  * density-normalized order-2 residual vanishes on Ω-compacts.
-/

set_option autoImplicit false

namespace RHFormalization

noncomputable section

open Complex Filter

open scoped Topology BigOperators

/-- O2 short residual: first Born/window error plus order-2 residual. -/
def DBFFO2ShortResidual (n : ℕ) (s : ℂ) : ℂ :=
  FirstOrderWindow n s + SecondResolventResidual n s

/-- O2 short residual tends to zero uniformly on Ω-compacts, eps-N form. -/
theorem DBFFO2_short_residual_epsN
    (K : Set ℂ) (hK : IsCompact K) (hKO : K ⊆ Ω) :
    ∀ ε : ℝ, 0 < ε →
      ∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n → ∀ s ∈ K,
        ‖DBFFO2ShortResidual n s‖ ≤ ε := by
  intro ε hε
  have hε2 : (0 : ℝ) < ε / 2 := by positivity
  obtain ⟨N₁, hFOW⟩ :=
    FirstOrderWindow_epsN K hK hKO (ε / 2) hε2
  obtain ⟨N₂, hRES⟩ :=
    DBFFO2_order2_anchor_epsN K hK hKO (ε / 2) hε2
  refine ⟨max N₁ N₂, ?_⟩
  intro n hn s hs
  have hn₁ : N₁ ≤ n := le_trans (Nat.le_max_left N₁ N₂) hn
  have hn₂ : N₂ ≤ n := le_trans (Nat.le_max_right N₁ N₂) hn
  have h1 : ‖FirstOrderWindow n s‖ ≤ ε / 2 :=
    hFOW n hn₁ s hs
  have h2 : ‖SecondResolventResidual n s‖ ≤ ε / 2 :=
    hRES n hn₂ s hs
  unfold DBFFO2ShortResidual
  calc
    ‖FirstOrderWindow n s + SecondResolventResidual n s‖
        ≤ ‖FirstOrderWindow n s‖ + ‖SecondResolventResidual n s‖ := norm_add_le _ _
    _ ≤ ε / 2 + ε / 2 := add_le_add h1 h2
    _ = ε := by ring

/-- O2 short residual tends to zero uniformly on Ω-compacts, filter form. -/
theorem DBFFO2_short_residual_eventually
    (K : Set ℂ) (hK : IsCompact K) (hKO : K ⊆ Ω) :
    ∀ ε : ℝ, 0 < ε →
      ∀ᶠ n in atTop, ∀ s ∈ K,
        ‖DBFFO2ShortResidual n s‖ ≤ ε := by
  intro ε hε
  obtain ⟨N₀, hN₀⟩ :=
    DBFFO2_short_residual_epsN K hK hKO ε hε
  exact Filter.eventually_atTop.2 ⟨N₀, hN₀⟩

#print axioms DBFFO2ShortResidual
#print axioms DBFFO2_short_residual_epsN
#print axioms DBFFO2_short_residual_eventually

end

end RHFormalization
