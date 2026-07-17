import RHFormalization.RHFromDBFFExpansion

/-!
# DBFFCanonicalProfileSpec

ROUTE CARD
1. Target: bridge the manuscript's D.BFF.6 finite-profile expansion into the
   banked generic `DBFFProfileExpansionData` engine.
2. Raw B on Ω? NO.
3. R = F − raw B on Ω? NO.
4. Object: abstract D.BFF bulk/profile residual family
      Rbulk_n(s) = Σ_j coeff_n,j · Phi_j(s) + eps_n(s).
5. Consumer:
      RH_from_DBFF_expansion.
6. This file does NOT choose the actual manuscript profiles. It only fixes the
   exact Lean contract the manuscript instantiation must satisfy.
-/

set_option autoImplicit false

namespace RHFormalization

noncomputable section

open Complex Filter

open scoped BigOperators Topology

/-- Manuscript-shaped D.BFF finite-profile expansion specification.

This is the next layer below `RH_from_DBFF_expansion`: it records the finite
profile list, coefficient convergence, error convergence, and overlap
identification required by D.BFF / D.CAN-REM. -/
structure DBFFCanonicalProfileSpec where
  J : ℕ
  Phi : Fin J → ℂ → ℂ
  coeff : ℕ → Fin J → ℂ
  coeffLimit : Fin J → ℂ
  eps : ℕ → ℂ → ℂ
  Rbulk : ℕ → ℂ → ℂ

  h_expansion :
    ∀ n : ℕ, ∀ s ∈ Ω,
      Rbulk n s = (∑ j : Fin J, coeff n j * Phi j s) + eps n s

  h_Phi_holo :
    ∀ j : Fin J, HolomorphicOnC (Phi j) Ω

  h_coeff_bdd :
    ∃ Cc : ℝ, 0 ≤ Cc ∧ ∀ n : ℕ, ∀ j : Fin J, ‖coeff n j‖ ≤ Cc

  h_eps_bdd :
    ∀ K : Set ℂ, IsCompact K → K ⊆ Ω →
      ∃ Ce : ℝ, ∀ n : ℕ, ∀ s ∈ K, ‖eps n s‖ ≤ Ce

  h_coeff_tendsto :
    ∀ j : Fin J, Tendsto (fun n => coeff n j) atTop (𝓝 (coeffLimit j))

  h_eps0 :
    ∀ K : Set ℂ, IsCompact K → K ⊆ Ω →
      ∀ ε : ℝ, 0 < ε →
        ∀ᶠ n in atTop, ∀ s ∈ K, ‖eps n s‖ ≤ ε

  h_overlap :
    ∀ s ∈ RightHalfPlane (1 : ℝ),
      Tendsto (fun n => Rbulk n s) atTop
        (𝓝 (FHadmFree s - (shiftedLaplacePrimePackageAt 1).Bshared s))

namespace DBFFCanonicalProfileSpec

/-- Forget the manuscript-specific fields and produce the generic DBFF engine data. -/
def toExpansionData (S : DBFFCanonicalProfileSpec) :
    DBFFProfileExpansionData where
  J := S.J
  Phi := S.Phi
  coeff := S.coeff
  eps := S.eps
  Rbulk := S.Rbulk
  h_expansion := S.h_expansion
  h_Phi_holo := S.h_Phi_holo
  h_coeff_bdd := S.h_coeff_bdd
  h_eps_bdd := S.h_eps_bdd

/-- The manuscript-shaped D.BFF spec feeds the banked DBFF endpoint. -/
theorem RH_from_DBFF_canonical_profile_spec
    (S : DBFFCanonicalProfileSpec) :
    RiemannHypothesis :=
  RH_from_DBFF_expansion
    S.toExpansionData
    S.coeffLimit
    S.h_coeff_tendsto
    S.h_eps0
    S.h_overlap

#print axioms DBFFCanonicalProfileSpec.toExpansionData
#print axioms DBFFCanonicalProfileSpec.RH_from_DBFF_canonical_profile_spec

end DBFFCanonicalProfileSpec

end

end RHFormalization
