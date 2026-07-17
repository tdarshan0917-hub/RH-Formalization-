/- ⚠ VACUOUS-BY-AUDIT (Session 10) — DO NOT TARGET.
This structure pins `Rbulk := galerkinStagePackage.R_stage (admissibleGalerkinStageSeq n)`
and requires the bounded-coefficient finite-profile expansion on ALL of Ω.
By `DBFFProfileExpansionData.loc_bdd`, any inhabitant forces the admissible
`R_stage` to be locally bounded on Ω-compacts. The Session-9 raw-B audit proved
`R_stage = F_stage − B_stage` DIVERGES inside the abs-conv parabola
(F converges; raw B carries the PNT main term X_n^(1/2−w)/(1/2−w)).
Hence this structure has NO inhabitants; `RH_from_DBFF_admissible_profile_provider`
is a valid but UNUSABLE implication. The corrected route changes the B-slot
content per manuscript D.ANCHOR (windowed spike + A_class bulk, density-
normalized): see the corrected-bulk provider. Kept for the ledger only. -/

import RHFormalization.DBFFProfileCatalog
import RHFormalization.DBFFAdmissibleRStageOverlap

/-!
# DBFFAdmissibleProfileProvider

ROUTE CARD

`DBFFAdmissibleRStageOverlap` has now banked the overlap limit for the actual
admissible `R_stage`.

This file removes `h_overlap` from the remaining D.BFF burden.  The only
remaining mathematical input is now the genuine finite-profile expansion of the
admissible `R_stage`:

  R_stage_n(s) = Σ_j coeff_n,j * Phi_j(s) + eps_n(s).

No raw B on Ω.
No fake one-profile shortcut.
No manuscript/PDF extraction.
No endpoint rewrite.

The next layer after this is the actual D.BFF finite-profile construction:
the concrete `Phi`, `coeff`, `coeffLimit`, and `eps` data.
-/

set_option autoImplicit false

namespace RHFormalization

noncomputable section

open Complex Filter

open scoped BigOperators Topology

/--
Admissible D.BFF finite-profile provider.

Compared with `DBFFProfileCatalog`, this structure fixes

  Rbulk n s := galerkinStagePackage.R_stage (admissibleGalerkinStageSeq n) s

and obtains `h_overlap` from the banked theorem
`admissible_R_stage_to_DBFF_overlap`.

Thus the fields here are exactly the remaining finite-profile expansion data.
-/
structure DBFFAdmissibleProfileProvider where
  J_free : ℕ
  J_env  : ℕ
  J_left : ℕ
  J_loc  : ℕ

  Phi :
    Fin (J_free + J_env + J_left + J_loc) → ℂ → ℂ

  coeff :
    ℕ → Fin (J_free + J_env + J_left + J_loc) → ℂ

  coeffLimit :
    Fin (J_free + J_env + J_left + J_loc) → ℂ

  eps :
    ℕ → ℂ → ℂ

  h_expansion :
    ∀ n : ℕ, ∀ s ∈ Ω,
      galerkinStagePackage.R_stage (admissibleGalerkinStageSeq n) s =
        (∑ j : Fin (J_free + J_env + J_left + J_loc),
          coeff n j * Phi j s) + eps n s

  h_Phi_holo :
    ∀ j : Fin (J_free + J_env + J_left + J_loc),
      HolomorphicOnC (Phi j) Ω

  h_coeff_bdd :
    ∃ Cc : ℝ, 0 ≤ Cc ∧
      ∀ n : ℕ,
      ∀ j : Fin (J_free + J_env + J_left + J_loc),
        ‖coeff n j‖ ≤ Cc

  h_eps_bdd :
    ∀ K : Set ℂ, IsCompact K → K ⊆ Ω →
      ∃ Ce : ℝ, ∀ n : ℕ, ∀ s ∈ K, ‖eps n s‖ ≤ Ce

  h_coeff_tendsto :
    ∀ j : Fin (J_free + J_env + J_left + J_loc),
      Tendsto (fun n => coeff n j) atTop (𝓝 (coeffLimit j))

  h_eps0 :
    ∀ K : Set ℂ, IsCompact K → K ⊆ Ω →
      ∀ ε : ℝ, 0 < ε →
        ∀ᶠ n in atTop, ∀ s ∈ K, ‖eps n s‖ ≤ ε

namespace DBFFAdmissibleProfileProvider

/-- Total number of profiles in the admissible D.BFF provider. -/
abbrev totalJ (P : DBFFAdmissibleProfileProvider) : ℕ :=
  P.J_free + P.J_env + P.J_left + P.J_loc

/--
Turn an admissible finite-profile provider into the catalog consumed by the
banked DBFF endpoint.

The overlap field is supplied by `admissible_R_stage_to_DBFF_overlap`.
-/
def toProfileCatalog
    (P : DBFFAdmissibleProfileProvider) :
    DBFFProfileCatalog where
  J_free := P.J_free
  J_env := P.J_env
  J_left := P.J_left
  J_loc := P.J_loc
  Phi := P.Phi
  coeff := P.coeff
  coeffLimit := P.coeffLimit
  eps := P.eps
  Rbulk := fun n s =>
    galerkinStagePackage.R_stage (admissibleGalerkinStageSeq n) s
  h_expansion := P.h_expansion
  h_Phi_holo := P.h_Phi_holo
  h_coeff_bdd := P.h_coeff_bdd
  h_eps_bdd := P.h_eps_bdd
  h_coeff_tendsto := P.h_coeff_tendsto
  h_eps0 := P.h_eps0
  h_overlap := by
    intro s hs
    exact admissible_R_stage_to_DBFF_overlap s hs

/--
Once the genuine admissible D.BFF finite-profile expansion is supplied, RH
follows through the already-banked DBFF/profile/catalog endpoint.
-/
theorem RH_from_DBFF_admissible_profile_provider
    (P : DBFFAdmissibleProfileProvider) :
    RiemannHypothesis :=
  DBFFProfileCatalog.RH_from_DBFF_profile_catalog
    P.toProfileCatalog

#print axioms DBFFAdmissibleProfileProvider.toProfileCatalog
#print axioms DBFFAdmissibleProfileProvider.RH_from_DBFF_admissible_profile_provider

end DBFFAdmissibleProfileProvider

end

end RHFormalization
