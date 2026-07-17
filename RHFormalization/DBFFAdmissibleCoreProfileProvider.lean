/- ⚠ VACUOUS-BY-AUDIT (Session 10) — DO NOT TARGET.
`h_core_expansion` + `h_coeff_bdd` + `h_epsCore0` force
`admissibleDBFFCore = admissibleFreeStage − B_stage` to be eventually bounded
on Ω-compacts. But freeStage converges on Ω-compacts (banked) while raw
`B_stage` diverges pointwise inside the abs-conv parabola (Session-9 audit:
PNT main term). Hence this structure has NO inhabitants and
`RH_from_DBFF_admissible_core_profile_provider` is a valid but UNUSABLE
implication. The corrected route adds the D.ANCHOR package correction slot:
see DBFFCorrectedBulkProvider. Kept for the ledger only. -/

import RHFormalization.DBFFAdmissibleProfileProvider
import RHFormalization.DBFFAdmissibleVanishingError

/-!
# DBFFAdmissibleCoreProfileProvider

ROUTE CARD

`DBFFAdmissibleVanishingError` banked the exact split

  R_stage_n =
    (admissibleFreeStage_n - B_stage_n)
      + admissibleDBFFVanishingError_n

and proved the second term tends locally uniformly to zero on Ω-compacts.

This file reduces the final D.BFF burden to the genuine nonvanishing core

  admissibleFreeStage n s
    - galerkinStagePackage.B_stage (admissibleGalerkinStageSeq n) s.

No raw B on Ω.
No fake one-profile shortcut.
No manuscript/PDF extraction.
No endpoint rewrite.

The next file after this should construct the actual finite-profile expansion
for this core.
-/

set_option autoImplicit false

namespace RHFormalization

noncomputable section

open Complex Filter

open scoped BigOperators Topology

/-- The nonvanishing admissible DBFF core after removing the banked vanishing error. -/
def admissibleDBFFCore (n : ℕ) (s : ℂ) : ℂ :=
  admissibleFreeStage n s
    - galerkinStagePackage.B_stage (admissibleGalerkinStageSeq n) s

/--
Finite-profile provider for the admissible DBFF core.

The full residual error will be

  epsCore + admissibleDBFFVanishingError.

The field `h_total_eps_bdd` is stated for this full error, because that is
exactly the boundedness field consumed by `DBFFAdmissibleProfileProvider`.
-/
structure DBFFAdmissibleCoreProfileProvider where
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

  epsCore :
    ℕ → ℂ → ℂ

  h_core_expansion :
    ∀ n : ℕ, ∀ s ∈ Ω,
      admissibleDBFFCore n s =
        (∑ j : Fin (J_free + J_env + J_left + J_loc),
          coeff n j * Phi j s) + epsCore n s

  h_Phi_holo :
    ∀ j : Fin (J_free + J_env + J_left + J_loc),
      HolomorphicOnC (Phi j) Ω

  h_coeff_bdd :
    ∃ Cc : ℝ, 0 ≤ Cc ∧
      ∀ n : ℕ,
      ∀ j : Fin (J_free + J_env + J_left + J_loc),
        ‖coeff n j‖ ≤ Cc

  h_total_eps_bdd :
    ∀ K : Set ℂ, IsCompact K → K ⊆ Ω →
      ∃ Ce : ℝ, ∀ n : ℕ, ∀ s ∈ K,
        ‖epsCore n s + admissibleDBFFVanishingError n s‖ ≤ Ce

  h_coeff_tendsto :
    ∀ j : Fin (J_free + J_env + J_left + J_loc),
      Tendsto (fun n => coeff n j) atTop (𝓝 (coeffLimit j))

  h_epsCore0 :
    ∀ K : Set ℂ, IsCompact K → K ⊆ Ω →
      ∀ ε : ℝ, 0 < ε →
        ∀ᶠ n in atTop, ∀ s ∈ K, ‖epsCore n s‖ ≤ ε

namespace DBFFAdmissibleCoreProfileProvider

/-- Total number of profiles in the admissible DBFF core provider. -/
abbrev totalJ (P : DBFFAdmissibleCoreProfileProvider) : ℕ :=
  P.J_free + P.J_env + P.J_left + P.J_loc

/--
Upgrade a core finite-profile provider to the full admissible profile provider
by adding the banked vanishing error.
-/
def toAdmissibleProfileProvider
    (P : DBFFAdmissibleCoreProfileProvider) :
    DBFFAdmissibleProfileProvider where
  J_free := P.J_free
  J_env := P.J_env
  J_left := P.J_left
  J_loc := P.J_loc
  Phi := P.Phi
  coeff := P.coeff
  coeffLimit := P.coeffLimit
  eps := fun n s => P.epsCore n s + admissibleDBFFVanishingError n s

  h_expansion := by
    intro n s hs
    have hR :
        galerkinStagePackage.R_stage (admissibleGalerkinStageSeq n) s =
          admissibleDBFFCore n s + admissibleDBFFVanishingError n s := by
      simpa [admissibleDBFFCore]
        using admissible_R_stage_eq_core_plus_vanishing n hs
    have hC := P.h_core_expansion n s hs
    rw [hR, hC]
    ring

  h_Phi_holo := P.h_Phi_holo
  h_coeff_bdd := P.h_coeff_bdd
  h_eps_bdd := P.h_total_eps_bdd
  h_coeff_tendsto := P.h_coeff_tendsto

  h_eps0 := by
    intro K hK hKO ε hε
    have hε2 : (0 : ℝ) < ε / 2 := by positivity
    have hcore := P.h_epsCore0 K hK hKO (ε / 2) hε2
    have hvan :=
      admissibleDBFFVanishingError_eventually_eps0 K hK hKO (ε / 2) hε2
    filter_upwards [hcore, hvan] with n hncore hnvan
    intro s hs
    have hc : ‖P.epsCore n s‖ ≤ ε / 2 := hncore s hs
    have hv : ‖admissibleDBFFVanishingError n s‖ ≤ ε / 2 := hnvan s hs
    calc
      ‖P.epsCore n s + admissibleDBFFVanishingError n s‖
          ≤ ‖P.epsCore n s‖ + ‖admissibleDBFFVanishingError n s‖ := norm_add_le _ _
      _ ≤ ε / 2 + ε / 2 := add_le_add hc hv
      _ = ε := by ring

/--
Once the genuine core D.BFF finite-profile expansion is supplied, RH follows.
-/
theorem RH_from_DBFF_admissible_core_profile_provider
    (P : DBFFAdmissibleCoreProfileProvider) :
    RiemannHypothesis :=
  DBFFAdmissibleProfileProvider.RH_from_DBFF_admissible_profile_provider
    P.toAdmissibleProfileProvider

#print axioms admissibleDBFFCore
#print axioms DBFFAdmissibleCoreProfileProvider.toAdmissibleProfileProvider
#print axioms DBFFAdmissibleCoreProfileProvider.RH_from_DBFF_admissible_core_profile_provider

end DBFFAdmissibleCoreProfileProvider

end

end RHFormalization
