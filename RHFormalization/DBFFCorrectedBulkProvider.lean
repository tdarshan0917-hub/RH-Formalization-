import RHFormalization.DBFFProfileCatalog
import RHFormalization.DBFFAdmissibleRStageOverlap

/-!
# DBFFCorrectedBulkProvider — the satisfiable Front R endpoint

ROUTE CARD
1. Target: `RH_from_model_continuation` corridor, via
   `DBFFProfileCatalog.RH_from_DBFF_profile_catalog`.
2. F/B/R objects, exactly: F-slot = banked admissible F_stage (limit FHadmFree).
   B-slot content CORRECTED per manuscript D.ANCHOR: the canonical finite-stage
   package is `B_stage n − Bcorr n`, where `Bcorr` carries the window
   (g_{t,L} vs G_t) and bulk (A_class) terms plus density-normalization deltas.
   R-slot target: `Rcan n := R_stage n + Bcorr n = F_stage n − (B_stage n − Bcorr n)`.
3. Raw B on Ω beyond the overlap? NO — raw `B_stage` appears only inside
   per-stage finite identities; no regularity of its limit on Ω is asserted.
4. R forced = F − raw B on Ω? NO — `Bcorr ≠ 0` per stage breaks the
   identity-theorem forcing (Rcan and R_stage share only the RHP(1) limit).
5. Satisfiability: NOT provably false by any banked audit. Inhabiting this
   structure is exactly the manuscript's D.MR.2 / D.BULK-FINITE-FORM claim —
   the genuine open frontier, in the correct shape. (Contrast the two
   VACUOUS-BY-AUDIT providers, which pinned raw `R_stage`/core.)
6. Manuscript objects: D.ANCHOR (continued finite-cutoff package),
   D.BULK-FINITE-FORM / D.BFF.6 (profiles + coefficients), D.CAN-REM (limit).
7. Named consumer: `RH_from_DBFF_corrected_bulk` (this file) →
   `RH_from_DBFF_profile_catalog` → `RH_from_admissible_continuation`.

Remaining input after this brick: ONE concrete term of this structure —
the finite-stage `Bcorr` formula in repo objects, the profile list, and the
expansion identity. `Bcorr`'s per-stage Ω-holomorphy is not required by the
engine (profiles carry all holomorphy) and is deliberately not a field.
-/

set_option autoImplicit false

namespace RHFormalization

noncomputable section

open Complex Filter

open scoped BigOperators Topology

/-- **Corrected-bulk D.BFF provider**: finite-profile expansion data for the
canonical residual `R_stage + Bcorr`, with the package correction vanishing
on the overlap half-plane. -/
structure DBFFCorrectedBulkProvider where
  J_free : ℕ
  J_env  : ℕ
  J_left : ℕ
  J_loc  : ℕ
  Phi : Fin (J_free + J_env + J_left + J_loc) → ℂ → ℂ
  coeff : ℕ → Fin (J_free + J_env + J_left + J_loc) → ℂ
  coeffLimit : Fin (J_free + J_env + J_left + J_loc) → ℂ
  eps : ℕ → ℂ → ℂ
  Bcorr : ℕ → ℂ → ℂ
  h_Bcorr_overlap0 :
    ∀ s ∈ RightHalfPlane (1 : ℝ),
      Tendsto (fun n => Bcorr n s) atTop (𝓝 (0 : ℂ))
  h_expansion :
    ∀ n : ℕ, ∀ s ∈ Ω,
      galerkinStagePackage.R_stage (admissibleGalerkinStageSeq n) s
          + Bcorr n s =
        (∑ j : Fin (J_free + J_env + J_left + J_loc),
          coeff n j * Phi j s) + eps n s
  h_Phi_holo :
    ∀ j : Fin (J_free + J_env + J_left + J_loc),
      HolomorphicOnC (Phi j) Ω
  h_coeff_bdd :
    ∃ Cc : ℝ, 0 ≤ Cc ∧
      ∀ n : ℕ, ∀ j : Fin (J_free + J_env + J_left + J_loc),
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

namespace DBFFCorrectedBulkProvider

/-- The canonical corrected residual: `R_stage + Bcorr`. -/
def canonicalResidual (P : DBFFCorrectedBulkProvider) (n : ℕ) (s : ℂ) : ℂ :=
  galerkinStagePackage.R_stage (admissibleGalerkinStageSeq n) s + P.Bcorr n s

/-- Package the corrected-bulk provider as a profile catalog; the overlap
field is the banked `admissible_R_stage_to_DBFF_overlap` plus `Bcorr → 0`. -/
def toProfileCatalog (P : DBFFCorrectedBulkProvider) : DBFFProfileCatalog where
  J_free := P.J_free
  J_env := P.J_env
  J_left := P.J_left
  J_loc := P.J_loc
  Phi := P.Phi
  coeff := P.coeff
  coeffLimit := P.coeffLimit
  eps := P.eps
  Rbulk := fun n s =>
    galerkinStagePackage.R_stage (admissibleGalerkinStageSeq n) s + P.Bcorr n s
  h_expansion := P.h_expansion
  h_Phi_holo := P.h_Phi_holo
  h_coeff_bdd := P.h_coeff_bdd
  h_eps_bdd := P.h_eps_bdd
  h_coeff_tendsto := P.h_coeff_tendsto
  h_eps0 := P.h_eps0
  h_overlap := by
    intro s hs
    have h :=
      (admissible_R_stage_to_DBFF_overlap s hs).add (P.h_Bcorr_overlap0 s hs)
    simpa using h

/-- **RH from a corrected-bulk D.BFF expansion** — the satisfiable Front R
endpoint. -/
theorem RH_from_DBFF_corrected_bulk
    (P : DBFFCorrectedBulkProvider) :
    RiemannHypothesis :=
  DBFFProfileCatalog.RH_from_DBFF_profile_catalog P.toProfileCatalog

#print axioms DBFFCorrectedBulkProvider.toProfileCatalog
#print axioms DBFFCorrectedBulkProvider.RH_from_DBFF_corrected_bulk

end DBFFCorrectedBulkProvider

end

end RHFormalization
