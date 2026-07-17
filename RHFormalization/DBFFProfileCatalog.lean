import RHFormalization.DBFFCanonicalProfileSpec

/-!
# DBFFProfileCatalog

ROUTE CARD

1. Target: record the manuscript D.BFF / D.BULK finite-profile catalog.
2. This is NOT the final instantiation and NOT a new endpoint.
3. Raw B on Ω? NO.
4. Fake one-profile shortcut `FHadmFree - shiftedLaplaceLogDerivModel`? NO.
5. Purpose:
   split the finite profile index into the manuscript sectors

      J_bulk = J_free ⊔ J_env ⊔ J_left ⊔ J_loc

   and package the resulting finite profile expansion into the already-banked
   `DBFFCanonicalProfileSpec`.

The next file after this should provide the actual admissible catalog data:
the profile functions, coefficient maps, error term, expansion identity,
coefficient convergence, epsilon convergence, and overlap convergence.
-/

set_option autoImplicit false

namespace RHFormalization

noncomputable section

open Complex Filter

open scoped BigOperators Topology

/--
Manuscript-labeled finite profile catalog for D.BFF / D.BULK.

The four natural finite sectors are:

* `J_free`  : free/background subtraction profiles;
* `J_env`   : confining-envelope profiles;
* `J_left`  : left-wall profiles;
* `J_loc`   : local heat / finite correction profiles.

The total finite profile count is their sum.  The analytic fields are exactly
the fields needed by `DBFFCanonicalProfileSpec`, but with the sector split kept
visible so the later concrete instantiation cannot hide the profile source.
-/
structure DBFFProfileCatalog where
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

  Rbulk :
    ℕ → ℂ → ℂ

  h_expansion :
    ∀ n : ℕ, ∀ s ∈ Ω,
      Rbulk n s =
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

  h_overlap :
    ∀ s ∈ RightHalfPlane (1 : ℝ),
      Tendsto (fun n => Rbulk n s) atTop
        (𝓝 (FHadmFree s - (shiftedLaplacePrimePackageAt 1).Bshared s))

namespace DBFFProfileCatalog

/-- Total number of profiles in the manuscript D.BFF catalog. -/
abbrev totalJ (C : DBFFProfileCatalog) : ℕ :=
  C.J_free + C.J_env + C.J_left + C.J_loc

/--
Forget the sector labels and produce the generic manuscript-shaped DBFF spec.

This is intentionally only a coercion from the labeled catalog to the already
banked contract.  It does not manufacture profiles and does not identify the
profile limit with the target by definition.
-/
def toCanonicalProfileSpec
    (C : DBFFProfileCatalog) :
    DBFFCanonicalProfileSpec where
  J := C.totalJ
  Phi := C.Phi
  coeff := C.coeff
  coeffLimit := C.coeffLimit
  eps := C.eps
  Rbulk := C.Rbulk
  h_expansion := C.h_expansion
  h_Phi_holo := C.h_Phi_holo
  h_coeff_bdd := C.h_coeff_bdd
  h_eps_bdd := C.h_eps_bdd
  h_coeff_tendsto := C.h_coeff_tendsto
  h_eps0 := C.h_eps0
  h_overlap := C.h_overlap

/--
Once the concrete D.BFF profile catalog is supplied, the already-banked DBFF
endpoint gives RH.
-/
theorem RH_from_DBFF_profile_catalog
    (C : DBFFProfileCatalog) :
    RiemannHypothesis :=
  DBFFCanonicalProfileSpec.RH_from_DBFF_canonical_profile_spec
    C.toCanonicalProfileSpec

#print axioms DBFFProfileCatalog.toCanonicalProfileSpec
#print axioms DBFFProfileCatalog.RH_from_DBFF_profile_catalog

end DBFFProfileCatalog

end

end RHFormalization
