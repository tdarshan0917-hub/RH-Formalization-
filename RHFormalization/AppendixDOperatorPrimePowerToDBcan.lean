import RHFormalization.DFiniteStageOperator
import RHFormalization.AppendixDPrimePowerToDBcan

/-!
# RHFormalization.AppendixDOperatorPrimePowerToDBcan

D-side bridge from the finite operator layer to the strengthened `DBcanLimitData`.

This is not an RH endpoint.

It connects the theorem-backed finite operator spike-sum formula

  `DFiniteStagePackageFromOperatorLayer.toFiniteCanonicalPrimePowerFormula`

to the existing prime-power limit comparison layer

  `DPrimePowerLimitAtOverlapData`

and produces the D-side canonical package evidence consumed by Appendix E.
-/

namespace RHFormalization

noncomputable section

open Complex Topology Filter

/--
Limit data for the finite operator layer itself.

This packages the two remaining finite-to-limit convergence statements after
the finite spike-sum formula has already been extracted from the operator layer.
-/
abbrev DOperatorPrimePowerLimitAtOverlapData
    (X : DFiniteStagePackageFromOperatorLayer)
    (Bcan : ℂ → ℂ)
    (C : CanonicalPrimePowerPackage) : Type 1 :=
  DPrimePowerLimitAtOverlapData
    X.toStagePackage
    X.toFiniteCanonicalPrimePowerFormula
    Bcan
    C

/--
Build the strengthened D-side canonical package data directly from the finite
operator layer plus the prime-power limit data.

This is the composed D-side chain:

finite operator layer
  → spike-sum finite formula
  → prime-power limit at overlap
  → `DBcanLimitData`.
-/
def buildDBcanLimitDataFromOperatorPrimePowerLimit
    (X : DFiniteStagePackageFromOperatorLayer)
    (Bcan : ℂ → ℂ)
    (C : CanonicalPrimePowerPackage)
    (L : DOperatorPrimePowerLimitAtOverlapData X Bcan C) :
    DBcanLimitData X.toStagePackage :=
  buildDBcanLimitDataFromPrimePowerLimit
    X.toStagePackage
    X.toFiniteCanonicalPrimePowerFormula
    Bcan
    C
    L

/--
Extract the D-side shared-package identity from the operator-layer limit data.
-/
theorem operatorPrimePowerLimit_h_Bcan_matches_shared
    (X : DFiniteStagePackageFromOperatorLayer)
    (Bcan : ℂ → ℂ)
    (C : CanonicalPrimePowerPackage)
    (L : DOperatorPrimePowerLimitAtOverlapData X Bcan C) :
    ∀ s : ℂ, s ∈ RightHalfPlane X.toStagePackage.sigma0 →
      Bcan s = C.Bshared s := by
  intro s hs
  exact
    (buildDBcanLimitDataFromOperatorPrimePowerLimit X Bcan C L).h_Bcan_matches_shared
      s
      hs

end

end RHFormalization
