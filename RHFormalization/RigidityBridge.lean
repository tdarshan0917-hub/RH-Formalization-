import RHFormalization.PoleGeometry
import RHFormalization.GlobalRigidity

/-!
# RHFormalization.RigidityBridge

Final contradiction interface for Appendix F.

Iteration 4 update:
the former monolithic `RigidityNoPoleAPI` has been moved into
`GlobalRigidity.lean` and split into:
* `GlobalIdentityAPI`;
* `HolomorphicShieldAPI`;
* `NoPoleFromGlobalIdentityAPI`.

This file now contains only the zero-witness construction and the final
pole/no-pole contradiction.
-/


namespace RHFormalization

noncomputable section

open Complex

/-- Build the zero witness used in the final contradiction. -/
def mkZeroWitness
    (ZF : ZetaZeroFacts)
    (ρ : ℂ)
    (h_zero : IsNontrivialZetaZero ρ)
    (h_off : ρ.re ≠ (1 / 2 : ℝ)) :
    ZeroWitness :=
  { ρ := ρ
    h_zero := h_zero
    h_offline := h_off
    s0 := polePoint ρ
    hs0_def := rfl
    hs0_in_Omega := by
      exact offLine_zeroPolePoint_in_Omega ZF h_zero h_off }

/-- H-side pole witness API: every off-critical nontrivial zero contributes a genuine pole. -/
structure PoleWitnessAPI (H : ZeroPolePackageAPI) where
  h_genuine_pole :
    ∀ W : ZeroWitness, HasGenuinePole H.Zpole W.s0

/-- Conditional F-contradiction: a pole witness contradicts the no-pole shield. -/
theorem no_ZeroWitness_of_rigidity
    (D : OperatorResolventBridge)
    (H : ZeroPolePackageAPI)
    (E : InterfaceBridgeAPI D H)
    (P : PoleWitnessAPI H)
    (R : RigidityNoPoleAPI D H E) :
    ∀ W : ZeroWitness, False := by
  intro W
  exact (R.h_no_genuine_pole W) (P.h_genuine_pole W)

/-- The local identity that feeds the global identity theorem. -/
theorem local_identity_for_globalization
    (D : OperatorResolventBridge)
    (H : ZeroPolePackageAPI)
    (E : InterfaceBridgeAPI D H) :
    Set.EqOn D.FH (fun s => Htot D H s - H.Zpole s) (InterfaceOverlap E) := by
  exact local_split_eqOn D H E

end

end RHFormalization
