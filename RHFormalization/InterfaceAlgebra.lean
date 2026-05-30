import RHFormalization.AnnexSpine

/-!
# RHFormalization.InterfaceAlgebra

Iteration 3: discharge the local Appendix-E / Appendix-F algebra.

Mathematical target from the manuscript:

Appendix D gives, on the overlap half-plane,
  `FH = B + RH`.

Appendix E identifies the D-side package with the H-side package:
  `B = Bzero`.

Appendix H gives, on the same overlap half-plane,
  `Bzero = Harch - Zpole`.

Therefore, on the overlap half-plane,
  `FH = Htot - Zpole`,
where
  `Htot = RH + Harch`.

This file proves that substitution algebra at the API level.
The global continuation from the overlap half-plane to all of `Ω` remains
the next Appendix-F layer.
-/


namespace RHFormalization

noncomputable section

open Complex

/-- The holomorphic total term used in Appendix F:
`Htot = RH + Harch`. -/
def Htot
    (D : OperatorResolventBridge)
    (H : ZeroPolePackageAPI) : ℂ → ℂ :=
  fun s => D.RH s + H.Harch s

/--
Local interface split on the common overlap half-plane.

This is the formal version of the Appendix-E substitution step:
`D.FH = Htot - H.Zpole` on `InterfaceOverlap E`.
-/
theorem local_split_identity
    (D : OperatorResolventBridge)
    (H : ZeroPolePackageAPI)
    (E : InterfaceBridgeAPI D H) :
    ∀ s : ℂ, s ∈ InterfaceOverlap E →
      D.FH s = Htot D H s - H.Zpole s := by
  intro s hs

  have hD : D.FH s = D.B s + D.RH s :=
    D.h_split s (lt_of_le_of_lt E.hsigma_ge_D hs)

  have hE : D.B s = H.Bzero s :=
    E.h_interface s hs

  have hH : H.Bzero s = H.Harch s - H.Zpole s :=
    H.h_split s (lt_of_le_of_lt E.hsigma_ge_H hs)

  calc
    D.FH s = D.B s + D.RH s := hD
    _ = H.Bzero s + D.RH s := by rw [hE]
    _ = (H.Harch s - H.Zpole s) + D.RH s := by rw [hH]
    _ = Htot D H s - H.Zpole s := by
      simp [Htot]
      ring

/--
Equivalent sign convention often used in the prose:
`FH = -Zpole + Htot` on the overlap half-plane.
-/
theorem local_split_identity_neg_first
    (D : OperatorResolventBridge)
    (H : ZeroPolePackageAPI)
    (E : InterfaceBridgeAPI D H) :
    ∀ s : ℂ, s ∈ InterfaceOverlap E →
      D.FH s = - H.Zpole s + Htot D H s := by
  intro s hs
  have h := local_split_identity D H E s hs
  calc
    D.FH s = Htot D H s - H.Zpole s := h
    _ = - H.Zpole s + Htot D H s := by ring

/--
The local split as an `Set.EqOn` statement.
This is the form the next global meromorphic identity layer will consume.
-/
theorem local_split_eqOn
    (D : OperatorResolventBridge)
    (H : ZeroPolePackageAPI)
    (E : InterfaceBridgeAPI D H) :
    Set.EqOn D.FH (fun s => Htot D H s - H.Zpole s) (InterfaceOverlap E) := by
  intro s hs
  exact local_split_identity D H E s hs

/--
The overlap region is a right half-plane.

This is a small bookkeeping lemma that helps later when the global identity
theorem consumes a nonempty open overlap domain.
-/
theorem interfaceOverlap_def
    {D : OperatorResolventBridge}
    {H : ZeroPolePackageAPI}
    (E : InterfaceBridgeAPI D H) :
    InterfaceOverlap E = RightHalfPlane E.sigma := by
  rfl

end

end RHFormalization
