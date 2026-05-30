import RHFormalization.OmegaMeromorphicZeroPropagationClopen
import RHFormalization.InterfaceBridgeNonnegativeFromPlain

/-!
# RHFormalization.AppendixELocalBridgeCore

Algebraic core of Appendix E.

The final RH spine currently consumes

`E : InterfaceBridgeAPI D H`,

whose main field is the package identity

`D.B = H.Bzero`

on a right half-plane.

The manuscript often states Appendix E as the local comparison identity

`D.FH = Htot D H - H.Zpole`

on a right half-plane.

This file proves that the manuscript-style local comparison identity implies the
Lean `InterfaceBridgeAPI`, using only the D-side split and H-side split already
carried by `OperatorResolventBridge` and `ZeroPolePackageAPI`.

This is not a new RH endpoint and not a wrapper around RH. It is the algebraic
bridge needed before attacking the analytic Appendix-E identity itself.
-/

namespace RHFormalization

noncomputable section

open Complex Topology Filter

/--
Build the formal interface bridge from the manuscript-style local comparison
identity

`D.FH = Htot D H - H.Zpole`

on a right half-plane.

This uses:
* D-side split: `D.FH = D.B + D.RH`;
* H-side split: `H.Bzero = H.Harch - H.Zpole`;
* definition `Htot D H = D.RH + H.Harch`.
-/
def buildInterfaceBridgeFromLocalComparison
    (D : OperatorResolventBridge)
    (H : ZeroPolePackageAPI)
    (sigma : ℝ)
    (hsigma_ge_D : D.sigma0 ≤ sigma)
    (hsigma_ge_H : H.sigma0 ≤ sigma)
    (h_local :
      ∀ s : ℂ, s ∈ RightHalfPlane sigma →
        D.FH s = Htot D H s - H.Zpole s) :
    InterfaceBridgeAPI D H :=
  { sigma := sigma
    hsigma_ge_D := hsigma_ge_D
    hsigma_ge_H := hsigma_ge_H
    h_interface := by
      intro s hs

      have hDsplit :
          D.FH s = D.B s + D.RH s :=
        D.h_split s
          (RightHalfPlane_subset_of_le hsigma_ge_D hs)

      have hHsplit :
          H.Bzero s = H.Harch s - H.Zpole s :=
        H.h_split s
          (RightHalfPlane_subset_of_le hsigma_ge_H hs)

      have hmain :
          D.B s + D.RH s =
            (H.Harch s - H.Zpole s) + D.RH s := by
        calc
          D.B s + D.RH s = D.FH s := hDsplit.symm
          _ = Htot D H s - H.Zpole s := h_local s hs
          _ = (H.Harch s - H.Zpole s) + D.RH s := by
            simp [Htot, sub_eq_add_neg, add_assoc, add_comm, add_left_comm]

      have hB :
          D.B s = H.Harch s - H.Zpole s :=
        add_right_cancel hmain

      exact hB.trans hHsplit.symm }

end

end RHFormalization
