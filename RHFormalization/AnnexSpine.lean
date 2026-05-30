import RHFormalization.AnalyticWrappers

/-!
# RHFormalization.AnnexSpine

High-level D/H/E proof-spine scaffold.

This file records what the analytic manuscript exports at the interface
level. It intentionally does not prove the analytic exports.

Important V2 repair:
Appendix D exports `FH ∈ O(Ω)`, `RH ∈ O(Ω)`, and an overlap split.
It does **not** export global holomorphy of `B`.

Iteration 3 note:
the local E/F substitution algebra is now proved in
`RHFormalization.InterfaceAlgebra`.
-/


namespace RHFormalization

noncomputable section

open Complex

/-!
## D. Operator-side API, Appendix D
-/

/-- Operator-side bridge exported by Appendix D. -/
structure OperatorResolventBridge where
  FH : ℂ → ℂ
  B  : ℂ → ℂ
  RH : ℂ → ℂ
  sigma0 : ℝ

  hFH_holo : HolomorphicOnC FH Ω
  hRH_holo : HolomorphicOnC RH Ω

  h_split :
    ∀ s : ℂ, s ∈ RightHalfPlane sigma0 →
      FH s = B s + RH s

/-!
## H. Zero-side package API, Appendix H
-/

/-- Independent zero-side meromorphic package. -/
structure ZeroPolePackageAPI where
  Zpole : ℂ → ℂ
  Harch : ℂ → ℂ
  Bzero : ℂ → ℂ
  sigma0 : ℝ

  hZ_meromorphic : MeromorphicOnC Zpole Ω
  hHarch_holo : HolomorphicOnC Harch Ω

  h_split :
    ∀ s : ℂ, s ∈ RightHalfPlane sigma0 →
      Bzero s = Harch s - Zpole s

/-!
## E. Local interface API, Appendix E
-/

/-- Appendix E identifies the D-side and H-side canonical packages on an overlap half-plane. -/
structure InterfaceBridgeAPI
    (D : OperatorResolventBridge)
    (H : ZeroPolePackageAPI) where
  sigma : ℝ
  hsigma_ge_D : D.sigma0 ≤ sigma
  hsigma_ge_H : H.sigma0 ≤ sigma

  h_interface :
    ∀ s : ℂ, s ∈ RightHalfPlane sigma →
      D.B s = H.Bzero s

/-- The overlap half-plane used by the interface. -/
def InterfaceOverlap
    {D : OperatorResolventBridge}
    {H : ZeroPolePackageAPI}
    (E : InterfaceBridgeAPI D H) : Set ℂ :=
  RightHalfPlane E.sigma

end

end RHFormalization
