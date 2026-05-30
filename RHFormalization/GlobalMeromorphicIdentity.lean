import RHFormalization.OmegaTopology
import RHFormalization.PoleObstructionFromNormalForm
import RHFormalization.FSideWrapperBuilders

/-!
# RHFormalization.GlobalMeromorphicIdentity

Iteration 17: global meromorphic identity theorem layer.

Appendix F uses the meromorphic identity theorem on `Ω`:

* Appendix E proves the local identity on a nonempty overlap half-plane.
* Appendix D supplies the operator-side holomorphic function.
* Appendix H supplies the zero-side meromorphic function.
* Since `Ω` is connected, equality on the overlap propagates to all of `Ω`.

Earlier iterations represented this as:

  `MeromorphicIdentityTheoremAPI`.

This file splits that single API into smaller components:

1. connectedness of `Ω`;
2. geometry of the overlap half-plane;
3. meromorphicity of the two sides;
4. the abstract meromorphic identity principle.

The old `MeromorphicIdentityTheoremAPI` is then built from these components.
-/


namespace RHFormalization

noncomputable section

open Complex Topology Filter

/-!
## 1. Connectedness of Ω
-/

/--
Connectedness/preconnectedness of the manuscript slit plane `Ω`.

This is a standard topological fact for the complex slit plane.  We keep it as a
named component because the global identity theorem depends on it explicitly.
-/
structure ConnectedOmegaAPI where
  h_preconnected_Omega :
    IsPreconnected Ω

/-!
## 2. Geometry of the overlap half-plane
-/

/--
Geometry of right half-planes relative to `Ω`.

The overlap used by Appendix E is a right half-plane `Re s > σ`.
When `σ ≥ 0`, this half-plane is contained in `Ω`.
-/
structure RightHalfPlaneGeometryAPI where
  h_open :
    ∀ σ : ℝ, IsOpen (RightHalfPlane σ)
  h_nonempty :
    ∀ σ : ℝ, (RightHalfPlane σ).Nonempty
  h_subset_Omega :
    ∀ σ : ℝ, 0 ≤ σ → RightHalfPlane σ ⊆ Ω

/--
The Appendix-E interface threshold is nonnegative.

This corresponds to the manuscript convention that the overlap half-plane
`U_σ` lies inside `Ω`.
-/
structure InterfaceSigmaNonnegativeAPI
    {D : OperatorResolventBridge}
    {H : ZeroPolePackageAPI}
    (E : InterfaceBridgeAPI D H) where
  h_sigma_nonneg :
    0 ≤ E.sigma

/--
The actual overlap-geometry object consumed by the identity principle.
-/
structure OverlapGeometryAPI
    (D : OperatorResolventBridge)
    (H : ZeroPolePackageAPI)
    (E : InterfaceBridgeAPI D H) where
  h_overlap_subset_Omega :
    InterfaceOverlap E ⊆ Ω
  h_overlap_open :
    IsOpen (InterfaceOverlap E)
  h_overlap_nonempty :
    (InterfaceOverlap E).Nonempty

/--
Build overlap geometry from the right-half-plane geometry and nonnegativity of the
interface threshold.
-/
def buildOverlapGeometryFromHalfPlane
    (D : OperatorResolventBridge)
    (H : ZeroPolePackageAPI)
    (E : InterfaceBridgeAPI D H)
    (R : RightHalfPlaneGeometryAPI)
    (S : InterfaceSigmaNonnegativeAPI E) :
    OverlapGeometryAPI D H E :=
  { h_overlap_subset_Omega := by
      intro s hs
      rw [interfaceOverlap_def E] at hs
      exact R.h_subset_Omega E.sigma S.h_sigma_nonneg hs
    h_overlap_open := by
      rw [interfaceOverlap_def E]
      exact R.h_open E.sigma
    h_overlap_nonempty := by
      rw [interfaceOverlap_def E]
      exact R.h_nonempty E.sigma }

/-!
## 3. Meromorphicity of both sides
-/

/--
Algebra rules converting holomorphic/meromorphic statements into the comparison
meromorphicity required by the identity theorem.
-/
structure MeromorphicAlgebraAPI where
  h_holomorphic_to_meromorphic :
    ∀ (f : ℂ → ℂ) (U : Set ℂ),
      IsOpen U →
      HolomorphicOnC f U →
      MeromorphicOnC f U
  h_holomorphic_sub_meromorphic :
    ∀ (f g : ℂ → ℂ) (U : Set ℂ),
      IsOpen U →
      HolomorphicOnC f U →
      MeromorphicOnC g U →
      MeromorphicOnC (fun s => f s - g s) U

/--
The two sides of the Appendix-F comparison are meromorphic on `Ω`.
-/
structure ComparisonMeromorphicAPI
    (D : OperatorResolventBridge)
    (H : ZeroPolePackageAPI) where
  h_left_meromorphic :
    MeromorphicOnC D.FH Ω
  h_right_meromorphic :
    MeromorphicOnC (fun s => Htot D H s - H.Zpole s) Ω

/--
Build meromorphicity of both sides from the D/H packages and meromorphic algebra.
-/
def buildComparisonMeromorphicAPI
    (D : OperatorResolventBridge)
    (H : ZeroPolePackageAPI)
    (A : MeromorphicAlgebraAPI) :
    ComparisonMeromorphicAPI D H :=
  { h_left_meromorphic :=
      A.h_holomorphic_to_meromorphic D.FH Ω isOpen_Omega_native D.hFH_holo
    h_right_meromorphic :=
      A.h_holomorphic_sub_meromorphic
        (Htot D H)
        H.Zpole
        Ω
        isOpen_Omega_native
        (buildHtotHolomorphicAPIFromSummands D H).h_Htot_holo
        H.hZ_meromorphic }

/-!
## 4. Meromorphic identity principle
-/

/--
Meromorphic identity principle.

If two meromorphic functions on a connected/preconnected domain agree on a
nonempty open subset, then they agree on the whole domain.

This is the precise analytic theorem used by Appendix F.
-/
structure MeromorphicIdentityPrincipleAPI where
  h_identity :
    ∀ (f g : ℂ → ℂ) (U V : Set ℂ),
      IsPreconnected U →
      IsOpen V →
      V.Nonempty →
      V ⊆ U →
      MeromorphicOnC f U →
      MeromorphicOnC g U →
      Set.EqOn f g V →
      Set.EqOn f g U

/--
Build the old `MeromorphicIdentityTheoremAPI` from the decomposed global identity
components.
-/
def buildMeromorphicIdentityTheoremAPIFromComponents
    (D : OperatorResolventBridge)
    (H : ZeroPolePackageAPI)
    (E : InterfaceBridgeAPI D H)
    (C : ConnectedOmegaAPI)
    (O : OverlapGeometryAPI D H E)
    (M : ComparisonMeromorphicAPI D H)
    (I : MeromorphicIdentityPrincipleAPI) :
    MeromorphicIdentityTheoremAPI D H E :=
  { h_globalize := fun h_local =>
      I.h_identity
        D.FH
        (fun s => Htot D H s - H.Zpole s)
        Ω
        (InterfaceOverlap E)
        C.h_preconnected_Omega
        O.h_overlap_open
        O.h_overlap_nonempty
        O.h_overlap_subset_Omega
        M.h_left_meromorphic
        M.h_right_meromorphic
        h_local }

/--
Convenience builder using meromorphic algebra rather than a prebuilt
`ComparisonMeromorphicAPI`.
-/
def buildMeromorphicIdentityTheoremAPIFromGeometryAndAlgebra
    (D : OperatorResolventBridge)
    (H : ZeroPolePackageAPI)
    (E : InterfaceBridgeAPI D H)
    (C : ConnectedOmegaAPI)
    (O : OverlapGeometryAPI D H E)
    (A : MeromorphicAlgebraAPI)
    (I : MeromorphicIdentityPrincipleAPI) :
    MeromorphicIdentityTheoremAPI D H E :=
  buildMeromorphicIdentityTheoremAPIFromComponents
    D H E C O
    (buildComparisonMeromorphicAPI D H A)
    I

end

end RHFormalization
