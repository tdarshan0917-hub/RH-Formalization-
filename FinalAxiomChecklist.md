# Final Axiom/API Checklist — Iteration 20

The remaining proof debt is concentrated in these gates.

## Zeta-zero facts

- `ZetaZeroFacts.nontrivial_zero_im_ne_zero`

## Topology / global identity

- `ConnectedOmegaAPI.h_preconnected_Omega`
- `MeromorphicAlgebraAPI`
- `MeromorphicIdentityPrincipleAPI.h_identity`

## Local pole theory

- `MeromorphicOnC`
- `HasPrincipalPartAtC`
- `HasGenuinePole`
- `LocalLaurentPrincipalModelC`
- `PrincipalPartToNormalFormAPI`
- `NormalFormImpliesGenuinePoleAPI`
- `LocalNormalFormObstructionAPI.h_no_normal_form`

## H-side zero package

- `ZeroPoleLocalUniformConvergenceAPI.h_luc`
- `ZpoleMeromorphicFromSeriesAPI.h_meromorphic`
- `HSideGroupedPoleNormalFormData.h_principalPart`
- `HArchPackage.h_Harch_holo`
- `HSideOverlapPackage.h_split`

## D-side operator export

- `DFiniteStageOperatorLegality`
- `DFiniteTraceConstructionAPI`
- `DFiniteStageSplitFromDuhamelAPI`
- `DCanonicalWindowAPI`
- `DResidualSectorBoundsAPI`
- `DMasterResidualAPI`
- `DCanRemAPI`
- `DOverlapIdentityAPI`

## Appendix E interface

- `InterfaceBridgeNonnegativeAPI.bridge.h_interface`

## Build audit

Run:

```lean
#print axioms RHFormalization.mainTheorem_from_nonnegative_interface_layer
```

The output should eventually contain only foundational Lean/Mathlib axioms, not project-specific constants.
