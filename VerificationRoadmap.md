# Verification Roadmap — Iteration 20

This file separates three notions that must not be conflated.

## 1. Architecture mapped

The D/H/E/F proof spine has been represented as Lean-facing structures, builders, and theorem endpoints.

Current estimate: **99% architecture mapped**.

This means the proof dependencies are now visible in code form. It does **not** mean the proof is verified.

## 2. Build-certified Lean code

A local `lake build` has not been run in this environment.

Current confirmed build-certified percentage here: **0%**.

Expected build-readiness before a local repair pass: **25–40%**.

Likely parser/build issues:
- Mathlib import names may need adjustment.
- Some theorem names such as continuity or analytic congruence lemmas may need active-version correction.
- Some notation paths may require namespace qualification.
- Some structure projections through long coercion chains may require simplification lemmas.
- Some generated proof terms may need replacement by simpler `by` proofs.

## 3. Axiom-free verification

Axiom-free verification means the preferred endpoint has no manuscript-specific APIs/constants when inspected with `#print axioms`.

Current estimate: **12–22%**.

This estimate is modest because the heavy analytic gates remain explicit APIs.

## Preferred endpoint

```lean
mainTheorem_from_nonnegative_interface_layer
```

## First local commands to run

```bash
lake update
lake build RHFormalization.Basic
lake build RHFormalization.OmegaTopology
lake build RHFormalization.AnalyticWrappers
lake build RHFormalization.MainTheorem
```

Then inspect:

```lean
#print axioms RHFormalization.mainTheorem_from_nonnegative_interface_layer
```

## Priority order for axiom discharge

1. Repair compilation.
2. Replace easy topology/analysis wrappers with Mathlib-native proofs.
3. Choose a meromorphic API.
4. Define principal parts and genuine poles.
5. Prove the local normal-form obstruction.
6. Prove the meromorphic identity theorem on Ω.
7. Prove H-side zero-pole package construction.
8. Prove D-side operator export construction.

## Non-negotiable honesty note

The companion is not yet an axiom-free Lean proof of RH. It is a detailed formal blueprint and partial formal scaffold.
