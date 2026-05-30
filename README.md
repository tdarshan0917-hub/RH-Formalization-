# RHFormalization — Lean 4 Companion V2, Iteration 20

This directory is a separate non-load-bearing Lean 4 companion scaffold for the manuscript.

It is intended to map the D/H/E/F proof spine into Lean-facing structures and theorem statements:

- **D**: Appendix D operator-side Ω-holomorphic export;
- **H**: Appendix H independent zero-side Ω-meromorphic pole package;
- **E**: Appendix E local overlap/interface identity;
- **F**: Appendix F rigidity and pole non-cancellation.

## Status

This is **not** an end-to-end Lean verification of RH.

Iteration 20 is the final structural/status pass. It adds:

```lean
RHFormalization/FinalBlueprint.lean
```

plus:

```text
VerificationRoadmap.md
FinalAxiomChecklist.md
LocalBuildChecklist.md
```

## Honest calibration

Earlier percentage labels should be read as **architecture mapping**, not as successful Lean verification.

Current status:

```text
Architecture mapped:              ~99%
Build-certified in this env:       0%
Estimated build readiness:         25–40%
Estimated axiom-free verification: 12–22%
```

The companion is therefore a detailed formal blueprint and partial Lean scaffold, not a completed formal proof.

## Preferred endpoint theorem

```lean
mainTheorem_from_nonnegative_interface_layer
```

## First audit command after local build repair

```lean
#print axioms RHFormalization.mainTheorem_from_nonnegative_interface_layer
```

## Remaining hard gates

The remaining hard gates are listed in:

```text
FinalAxiomChecklist.md
VerificationRoadmap.md
RHFormalization/FinalBlueprint.lean
```

The largest unresolved areas are:

- D-side operator export and residual estimates;
- H-side zero-pole meromorphic construction;
- meromorphic identity theorem on Ω;
- local Laurent/principal-part pole obstruction;
- actual Lake build and axiom audit.
