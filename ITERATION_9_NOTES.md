# Iteration 9 Notes

## What this iteration does

This iteration adds the finite-stage operator legality layer behind Appendix D.

The manuscript says the final operator-side transform is not a raw finite-volume
trace, but Appendix D begins from finite cutoff/window trace identities and then
exports the canonical whole-line object.

Iteration 9 formalizes that finite-stage foundation as:

```lean
DFiniteStageOperatorLegality
DGlobalShiftAPI
DFiniteTraceConstructionAPI
DFiniteStageSplitFromDuhamelAPI
DFiniteStagePackageFromOperatorLayer
DDetailedConstructionWithOperatorLegality
```

## Faithful vs axiom-free

The code is real in the sense that the objects and dependencies are represented
in Lean-like formal declarations. But this is not yet axiom-free verification:
many fields are APIs/constants that still need proofs.

That is why the faithful-formalization percentage can be high while the
axiom-free-verification percentage remains low.

## Percentage covered

Estimated progress toward **100% Lean-faithful formalization**:

- Iteration 1: 8%
- Iteration 2: +6%
- Iteration 3: +6%
- Iteration 4: +7%
- Iteration 5: +7%
- Iteration 6: +7%
- Iteration 7: +8%
- Iteration 8: +9%
- Iteration 9: +8%
- Current total: **66%**

Estimated progress toward **100% axiom-free Lean verification**: **0–10%**.
