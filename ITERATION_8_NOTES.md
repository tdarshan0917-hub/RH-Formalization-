# Iteration 8 Notes

## What this iteration does

This iteration starts the Appendix-D side.

The manuscript requires Appendix D to export:

```text
FH ∈ O(Ω)
RH ∈ O(Ω)
FH = Bcan + RH on an overlap half-plane
```

and also says Appendix D does **not** assert `Bcan ∈ O(Ω)`.

Iteration 8 formalizes that as:

```lean
DExportLayer
```

and builds:

```lean
OperatorResolventBridge
```

from it.

## What remains

The actual D estimates are now isolated:

```lean
DCanonicalWindowAPI
DResidualSectorBoundsAPI
DMasterResidualAPI
DCanRemAPI
```

The next task is to refine the finite-stage operator/trace legality that feeds these APIs.

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
- Current total: **58%**

Estimated progress toward **100% axiom-free Lean verification**: **0–9%**.
