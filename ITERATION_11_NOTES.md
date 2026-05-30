# Iteration 11 Notes

## What this iteration does

This iteration discharges easy F-side wrapper APIs from the Mathlib-facing wrapper layer.

Instead of assuming these:

```lean
HtotHolomorphicAPI
HolomorphicOnToAtAPI
LocalEqualityAtWitnessAPI
```

we now build them from:

```lean
OmegaMathlibCompatibilityAPI
AnalyticOn / AnalyticAt
EqOn on open Ω
```

## What remains

The hard analytic F-side theorem remains:

```lean
LocalPoleObstructionAPI
```

That is the actual meromorphic normal-form/removable-singularity theorem.

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
- Iteration 10: +5%
- Iteration 11: +5%
- Current total: **76%**

Estimated progress toward **100% axiom-free Lean verification**: **5–14%**.
