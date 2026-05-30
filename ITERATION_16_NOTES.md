# Iteration 16 Notes

## What this iteration does

This iteration narrows the local pole obstruction.

Instead of treating

```lean
LocalPoleObstructionAPI
```

as primitive, we build it from the exact normal-form contradiction theorem:

```lean
LocalNormalFormObstructionAPI
```

## What remains

The hard theorem is now sharply isolated:

```text
local equality FH = Htot - Zpole
holomorphic FH
holomorphic Htot
nonzero principal-part normal form for Zpole
⇒ contradiction
```

This should eventually be discharged using Laurent-series or meromorphic normal-form
definitions.

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
- Iteration 12: +4%
- Iteration 13: +3%
- Iteration 14: +4%
- Iteration 15: +3%
- Iteration 16: +3%
- Current total: **93%**

Estimated progress toward **100% axiom-free Lean verification**: **10–20%**.
