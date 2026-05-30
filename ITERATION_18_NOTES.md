# Iteration 18 Notes

## What this iteration does

This iteration theorem-backs right-half-plane and overlap geometry.

The global meromorphic identity theorem needs the overlap domain to be:

```text
open
nonempty
contained in Ω
```

For a right half-plane with nonnegative threshold, those are now represented by theorem-backed
Lean-facing code.

## What remains

The theorem now needs only the actual interface threshold nonnegativity:

```lean
hσ : 0 ≤ E.sigma
```

The next iteration should move this into the interface API itself.

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
- Iteration 17: +2%
- Iteration 18: +2%
- Current total: **97%**

Estimated progress toward **100% axiom-free Lean verification**: **12–22%**.
