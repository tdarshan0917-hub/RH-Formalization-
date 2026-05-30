# Iteration 14 Notes

## What this iteration does

This iteration reduces the grouped-residue arithmetic APIs.

The manuscript's grouped pole argument says:

```text
several zeros may map to the same pole location,
but their multiplicities are positive,
so the grouped principal coefficient is nonzero.
```

Iteration 14 encodes this as theorem-backed Lean-facing arithmetic.

## What remains

The actual analytic claim that the zero-pole series has that principal part remains API-level.
That is the correct remaining burden for Appendix H.

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
- Current total: **87%**

Estimated progress toward **100% axiom-free Lean verification**: **8–18%**.
