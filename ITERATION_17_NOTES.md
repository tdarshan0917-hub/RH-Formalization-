# Iteration 17 Notes

## What this iteration does

This iteration decomposes the global meromorphic identity theorem.

The prior monolithic API

```lean
MeromorphicIdentityTheoremAPI
```

is now built from explicit components:

```lean
ConnectedOmegaAPI
OverlapGeometryAPI
ComparisonMeromorphicAPI
MeromorphicIdentityPrincipleAPI
```

## Why this matters

Appendix F's global step is not a mystery step. It requires:

```text
Ω connected
overlap open and nonempty
overlap contained in Ω
both sides meromorphic on Ω
local equality on overlap
identity principle
```

Now these are visible in Lean.

## What remains

The meromorphic identity principle itself remains a hard API, as do the D/H analytic
construction packages.

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
- Current total: **95%**

Estimated progress toward **100% axiom-free Lean verification**: **11–21%**.
