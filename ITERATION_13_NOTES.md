# Iteration 13 Notes

## What this iteration does

This iteration removes the small topological assumption:

```lean
constant isOpen_Omega_native : IsOpen Ω
```

and replaces it with theorem-backed code.

## Why this matters

The F-side local equality and holomorphic-at transfer only need openness of `Ω`.
Now that openness is no longer an arbitrary field supplied by the user; it is generated from
the manuscript definition of the slit plane.

## What remains

The hard analytic gates remain:

```lean
MeromorphicIdentityTheoremAPI
LocalPoleObstructionAPI
D residual sector estimates
H zero-series convergence
operator trace-class infrastructure
```

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
- Current total: **83%**

Estimated progress toward **100% axiom-free Lean verification**: **7–16%**.
