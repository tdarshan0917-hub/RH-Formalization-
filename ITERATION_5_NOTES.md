# Iteration 5 Notes

## What this iteration does

This iteration isolates the local pole-obstruction theorem behind the final Appendix-F
contradiction.

The manuscript's local idea is:

```text
FH = Htot - Zpole
FH holomorphic
Htot holomorphic
Zpole has a genuine uncancelled pole
```

These cannot all hold at the same point `s0 ∈ Ω`.

Iteration 5 formalizes this as a local API:

```lean
LocalPoleObstructionAPI
```

and provides a bridge from this local obstruction to the previous global no-pole API.

## What remains

The local normal-form theorem is still API-level. The next step is to formalize the H-side
grouped residue / non-cancellation layer so that `HasGenuinePole` and the normal form are
owned by the zero-side package.

## Percentage covered

Estimated progress toward **100% Lean-faithful formalization**:

- Iteration 1: 8%
- Iteration 2: +6%
- Iteration 3: +6%
- Iteration 4: +7%
- Iteration 5: +7%
- Current total: **34%**

Estimated progress toward **100% axiom-free Lean verification**: **0–6%**.
