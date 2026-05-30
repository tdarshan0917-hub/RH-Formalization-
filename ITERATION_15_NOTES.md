# Iteration 15 Notes

## What this iteration does

This iteration refines the local pole-normal-form interface.

The old bridge

```lean
PrincipalPartImpliesGenuinePoleAPI
```

is now built from a narrower normal-form layer.

## What remains

The project still needs a real Laurent/meromorphic definition for:

```lean
HasPrincipalPartAtC
HasGenuinePole
LocalLaurentPrincipalModelC
```

Once those are defined, the normal-form bridge should become a small theorem or a definition.

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
- Current total: **90%**

Estimated progress toward **100% axiom-free Lean verification**: **9–19%**.
