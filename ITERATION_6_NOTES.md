# Iteration 6 Notes

## What this iteration does

This iteration refines the H-side pole witness.

The manuscript's grouped-pole claim is:

```text
if several zeros map to the same pole location -ρ(1-ρ),
their positive multiplicities add, so the principal part cannot cancel.
```

Iteration 6 formalizes this as:

```lean
GroupedPoleClass
groupedMultiplicitySum
groupedResidueCoeff
GroupedResidueNonzeroAPI
HSideGroupedPoleData
```

and then builds:

```lean
PoleWitnessAPI H
GenuinePoleNormalFormAPI H
```

from the grouped H-side data.

## What remains

The grouped-residue positivity is now isolated, but the actual construction of the H-side
meromorphic package from the infinite zero-pole series remains API-level.

## Percentage covered

Estimated progress toward **100% Lean-faithful formalization**:

- Iteration 1: 8%
- Iteration 2: +6%
- Iteration 3: +6%
- Iteration 4: +7%
- Iteration 5: +7%
- Iteration 6: +7%
- Current total: **41%**

Estimated progress toward **100% axiom-free Lean verification**: **0–7%**.
