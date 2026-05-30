# Iteration 3 Notes

## What this iteration does

This iteration discharges the local Appendix-E algebra.

The manuscript's local substitution is:

```text
D: FH = B + RH
E: B = Bzero
H: Bzero = Harch - Zpole
```

Therefore:

```text
FH = RH + Harch - Zpole = Htot - Zpole
```

where:

```lean
Htot D H s := D.RH s + H.Harch s
```

## What remains

The identity is still only local on the overlap half-plane. The next step is the Appendix-F
globalization by the meromorphic identity theorem on `Ω`.

## Percentage covered

Estimated progress toward **100% Lean-faithful formalization**:

- Iteration 1: 8%
- Iteration 2: +6%
- Iteration 3: +6%
- Current total: **20%**

Estimated progress toward **100% axiom-free Lean verification**: **0–4%**.
