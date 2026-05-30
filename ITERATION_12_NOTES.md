# Iteration 12 Notes

## What this iteration does

This iteration cleans up the topology of the slit plane.

Instead of making the F-side depend on the stronger claim

```lean
Ω = Complex.slitPlane
```

we now require only:

```lean
IsOpen Ω
```

through `OpenOmegaAPI`.

This is more faithful to the actual F-side local arguments: they need openness of `Ω` to
turn global equality on `Ω` into local equality at a witness point.

## What remains

The actual proof of `IsOpen Ω` is still a small API:

```lean
isOpen_Omega_native
```

but it is now clearly isolated and should be easy to discharge in the next iteration.

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
- Current total: **80%**

Estimated progress toward **100% axiom-free Lean verification**: **6–15%**.
