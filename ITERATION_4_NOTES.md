# Iteration 4 Notes

## What this iteration does

This iteration refines Appendix F's global rigidity step.

The manuscript says:

```text
local identity on Uσ0
  FH = Htot - Zpole
extends to all of Ω by the meromorphic identity theorem.
Since FH and Htot are holomorphic on Ω, Zpole cannot have a genuine uncancelled
pole inside Ω.
```

This iteration represents that as three precise interfaces:

```lean
MeromorphicIdentityTheoremAPI
HolomorphicShieldAPI
NoPoleFromGlobalIdentityAPI
```

and then rebuilds the previous no-pole rigidity object from them.

## What remains

The meromorphic identity theorem and local no-pole obstruction are still API-level.
They are now isolated as small formal targets rather than hidden inside one large
rigidity assumption.

## Percentage covered

Estimated progress toward **100% Lean-faithful formalization**:

- Iteration 1: 8%
- Iteration 2: +6%
- Iteration 3: +6%
- Iteration 4: +7%
- Current total: **27%**

Estimated progress toward **100% axiom-free Lean verification**: **0–5%**.
