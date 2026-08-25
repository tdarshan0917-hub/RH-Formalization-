# Verifying the RH dense endpoint

The certified result is the implication

```
RHFormalization.RH_from_pairedTransform_only_dense : hP_dense -> RiemannHypothesis
```

on the dense schedule L = X^(3/4). Verification means: build the project from
source and confirm the endpoint's axiom dependency is exactly the standard
Mathlib base — [propext, Classical.choice, Quot.sound] — with no sorryAx in
its dependency cone.

## One-command verification

```bash
git clone https://github.com/tdarshan0917-hub/RH-Formalization- rh-verify && cd rh-verify && bash verify.sh
```

## Manual steps

Requires elan (https://github.com/leanprover/elan). The repo's lean-toolchain
pins the Lean version and lake-manifest.json locks the Mathlib commit, so you
get exactly the environment the result was certified in.

```bash
git clone https://github.com/tdarshan0917-hub/RH-Formalization- rh-verify
cd rh-verify
lake exe cache get        # prebuilt Mathlib oleans; omit to build Mathlib from source
lake build                # builds every RHFormalization module
printf 'import RHFormalization.DenseSealEndpoint\n#print axioms RHFormalization.RH_from_pairedTransform_only_dense\n' > AxiomCheck.lean
lake env lean AxiomCheck.lean
```

## Expected output

```
'RHFormalization.RH_from_pairedTransform_only_dense' depends on axioms: [propext, Classical.choice, Quot.sound]
```

That single line is the verification: the kernel-checked endpoint depends on
nothing beyond the three axioms Mathlib itself uses for classical mathematics.
An admitted (sorry) theorem anywhere in the endpoint's dependency chain would
appear here as sorryAx; a custom axiom would be listed by name.

## Notes

- Lake may report modules as Built or Replayed depending on cache state;
  either is fine — the checks that matter are the successful build and the
  axiom line above.
- Warnings about unused or unreachable tactics are style linters, not errors.
- The first build takes a while; lake exe cache get keeps it to the
  RHFormalization modules only.
