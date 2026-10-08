# Verifying the certified endpoints

The principal certified result is the implication

```text
RHFormalization.RH_from_pairedTransform_only_dense : hP_dense -> RiemannHypothesis
```

on the dense schedule L = X^(3/4), together with its semantic lock to Mathlib's
root-level `RiemannHypothesis`. Verification means: build the project from
source and confirm that each endpoint's axiom dependency is exactly the standard
Mathlib base — [propext, Classical.choice, Quot.sound] — with no sorryAx in its
dependency cone.

## One-command verification

```bash
git clone https://github.com/tdarshan0917-hub/RH-Formalization- rh-verify && cd rh-verify && bash verify.sh
```

`verify.sh` runs `lake exe cache get`, `lake build`, and then `#print axioms` on:

| Declaration | What it states |
| --- | --- |
| `RH_from_pairedTransform_only_dense` | Stage A: `hP_dense → RiemannHypothesis` |
| `RH_semantic_lock` | project predicate ↔ Mathlib `RiemannHypothesis` |
| `RH_from_pairedTransform_only_dense_mathlib` | Stage A against Mathlib's predicate |
| `RH_of_denseQV_uniform` | energy route (certified; its hypothesis cannot hold — see README) |

## Expected output

```text
'RHFormalization.RH_from_pairedTransform_only_dense' depends on axioms: [propext, Classical.choice, Quot.sound]
'RHFormalization.RH_of_denseQV_uniform' depends on axioms: [propext, Classical.choice, Quot.sound]
'RHFormalization.RH_semantic_lock' depends on axioms: [propext, Classical.choice, Quot.sound]
'RHFormalization.RH_from_pairedTransform_only_dense_mathlib' depends on axioms: [propext, Classical.choice, Quot.sound]
```

An admitted (`sorry`) theorem anywhere in a dependency chain would appear as
`sorryAx`; a custom axiom would be listed by name.

## Manual steps

Requires elan (https://github.com/leanprover/elan). `lean-toolchain` pins the
Lean version and `lake-manifest.json` locks the Mathlib commit.

```bash
git clone https://github.com/tdarshan0917-hub/RH-Formalization- rh-verify
cd rh-verify
lake exe cache get        # prebuilt Mathlib oleans
lake build                # builds RHFormalization and everything it imports
printf 'import RHFormalization.DenseSealEndpoint\n#print axioms RHFormalization.RH_from_pairedTransform_only_dense\n' > AxiomCheck.lean
lake env lean AxiomCheck.lean
```

## Notes

- A full cold build takes roughly 1–2 hours on a laptop (measured: 1 h 42 min, October 7, 2026, fresh clone). `verify.sh` prints nothing until the end; that is expected.

- `lake build` compiles the root module `RHFormalization.lean` and its
  transitive imports (676 files as of October 7, 2026). Files in
  `RHFormalization/` not imported by the root are retained research history and
  are not part of any certified endpoint.
- Lake may report modules as Built or Replayed depending on cache state; either
  is fine.
- Warnings about unused or unreachable tactics are style linters, not errors.
