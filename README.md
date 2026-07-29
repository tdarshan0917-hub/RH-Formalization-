# RH-Formalization

Lean 4 formalization of an operator-theoretic approach to the Riemann Hypothesis.
Lean `v4.30.0-rc2` with pinned Mathlib.

## Audit

- **~115,000** non-blank lines of Lean 4 (**~135,000** with blanks and comments) across **1,801** files
- **2,538** declared theorems and lemmas
- **0** axiom declarations
- `sorry` confined to named probe/attempt files
- Live chain: `#print axioms` gives `[propext, Classical.choice, Quot.sound]`

## Build

    lake exe cache get
    lake build

## What is proved

A machine-checked **conditional proof** of the Riemann Hypothesis:
`RH_from_Htail : HtailExists → RiemannHypothesis`, verified by Lean's kernel
with no axioms beyond the standard three. The live chain reduces Mathlib's
`RiemannHypothesis` to a single named analytic
estimate on the compensated prime-power package (`h_ctail_le` / `HtailExists`),
via `RH_from_Htail`. That estimate is open and is the subject of ongoing work.

Everything upstream of it is machine-checked and axiom-clean: the Galerkin
operator tower, Duhamel expansions, heat-trace machinery, the defect gate,
the compensator and seam identities, and the zero-side meromorphic package.

## Repository layout

- `RHFormalization/` — the compiled library
- `_scratch*/`, `_failed_experiments/`, `_proof_targets/` — exploratory work,
  retained deliberately as a record of routes tried
- top-level `*Audit.lean`, `*Probe.lean`, `*Check.lean` — one-off API
  investigations, not part of the build

## Status

A machine-checked **conditional proof**: RH follows from a single named
analytic estimate (`HtailExists`), with every other step verified and
axiom-clean. Work on the unconditional route — closing that estimate — is
ongoing, and this repository is the working record of it.
