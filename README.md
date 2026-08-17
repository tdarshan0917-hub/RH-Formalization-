# RH-Formalization

**Author and project lead: Travis Darshan**

[![DOI](https://zenodo.org/badge/1316438323.svg)](https://doi.org/10.5281/zenodo.21960406)

**Lean 4 formalization and formal audit of an operator-theoretic / prime-power approach to the Riemann Hypothesis**

Lean `v4.30.0-rc2` with pinned Mathlib.

> **Public development began May 30, 2026. Current status — August 14, 2026:** RH-Formalization contains a machine-checked conditional theorem whose conclusion is the full Riemann Hypothesis: `RH_from_pairedTransform_only : hP → RiemannHypothesis`. The active research program is to prove the explicit analytic frontier `hP` unconditionally.

> **Stage A is now machine-certified through D1–D6.** The dense reconstruction culminates in `RH_from_pairedTransform_only_dense : hP_dense → RiemannHypothesis` on the dense `L = X^(3/4) = o(X)` schedule. The active research frontier is to establish the explicit analytic hypothesis `hP_dense` unconditionally.

## Why this repository is significant

This is a large, author-led Lean 4 research development built around an original mathematical program rather than a textbook transcription. The compiled `RHFormalization/` library currently contains **1,255 Lean files, 125,189 lines of Lean, 2,762 theorem/lemma declarations, 1,132 definitions, and 0 explicit axiom declarations**. The full tracked Lean research record contains **1,878 Lean files and 144,077 lines of Lean**.

The formalization has functioned as a mathematical instrument as well as a verifier. It has produced a machine-checked conditional theorem to the full Riemann Hypothesis, exact residual-accounting identities that sharpened the operator architecture, structural results clarifying which mechanisms remain viable, and the current dense-schedule reconstruction aimed at proving the remaining analytic frontier unconditionally.

The current RH dependency cone is intentionally narrow, but that should not be confused with the scope of the project. The repository contains a substantially broader body of machine-checked operator theory, Galerkin analysis, heat-kernel and resolvent identities, explicit-formula interfaces, arithmetic estimates, positive-energy constructions, earlier conditional endpoints, Duhamel machinery, and formally established negative or obstruction results. Results no longer required by the shortest live route remain part of the mathematical contribution and reusable infrastructure of the project.

---

## Repository scale

### Compiled Lean library

The compiled `RHFormalization/` library currently contains:

| Metric | Current snapshot |
| --- | ---: |
| Lean 4 source files | **1,255** |
| Total Lean source lines | **125,189** |
| Nonblank Lean source lines | **107,955** |
| Theorem + lemma declarations | **2,762** |
| Definition declarations | **1,132** |
| Explicit `axiom` declarations | **0** |

### Full research repository

Including the compiled mathematical library together with retained certified infrastructure, historical route work, audit files, reconstruction work, and incomplete probes preserved separately under `Experimental/`:

| Metric | Current snapshot |
| --- | ---: |
| Lean files | **1,878** |
| Total Lean source lines | **144,077** |
| Nonblank Lean source lines | **123,187** |

The distinction is deliberate: `RHFormalization/` is the principal mathematical library. Results that are no longer required by the shortest live RH path remain part of the mathematical record and reusable infrastructure; only incomplete or superseded probes are separated under `Experimental/`.

### Current machine audit

Current archived Stage A release: `v2026.08.15-stage-a` — Zenodo DOI: `10.5281/zenodo.21960407`.

The present public Stage A baseline is the machine-certified dense reconstruction through D1–D6. Its dense conditional endpoint is `RH_from_pairedTransform_only_dense : hP_dense → RiemannHypothesis`. The earlier endpoint `RH_from_pairedTransform_only : hP → RiemannHypothesis` remains part of the certified development.

The Stage A dense endpoint dependency cone audits under `#print axioms` to `[propext, Classical.choice, Quot.sound]`, with no project-specific mathematical axioms. The published Stage A build emitted no `declaration uses 'sorry'` warnings.

---

# What is machine-certified

## 1. A clean conditional RH endpoint

The current compact endpoint is:

```lean
RH_from_pairedTransform_only
```

schematically:

```text
hP  →  RiemannHypothesis
```

where `hP` is the compact-local boundedness statement

$$
\forall K\Subset\Omega,\;
\exists C_K,\;
\forall n,\;\forall s\in K,\qquad
\left\|
2\,\mathrm{adaptiveFreePairedTransform}(c,n,s)
-
\mathrm{compensatorM}(n,s)
\right\|
\le C_K.
$$

Here

$$
\Omega=\mathbb C\setminus(-\infty,0].
$$

The theorem is checked by Lean's kernel and, in the current audit, depends only on:

```text
[propext, Classical.choice, Quot.sound]
```

This is presently the cleanest machine-certified description of the unconditional frontier.

The repository also retains the earlier certified route

```text
hSC → HtailExists → RiemannHypothesis
```

and the older endpoint

```lean
RH_from_Htail : HtailExists → RiemannHypothesis
```

as part of the development history.

---

## 2. Certified residual accounting and route refinement

A major purpose of the formalization has been **mathematical auditing**, not merely transcription.

The current repository certifies the exact accounting identity

$$
R_{\mathrm{stage}}
=
\mathrm{galHead}
+
\left(
\mathrm{galFTailClosed}
-
\mathrm{galBTail}
\right),
$$

implemented as:

```lean
raw_R_stage_tail_accounting
```

on the appropriate half-plane.

The August 2026 audit established the exact relation among the stage residual, the earlier sector package, and the large-time prime-package tail. This clarified which contributions must be tracked explicitly in the certified accounting and directly informed the current live route.

The formal audit established identities including:

```text
Rcan = manuscript sectors + pairedTailGap
```

and, in the corresponding sector comparison,

```text
D.MR.3 RHS − Rcan = galBTail
```

The machine accounting identifies exactly how the additional prime-package contribution enters the residual structure, replacing informal bookkeeping with a certified identity.

The current live route therefore keeps the operator tail and prime-package tail visible separately in the certified architecture.

Selected audit milestones from August 8:

```text
cd992e2  RAW ACCOUNTING CERTIFIED:
         R_stage = head + (Ftail - Btail)

0fff99d  SECTOR CORRESPONDENCE:
         D.MR.3 RHS minus Rcan = galBTail exactly

1216ab2  FOUR-SECTOR ACCOUNTING:
         Rcan = manuscript sectors + pairedTailGap

38f3251  TERMINAL CERTIFICATE:
         obstruction bound => RiemannHypothesis

b13def9  ROUTE CERTIFICATE:
         hSC => HtailExists => RiemannHypothesis
```

This audit is one of the central results of the formalization effort. It shows Lean functioning as a mathematical research instrument rather than a transcription layer: exact machine-certified identities sharpened the residual structure and helped reduce the broader program to the current live RH architecture.

---

# New positive-energy framework

After the residual audit isolated the remaining analytic seam, the project began developing a quadratic positive-energy formulation rather than another absolute-value estimate on the original linear transform.

At HEAD `c30fd23`, the first four bricks of this framework are machine-certified.

## E1 — Tilted centered observable

`RHFormalization/TiltedEnergyDefinitions.lean`

The finite Galerkin observable is assembled entrywise:

$$
C_{n,\eta}
=
\sum_q
w(q)e^{-\eta\log q}\,T_n(\log q)
-
\int_0^{R_n}
e^{(1/2-\eta)u}T_n(u)\,du.
$$

The Lean implementation is parameterized by the finite set `qs` and weight function `w`; the intended RH instantiation retains the project's frozen prime-power normalization

$$
w(q)=\frac{\Lambda(q)}{\sqrt q}.
$$

Key definitions:

```lean
tiltedCenteredEntry
tiltedCenteredMatrix
```

---

## E2 — Positive tilted energy

The corresponding finite energy is defined in basis-sum form:

$$
Q_{n,\eta}(a)
=
\frac1{2L_n}
\sum_k
\frac1{\lambda_{k,n}+a}
\sum_j
C_{n,\eta}(k,j)^2.
$$

Lean theorem:

```lean
tiltedEnergy_nonneg
```

proves

$$
Q_{n,\eta}(a)\ge0
$$

for $L>0$ and $a>0$.

This positivity is finite-dimensional and arithmetic: positive spectral denominators, squares, and finite sums.

---

## E3 — Exact trace / resolvent representation

`RHFormalization/TiltedEnergyTraceForm.lean`

A reusable generic matrix theorem was proved:

```lean
trace_transpose_diag_sandwich
```

which identifies, for a real matrix $C$ and diagonal weights $d_k$,

$$
\operatorname{Tr}
\left(
C^{T}\operatorname{diag}(d)C
\right)
=
\sum_k d_k\sum_j C_{kj}^2.
$$

The energy therefore has the exact operator representation

$$
Q_{n,\eta}(a)
=
\frac1{2L_n}
\operatorname{Tr}
\left[
C_{n,\eta}^{T}
\operatorname{diag}
\left(
\frac1{\lambda_{k,n}+a}
\right)
C_{n,\eta}
\right].
$$

Machine-certified theorem:

```lean
tiltedEnergy_eq_trace_resolvent
```

This establishes the operator meaning of the computational basis-sum energy without introducing a matrix inverse.

---

## E4a — Finite energy kernel

`RHFormalization/TiltedEnergyKernel.lean`

The finite pair kernel is now defined by

$$
G_{n,a}(u,v)
=
\frac1{2L_n}
\sum_k
\frac1{\lambda_{k,n}+a}
\sum_j
T_n(u)_{kj}T_n(v)_{kj}.
$$

The current machine-certified results include:

```lean
tiltedEnergyKernel_symm
tiltedEnergyKernel_diag_nonneg
```

giving

$$
G_{n,a}(u,v)=G_{n,a}(v,u)
$$

and

$$
G_{n,a}(u,u)\ge0
$$

for the positive spectral regime.

The current energy-route commits are:

```text
6d145db  E1+E2:
         tilted centered observable + tilted energy + positivity

a129fa5  E3:
         trace representation via generic diagonal sandwich lemma

c30fd23  E4a:
         finite energy kernel, symmetry, diagonal nonnegativity
```

Together these files add a machine-checked positive quadratic structure on top of the existing Galerkin displacement machinery.

---

# Research-stage mathematics

The results in this section are **paper-derived and under active formalization/audit**. They should not yet be read as kernel-certified Lean theorems.

## Finite Galerkin to continuum energy

The current paper derivation obtains, along the adaptive Galerkin schedule,

$$
Q_{n,\eta}(1)
=
\mathcal E_{n,\eta}
+
\varepsilon_{n,\eta},
\qquad
\varepsilon_{n,\eta}\to0,
$$

where the continuum energy is

$$
\mathcal E_{n,\eta}
=
\frac1{2\pi}
\int_{\mathbb R}
\frac{
|\widehat{\mu}_{n,\eta}(\xi)|^2
}{
1+\xi^2
}
\,d\xi.
$$

The finite-to-continuum analysis includes:

- an exact trace-kernel identity;
- the Dirichlet resolvent / whole-line kernel comparison;
- explicit boundary-image terms;
- both Galerkin projection tails;
- an off-diagonal displacement-entry estimate;
- adaptive-schedule error arithmetic;
- a crude unconditional $\Lambda(m)\le\log m$ mass bound.

The current paper estimate has an explicit vanishing finite-size error rather than a heuristic continuum replacement.

---

## Positive real-variable energy identity

For

$$
D_\eta(X)
=
\sum_{q\le X}
\Lambda(q)q^{1/2-\eta}
-
\int_1^X t^{1/2-\eta}\,dt,
$$

the continuum kernel

$$
\frac12e^{-|x|}
$$

factors as a one-sided exponential convolution, leading to the positive identity

$$
\mathcal E_{n,\eta}
=
\int_1^{X_n}
\frac{|D_\eta(X)|^2}{X^3}\,dX
+
\frac{|D_\eta(X_n)|^2}{2X_n^2}.
$$

This converts the operator energy into a weighted mean-square statement about a centered prime-power discrepancy.

The current research frontier is therefore expressible as the positive arithmetic problem

$$
(QE)_\eta:
\qquad
\sup_n Q_{n,\eta}(1)<\infty,
$$

or, after the continuum reduction, the corresponding weighted $H^{-1}$ / mean-square bound.

For fixed $\eta>0$, the deterministic research-stage bridge gives

$$
(QE)_\eta
\Longrightarrow
\zeta(s)\neq0
\qquad
\left(\Re s>\frac12+\eta\right).
$$

The converse paper argument requires a strict zero-free margin at fixed $\eta$. At the family level, requiring the energy bound for every $\eta>0$ is aligned with RH.

These implications are being kept distinct from the machine-certified results above until their Lean formalization is complete.

---

# Current unconditional frontier

The decisive theorem is **not proved**:

$$
\boxed{
\forall\eta>0,\qquad
\sup_n Q_{n,\eta}(1)<\infty.
}
$$

Equivalently, at the current research level, the problem is to establish the weighted mean-square convergence

$$
\int_1^\infty
\frac{|D_\eta(X)|^2}{X^3}\,dX
<\infty
$$

for every $\eta>0$.

Even a proof for one fixed $0<\eta<1/2$ would be significant. For example, the current intermediate research target

$$
\eta=\frac14
$$

would correspond to a zero-free region to the right of

$$
\Re s=\frac34.
$$

No such theorem is claimed here.

---

# Research findings and pruned routes

The repository and associated paper work retain negative results because identifying why a plausible route fails is part of the formal research program.

Among the current findings:

### Linear renewal at $\eta=1/4$

A weighted Dirichlet-convolution computation gives the paper-level identity

$$
\sum_{m\le X}
m^{1/4}D(X/m)
=
-\frac{4\gamma}{5}X^{5/4}
+
O(X^{1/4}\log X).
$$

The associated positive renewal kernel is supercritical rather than contractive, so this particular linear renewal identity does not supply the required energy contraction.

### Direct weighted Selberg-energy route

Weighting Selberg's quadratic identity by $n^{1/4}$ preserves its convolution structure, but the classical elementary forcing term lives at the weighted main-term scale rather than in the required energy space.

Under a separated Cauchy-Schwarz treatment, the forcing term is too large for

$$
L^2([1,\infty),X^{-3}dX).
$$

The conclusion is deliberately narrow: the direct classical weighted-Selberg implementation does not close the $\eta=1/4$ energy bound. This is not being asserted as a general impossibility theorem for every possible use of Selberg symmetry.

### Current research direction

The centered Dirichlet-polynomial energy is now being analyzed by smooth dyadic frequency localization. The paper audit indicates that sufficiently high-frequency blocks are favorable, aided by the convergent diagonal series

$$
\sum_{n\ge1}\frac{\Lambda(n)^2}{n^{3/2}}<\infty.
$$

The exact low/intermediate-frequency split is **not yet closed**. A key correction from the current audit is that smooth localization in the frequency variable does not automatically localize the explicit-formula zero sum by zero ordinate: high-ordinate zeros can leak polynomially into bounded frequency windows. The current paper task is therefore an exact zero-response / zero-leakage kernel analysis before any stronger obstruction classification is frozen.

This remains research-stage mathematics and is not part of the machine-certified claims above.

---

# Why the formalization matters

This repository is intended to do more than encode a proposed proof.

The formal system has already served three distinct roles:

1. **Verification** — long operator, Galerkin, heat-trace, resolvent, compensator, and meromorphic chains are checked by Lean's kernel.
2. **Audit** — an apparently exhaustive residual decomposition was tested algebraically and found to omit a specific large-time prime-package term.
3. **Research compression** — after thousands of intermediate lemmas, the current unconditional question can be stated as one explicit boundedness problem rather than an informal collection of unresolved estimates.

That distinction is important: the project treats a failed proof step as information to be isolated and preserved, not something to hide behind downstream formal machinery.

---

# Build

The project uses Lean `v4.30.0-rc2` with pinned Mathlib.

```bash
lake exe cache get
lake build
```

For critical endpoint theorems, the repository additionally uses:

```lean
#print axioms theoremName
```

to audit theorem dependencies.

The August 9, 2026 targeted snapshot returned:

```text
Build completed successfully (9107 jobs).
BUILD_EXIT=0
AXCHECK_EXIT=0
```

for the audited raw-tail, RH-endpoint, and tilted-energy targets.

---

# Repository layout

```text
RHFormalization/
```

Main compiled Lean library.

```text
_scratch*/
_failed_experiments/
_proof_targets/
```

Exploratory and historical material retained to document attempted routes and failed constructions.

Top-level files such as:

```text
*Audit.lean
*Probe.lean
*Check.lean
```

are generally API investigations, audits, or research probes rather than part of the primary certified endpoint.

The repository intentionally preserves substantial research history rather than presenting only the surviving final route.

---

# Claim discipline

The current state should be read as follows:

### Machine-certified

- conditional RH endpoints;
- the clean `RH_from_pairedTransform_only` reduction;
- raw-tail accounting;
- the formal diagnosis of the large-time prime-package seam;
- the established Galerkin/operator infrastructure;
- the tilted centered observable;
- positivity of the finite tilted energy;
- the exact trace/resolvent representation;
- the finite symmetric energy kernel and its diagonal nonnegativity.

### Paper-derived / awaiting Lean formalization

- the complete finite-to-continuum tilted-energy estimate;
- the positive $H^{-1}$ representation;
- the weighted prime-discrepancy identity;
- the deterministic tilted-energy-to-zero-free-half-plane bridge;
- the family-level mean-square criterion.

### Open

- the unconditional tilted-energy / weighted mean-square bound required to close the RH frontier.

---

# Current status

The project has therefore moved beyond the statement

```text
"RH follows if HtailExists."
```

to a more precise certified picture:

```text
explicit compensated paired-transform bound
                    ↓
          RiemannHypothesis
```

together with a new positive-energy research interface:

```text
tilted centered prime observable
            ↓
positive Galerkin energy Q
            ↓
finite symmetric pair kernel G
            ↓
weighted mean-square prime discrepancy
            ↓
open energy bound
            ↓
paired-transform bound
            ↓
RiemannHypothesis
```

The first several arrows are machine-certified or paper-closed as indicated above.

The remaining unconditional energy bound is open.

That open theorem — not hidden corrections elsewhere in the formal chain — is the present research frontier.

---

## Copyright and citation

Copyright © 2026 Travis Darshan. All rights reserved. No open-source license is currently granted for this repository.

If you use or reference this Lean 4 formalization, please cite Travis Darshan. Formal citation metadata is available in `CITATION.cff`.

### Zenodo archive

**Stage A release DOI:** https://doi.org/10.5281/zenodo.21960407

**All versions / persistent project DOI:** https://doi.org/10.5281/zenodo.21960406

Archived release: `v2026.08.15-stage-a`

---

## Independent verification

RH-Formalization is intended to be independently inspectable. To reproduce the archived Stage A endpoint from a fresh clone:

```bash
git clone https://github.com/tdarshan0917-hub/RH-Formalization-.git
cd RH-Formalization-
git checkout v2026.08.15-stage-a
lake exe cache get
lake build RHFormalization.DenseSealEndpoint
```

The Stage A endpoint is:

```lean
RH_from_pairedTransform_only_dense :
    hP_dense → RiemannHypothesis
```

The build prints the theorem's axiom dependency audit:

```text
'RHFormalization.RH_from_pairedTransform_only_dense'
depends on axioms: [propext, Classical.choice, Quot.sound]
```

with no project-specific mathematical axioms in that dependency cone.

This command verifies that the published conditional Stage A theorem is accepted by Lean and exposes its axiom dependencies. It does not assert that RH has already been proved unconditionally: the active research objective is to establish the remaining analytic hypothesis `hP_dense` unconditionally.

The project's RH predicate is defined from Mathlib's actual `riemannZeta`. In `RHFormalization/Basic.lean`, nontrivial zeros are represented by

```lean
riemannZeta ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1
```

and the project endpoint asserts that every such zero has real part `1/2`.

Independent reviewers are encouraged to inspect the theorem statement, semantic definitions, dependency cone, and source directly rather than relying on screenshots or AI assessments.

