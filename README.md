# RH-Formalization

**Author and project lead: Travis Darshan**

[![DOI](https://zenodo.org/badge/1316438323.svg)](https://doi.org/10.5281/zenodo.21960406)

**Lean 4 formalization of an operator-theoretic / prime-power criterion for the Riemann Hypothesis**

Lean `v4.30.0-rc2` with pinned Mathlib.

> **Status — October 7, 2026.** The principal result is **Stage A**, complete and machine-certified:
>
> `RH_from_pairedTransform_only_dense : hP_dense → RiemannHypothesis`
>
> with the conclusion locked to Mathlib's root-level `RiemannHypothesis` by the certified equivalence `RH_semantic_lock` and exported as `RH_from_pairedTransform_only_dense_mathlib`. All endpoints audit to `[propext, Classical.choice, Quot.sound]`; reproduce from a fresh clone with one command (see *Independent verification*).
>
> **What the hypothesis is.** `hP_dense` asks that the compensated prime package of a finite Galerkin prime-weighted operator family stay locally bounded on every compact subset of Ω = ℂ ∖ (−∞, 0], uniformly along the dense schedule. An off-critical-line zero ρ produces a pole of the limiting object at −ρ(1−ρ) ∈ Ω; the certified chain turns local boundedness into holomorphy and the pole into a contradiction. Classically, `hP_dense` holds under RH, so the criterion is of exactly RH strength. **No unconditional result is claimed.**
>
> **Stage B(i) (the energy route, `RH_of_denseQV_uniform`) is certified but is no longer the live route** — see *Status of the energy route* below. The live frontier is the polylog widening of Stage A (PL series) and the shield question for `hP_dense`.

## Why this repository is significant

This is a large, author-led Lean 4 research development built around an original mathematical program rather than a textbook transcription. The `RHFormalization/` library currently contains **1,287 Lean files and 129,400 lines of Lean, with 0 explicit axiom declarations and no `sorry`**; the default `lake build` compiles the **676 files (81,054 lines)** reachable from the root module, and the Stage A dependency cone alone is **553 files (66,822 lines)**.

The formalization has functioned as a mathematical instrument as well as a verifier. It has produced a machine-checked conditional theorem to the full Riemann Hypothesis, exact residual-accounting identities that sharpened the operator architecture, structural results clarifying which mechanisms remain viable, and the current dense-schedule reconstruction aimed at proving the remaining analytic frontier unconditionally.

The current RH dependency cone is intentionally narrow, but that should not be confused with the scope of the project. The repository contains a substantially broader body of machine-checked operator theory, Galerkin analysis, heat-kernel and resolvent identities, explicit-formula interfaces, arithmetic estimates, positive-energy constructions, earlier conditional endpoints, Duhamel machinery, and formally established negative or obstruction results. Results no longer required by the shortest live route remain part of the mathematical contribution and reusable infrastructure of the project.

---

## Repository scale

| Metric (October 7, 2026) | Count |
| --- | ---: |
| Lean files in `RHFormalization/` | **1,287** |
| Lean lines in `RHFormalization/` | **129,400** |
| Files compiled by default `lake build` (root-reachable) | **676** |
| Lines compiled by default `lake build` | **81,054** |
| Theorem + lemma declarations (compiled) | **1,798** |
| Definitions (compiled) | **1,030** |
| Stage A dependency cone | **553 files / 66,822 lines** |
| Explicit `axiom` declarations | **0** |
| Files containing `sorry` | **0** |

Files in `RHFormalization/` not reachable from the root module are earlier routes and probes retained as part of the research record; they are not compiled by default and nothing in the certified endpoints depends on them.

Current archived Stage A release: `v2026.08.15-stage-a` — Zenodo DOI: `10.5281/zenodo.21960407`.

---

# What is machine-certified

## 1. The certified criterion (Stage A)

```lean
RH_from_pairedTransform_only_dense : hP_dense → RiemannHypothesis
RH_semantic_lock : RHFormalization.RiemannHypothesis ↔ _root_.RiemannHypothesis
RH_from_pairedTransform_only_dense_mathlib : hP_dense → _root_.RiemannHypothesis
```

`hP_dense` is the compact-local boundedness statement

$$
\forall K\Subset\Omega,\;\exists C_K,\;\forall n,\;\forall s\in K,\qquad
\left\|\,2\,\mathrm{denseFreePairedTransform}(n,s)-\mathrm{compensatorM}(n,s)\right\|\le C_K,
\qquad \Omega=\mathbb C\setminus(-\infty,0],
$$

on the dense schedule `L = X^(3/4)`. The chain is: finite Galerkin prime-weighted operator family → stage transforms and the compensator identity → the zero-side pole package (poles at −ρ(1−ρ), inside Ω exactly when ρ is off the critical line) → overlap identity on Re s > 1 → Montel/identity-theorem rigidity → RH. Every step is kernel-checked; the theorem audits to

```text
[propext, Classical.choice, Quot.sound]
```

**Strength.** Classically (von Koch, partial summation) `hP_dense` holds under RH, so the criterion is equivalent to RH up to a Galerkin error that vanishes on the dense schedule. The converse direction is not yet formalized.

The repository also retains the earlier certified endpoints `RH_from_pairedTransform_only : hP → RiemannHypothesis`, `hSC → HtailExists → RiemannHypothesis` and `RH_from_Htail` as part of the development history.

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

# Earlier positive-energy framework (tilted route — certified, off-live)

> **Note (August 28, 2026):** the E1–E4a bricks below remain valid kernel-certified Lean theorems, but this tilted (`η`), code-centered framework has been superseded as the live route. The live Stage B(i) route uses the untilted (`η = 0`) endpoint with decoded physical prime-power centers: `denseCenteredMatrix`, `denseV`, `denseAV`, `denseQV` (see the live chain at the top). This section is retained as certified research record.

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

# Research-stage mathematics (earlier free-energy reduction — superseded as live route)

> **Note (August 28, 2026):** the finite-to-continuum and weighted mean-square material below belongs to the earlier free/tilted energy program. The live route keeps the full potential `Vₙ` inside the resolvent (`denseQV`) precisely because the free-energy reduction collapses to a classical criterion. Retained as research record.

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

# Status of the energy route (Stage B(i), `RH_of_denseQV_uniform`)

`RH_of_denseQV_uniform : (∃ a > 0, ∃ C, ∀ n, denseQV n a ≤ C) → RiemannHypothesis` is machine-certified (bricks B1–B8), with `denseQV n a = (1/(2Lₙ))·Tr[Cₙᵀ(Λₙ + aI + Vₙ)⁻¹Cₙ]`. **Its hypothesis cannot hold**, so it is not a route to RH:

- *Argument (paper-level, numerically checked).* The diagonal of `Cₙ` at low Galerkin frequency is, up to a vanishing error, the normalized Chebyshev discrepancy Dₙ = (ψ(Xₙ) − Xₙ)/√Xₙ + O(1). Hence `denseQV n a ≥ c(a)·Dₙ² − C`. By Littlewood (1914), ψ(x) − x = Ω±(√x·log log log x), so `denseQV` is unbounded **whether or not RH holds** (if RH fails, the certified theorem itself forbids the bound). A direct numerical computation of `denseQV` from the definitions matches the continuum form (1/2π)∫|F(Xₙ, ½ − iξ)|²/(ξ² + a)dξ to within 1–2%.
- *Where the strength is lost.* One Cauchy–Schwarz step (B8c) bounds an off-line quantity by an on-line energy; the energy is positive in every world and so cannot encode RH.
- *Formalization status.* Certified: KB1 `denseQV_ge_diag_sum`, KB2 `denseCenteredMatrix_diag_closed`, KB3a `abs_diag_sub_lowFreqWitness_le`, KB3b-i `cos_sq_add_cos_sq_quarter_ge`, KB3b-ii/iii `sum_range_two_blocks`, `pair_sq_ge_of_phase`. Remaining: the assembly (KB3b-iv) and the final statement with Littlewood as a named classical hypothesis (KB3c).

This is recorded as an obstruction result, alongside the other certified obstructions (dilution theorems, the per-spike log N loss, and the raw Gaussian frame Bessel bound `rawGaussianFrame_bessel_ge`).

# Current frontier (October 2026)

1. **Polylog widening of Stage A (PL series).** Target: `hP_dense` weakened from *bounded* to *≤ C·(log n)^A* on compacts, by Abel summation against k^(−δ) at the square stages n = M² − 2. Certified so far: PL-1 `abel_transfer_norm_bound_growing`, PL-2 `polylog_abel_weights_bounded`, PL-3 `starObject_square_stage_closed`, PL-4a `partialSum_shift_eq`. In progress: PL-4b (centered Abel bound and main-term comparison), PL-5/6 assembly.
2. **The shield question.** Any proof of `hP_dense` must supply a bound on the prime side that does not already presuppose the location of the zeros. Since the operator family is built from the prime measure, such a bound is an arithmetic statement; identifying which one is the current research question.

None of this is claimed proved beyond the declarations listed as certified.

# Earlier unconditional frontier (tilted mean-square form — superseded)

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

### Machine-certified

- Stage A: `RH_from_pairedTransform_only_dense : hP_dense → RiemannHypothesis`, with `RH_semantic_lock` and the Mathlib-predicate export;
- the energy-route endpoint `RH_of_denseQV_uniform` (certified; hypothesis unsatisfiable — see above);
- the certified obstruction results (dilution, log N loss, raw Gaussian frame Bessel bound) and the KB bricks listed above;
- the PL bricks listed above;
- the Galerkin/operator, heat-trace, resolvent, compensator, explicit-formula and meromorphy infrastructure in the Stage A cone;
- earlier conditional endpoints and the tilted-energy infrastructure (off the live route).

### Paper-level, not yet formalized

- `hP_dense` holds under RH (the converse of Stage A);
- unboundedness of `denseQV` (KB3b-iv/KB3c remaining; Littlewood's theorem enters as a classical input);
- the remaining PL steps.

### Open

- an unconditional proof of `hP_dense` (equivalently, of RH).

---

# Current status

```text
finite Galerkin prime-weighted operator family
            ↓  (certified)
compensated prime package hP_dense
            ↓  (certified: Stage A)
RiemannHypothesis
```

The arrow into `hP_dense` is the open problem. It is of exactly RH strength; the project's certified contribution is the criterion, its semantic lock to Mathlib, and a certified map of routes that provably do not supply it.

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

**Semantic lock (added August 2026):** the project predicate is certified equivalent to Mathlib's root-level statement: `RH_semantic_lock : RHFormalization.RiemannHypothesis ↔ _root_.RiemannHypothesis`, and the endpoint is exported against Mathlib's own predicate as `RH_from_pairedTransform_only_dense_mathlib`, both auditing to `[propext, Classical.choice, Quot.sound]`. A reviewer therefore does not need to trust the project's definitions to know what the conclusion asserts.

RH-Formalization is intended to be independently inspectable. **One command, current version** (builds the root library and prints the axiom audit of all four endpoints):

```bash
git clone https://github.com/tdarshan0917-hub/RH-Formalization- rh-verify && cd rh-verify && bash verify.sh
```

Expected: four lines, each ending `depends on axioms: [propext, Classical.choice, Quot.sound]`. See `VERIFICATION.md`.

To reproduce the archived Stage A release instead:

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

These commands verify that the conditional Stage A theorem is accepted by Lean and expose its axiom dependencies. They do not assert that RH has been proved: `hP_dense` remains open.

The project's RH predicate is defined from Mathlib's actual `riemannZeta`. In `RHFormalization/Basic.lean`, nontrivial zeros are represented by

```lean
riemannZeta ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1
```

and the project endpoint asserts that every such zero has real part `1/2`.

Independent reviewers are encouraged to inspect the theorem statement, semantic definitions, dependency cone, and source directly rather than relying on screenshots or AI assessments.

