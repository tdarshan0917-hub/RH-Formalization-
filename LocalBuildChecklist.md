# Local Build Checklist

## Step 1 — Create a clean Lean project

```bash
lake update
lake build RHFormalization.Basic
```

## Step 2 — Repair topology and wrappers

```bash
lake build RHFormalization.OmegaTopology
lake build RHFormalization.AnalyticWrappers
lake build RHFormalization.HalfPlaneGeometry
```

Expected repairs:
- theorem names for `Complex.continuous_re`, `Complex.continuous_im`;
- `isOpen_lt` / `isOpen_ne` syntax;
- analytic congruence theorem names.

## Step 3 — Repair algebraic modules

```bash
lake build RHFormalization.PoleGeometry
lake build RHFormalization.InterfaceAlgebra
lake build RHFormalization.HSideResidueArithmetic
```

Expected repairs:
- complex real/imag simplification;
- `ring`, `linarith`, `nlinarith`;
- `Finset.single_le_sum`;
- nat-to-complex coercion.

## Step 4 — Repair structural API modules

```bash
lake build RHFormalization.GlobalMeromorphicIdentity
lake build RHFormalization.PoleNormalForm
lake build RHFormalization.PoleObstructionFromNormalForm
lake build RHFormalization.DOperatorExport
lake build RHFormalization.DFiniteStageOperator
```

Expected repairs:
- long projection paths;
- typeclass search for set nonempty/open predicates;
- occasional explicit arguments.

## Step 5 — Build endpoint

```bash
lake build RHFormalization.MainTheorem
```

## Step 6 — Axiom audit

Inside Lean:

```lean
#print axioms RHFormalization.mainTheorem_from_nonnegative_interface_layer
```

Then discharge APIs in priority order.
