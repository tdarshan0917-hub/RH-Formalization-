import RHFormalization.DCanonicalWindowSharpCutoffCompactSpeed

/-!
# RHFormalization.DCanonicalWindowSharpCutoffConcrete

Concrete sharp-cutoff D-window data.

This file is the direct response to the remaining sharp-cutoff field

  h_sharp_formula

in `DCanonicalWindowSharpCutoffCompactSpeedData`.

It defines a concrete `DCanonicalWindowData` whose normalized finite-stage window
is definitionally

  ((2L - |a|) / (2L)) • G_limit a.

Thus the sharp-cutoff formula is no longer a supplied field for this concrete
window model; it is `rfl`.
-/

namespace RHFormalization

noncomputable section

open Complex Topology Filter
open scoped BigOperators

/--
The linear sharp-cutoff overlap factor used on the compact range `|a| ≤ L`.

This is the factor appearing in the simplified D.CANONICAL-WINDOW formula:

  gbar_{t,L}(a) = ((2L - |a|)/(2L)) • G_t(a).

The positive-part version is the globally correct formula, but the current
compact-speed API field asks for this simplified formula on the active compact
range.
-/
def sharpCutoffLinearOverlapFactor (L a : ℝ) : ℝ :=
  (2 * L - |a|) / (2 * L)

/--
Concrete sharp-cutoff D-window data.

`Lstage stage` is the cutoff length attached to a finite stage.
`G` is the limiting heat/window kernel.
-/
def sharpCutoffDCanonicalWindowData
    (G : ℝ → ℂ)
    (Lstage : DFiniteStage → ℝ) :
    DCanonicalWindowData :=
  { c_w := 1
    G_limit := G
    gbar_stage := fun stage a =>
      (sharpCutoffLinearOverlapFactor (Lstage stage) a : ℝ) • G a }

/--
The sharp-cutoff formula for the concrete sharp-cutoff D-window data.

This is the field `h_sharp_formula` in concrete form.
-/
theorem sharpCutoffDCanonicalWindowData_formula
    (G : ℝ → ℂ)
    (Lstage : DFiniteStage → ℝ)
    (alpha : ℕ → DFiniteStage)
    (n : ℕ)
    (a : ℝ) :
    (sharpCutoffDCanonicalWindowData G Lstage).gbar_stage (alpha n) a =
      (sharpCutoffLinearOverlapFactor (Lstage (alpha n)) a : ℝ) •
        (sharpCutoffDCanonicalWindowData G Lstage).G_limit a := by
  rfl

/--
Same formula expanded into the exact algebraic shape used by the compact-speed
sharp-cutoff data, with `L n = Lstage (alpha n)`.
-/
theorem sharpCutoffDCanonicalWindowData_formula_expanded
    (G : ℝ → ℂ)
    (Lstage : DFiniteStage → ℝ)
    (alpha : ℕ → DFiniteStage)
    (n : ℕ)
    (a : ℝ) :
    (sharpCutoffDCanonicalWindowData G Lstage).gbar_stage (alpha n) a =
      (((2 * Lstage (alpha n) - |a|) / (2 * Lstage (alpha n))) : ℝ) •
        (sharpCutoffDCanonicalWindowData G Lstage).G_limit a := by
  rfl

end

end RHFormalization
