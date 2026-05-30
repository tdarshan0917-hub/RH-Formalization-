import RHFormalization.DCanonicalWindowSharpCutoffConcrete

/-!
# RHFormalization.DCanonicalWindowSharpCutoffConcreteCompactSpeed

Concrete compact-speed API for the sharp-cutoff D-window.

This is the direct use of the concrete sharp-cutoff window data:

  gbar_stage stage a =
    ((2L_stage - |a|)/(2L_stage)) • G_limit a

to remove the `h_sharp_formula` field from the compact-speed construction.

This is not another endpoint and not another broad wrapper. It builds the actual
`DCanonicalWindowCompactSpeedAPI` for the concrete sharp-cutoff window model.
-/

namespace RHFormalization

noncomputable section

open Complex Topology Filter
open scoped BigOperators

/--
Compact-speed data for the concrete sharp-cutoff D-window.

Compared with `DCanonicalWindowSharpCutoffCompactSpeedData`, this structure does
not ask for `h_sharp_formula`: the formula is definitional from
`sharpCutoffDCanonicalWindowData`.
-/
structure DCanonicalWindowSharpCutoffConcreteCompactSpeedData
    (G : ℝ → ℂ)
    (Lstage : DFiniteStage → ℝ)
    (alpha : ℕ → DFiniteStage) where

  /-- Positivity of the cutoff length along the selected stages. -/
  hL_pos :
    ∀ n : ℕ, 0 < Lstage (alpha n)

  /-- Radius assigned to each compact coordinate set. -/
  compactRadius : Set ℝ → ℝ

  /-- The radius is nonnegative. -/
  h_compactRadius_nonneg :
    ∀ A : Set ℝ, IsCompact A → 0 ≤ compactRadius A

  /-- Every point of the compact set lies inside the chosen radius. -/
  h_mem_le_radius :
    ∀ A : Set ℝ,
      IsCompact A →
      ∀ a : ℝ,
        a ∈ A →
          |a| ≤ compactRadius A

  /-- Uniform norm bound for the limiting complex heat/window kernel. -/
  Gbound : Set ℝ → ℝ

  /-- Nonnegativity of the compact kernel bound. -/
  h_Gbound_nonneg :
    ∀ A : Set ℝ, IsCompact A → 0 ≤ Gbound A

  /-- The concrete limiting kernel is bounded on the compact radius. -/
  h_G_bound :
    ∀ A : Set ℝ,
      IsCompact A →
      ∀ x : ℝ,
        |x| ≤ compactRadius A →
          ‖G x‖ ≤ Gbound A

  /-- Compact speed function. -/
  speed : Set ℝ → ℕ → ℝ

  /-- Positivity of the compact speed. -/
  h_speed_pos :
    ∀ A : Set ℝ,
      IsCompact A →
      ∀ n : ℕ,
        0 < speed A n

  /--
  Budget inequality connecting the sharp-cutoff scalar error to the inverse speed.
  -/
  h_budget :
    ∀ A : Set ℝ,
      IsCompact A →
      ∀ n : ℕ,
        Gbound A * (compactRadius A / (2 * Lstage (alpha n)))
          ≤ (1 : ℝ) / speed A n

/--
Convert concrete sharp-cutoff compact-speed data into the previous compact-speed
data. The field `h_sharp_formula` is filled by the definitional concrete formula.
-/
def DCanonicalWindowSharpCutoffConcreteCompactSpeedData.toCompactSpeedData
    {G : ℝ → ℂ}
    {Lstage : DFiniteStage → ℝ}
    {alpha : ℕ → DFiniteStage}
    (S : DCanonicalWindowSharpCutoffConcreteCompactSpeedData G Lstage alpha) :
    DCanonicalWindowSharpCutoffCompactSpeedData
      (sharpCutoffDCanonicalWindowData G Lstage)
      alpha :=
  { L := fun n : ℕ => Lstage (alpha n)

    hL_pos := S.hL_pos

    compactRadius := S.compactRadius
    h_compactRadius_nonneg := S.h_compactRadius_nonneg
    h_mem_le_radius := S.h_mem_le_radius

    Gbound := S.Gbound
    h_Gbound_nonneg := S.h_Gbound_nonneg

    h_G_bound := by
      intro A hA x hx
      simpa [sharpCutoffDCanonicalWindowData] using
        S.h_G_bound A hA x hx

    h_sharp_formula := by
      intro A hA n a ha
      exact
        sharpCutoffDCanonicalWindowData_formula_expanded
          G
          Lstage
          alpha
          n
          a

    speed := S.speed
    h_speed_pos := S.h_speed_pos

    h_budget := by
      intro A hA n
      exact S.h_budget A hA n }

/--
Build the actual compact-speed API for the concrete sharp-cutoff window.
-/
def DCanonicalWindowSharpCutoffConcreteCompactSpeedData.toCompactSpeedAPI
    {G : ℝ → ℂ}
    {Lstage : DFiniteStage → ℝ}
    {alpha : ℕ → DFiniteStage}
    (S : DCanonicalWindowSharpCutoffConcreteCompactSpeedData G Lstage alpha) :
    DCanonicalWindowCompactSpeedAPI
      (sharpCutoffDCanonicalWindowData G Lstage)
      alpha :=
  DCanonicalWindowSharpCutoffCompactSpeedData.toCompactSpeedAPI
    S.toCompactSpeedData

/--
The compact inverse-speed estimate for the concrete sharp-cutoff window.
-/
theorem sharpCutoffConcrete_compact_window_speed_rate
    {G : ℝ → ℂ}
    {Lstage : DFiniteStage → ℝ}
    {alpha : ℕ → DFiniteStage}
    (S : DCanonicalWindowSharpCutoffConcreteCompactSpeedData G Lstage alpha) :
    ∀ A : Set ℝ,
      IsCompact A →
      ∀ n : ℕ,
      ∀ a : ℝ,
        a ∈ A →
          dist
            ((sharpCutoffDCanonicalWindowData G Lstage).gbar_stage (alpha n) a)
            ((sharpCutoffDCanonicalWindowData G Lstage).G_limit a)
            ≤ (1 : ℝ) / S.speed A n :=
  S.toCompactSpeedAPI.h_compact_window_speed_rate

end

end RHFormalization
