import RHFormalization.DCanonicalWindowSharpCutoffNormedSpeedBridge
import RHFormalization.CanonicalPrimePowerDWindowSpeedAPI

/-!
# RHFormalization.DCanonicalWindowSharpCutoffCompactSpeed

Complex-valued compact-speed instantiation of D.CANONICAL-WINDOW.

The actual `DCanonicalWindowData` API has complex-valued window functions:

  W.gbar_stage (alpha n) : ℝ → ℂ
  W.G_limit              : ℝ → ℂ

so the sharp-cutoff formula must be expressed using real scalar multiplication:

  W.gbar_stage (alpha n) a =
    ((2L_n - |a|)/(2L_n)) • W.G_limit a.

This file builds the actual `DCanonicalWindowCompactSpeedAPI` from the
sharp-cutoff compact-speed data.
-/

namespace RHFormalization

noncomputable section

open Complex Topology Filter
open scoped BigOperators

/--
Concrete data needed to turn the sharp-cutoff formula into the compact
D.CANONICAL-WINDOW speed API.
-/
structure DCanonicalWindowSharpCutoffCompactSpeedData
    (W : DCanonicalWindowData)
    (alpha : ℕ → DFiniteStage) where

  /-- Sharp cutoff length attached to stage `n`. -/
  L : ℕ → ℝ

  /-- Positivity of the sharp cutoff length. -/
  hL_pos : ∀ n : ℕ, 0 < L n

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

  /-- `W.G_limit` is bounded in norm by `Gbound A` on the compact radius. -/
  h_G_bound :
    ∀ A : Set ℝ,
      IsCompact A →
      ∀ x : ℝ,
        |x| ≤ compactRadius A →
          ‖W.G_limit x‖ ≤ Gbound A

  /--
  Sharp-cutoff formula for the normalized canonical window.

  This is the complex-valued formal version of:

    gbar_{t,L}(a) =
      ((2L - |a|)/(2L)) · G_t(a).
  -/
  h_sharp_formula :
    ∀ A : Set ℝ,
      IsCompact A →
      ∀ n : ℕ,
      ∀ a : ℝ,
        a ∈ A →
          W.gbar_stage (alpha n) a =
            (((2 * L n - |a|) / (2 * L n)) : ℝ) •
              W.G_limit a

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
        Gbound A * (compactRadius A / (2 * L n))
          ≤ (1 : ℝ) / speed A n

/--
Build the actual compact-speed API from sharp-cutoff compact-speed data.

This is the repaired field-killer for
`DCanonicalWindowCompactSpeedAPI.h_compact_window_speed_rate`.
-/
def DCanonicalWindowSharpCutoffCompactSpeedData.toCompactSpeedAPI
    {W : DCanonicalWindowData}
    {alpha : ℕ → DFiniteStage}
    (S : DCanonicalWindowSharpCutoffCompactSpeedData W alpha) :
    DCanonicalWindowCompactSpeedAPI W alpha :=
  { speed := S.speed

    h_speed_pos := S.h_speed_pos

    h_compact_window_speed_rate := by
      intro A hA n a ha
      exact
        sharpCutoff_dist_le_invSpeed_of_smul_formula
          (fun n : ℕ => W.gbar_stage (alpha n))
          W.G_limit
          S.L
          (S.speed A)
          (S.Gbound A)
          (S.compactRadius A)
          n
          a
          (S.hL_pos n)
          (S.h_compactRadius_nonneg A hA)
          (S.h_Gbound_nonneg A hA)
          (S.h_mem_le_radius A hA a ha)
          (S.h_G_bound A hA)
          (S.h_sharp_formula A hA n a ha)
          (S.h_budget A hA n) }

end

end RHFormalization
