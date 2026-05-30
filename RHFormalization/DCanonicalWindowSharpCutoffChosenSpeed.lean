import RHFormalization.DCanonicalWindowSharpCutoffCompactSpeed

/-!
# RHFormalization.DCanonicalWindowSharpCutoffChosenSpeed

Chosen-speed version of the sharp-cutoff compact D-window theorem.

The previous compact-speed file still carried:

* `speed`;
* `h_speed_pos`;
* `h_budget`.

This file removes those fields by choosing

  speed A n := (2 * L n) / (Gbound A * compactRadius A + 1).

Then

  Gbound A * (compactRadius A / (2 * L n)) ≤ 1 / speed A n

is a real arithmetic theorem.
-/

namespace RHFormalization

noncomputable section

open Complex Topology Filter
open scoped BigOperators

/--
The chosen compact speed is positive.
-/
theorem sharpCutoff_chosenSpeed_pos
    (L G R : ℝ)
    (hL : 0 < L)
    (hG : 0 ≤ G)
    (hR : 0 ≤ R) :
    0 < (2 * L) / (G * R + 1) := by
  have hnum : 0 < 2 * L := by
    nlinarith
  have hGR : 0 ≤ G * R :=
    mul_nonneg hG hR
  have hden : 0 < G * R + 1 := by
    nlinarith
  exact div_pos hnum hden

/--
The chosen compact speed satisfies the sharp-cutoff inverse-speed budget.
-/
theorem sharpCutoff_chosenSpeed_budget
    (L G R : ℝ)
    (hL : 0 < L)
    (hG : 0 ≤ G)
    (hR : 0 ≤ R) :
    G * (R / (2 * L)) ≤
      (1 : ℝ) / ((2 * L) / (G * R + 1)) := by
  have hnum : 0 < 2 * L := by
    nlinarith
  have hnum_ne : 2 * L ≠ 0 :=
    ne_of_gt hnum
  have hGR : 0 ≤ G * R :=
    mul_nonneg hG hR
  have hden : 0 < G * R + 1 := by
    nlinarith
  have hden_ne : G * R + 1 ≠ 0 :=
    ne_of_gt hden

  have h_inv :
      (1 : ℝ) / ((2 * L) / (G * R + 1)) =
        (G * R + 1) / (2 * L) := by
    field_simp [hnum_ne, hden_ne]

  have h_left :
      G * (R / (2 * L)) = (G * R) / (2 * L) := by
    field_simp [hnum_ne]

  rw [h_inv, h_left]
  exact
    div_le_div_of_nonneg_right
      (by nlinarith)
      (le_of_lt hnum)

/--
Sharp-cutoff compact-speed data with the speed chosen explicitly.

Compared with `DCanonicalWindowSharpCutoffCompactSpeedData`, this removes the
arbitrary `speed`, `h_speed_pos`, and `h_budget` fields.
-/
structure DCanonicalWindowSharpCutoffChosenSpeedData
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

  This is the main remaining D.CANONICAL-WINDOW identity:

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

/--
Convert chosen-speed sharp-cutoff data into the previous compact-speed data.
This discharges `speed`, `h_speed_pos`, and `h_budget` by arithmetic.
-/
def DCanonicalWindowSharpCutoffChosenSpeedData.toCompactSpeedData
    {W : DCanonicalWindowData}
    {alpha : ℕ → DFiniteStage}
    (S : DCanonicalWindowSharpCutoffChosenSpeedData W alpha) :
    DCanonicalWindowSharpCutoffCompactSpeedData W alpha :=
  { L := S.L
    hL_pos := S.hL_pos

    compactRadius := S.compactRadius
    h_compactRadius_nonneg := S.h_compactRadius_nonneg
    h_mem_le_radius := S.h_mem_le_radius

    Gbound := S.Gbound
    h_Gbound_nonneg := S.h_Gbound_nonneg
    h_G_bound := S.h_G_bound

    h_sharp_formula := S.h_sharp_formula

    speed := fun A n =>
      (2 * S.L n) / (S.Gbound A * S.compactRadius A + 1)

    h_speed_pos := by
      intro A hA n
      exact
        sharpCutoff_chosenSpeed_pos
          (S.L n)
          (S.Gbound A)
          (S.compactRadius A)
          (S.hL_pos n)
          (S.h_Gbound_nonneg A hA)
          (S.h_compactRadius_nonneg A hA)

    h_budget := by
      intro A hA n
      exact
        sharpCutoff_chosenSpeed_budget
          (S.L n)
          (S.Gbound A)
          (S.compactRadius A)
          (S.hL_pos n)
          (S.h_Gbound_nonneg A hA)
          (S.h_compactRadius_nonneg A hA) }

/--
Build the actual compact-speed API with the chosen speed.
-/
def DCanonicalWindowSharpCutoffChosenSpeedData.toCompactSpeedAPI
    {W : DCanonicalWindowData}
    {alpha : ℕ → DFiniteStage}
    (S : DCanonicalWindowSharpCutoffChosenSpeedData W alpha) :
    DCanonicalWindowCompactSpeedAPI W alpha :=
  DCanonicalWindowSharpCutoffCompactSpeedData.toCompactSpeedAPI
    S.toCompactSpeedData

end

end RHFormalization
