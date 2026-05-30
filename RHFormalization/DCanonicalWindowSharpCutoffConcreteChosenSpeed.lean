import RHFormalization.DCanonicalWindowSharpCutoffConcreteCompactSpeed

/-!
# RHFormalization.DCanonicalWindowSharpCutoffConcreteChosenSpeed

Concrete chosen-speed version of the sharp-cutoff compact D-window theorem.

This removes the arbitrary `speed`, `h_speed_pos`, and `h_budget` fields from
`DCanonicalWindowSharpCutoffConcreteCompactSpeedData` by choosing

  speed A n := (2 * Lstage (alpha n)) /
                 (Gbound A * compactRadius A + 1).

This is a real reduction of the compact-speed debt.
-/

namespace RHFormalization

noncomputable section

open Complex Topology Filter
open scoped BigOperators

theorem sharpCutoff_concreteChosenSpeed_pos
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

theorem sharpCutoff_concreteChosenSpeed_budget
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
Concrete sharp-cutoff compact-speed data with the speed chosen explicitly.

Compared with `DCanonicalWindowSharpCutoffConcreteCompactSpeedData`, this
structure no longer asks for:

* `speed`;
* `h_speed_pos`;
* `h_budget`.

Those are discharged by arithmetic.
-/
structure DCanonicalWindowSharpCutoffConcreteChosenSpeedData
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

/--
Convert chosen-speed data into the previous concrete compact-speed data.
-/
def DCanonicalWindowSharpCutoffConcreteChosenSpeedData.toConcreteCompactSpeedData
    {G : ℝ → ℂ}
    {Lstage : DFiniteStage → ℝ}
    {alpha : ℕ → DFiniteStage}
    (S : DCanonicalWindowSharpCutoffConcreteChosenSpeedData G Lstage alpha) :
    DCanonicalWindowSharpCutoffConcreteCompactSpeedData G Lstage alpha :=
  { hL_pos := S.hL_pos

    compactRadius := S.compactRadius
    h_compactRadius_nonneg := S.h_compactRadius_nonneg
    h_mem_le_radius := S.h_mem_le_radius

    Gbound := S.Gbound
    h_Gbound_nonneg := S.h_Gbound_nonneg
    h_G_bound := S.h_G_bound

    speed := fun A n =>
      (2 * Lstage (alpha n)) /
        (S.Gbound A * S.compactRadius A + 1)

    h_speed_pos := by
      intro A hA n
      exact
        sharpCutoff_concreteChosenSpeed_pos
          (Lstage (alpha n))
          (S.Gbound A)
          (S.compactRadius A)
          (S.hL_pos n)
          (S.h_Gbound_nonneg A hA)
          (S.h_compactRadius_nonneg A hA)

    h_budget := by
      intro A hA n
      exact
        sharpCutoff_concreteChosenSpeed_budget
          (Lstage (alpha n))
          (S.Gbound A)
          (S.compactRadius A)
          (S.hL_pos n)
          (S.h_Gbound_nonneg A hA)
          (S.h_compactRadius_nonneg A hA) }

/--
Build the actual compact-speed API for the concrete sharp-cutoff window with
the chosen speed.
-/
def DCanonicalWindowSharpCutoffConcreteChosenSpeedData.toCompactSpeedAPI
    {G : ℝ → ℂ}
    {Lstage : DFiniteStage → ℝ}
    {alpha : ℕ → DFiniteStage}
    (S : DCanonicalWindowSharpCutoffConcreteChosenSpeedData G Lstage alpha) :
    DCanonicalWindowCompactSpeedAPI
      (sharpCutoffDCanonicalWindowData G Lstage)
      alpha :=
  DCanonicalWindowSharpCutoffConcreteCompactSpeedData.toCompactSpeedAPI
    S.toConcreteCompactSpeedData

/--
Concrete compact inverse-speed estimate with the speed chosen explicitly.
-/
theorem sharpCutoffConcreteChosen_compact_window_speed_rate
    {G : ℝ → ℂ}
    {Lstage : DFiniteStage → ℝ}
    {alpha : ℕ → DFiniteStage}
    (S : DCanonicalWindowSharpCutoffConcreteChosenSpeedData G Lstage alpha) :
    ∀ A : Set ℝ,
      IsCompact A →
      ∀ n : ℕ,
      ∀ a : ℝ,
        a ∈ A →
          dist
            ((sharpCutoffDCanonicalWindowData G Lstage).gbar_stage (alpha n) a)
            ((sharpCutoffDCanonicalWindowData G Lstage).G_limit a)
            ≤
          (1 : ℝ) /
            ((2 * Lstage (alpha n)) /
              (S.Gbound A * S.compactRadius A + 1)) :=
  S.toCompactSpeedAPI.h_compact_window_speed_rate

end

end RHFormalization
