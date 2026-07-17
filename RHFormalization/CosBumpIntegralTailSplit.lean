import RHFormalization.CosBumpIntegralFull
import RHFormalization.CosBumpRecenter
import Mathlib

set_option autoImplicit false

namespace RHFormalization

open Real MeasureTheory
open scoped Real BigOperators

/-!
# O3 brick 7 — finite interval = full line minus tails.

The operator's finite `cosBumpIntegral` equals the full-line `cosBumpIntegralFull`
minus the two explicit Gaussian tails. After recentering (brick 1) the integrand is
  F u := cos(j π (u + log q)/L) · gaussBump δ u,
and  ∫ x in 0..L, (orig) = ∫ u in (0-log q)..(L-log q), F u  (brick 1),
so  cosBumpIntegral = cosBumpIntegralFull − (leftTail + rightTail),
with leftTail = ∫_{Iic (0-log q)} F, rightTail = ∫_{Ioi (L-log q)} F.
Brick 8 bounds the tails by Gaussian decay.
-/

/-- The recentered full-line integrand. -/
noncomputable def cosBumpFullIntegrand (δ : ℝ) (q : ℕ) (L : ℝ) (j : ℝ) : ℝ → ℝ :=
  fun u => Real.cos (j * Real.pi * (u + Real.log q) / L) * gaussBump δ u

/-- Integrability of the recentered full-line integrand. -/
theorem integrable_cosBumpFullIntegrand (δ : ℝ) (hδ : 0 < δ) (q : ℕ) (L : ℝ) (j : ℝ) :
    Integrable (cosBumpFullIntegrand δ q L j) := by
  unfold cosBumpFullIntegrand
  set A : ℝ := j * Real.pi / L with hA
  set B : ℝ := j * Real.pi * Real.log q / L with hB
  -- phase-split pointwise into cos·g and sin·g pieces (both integrable via brick 6 helper)
  have hpt : (fun u : ℝ => Real.cos (j * Real.pi * (u + Real.log q) / L) * gaussBump δ u)
      = (fun u : ℝ => Real.cos B * (Real.cos (A * u) * gaussBump δ u)
          - Real.sin B * (Real.sin (A * u) * gaussBump δ u)) := by
    funext u
    have harg : j * Real.pi * (u + Real.log q) / L = A * u + B := by rw [hA, hB]; ring
    rw [harg, Real.cos_add]; ring
  rw [hpt]
  have hcC : Integrable (fun u : ℝ => Real.cos (A * u) * gaussBump δ u) :=
    integrable_trig_mul_gaussBump δ hδ A Real.cos (fun x => Real.abs_cos_le_one x) Real.continuous_cos.measurable
  have hcS : Integrable (fun u : ℝ => Real.sin (A * u) * gaussBump δ u) :=
    integrable_trig_mul_gaussBump δ hδ A Real.sin (fun x => Real.abs_sin_le_one x) Real.continuous_sin.measurable
  exact (hcC.const_mul _).sub (hcS.const_mul _)

/-- Left Gaussian tail: integral of the recentered integrand over `Iic (0 - log q)`. -/
noncomputable def cosBumpLeftTail (δ : ℝ) (q : ℕ) (L : ℝ) (j : ℝ) : ℝ :=
  ∫ u in Set.Iic (0 - Real.log q), cosBumpFullIntegrand δ q L j u

/-- Right Gaussian tail: integral of the recentered integrand over `Ioi (L - log q)`. -/
noncomputable def cosBumpRightTail (δ : ℝ) (q : ℕ) (L : ℝ) (j : ℝ) : ℝ :=
  ∫ u in Set.Ioi (L - Real.log q), cosBumpFullIntegrand δ q L j u

/-- **Brick 7**: the finite interval integral equals the full line minus the two tails. -/
theorem cosBumpIntegral_eq_full_sub_tails
    (δ : ℝ) (hδ : 0 < δ) (q : ℕ) (L : ℝ) (hL : 0 ≤ L) (j : ℝ) :
    cosBumpIntegral δ q L j
      = cosBumpIntegralFull δ q L j
          - (cosBumpLeftTail δ q L j + cosBumpRightTail δ q L j) := by
  have hInt := integrable_cosBumpFullIntegrand δ hδ q L j
  set F : ℝ → ℝ := cosBumpFullIntegrand δ q L j with hFdef
  set a : ℝ := 0 - Real.log q with ha
  set b : ℝ := L - Real.log q with hb
  have hab : a ≤ b := by rw [ha, hb]; linarith
  -- recenter: cosBumpIntegral = ∫ u in a..b, F u
  have hrec : cosBumpIntegral δ q L j = ∫ u in a..b, F u := by
    rw [cosBumpIntegral_recenter, ha, hb, hFdef]
    rfl
  -- ∫ a..b F = ∫ Ioc a b F  (a ≤ b)
  have hInterval : (∫ u in a..b, F u) = ∫ u in Set.Ioc a b, F u :=
    intervalIntegral.integral_of_le hab
  -- Split ℝ at a: ∫_univ = ∫_Iic a + ∫_Ioi a
  have hSplit1 : (∫ u in Set.Iic a, F u) + (∫ u in Set.Ioi a, F u) = ∫ u : ℝ, F u := by
    have h := integral_add_compl (s := Set.Iic a) measurableSet_Iic hInt
    rwa [Set.compl_Iic] at h
  -- Split Ioi a at b: ∫_Ioi a = ∫_Ioc a b + ∫_Ioi b
  have hSplit2 : (∫ u in Set.Ioc a b, F u) + (∫ u in Set.Ioi b, F u) = ∫ u in Set.Ioi a, F u := by
    rw [← setIntegral_union Set.Ioc_disjoint_Ioi_same measurableSet_Ioi
        hInt.integrableOn hInt.integrableOn, Set.Ioc_union_Ioi_eq_Ioi hab]
  -- assemble: cosBumpIntegralFull = ∫_univ F ; cosBumpIntegral = ∫_Ioc a b F
  have hFull : cosBumpIntegralFull δ q L j = ∫ u : ℝ, F u := by
    rw [cosBumpIntegralFull, hFdef]; rfl
  rw [hrec, hInterval, hFull]
  rw [cosBumpLeftTail, cosBumpRightTail, ← hFdef, ← ha, ← hb]
  -- ∫_Ioc a b = ∫_univ − ∫_Iic a − ∫_Ioi b
  rw [← hSplit1, ← hSplit2]
  ring

#print axioms cosBumpIntegral_eq_full_sub_tails

end RHFormalization
