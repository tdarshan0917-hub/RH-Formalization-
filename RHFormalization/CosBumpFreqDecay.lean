/-
CosBumpFreqDecay.lean

Stone 3b: frequency decay of the cosine-bump integral by one integration by
parts. |C_j(q)| <= (boundary + derivative-mass) * L / (j*pi) for j > 0.
Combined with Stone 5.5's flat bound this gives min(S, K/j) entry decay —
enough for the uniform Frobenius bound on galerkinV (squares of 1/j sum).
-/
import RHFormalization.BumpMatrixElementCosForm
import RHFormalization.CosBumpIntegralBound
import Mathlib

namespace RHFormalization
noncomputable section
open Real intervalIntegral

/-- The Gaussian bump is differentiable, with derivative -(x/δ²)·W(x). -/
theorem hasDerivAt_gaussBump (δ : ℝ) (hδ : 0 < δ) (x : ℝ) :
    HasDerivAt (gaussBump δ) (-(x / δ ^ 2) * gaussBump δ x) x := by
  unfold gaussBump
  have h1 : HasDerivAt (fun y : ℝ => -y ^ 2 / (2 * δ ^ 2))
      (-(2 * x) / (2 * δ ^ 2)) x := by
    have := ((hasDerivAt_pow 2 x).neg).div_const (2 * δ ^ 2)
    simpa using this
  have h2 : HasDerivAt (fun y : ℝ => Real.exp (-y ^ 2 / (2 * δ ^ 2)))
      (Real.exp (-x ^ 2 / (2 * δ ^ 2)) * (-(2 * x) / (2 * δ ^ 2))) x :=
    (Real.hasDerivAt_exp _).comp x h1
  have h3 := h2.div_const (Real.sqrt (2 * Real.pi * δ ^ 2))
  convert h3 using 1
  first
    | (field_simp; ring)
    | field_simp
    | ring

/-- Derivative-mass of the bump over the box. -/
def bumpDerivMass (δ : ℝ) (q : ℕ) (L : ℝ) : ℝ :=
  ∫ x in (0:ℝ)..L, |(x - Real.log q) / δ ^ 2| * gaussBump δ (x - Real.log q)

theorem bumpDerivMass_nonneg (δ : ℝ) (hδ : 0 < δ) (q : ℕ) (L : ℝ) (hL : 0 ≤ L) :
    0 ≤ bumpDerivMass δ q L := by
  unfold bumpDerivMass
  apply intervalIntegral.integral_nonneg hL
  intro x _
  exact mul_nonneg (abs_nonneg _) (le_of_lt (gaussBump_pos δ hδ _))

/-- Integrability of the derivative-mass integrand. -/
theorem intervalIntegrable_derivMass (δ : ℝ) (q : ℕ) (L : ℝ) :
    IntervalIntegrable
      (fun x : ℝ => |(x - Real.log q) / δ ^ 2| * gaussBump δ (x - Real.log q))
      MeasureTheory.volume 0 L := by
  apply Continuous.intervalIntegrable
  unfold gaussBump
  fun_prop

/-- **Stone 3b (one IBP)**: frequency decay of the cosine-bump integral.
For ω := j·π/L > 0,
|∫₀ᴸ cos(ωx)·W(x−log q) dx| ≤ (W(−log q) + W(L−log q) + derivMass)·L/(j·π). -/
theorem abs_cosBumpIntegral_le_inv_freq
    (δ : ℝ) (hδ : 0 < δ) (q : ℕ) (L : ℝ) (hL : 0 < L) (j : ℝ) (hj : 0 < j) :
    |cosBumpIntegral δ q L j|
      ≤ (gaussBump δ (0 - Real.log q) + gaussBump δ (L - Real.log q)
          + bumpDerivMass δ q L) * L / (j * Real.pi) := by
  set ω : ℝ := j * Real.pi / L with hω
  have hωpos : 0 < ω := by
    apply div_pos (mul_pos hj Real.pi_pos) hL
  set W : ℝ → ℝ := fun x => gaussBump δ (x - Real.log q) with hW
  set W' : ℝ → ℝ := fun x => -((x - Real.log q) / δ ^ 2) * gaussBump δ (x - Real.log q)
    with hW'
  have hWd : ∀ x ∈ Set.uIcc (0:ℝ) L, HasDerivAt W (W' x) x := by
    intro x _
    have := (hasDerivAt_gaussBump δ hδ (x - Real.log q)).comp x
      ((hasDerivAt_id x).sub_const (Real.log q))
    simpa [hW, hW'] using this
  set V : ℝ → ℝ := fun x => Real.sin (ω * x) / ω with hV
  have hVd : ∀ x ∈ Set.uIcc (0:ℝ) L, HasDerivAt V (Real.cos (ω * x)) x := by
    intro x _
    have h1 : HasDerivAt (fun y : ℝ => ω * y) ω x := by
      simpa using (hasDerivAt_id x).const_mul ω
    have h2 : HasDerivAt (fun y : ℝ => Real.sin (ω * y))
        (Real.cos (ω * x) * ω) x := (Real.hasDerivAt_sin _).comp x h1
    have h3 := h2.div_const ω
    convert h3 using 1
    first
      | (field_simp; ring)
      | field_simp
      | rfl
  -- IBP: ∫ W·cos(ωx) = [W·V]₀ᴸ − ∫ W'·V
  have hWcont : Continuous W := by
    simp only [hW]; unfold gaussBump; fun_prop
  have hVcont : Continuous V := by
    simp only [hV]; fun_prop
  have hW'int : IntervalIntegrable W' MeasureTheory.volume 0 L := by
    apply Continuous.intervalIntegrable
    simp only [hW']; unfold gaussBump; fun_prop
  have hcosint : IntervalIntegrable (fun x => Real.cos (ω * x))
      MeasureTheory.volume 0 L := by
    apply Continuous.intervalIntegrable
    fun_prop
  have hIBP : (∫ x in (0:ℝ)..L, W x * Real.cos (ω * x))
      = W L * V L - W 0 * V 0 - ∫ x in (0:ℝ)..L, W' x * V x := by
    apply intervalIntegral.integral_mul_deriv_eq_deriv_mul_of_hasDerivAt
      hWcont.continuousOn hVcont.continuousOn
      (fun x _ => hWd x (by
        first
          | exact Set.mem_uIcc_of_mem_Icc (Set.mem_Icc_of_Ioo (by
              simpa [min_eq_left (le_of_lt hL), max_eq_right (le_of_lt hL)]
                using ‹x ∈ Set.Ioo (min (0:ℝ) L) (max (0:ℝ) L)›))
          | exact Set.mem_uIcc.mpr (Or.inl ⟨le_of_lt (by
              have hx := ‹x ∈ Set.Ioo (min (0:ℝ) L) (max (0:ℝ) L)›
              rw [min_eq_left (le_of_lt hL)] at hx
              exact hx.1), le_of_lt (by
              have hx := ‹x ∈ Set.Ioo (min (0:ℝ) L) (max (0:ℝ) L)›
              rw [max_eq_right (le_of_lt hL)] at hx
              exact hx.2)⟩)))
      (fun x _ => hVd x (by
        first
          | exact Set.mem_uIcc.mpr (Or.inl ⟨le_of_lt (by
              have hx := ‹x ∈ Set.Ioo (min (0:ℝ) L) (max (0:ℝ) L)›
              rw [min_eq_left (le_of_lt hL)] at hx
              exact hx.1), le_of_lt (by
              have hx := ‹x ∈ Set.Ioo (min (0:ℝ) L) (max (0:ℝ) L)›
              rw [max_eq_right (le_of_lt hL)] at hx
              exact hx.2)⟩)
          | skip))
      hW'int hcosint
  have hCos : cosBumpIntegral δ q L j = ∫ x in (0:ℝ)..L, W x * Real.cos (ω * x) := by
    unfold cosBumpIntegral
    apply intervalIntegral.integral_congr
    intro x _
    simp only [hW, hω]
    ring_nf
  rw [hCos, hIBP]
  have hVb : ∀ x : ℝ, |V x| ≤ 1 / ω := by
    intro x
    simp only [hV, abs_div, abs_of_pos hωpos]
    gcongr
    exact abs_sin_le_one _
  have hWpos : ∀ x : ℝ, 0 < W x := fun x => gaussBump_pos δ hδ _
  have hb1 : |W L * V L| ≤ W L / ω := by
    rw [abs_mul, abs_of_pos (hWpos L)]
    calc W L * |V L| ≤ W L * (1 / ω) :=
          mul_le_mul_of_nonneg_left (hVb L) (le_of_lt (hWpos L))
      _ = W L / ω := by ring
  have hb0 : |W 0 * V 0| ≤ W 0 / ω := by
    rw [abs_mul, abs_of_pos (hWpos 0)]
    calc W 0 * |V 0| ≤ W 0 * (1 / ω) :=
          mul_le_mul_of_nonneg_left (hVb 0) (le_of_lt (hWpos 0))
      _ = W 0 / ω := by ring
  have hbI : |∫ x in (0:ℝ)..L, W' x * V x| ≤ bumpDerivMass δ q L / ω := by
    have hptw : ∀ x ∈ Set.uIcc (0:ℝ) L, |W' x * V x|
        ≤ |(x - Real.log q) / δ ^ 2| * gaussBump δ (x - Real.log q) * (1/ω) := by
      intro x _
      rw [abs_mul]
      have h1 : |W' x| = |(x - Real.log q) / δ ^ 2| * gaussBump δ (x - Real.log q) := by
        simp only [hW']
        rw [abs_mul, abs_neg, abs_of_pos (gaussBump_pos δ hδ _)]
      rw [h1]
      exact mul_le_mul_of_nonneg_left (hVb x)
        (mul_nonneg (abs_nonneg _) (le_of_lt (gaussBump_pos δ hδ _)))
    have hWVint : IntervalIntegrable (fun x => W' x * V x)
        MeasureTheory.volume 0 L := by
      apply Continuous.intervalIntegrable
      simp only [hW', hV]
      unfold gaussBump
      fun_prop
    calc |∫ x in (0:ℝ)..L, W' x * V x|
        ≤ ∫ x in (0:ℝ)..L, |W' x * V x| := by
          have := intervalIntegral.norm_integral_le_integral_norm
            (f := fun x => W' x * V x) (μ := MeasureTheory.volume) (le_of_lt hL)
          simpa using this
      _ ≤ ∫ x in (0:ℝ)..L, |(x - Real.log q) / δ ^ 2|
            * gaussBump δ (x - Real.log q) * (1/ω) := by
          apply intervalIntegral.integral_mono_on (le_of_lt hL)
          · exact hWVint.abs
          · exact ((intervalIntegrable_derivMass δ q L).mul_const _)
          · intro x hx
            apply hptw x
            rw [Set.uIcc_of_le (le_of_lt hL)]
            exact hx
      _ = (∫ x in (0:ℝ)..L, |(x - Real.log q) / δ ^ 2|
            * gaussBump δ (x - Real.log q)) * (1/ω) := by
          rw [intervalIntegral.integral_mul_const]
      _ = bumpDerivMass δ q L * (1/ω) := by rfl
      _ = bumpDerivMass δ q L / ω := by ring
  have hsum : |W L * V L - W 0 * V 0 - ∫ x in (0:ℝ)..L, W' x * V x|
      ≤ W 0 / ω + W L / ω + bumpDerivMass δ q L / ω := by
    calc |W L * V L - W 0 * V 0 - ∫ x in (0:ℝ)..L, W' x * V x|
        ≤ |W L * V L - W 0 * V 0| + |∫ x in (0:ℝ)..L, W' x * V x| := abs_sub _ _
      _ ≤ (|W L * V L| + |W 0 * V 0|) + |∫ x in (0:ℝ)..L, W' x * V x| := by
          have := abs_sub (W L * V L) (W 0 * V 0)
          first
            | linarith [abs_sub_abs_le_abs_sub (W L * V L) (W 0 * V 0),
                abs_sub_le (W L * V L) 0 (W 0 * V 0)]
            | nlinarith [abs_add (W L * V L) (-(W 0 * V 0)),
                abs_neg (W 0 * V 0)]
      _ ≤ W 0 / ω + W L / ω + bumpDerivMass δ q L / ω := by
          linarith [hb1, hb0, hbI]
  calc |W L * V L - W 0 * V 0 - ∫ x in (0:ℝ)..L, W' x * V x|
      ≤ W 0 / ω + W L / ω + bumpDerivMass δ q L / ω := hsum
    _ = (gaussBump δ (0 - Real.log q) + gaussBump δ (L - Real.log q)
          + bumpDerivMass δ q L) / ω := by
        simp only [hW]
        ring
    _ = (gaussBump δ (0 - Real.log q) + gaussBump δ (L - Real.log q)
          + bumpDerivMass δ q L) * L / (j * Real.pi) := by
        rw [hω]
        field_simp

#print axioms hasDerivAt_gaussBump
#print axioms abs_cosBumpIntegral_le_inv_freq

end
end RHFormalization
