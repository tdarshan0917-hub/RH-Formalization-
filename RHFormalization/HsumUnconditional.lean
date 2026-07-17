import RHFormalization.AbelSummableFromCumulative
import RHFormalization.XiCountBound
import RHFormalization.HsumFromBandCount
import RHFormalization.EnvelopeFromZeroDensity
import Mathlib

/-!
# PILLAR (b): unconditional zero-density summability + envelope

`cumulativeBand_loglinear` (Jensen, banked) + the Abel brick ⟹
`Summable (bandTotal k / (1+k²))` ⟹ (via `hsum_from_bandCount_summable`)
`hsum` ⟹ `ZeroPoleEnvelopeData`, with NO hypotheses.
Key elementary bound: `log x ≤ 2√x`.
-/

namespace RHFormalization
open Finset Real

/-- `log x ≤ 2√x` for `x > 0` (via `log x = 2 log √x ≤ 2(√x − 1)`). -/
theorem log_le_two_sqrt {x : ℝ} (hx : 0 < x) :
    Real.log x ≤ 2 * Real.sqrt x := by
  have hs : 0 < Real.sqrt x := Real.sqrt_pos.mpr hx
  have h1 : Real.log x = 2 * Real.log (Real.sqrt x) := by
    rw [Real.log_sqrt hx.le]; ring
  have h2 : Real.log (Real.sqrt x) ≤ Real.sqrt x - 1 :=
    Real.log_le_sub_one_of_pos hs
  nlinarith [Real.sqrt_nonneg x]

/-- The envelope-vs-weight majorant is summable: `Σ 1/((k+1)√(k+1)) < ∞`. -/
theorem summable_inv_add_one_sqrt :
    Summable (fun k : ℕ => 1 / (((k:ℝ)+1) * Real.sqrt ((k:ℝ)+1))) := by
  have hbase : Summable (fun n : ℕ => 1 / (n:ℝ) ^ ((3:ℝ)/2)) :=
    Real.summable_one_div_nat_rpow.mpr (by norm_num)
  have hshift : Summable (fun k : ℕ => 1 / ((k+1 : ℕ):ℝ) ^ ((3:ℝ)/2)) :=
    (summable_nat_add_iff 1).mpr hbase
  refine hshift.congr fun k => ?_
  have hpos : (0:ℝ) < (k:ℝ) + 1 := by positivity
  have hcast : ((k+1 : ℕ):ℝ) = (k:ℝ) + 1 := by push_cast; ring
  rw [hcast, show (3:ℝ)/2 = 1 + 1/2 by norm_num,
      Real.rpow_add hpos, Real.rpow_one, ← Real.sqrt_eq_rpow]

/-- **Pillar-(b) keystone.** The band totals against `1/(1+k²)` are summable —
Riemann–von Mangoldt-rate cumulative bound + Abel summation. Unconditional. -/
theorem summable_bandTotal_weighted :
    Summable (fun k => bandTotal k / (1 + (k : ℝ) ^ 2)) := by
  obtain ⟨C, D, hC0, hcum⟩ := cumulativeBand_loglinear
  set K : ℝ := 135 * C + max D 0 with hKdef
  have hK0 : 0 ≤ K := by positivity
  set F : ℕ → ℝ := fun n => K * (((n:ℝ)+1) * Real.sqrt ((n:ℝ)+1)) with hFdef
  set w : ℕ → ℝ := fun k => 1 / (1 + (k:ℝ)^2) with hwdef
  have hs_pos : ∀ n : ℕ, (0:ℝ) < Real.sqrt ((n:ℝ)+1) :=
    fun n => Real.sqrt_pos.mpr (by positivity)
  have hs_one : ∀ n : ℕ, (1:ℝ) ≤ Real.sqrt ((n:ℝ)+1) := by
    intro n
    have h0 : (0:ℝ) ≤ (n:ℝ) := Nat.cast_nonneg n
    calc (1:ℝ) = Real.sqrt 1 := Real.sqrt_one.symm
      _ ≤ Real.sqrt ((n:ℝ)+1) := Real.sqrt_le_sqrt (by linarith)
  have hs_sq : ∀ n : ℕ, Real.sqrt ((n:ℝ)+1) * Real.sqrt ((n:ℝ)+1) = (n:ℝ)+1 :=
    fun n => Real.mul_self_sqrt (by positivity)
  -- cumulative ≤ F
  have hAF : ∀ n, (∑ k ∈ range (n+1), bandTotal k) ≤ F n := by
    intro n
    have h0 : (0:ℝ) ≤ (n:ℝ) := Nat.cast_nonneg n
    refine (hcum n).trans ?_
    have hlog : Real.log (4 + 2*((n:ℝ)+5)) ≤ 2 * Real.sqrt (4 + 2*((n:ℝ)+5)) :=
      log_le_two_sqrt (by positivity)
    have h16 : (4 + 2*((n:ℝ)+5)) ≤ 16 * ((n:ℝ)+1) := by linarith
    have hsq16 : Real.sqrt (4 + 2*((n:ℝ)+5)) ≤ 4 * Real.sqrt ((n:ℝ)+1) := by
      have h1 := Real.sqrt_le_sqrt h16
      have h2 : Real.sqrt (16 * ((n:ℝ)+1)) = 4 * Real.sqrt ((n:ℝ)+1) := by
        rw [Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 16),
            show Real.sqrt 16 = 4 by
              rw [show (16:ℝ) = 4^2 by norm_num, Real.sqrt_sq (by norm_num : (0:ℝ) ≤ 4)]]
      rw [h2] at h1; exact h1
    have hlin : (3 + 2*((n:ℝ)+5)) ≤ 15 * ((n:ℝ)+1) := by linarith
    have hlog1 : Real.log (4 + 2*((n:ℝ)+5)) + 1 ≤ 9 * Real.sqrt ((n:ℝ)+1) := by
      have := hs_one n; linarith
    have hlog0 : (0:ℝ) ≤ Real.log (4 + 2*((n:ℝ)+5)) :=
      Real.log_nonneg (by linarith)
    have hprod : (3 + 2*((n:ℝ)+5)) * (Real.log (4 + 2*((n:ℝ)+5)) + 1)
        ≤ (15 * ((n:ℝ)+1)) * (9 * Real.sqrt ((n:ℝ)+1)) :=
      mul_le_mul hlin hlog1 (by linarith) (by positivity)
    have hone : (1:ℝ) ≤ ((n:ℝ)+1) * Real.sqrt ((n:ℝ)+1) := by
      have h2 := hs_one n
      nlinarith
    have hDle : D ≤ max D 0 * (((n:ℝ)+1) * Real.sqrt ((n:ℝ)+1)) := by
      calc D ≤ max D 0 := le_max_left _ _
        _ = max D 0 * 1 := by ring
        _ ≤ max D 0 * (((n:ℝ)+1) * Real.sqrt ((n:ℝ)+1)) :=
            mul_le_mul_of_nonneg_left hone (le_max_right _ _)
    calc C * ((3 + 2*((n:ℝ)+5)) * (Real.log (4 + 2*((n:ℝ)+5)) + 1)) + D
        ≤ C * (135 * (((n:ℝ)+1) * Real.sqrt ((n:ℝ)+1))) + D := by
          have := mul_le_mul_of_nonneg_left hprod hC0; nlinarith
      _ ≤ 135 * C * (((n:ℝ)+1) * Real.sqrt ((n:ℝ)+1))
            + max D 0 * (((n:ℝ)+1) * Real.sqrt ((n:ℝ)+1)) := by
          nlinarith [hDle]
      _ = F n := by rw [hFdef, hKdef]; ring
  -- F n * w n ≤ 2K
  have hFw : ∀ n, F n * w n ≤ 2 * K := by
    intro n
    have hden : (0:ℝ) < 1 + (n:ℝ)^2 := by positivity
    have h0 : (0:ℝ) ≤ (n:ℝ) := Nat.cast_nonneg n
    rw [hFdef, hwdef]
    rw [mul_one_div, div_le_iff₀ hden]
    have hsle : Real.sqrt ((n:ℝ)+1) ≤ (n:ℝ)+1 := by
      have h1 := Real.sqrt_le_sqrt (show ((n:ℝ)+1) ≤ ((n:ℝ)+1)^2 by nlinarith)
      rwa [Real.sqrt_sq (by positivity : (0:ℝ) ≤ (n:ℝ)+1)] at h1
    have hchain : ((n:ℝ)+1) * Real.sqrt ((n:ℝ)+1) ≤ 2 * (1 + (n:ℝ)^2) := by
      have h2 : ((n:ℝ)+1) * Real.sqrt ((n:ℝ)+1) ≤ ((n:ℝ)+1) * ((n:ℝ)+1) :=
        mul_le_mul_of_nonneg_left hsle (by linarith)
      nlinarith [sq_nonneg ((n:ℝ)-1)]
    calc K * (((n:ℝ)+1) * Real.sqrt ((n:ℝ)+1))
        ≤ K * (2 * (1 + (n:ℝ)^2)) := mul_le_mul_of_nonneg_left hchain hK0
      _ = 2 * K * (1 + (n:ℝ)^2) := by ring
  -- tail majorant
  set g : ℕ → ℝ := fun k => 4 * K * (1 / (((k:ℝ)+1) * Real.sqrt ((k:ℝ)+1))) with hgdef
  have hg_nonneg : ∀ k, 0 ≤ g k := by
    intro k; rw [hgdef]; positivity
  have hg_sum : Summable g := (summable_inv_add_one_sqrt.mul_left (4*K))
  have hg : ∀ k, F k * (w k - w (k+1)) ≤ g k := by
    intro k
    have hk0 : (0:ℝ) ≤ (k:ℝ) := Nat.cast_nonneg k
    have hd1 : (0:ℝ) < 1 + (k:ℝ)^2 := by positivity
    have hd2 : (0:ℝ) < 1 + ((k:ℝ)+1)^2 := by positivity
    have hΔ_eq : w k - w (k+1)
        = (2*(k:ℝ)+1) / ((1 + (k:ℝ)^2) * (1 + ((k:ℝ)+1)^2)) := by
      rw [hwdef]; push_cast; field_simp; ring
    have hΔ_le : w k - w (k+1) ≤ 4 / (((k:ℝ)+1)^3) := by
      rw [hΔ_eq, div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith [sq_nonneg ((k:ℝ)+1), sq_nonneg ((k:ℝ)-1)]
    have hF_nn : 0 ≤ F k := by rw [hFdef]; positivity
    calc F k * (w k - w (k+1))
        ≤ F k * (4 / (((k:ℝ)+1)^3)) := mul_le_mul_of_nonneg_left hΔ_le hF_nn
      _ = g k := by
          rw [hFdef, hgdef]
          have hsq := hs_sq k
          have hsp := hs_pos k
          have hkp : (0:ℝ) < (k:ℝ)+1 := by positivity
          have hcube : ((k:ℝ)+1)^3
              = (((k:ℝ)+1) * Real.sqrt ((k:ℝ)+1))
                * (Real.sqrt ((k:ℝ)+1) * ((k:ℝ)+1)) := by
            nlinarith [hsq]
          field_simp
          nlinarith [hsq, hsp, hkp, sq_nonneg (Real.sqrt ((k:ℝ)+1))]
  -- assemble via the Abel brick
  have habel : Summable (fun k => bandTotal k * w k) :=
    summable_mul_weight_of_cumulative_bound
      bandTotal w F bandTotal_nonneg
      (fun k => by simp only [hwdef]; positivity)
      (fun k => by
        simp only [hwdef]
        push_cast
        have hk : (0:ℝ) ≤ (k:ℝ) := Nat.cast_nonneg k
        first
          | (apply one_div_le_one_div_of_le (by positivity)
             nlinarith)
          | (rw [div_le_div_iff₀ (by positivity) (by positivity)]
             nlinarith)
          | (rw [div_le_div_iff₀ (by positivity) (by positivity)]
             ring_nf
             nlinarith))
      hAF (2*K) hFw g hg_nonneg hg_sum hg
  refine habel.congr fun k => ?_
  simp only [hwdef]
  rw [mul_one_div]

/-- **PILLAR (b): the unconditional envelope.** Zero hypotheses.
The subtype seam is `band_filter_le_bandTotal` (green), already wired
inside `hsum_from_bandCount_summable`. -/
noncomputable def unconditionalZeroPoleEnvelope :
    ZeroPoleEnvelopeData defaultZeroMultiplicityData :=
  buildEnvelopeFromZeroDensity defaultZeroMultiplicityData
    (hsum_from_bandCount_summable summable_bandTotal_weighted)

#print axioms summable_bandTotal_weighted
#print axioms unconditionalZeroPoleEnvelope

end RHFormalization
