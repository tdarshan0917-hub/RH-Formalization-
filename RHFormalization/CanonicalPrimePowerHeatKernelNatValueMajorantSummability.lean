import RHFormalization.CanonicalPrimePowerHeatKernelGaussianMajorant
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Analysis.PSeries

/-!
# RHFormalization.CanonicalPrimePowerHeatKernelNatValueMajorantSummability

Arithmetic summability target for the natValue majorant.
-/

namespace RHFormalization

noncomputable section

open Complex Topology Filter
open scoped BigOperators

/--
The arithmetic majorant produced by the log-Gaussian tail estimate.
-/
noncomputable def heatKernelNatValueMajorant :
    PrimePowerPair → ℝ :=
  fun q : PrimePowerPair =>
    ‖q.weightC‖ * ((q.natValue : ℝ) ^ 3)⁻¹

/--
Comparison principle for the natValue majorant.
-/
theorem heatKernelNatValueMajorant_summable_of_model
    (model : PrimePowerPair → ℝ)
    (h_model_summable : Summable model)
    (h_le_model :
      ∀ q : PrimePowerPair,
        heatKernelNatValueMajorant q ≤ model q) :
    Summable heatKernelNatValueMajorant := by
  refine
    Summable.of_nonneg_of_le
      ?h_nonneg
      h_le_model
      h_model_summable
  intro q
  unfold heatKernelNatValueMajorant
  exact
    mul_nonneg
      (norm_nonneg q.weightC)
      (by positivity)


/--
Invalid prime-power pairs contribute zero to the natValue majorant.
-/
theorem heatKernelNatValueMajorant_eq_zero_of_not_isPrimePowerPair
    (q : PrimePowerPair)
    (hq : ¬ IsPrimePowerPair q) :
    heatKernelNatValueMajorant q = 0 := by
  unfold heatKernelNatValueMajorant
  simp [PrimePowerPair.weightC, PrimePowerPair.weightReal, hq]

/--
On valid prime-power pairs, the natValue majorant has the explicit real formula.
-/
theorem heatKernelNatValueMajorant_eq_valid_primePower_formula
    (q : PrimePowerPair)
    (hq : IsPrimePowerPair q) :
    heatKernelNatValueMajorant q =
      |Real.log (q.p : ℝ) / Real.sqrt (q.natValue : ℝ)| *
        ((q.natValue : ℝ) ^ 3)⁻¹ := by
  unfold heatKernelNatValueMajorant
  rw [norm_weightC_eq_abs_weightReal]
  simp [PrimePowerPair.weightReal, hq]



/--
A simple summable product p-series model on `PrimePowerPair = ℕ × ℕ`.
-/
noncomputable def heatKernelPairPSeriesModel :
    PrimePowerPair → ℝ :=
  fun q : PrimePowerPair =>
    (1 / |(q.p : ℝ) + 1| ^ (2 : ℝ)) *
      (1 / |(q.m : ℝ) + 1| ^ (2 : ℝ))

/--
The product p-series model is summable.

This uses `summable_prod_of_nonneg`, which is available in this Mathlib checkout.
-/
theorem heatKernelPairPSeriesModel_summable :
    Summable heatKernelPairPSeriesModel := by
  let a : ℕ → ℝ := fun p : ℕ =>
    1 / |(p : ℝ) + 1| ^ (2 : ℝ)
  let b : ℕ → ℝ := fun m : ℕ =>
    1 / |(m : ℝ) + 1| ^ (2 : ℝ)

  have ha : Summable a := by
    simpa [a] using
      ((Real.summable_one_div_nat_add_rpow 1 2).2 (by norm_num))

  have hb : Summable b := by
    simpa [b] using
      ((Real.summable_one_div_nat_add_rpow 1 2).2 (by norm_num))

  have hf_nonneg :
      0 ≤ (fun x : ℕ × ℕ => a x.1 * b x.2) := by
    intro x
    dsimp [a, b]
    positivity

  have h_inner :
      ∀ p : ℕ, Summable fun m : ℕ => a p * b m := by
    intro p
    exact hb.mul_left (a p)

  have h_tsum :
      (fun p : ℕ => ∑' m : ℕ, a p * b m) =
        fun p : ℕ => a p * (∑' m : ℕ, b m) := by
    funext p
    simpa using
      (tsum_mul_left :
        (∑' m : ℕ, a p * b m) =
          a p * (∑' m : ℕ, b m))

  have h_outer :
      Summable fun p : ℕ => ∑' m : ℕ, a p * b m := by
    have houter' :
        Summable fun p : ℕ => (∑' m : ℕ, b m) * a p :=
      ha.mul_left (∑' m : ℕ, b m)
    have houter'' :
        Summable fun p : ℕ => a p * (∑' m : ℕ, b m) := by
      simpa [mul_comm] using houter'
    simpa [h_tsum] using houter''

  have hprod :
      Summable (fun x : ℕ × ℕ => a x.1 * b x.2) :=
    (summable_prod_of_nonneg hf_nonneg).2 ⟨h_inner, h_outer⟩

  change Summable (fun q : PrimePowerPair => a q.p * b q.m)
  simpa [heatKernelPairPSeriesModel, a, b,
    PrimePowerPair.p, PrimePowerPair.m] using hprod


/--
A geometric-in-`m` summable model.

This is better aligned with the prime-power decay than the polynomial `m` model.
-/
noncomputable def heatKernelPairGeomModel :
    PrimePowerPair → ℝ :=
  fun q : PrimePowerPair =>
    (1 / |(q.p : ℝ) + 1| ^ (2 : ℝ)) *
      ((1 / 2 : ℝ) ^ q.m)

/--
The geometric model is summable on `PrimePowerPair = ℕ × ℕ`.
-/
theorem heatKernelPairGeomModel_summable :
    Summable heatKernelPairGeomModel := by
  let a : ℕ → ℝ := fun p : ℕ =>
    1 / |(p : ℝ) + 1| ^ (2 : ℝ)
  let b : ℕ → ℝ := fun m : ℕ =>
    (1 / 2 : ℝ) ^ m

  have ha : Summable a := by
    simpa [a] using
      ((Real.summable_one_div_nat_add_rpow 1 2).2 (by norm_num))

  have hb : Summable b := by
    simpa [b] using
      (summable_geometric_two :
        Summable fun m : ℕ => (1 / 2 : ℝ) ^ m)

  have hf_nonneg :
      0 ≤ (fun x : ℕ × ℕ => a x.1 * b x.2) := by
    intro x
    dsimp [a, b]
    positivity

  have h_inner :
      ∀ p : ℕ, Summable fun m : ℕ => a p * b m := by
    intro p
    exact hb.mul_left (a p)

  have h_tsum :
      (fun p : ℕ => ∑' m : ℕ, a p * b m) =
        fun p : ℕ => a p * (∑' m : ℕ, b m) := by
    funext p
    simpa using
      (tsum_mul_left :
        (∑' m : ℕ, a p * b m) =
          a p * (∑' m : ℕ, b m))

  have h_outer :
      Summable fun p : ℕ => ∑' m : ℕ, a p * b m := by
    have houter' :
        Summable fun p : ℕ => (∑' m : ℕ, b m) * a p :=
      ha.mul_left (∑' m : ℕ, b m)
    have houter'' :
        Summable fun p : ℕ => a p * (∑' m : ℕ, b m) := by
      simpa [mul_comm] using houter'
    simpa [h_tsum] using houter''

  have hprod :
      Summable (fun x : ℕ × ℕ => a x.1 * b x.2) :=
    (summable_prod_of_nonneg hf_nonneg).2 ⟨h_inner, h_outer⟩

  change Summable (fun q : PrimePowerPair => a q.p * b q.m)
  simpa [heatKernelPairGeomModel, a, b,
    PrimePowerPair.p, PrimePowerPair.m] using hprod



/--
Power-decay helper for the geometric-in-`m` model.
For `p ≥ 2`, the geometric tail `2^k` is dominated by `p^(3k)`.
-/
lemma two_pow_le_prime_pow_three_mul
    {p k : ℕ} (hp : 2 ≤ p) :
    (2 : ℝ) ^ k ≤ (p : ℝ) ^ (3 * k) := by
  induction k with
  | zero =>
      norm_num
  | succ k ih =>
      have hpR : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
      have hp3 : (2 : ℝ) ≤ (p : ℝ) ^ 3 := by
        nlinarith [sq_nonneg (p : ℝ), hpR]
      calc
        (2 : ℝ) ^ (k + 1)
            = (2 : ℝ) ^ k * 2 := by
              rw [pow_succ]
        _ ≤ (p : ℝ) ^ (3 * k) * (p : ℝ) ^ 3 := by
              exact mul_le_mul ih hp3 (by norm_num) (by positivity)
        _ = (p : ℝ) ^ (3 * (k + 1)) := by
              rw [← pow_add]
              congr 1


/--
Pred-shifted power-decay helper for the geometric-in-`m` model.

For `p ≥ 2` and `m > 0`, the geometric factor `2^m` is bounded by
`2 * p^(3*(m-1))`.
-/
lemma two_pow_le_two_prime_pow_three_pred
    {p m : ℕ} (hp : 2 ≤ p) (hm : 0 < m) :
    (2 : ℝ) ^ m ≤ 2 * (p : ℝ) ^ (3 * (m - 1)) := by
  rcases Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hm) with ⟨k, rfl⟩
  simp [Nat.succ_eq_add_one]
  calc
    (2 : ℝ) ^ (k + 1)
        = (2 : ℝ) ^ k * 2 := by
          rw [pow_succ]
    _ ≤ (p : ℝ) ^ (3 * k) * 2 := by
          exact
            mul_le_mul_of_nonneg_right
              (two_pow_le_prime_pow_three_mul (p := p) (k := k) hp)
              (by norm_num)
    _ = 2 * (p : ℝ) ^ (3 * k) := by
          ring


/--
Numerator bound for the geometric-in-`m` model.

For `p ≥ 2` and `m > 0`,
`p * (p+1)^2 * 2^m ≤ 8 * p^(3m)`.
-/
lemma geom_numerator_bound
    {p m : ℕ} (hp : 2 ≤ p) (hm : 0 < m) :
    (p : ℝ) * ((p : ℝ) + 1)^2 * (2 : ℝ)^m
      ≤ 8 * (p : ℝ) ^ (3 * m) := by
  have hpR : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
  have hp_nonneg : 0 ≤ (p : ℝ) := by positivity

  have hp1_le_2p : (p : ℝ) + 1 ≤ 2 * (p : ℝ) := by
    nlinarith

  have hp1_sq_le : ((p : ℝ) + 1)^2 ≤ (2 * (p : ℝ))^2 := by
    exact pow_le_pow_left₀ (by positivity) hp1_le_2p 2

  have hfirst :
      (p : ℝ) * ((p : ℝ) + 1)^2 ≤ 4 * (p : ℝ)^3 := by
    have h :=
      mul_le_mul_of_nonneg_left hp1_sq_le hp_nonneg
    nlinarith [h]

  have htwo :
      (2 : ℝ)^m ≤ 2 * (p : ℝ) ^ (3 * (m - 1)) :=
    two_pow_le_two_prime_pow_three_pred (p := p) (m := m) hp hm

  have hprod :
      ((p : ℝ) * ((p : ℝ) + 1)^2) * (2 : ℝ)^m
        ≤ (4 * (p : ℝ)^3) * (2 * (p : ℝ) ^ (3 * (m - 1))) := by
    exact
      mul_le_mul
        hfirst
        htwo
        (by positivity)
        (by positivity)

  have hexp : 3 + 3 * (m - 1) = 3 * m := by
    omega

  calc
    (p : ℝ) * ((p : ℝ) + 1)^2 * (2 : ℝ)^m
        = ((p : ℝ) * ((p : ℝ) + 1)^2) * (2 : ℝ)^m := by
          ring
    _ ≤ (4 * (p : ℝ)^3) * (2 * (p : ℝ) ^ (3 * (m - 1))) := hprod
    _ = 8 * ((p : ℝ)^3 * (p : ℝ) ^ (3 * (m - 1))) := by
          ring
    _ = 8 * (p : ℝ) ^ (3 + 3 * (m - 1)) := by
          rw [← pow_add]
    _ = 8 * (p : ℝ) ^ (3 * m) := by
          rw [hexp]


/--
NatValue rewrite version of `geom_numerator_bound`.

This converts the bound with `(p : ℝ)^(3*m)` into the form using
`q.natValue = q.p ^ q.m`.
-/
lemma geom_numerator_bound_natValue
    (q : PrimePowerPair)
    (hp : 2 ≤ q.p)
    (hm : 0 < q.m) :
    (q.p : ℝ) * ((q.p : ℝ) + 1)^2 * (2 : ℝ)^q.m
      ≤ 8 * (q.natValue : ℝ)^3 := by
  have h :=
    geom_numerator_bound (p := q.p) (m := q.m) hp hm
  unfold PrimePowerPair.natValue

  have hpow :
      (q.p : ℝ) ^ (3 * q.m) =
        ((q.p : ℝ) ^ q.m) ^ 3 := by
    rw [Nat.mul_comm 3 q.m]
    rw [← pow_mul]

  rw [hpow] at h
  simpa [mul_comm, mul_left_comm, mul_assoc] using h

theorem heatKernelNatValueMajorant_le_scaled_pairGeomModel :
    ∃ C : ℝ,
      0 ≤ C ∧
      ∀ q : PrimePowerPair,
        heatKernelNatValueMajorant q ≤ C * heatKernelPairGeomModel q := by
  refine ⟨8, by norm_num, ?_⟩
  intro q
  by_cases hq : IsPrimePowerPair q
  · rw [heatKernelNatValueMajorant_eq_valid_primePower_formula q hq]
    rcases hq with ⟨hp, hm⟩

    have hp2 : 2 ≤ q.p := hp.two_le
    have hp_pos_nat : 0 < q.p := lt_of_lt_of_le (by norm_num) hp2

    have hnat_pos : 0 < (q.natValue : ℝ) := by
      unfold PrimePowerPair.natValue
      positivity

    have h_one_le_n : (1 : ℝ) ≤ (q.natValue : ℝ) := by
      exact_mod_cast (Nat.one_le_pow q.m q.p hp_pos_nat)

    have hsqrt_nonneg : 0 ≤ Real.sqrt (q.natValue : ℝ) := by
      positivity

    have hsqrt_sq :
        (Real.sqrt (q.natValue : ℝ)) ^ 2 = (q.natValue : ℝ) := by
      exact Real.sq_sqrt (by positivity)

    have hsqrt_ge_one : 1 ≤ Real.sqrt (q.natValue : ℝ) := by
      nlinarith [hsqrt_sq, h_one_le_n, hsqrt_nonneg]

    have hsqrt_pos : 0 < Real.sqrt (q.natValue : ℝ) := by
      exact Real.sqrt_pos.2 hnat_pos

    have hlog_nonneg : 0 ≤ Real.log (q.p : ℝ) := by
      have hp_one : (1 : ℝ) ≤ (q.p : ℝ) := by
        exact_mod_cast (le_trans (by norm_num : 1 ≤ 2) hp2)
      exact Real.log_nonneg hp_one

    have h_abs :
        |Real.log (q.p : ℝ) / Real.sqrt (q.natValue : ℝ)| =
          Real.log (q.p : ℝ) / Real.sqrt (q.natValue : ℝ) := by
      exact abs_of_nonneg (div_nonneg hlog_nonneg (le_of_lt hsqrt_pos))

    have h_inv_sqrt_le_one :
        (Real.sqrt (q.natValue : ℝ))⁻¹ ≤ 1 := by
      simpa [one_div] using
        (one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1) hsqrt_ge_one)

    have h_div_le_log :
        Real.log (q.p : ℝ) / Real.sqrt (q.natValue : ℝ) ≤
          Real.log (q.p : ℝ) := by
      simpa [div_eq_mul_inv] using
        mul_le_mul_of_nonneg_left h_inv_sqrt_le_one hlog_nonneg

    have hlog_le_p : Real.log (q.p : ℝ) ≤ (q.p : ℝ) := by
      exact Real.log_le_self (by positivity)

    have habs_le_p :
        |Real.log (q.p : ℝ) / Real.sqrt (q.natValue : ℝ)| ≤
          (q.p : ℝ) := by
      rw [h_abs]
      exact le_trans h_div_le_log hlog_le_p

    have hmajor_part :
        |Real.log (q.p : ℝ) / Real.sqrt (q.natValue : ℝ)| *
            ((q.natValue : ℝ) ^ 3)⁻¹
          ≤ (q.p : ℝ) * ((q.natValue : ℝ) ^ 3)⁻¹ := by
      exact mul_le_mul_of_nonneg_right habs_le_p (by positivity)

    have hpabs : |(q.p : ℝ) + 1| = (q.p : ℝ) + 1 := by
      exact abs_of_nonneg (by positivity)

    have hnum :
        (q.p : ℝ) * ((q.p : ℝ) + 1)^2 * (2 : ℝ)^q.m
          ≤ 8 * (q.natValue : ℝ)^3 :=
      geom_numerator_bound_natValue q hp2 hm

    have htarget :
        (q.p : ℝ) * ((q.natValue : ℝ) ^ 3)⁻¹
          ≤ 8 * heatKernelPairGeomModel q := by
      unfold heatKernelPairGeomModel
      rw [hpabs]

      have hp1_ne : ((q.p : ℝ) + 1) ≠ 0 := by positivity
      have hp1_sq_ne : ((q.p : ℝ) + 1)^2 ≠ 0 := by
        exact pow_ne_zero 2 hp1_ne
      have hn_ne : (q.natValue : ℝ) ≠ 0 := ne_of_gt hnat_pos
      have hn3_ne : ((q.natValue : ℝ) ^ 3) ≠ 0 := by
        exact pow_ne_zero 3 hn_ne
      have htwo_ne : (2 : ℝ) ≠ 0 := by norm_num
      have htwo_pow_ne : (2 : ℝ)^q.m ≠ 0 := by
        exact pow_ne_zero q.m htwo_ne

      have hgeom :
          ((1 / 2 : ℝ) ^ q.m) = ((2 : ℝ) ^ q.m)⁻¹ := by
        simp [one_div, inv_pow]

      rw [hgeom]
      field_simp [hp1_ne, hp1_sq_ne, hn_ne, hn3_ne, htwo_ne, htwo_pow_ne]
      have hnum_nat :
          (q.p : ℝ) * ((q.p : ℝ) + 1)^2 * (2 : ℝ)^q.m
            ≤ (q.natValue : ℝ)^3 * 8 := by
        simpa [mul_comm, mul_left_comm, mul_assoc] using hnum

      have hnum_realexp :
          (q.p : ℝ) * ((q.p : ℝ) + 1) ^ (2 : ℝ) * (2 : ℝ)^q.m
            ≤ (q.natValue : ℝ)^3 * 8 := by
        simpa [Real.rpow_natCast, mul_comm, mul_left_comm, mul_assoc] using hnum_nat

      exact hnum_realexp

    exact le_trans hmajor_part htarget

  · rw [heatKernelNatValueMajorant_eq_zero_of_not_isPrimePowerPair q hq]
    have hnonneg : 0 ≤ 8 * heatKernelPairGeomModel q := by
      unfold heatKernelPairGeomModel
      positivity
    linarith

/--
The natValue majorant is summable.

Closed by comparison with the geometric-in-`m` summable model.
-/
theorem heatKernelNatValueMajorant_summable :
    Summable heatKernelNatValueMajorant := by
  rcases heatKernelNatValueMajorant_le_scaled_pairGeomModel with
    ⟨C, _hC, hle⟩
  exact
    heatKernelNatValueMajorant_summable_of_model
      (fun q : PrimePowerPair => C * heatKernelPairGeomModel q)
      (heatKernelPairGeomModel_summable.mul_left C)
      hle

end

end RHFormalization
