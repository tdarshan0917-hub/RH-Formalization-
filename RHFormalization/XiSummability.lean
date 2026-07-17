import RHFormalization.XiCountBound
import RHFormalization.HsumFromBandCount
import Mathlib.NumberTheory.LSeries.SumCoeff
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Summability of the band density and `hsum`

Combines the sharp `O(n log n)` cumulative count (`cumulativeBand_loglinear`) with
`LSeriesSummable_of_sum_norm_bigO_and_nonneg` to prove `Summable (bandTotal k / (1+k²))`,
then routes through `hsum_from_bandCount_summable` to `hsum`.
-/

namespace RHFormalization

open Finset Filter Asymptotics

/-- The cumulative band sum is `O(n^(3/2))`. -/
theorem cumulativeBand_isBigO_rpow :
    (fun n : ℕ => ∑ k ∈ Finset.range (n + 1), bandTotal k)
      =O[atTop] (fun n : ℕ => (n : ℝ) ^ (3/2 : ℝ)) := by
  obtain ⟨C, D, hC0, hbound⟩ := cumulativeBand_loglinear
  -- log =o x^{1/2}, so eventually log x ≤ x^{1/2}
  have hlog_o : (fun x : ℝ => Real.log x) =o[atTop] (fun x : ℝ => x ^ (1/2 : ℝ)) :=
    isLittleO_log_rpow_atTop (by norm_num)
  rw [Asymptotics.isLittleO_iff] at hlog_o
  have hlog_ev : ∀ᶠ x : ℝ in atTop, Real.log x ≤ x ^ (1/2 : ℝ) := by
    have h1 := hlog_o (c := 1) (by norm_num)
    filter_upwards [h1, eventually_ge_atTop (1:ℝ)] with x hx hx1
    have hlogpos : 0 ≤ Real.log x := Real.log_nonneg hx1
    have hxpos : 0 ≤ x ^ (1/2:ℝ) := Real.rpow_nonneg (by linarith) _
    rwa [Real.norm_of_nonneg hlogpos, Real.norm_of_nonneg hxpos, one_mul] at hx
  -- transfer to the shifted nat argument: log(4+2(n+5)) ≤ (4+2(n+5))^{1/2} ≤ ... ≤ C·n^{1/2} eventually
  -- get N where for x ≥ N, log x ≤ x^{1/2}
  rw [eventually_atTop] at hlog_ev
  obtain ⟨X0, hX0⟩ := hlog_ev
  rw [Asymptotics.isBigO_iff]
  refine ⟨C * 100 + |D| + 100, ?_⟩
  rw [eventually_atTop]
  refine ⟨max 1 (Nat.ceil X0), fun n hn => ?_⟩
  have hn1 : 1 ≤ n := le_trans (le_max_left _ _) hn
  have hnX0 : X0 ≤ (4 + 2 * ((n:ℝ) + 5)) := by
    have : (Nat.ceil X0 : ℝ) ≤ (n:ℝ) := by exact_mod_cast le_trans (le_max_right _ _) hn
    have hcl : X0 ≤ (Nat.ceil X0 : ℝ) := Nat.le_ceil X0
    have hn0 : (0:ℝ) ≤ (n:ℝ) := Nat.cast_nonneg n
    linarith
  have hlogbound : Real.log (4 + 2 * ((n:ℝ) + 5)) ≤ (4 + 2 * ((n:ℝ) + 5)) ^ (1/2:ℝ) :=
    hX0 _ hnX0
  -- LHS nonneg
  have hLHS_nonneg : 0 ≤ ∑ k ∈ Finset.range (n + 1), bandTotal k :=
    Finset.sum_nonneg (fun k _ => bandTotal_nonneg k)
  -- bound LHS ≤ RHS
  have hb := hbound n
  -- now: RHS = C(3+2(n+5))(log(...)+1) + D ≤ (C*100+|D|+100)·n^{3/2}
  rw [Real.norm_of_nonneg hLHS_nonneg]
  have hnpos : (0:ℝ) < (n:ℝ) := by exact_mod_cast hn1
  have hn_rpow_pos : (0:ℝ) < (n:ℝ) ^ (3/2:ℝ) := Real.rpow_pos_of_pos hnpos _
  rw [Real.norm_of_nonneg (le_of_lt hn_rpow_pos)]
  -- sqrt(4+2(n+5)) ≤ sqrt(16 n) = 4 sqrt n  for n ≥ 1 (since 4+2(n+5) = 2n+14 ≤ 16n)
  have hshift_le : (4 + 2 * ((n:ℝ) + 5)) ^ (1/2:ℝ) ≤ 4 * (n:ℝ) ^ (1/2:ℝ) := by
    have h2n14 : 4 + 2 * ((n:ℝ) + 5) ≤ 16 * (n:ℝ) := by
      have : (1:ℝ) ≤ (n:ℝ) := by exact_mod_cast hn1
      linarith
    calc (4 + 2 * ((n:ℝ) + 5)) ^ (1/2:ℝ)
        ≤ (16 * (n:ℝ)) ^ (1/2:ℝ) :=
          Real.rpow_le_rpow (by positivity) h2n14 (by norm_num)
      _ = (16:ℝ) ^ (1/2:ℝ) * (n:ℝ) ^ (1/2:ℝ) :=
          Real.mul_rpow (by norm_num) (by positivity)
      _ ≤ 4 * (n:ℝ) ^ (1/2:ℝ) := by
          have h16 : (16:ℝ) ^ (1/2:ℝ) = 4 := by
            rw [show (16:ℝ) = 4^2 by norm_num, ← Real.rpow_natCast 4 2, ← Real.rpow_mul (by norm_num)]
            norm_num
          rw [h16]
  -- n^{3/2} = n * n^{1/2}
  have hsplit : (n:ℝ) ^ (3/2:ℝ) = (n:ℝ) * (n:ℝ) ^ (1/2:ℝ) := by
    rw [show (3/2:ℝ) = 1 + 1/2 by norm_num, Real.rpow_add hnpos, Real.rpow_one]
  -- assemble: LHS ≤ C(3+2(n+5))(log+1) + D ≤ C(2n+13)(4√n + 1) + D ≤ (C*100+|D|+100) n^{3/2}
  have hlogp1 : Real.log (4 + 2 * ((n:ℝ) + 5)) + 1 ≤ 4 * (n:ℝ) ^ (1/2:ℝ) + 1 := by linarith
  have hfac_nn : (0:ℝ) ≤ 3 + 2 * ((n:ℝ) + 5) := by positivity
  have hsqrt_ge1 : (1:ℝ) ≤ (n:ℝ) ^ (1/2:ℝ) := by
    have : (1:ℝ) ^ (1/2:ℝ) ≤ (n:ℝ) ^ (1/2:ℝ) :=
      Real.rpow_le_rpow (by norm_num) (by exact_mod_cast hn1) (by norm_num)
    rwa [Real.one_rpow] at this
  calc ∑ k ∈ Finset.range (n + 1), bandTotal k
      ≤ C * ((3 + 2 * ((n:ℝ) + 5)) * (Real.log (4 + 2 * ((n:ℝ) + 5)) + 1)) + D := hb
    _ ≤ C * ((3 + 2 * ((n:ℝ) + 5)) * (4 * (n:ℝ) ^ (1/2:ℝ) + 1)) + D := by
        have hinner : (3 + 2 * ((n:ℝ) + 5)) * (Real.log (4 + 2 * ((n:ℝ) + 5)) + 1)
            ≤ (3 + 2 * ((n:ℝ) + 5)) * (4 * (n:ℝ) ^ (1/2:ℝ) + 1) :=
          mul_le_mul_of_nonneg_left hlogp1 hfac_nn
        have := mul_le_mul_of_nonneg_left hinner hC0
        linarith
    _ ≤ (C * 100 + |D| + 100) * (n:ℝ) ^ (3/2:ℝ) := by
        rw [hsplit]
        set sq : ℝ := (n:ℝ) ^ (1/2:ℝ) with hsqdef
        have hn1r : (1:ℝ) ≤ (n:ℝ) := by exact_mod_cast hn1
        have hD_le : D ≤ |D| := le_abs_self D
        have hsq0 : 0 ≤ sq := le_trans (by norm_num) hsqrt_ge1
        have hns_n : (n:ℝ) ≤ (n:ℝ) * sq := by nlinarith [hsqrt_ge1, hn1r]
        have hns_sq : sq ≤ (n:ℝ) * sq := by nlinarith [hn1r, hsq0]
        have hns_1 : (1:ℝ) ≤ (n:ℝ) * sq := by nlinarith [hn1r, hsqrt_ge1]
        have hns_nsq : (n:ℝ) * sq ≤ (n:ℝ) * sq := le_refl _
        -- pre-multiplied product bounds (all ≤ (n*sq) times their coefficient)
        have hA : C * sq ≤ C * ((n:ℝ) * sq) := mul_le_mul_of_nonneg_left hns_sq hC0
        have hB : C * (n:ℝ) ≤ C * ((n:ℝ) * sq) := mul_le_mul_of_nonneg_left hns_n hC0
        have hE : C ≤ C * ((n:ℝ) * sq) := by nlinarith [hC0, hns_1]
        have hDabs_nn : 0 ≤ |D| := abs_nonneg D
        have hF : |D| ≤ |D| * ((n:ℝ) * sq) := by nlinarith [hDabs_nn, hns_1]
        have hCnsq_nn : 0 ≤ C * ((n:ℝ) * sq) := mul_nonneg hC0 (by nlinarith [hns_1])
        nlinarith [hA, hB, hE, hF, hD_le, hCnsq_nn, hC0, hsq0, hns_1, hn1r, hsqrt_ge1,
          mul_nonneg hC0 hsq0]

/-- Partial sums over `Icc 1 n` are `O(n^{3/2})` (subset of range, nonneg). -/
theorem bandTotal_sum_Icc_isBigO :
    (fun n : ℕ => ∑ k ∈ Finset.Icc 1 n, bandTotal k)
      =O[atTop] (fun n : ℕ => (n : ℝ) ^ (3/2 : ℝ)) := by
  refine (Asymptotics.isBigO_of_le atTop (fun n => ?_)).trans cumulativeBand_isBigO_rpow
  -- ‖∑_{Icc 1 n}‖ ≤ ‖∑_{range(n+1)}‖ : both nonneg, Icc 1 n ⊆ range(n+1)
  have hsub : Finset.Icc 1 n ⊆ Finset.range (n + 1) := by
    intro k hk
    rw [Finset.mem_Icc] at hk
    rw [Finset.mem_range]
    omega
  have hIcc_nn : 0 ≤ ∑ k ∈ Finset.Icc 1 n, bandTotal k :=
    Finset.sum_nonneg (fun k _ => bandTotal_nonneg k)
  have hrange_nn : 0 ≤ ∑ k ∈ Finset.range (n + 1), bandTotal k :=
    Finset.sum_nonneg (fun k _ => bandTotal_nonneg k)
  have hle : ∑ k ∈ Finset.Icc 1 n, bandTotal k ≤ ∑ k ∈ Finset.range (n + 1), bandTotal k :=
    Finset.sum_le_sum_of_subset_of_nonneg hsub (fun i _ _ => bandTotal_nonneg i)
  rw [Real.norm_of_nonneg hIcc_nn, Real.norm_of_nonneg hrange_nn]
  exact hle

/-- `Summable (fun n => bandTotal n / n²)` via the LSeries criterion at `s = 2`. -/
theorem bandTotal_div_sq_summable :
    Summable (fun n : ℕ => bandTotal n / (n : ℝ) ^ 2) := by
  have hls : LSeriesSummable (fun n => (bandTotal n : ℂ)) 2 := by
    refine LSeriesSummable_of_sum_norm_bigO_and_nonneg (r := 3/2) ?_ bandTotal_nonneg
      (by norm_num) (by norm_num)
    exact bandTotal_sum_Icc_isBigO
  -- LSeriesSummable = Summable (term), term n 2 = bandTotal n / n^2
  rw [LSeriesSummable] at hls
  -- term (↑bandTotal) 2 n = ↑(bandTotal n / n²); transfer ℂ→ℝ via summable_ofReal
  rw [← Complex.summable_ofReal]
  refine hls.congr (fun n => ?_)
  rcases eq_or_ne n 0 with hn | hn
  · subst hn
    simp [LSeries.term]
  · rw [LSeries.term_of_ne_zero hn]
    norm_cast

/-- Comparison helper with an OPAQUE nonneg `c` (prevents `whnf` unfolding `bandTotal`):
`Summable (c n / n²)` and `c ≥ 0` give `Summable (c n / (1+n²))`. -/
theorem summable_div_one_add_sq_of_div_sq {c : ℕ → ℝ} (hc : ∀ n, 0 ≤ c n)
    (h : Summable (fun n : ℕ => c n / (n : ℝ) ^ 2)) :
    Summable (fun n : ℕ => c n / (1 + (n : ℝ) ^ 2)) := by
  refine Summable.of_norm_bounded_eventually_nat (g := fun n : ℕ => c n / (n : ℝ) ^ 2) h ?_
  filter_upwards [eventually_ge_atTop 1] with n hn1
  have hfnn : 0 ≤ c n / (1 + (n : ℝ) ^ 2) := by
    apply div_nonneg (hc n); positivity
  rw [Real.norm_of_nonneg hfnn]
  have hnpos : (0:ℝ) < (n : ℝ) ^ 2 := by
    have h1 : (1:ℝ) ≤ (n : ℝ) := by exact_mod_cast hn1
    positivity
  have hden : (n : ℝ) ^ 2 ≤ 1 + (n : ℝ) ^ 2 := by linarith
  exact div_le_div_of_nonneg_left (hc n) hnpos hden

/-- **`hsum` target: band density summable.** `Summable (bandTotal k / (1+k²))`. -/
theorem bandTotal_density_summable :
    Summable (fun k : ℕ => bandTotal k / (1 + (k : ℝ) ^ 2)) :=
  summable_div_one_add_sq_of_div_sq bandTotal_nonneg bandTotal_div_sq_summable

/-- **`hsum` — the bottom input, now unconditional.** -/
theorem hsum_unconditional :
    Summable (fun ρ : {ρ : ℂ // IsNontrivialZetaZero ρ} =>
      (defaultZeroMultiplicityData.mult ρ.1 : ℝ) / (1 + ρ.1.im ^ 2)) :=
  hsum_from_bandCount_summable bandTotal_density_summable

end RHFormalization


#print axioms RHFormalization.hsum_unconditional
