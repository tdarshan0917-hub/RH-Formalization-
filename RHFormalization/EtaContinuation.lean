/-
EtaContinuation.lean — Real-zero-free campaign, Piece 2 (Stage 2a).

The eta function as the ZMod-2 L-function of the alternating coefficient.
Stage 2a: define Φ : ZMod 2 → ℂ (Φ 0 = -1, Φ 1 = 1), prove ∑ Φ = 0, and
record that ZMod.LFunction Φ is entire (hence analytic everywhere) via
Mathlib's differentiable_LFunction_of_sum_zero. This is the analytic
continuation of the eta series to the whole plane — the crux input that
lets Piece 3 reach the strip (0,1).
-/
import Mathlib.NumberTheory.LSeries.ZMod
import Mathlib.NumberTheory.LSeries.RiemannZeta
import RHFormalization.EtaZetaIdentity

open Complex

namespace RHFormalization

/-- The alternating coefficient as a function on `ZMod 2`. -/
def etaCoeff : ZMod 2 → ℂ := fun j => if j = 0 then -1 else 1

/-- The alternating coefficients sum to zero over `ZMod 2`. -/
theorem etaCoeff_sum_zero : ∑ j : ZMod 2, etaCoeff j = 0 := by
  rw [show (Finset.univ : Finset (ZMod 2)) = {0, 1} from rfl]
  simp only [etaCoeff, Finset.sum_insert, Finset.mem_singleton, Finset.sum_singleton]
  norm_num

/-- The eta L-function `ZMod.LFunction etaCoeff` is entire. -/
theorem etaLFunction_differentiable : Differentiable ℂ (ZMod.LFunction etaCoeff) :=
  ZMod.differentiable_LFunction_of_sum_zero etaCoeff_sum_zero

/-- Hence it is analytic on all of ℂ. -/
theorem etaLFunction_analytic : AnalyticOnNhd ℂ (ZMod.LFunction etaCoeff) Set.univ :=
  etaLFunction_differentiable.differentiableOn.analyticOnNhd isOpen_univ

/-- `etaCoeff` at a natural-number cast: `etaCoeff (↑n) = (-1)^(n+1)` by parity. -/
theorem etaCoeff_natCast (n : ℕ) : etaCoeff (n : ZMod 2) = (-1 : ℂ) ^ (n + 1) := by
  rcases Nat.even_or_odd n with he | ho
  · have h0 : (n : ZMod 2) = 0 := ZMod.natCast_eq_zero_iff_even.mpr he
    rw [etaCoeff, h0, if_pos rfl, (he.add_one).neg_one_pow]
  · have h1 : (n : ZMod 2) = 1 := ZMod.natCast_eq_one_iff_odd.mpr ho
    rw [etaCoeff, h1, if_neg (one_ne_zero), (ho.add_one).neg_one_pow]

/-- The eta term reindexed: `term (etaCoeff·) s (m+1) = (-1)^m / (m+1)^s`. -/
theorem etaTerm_succ {s : ℂ} (hs : 1 < s.re) (m : ℕ) :
    LSeries.term (etaCoeff ·) s (m + 1) = (-1 : ℂ) ^ m / ((m : ℂ) + 1) ^ s := by
  rw [LSeries.term_of_ne_zero (Nat.succ_ne_zero m)]
  rw [etaCoeff_natCast]
  rw [pow_succ]
  push_cast
  ring

/-- STAGE 2b: the ZMod-2 L-function equals our eta series for `re > 1`. -/
theorem etaLFunction_eq_etaSeries {s : ℂ} (hs : 1 < s.re) :
    ZMod.LFunction etaCoeff s = ∑' n : ℕ, (-1 : ℂ) ^ n * (1 / ((n : ℂ) + 1) ^ s) := by
  rw [ZMod.LFunction_eq_LSeries etaCoeff hs, LSeries]
  rw [tsum_eq_zero_add']
  · rw [LSeries.term_zero, zero_add]
    refine tsum_congr (fun m => ?_)
    rw [etaTerm_succ hs m]
    rw [div_eq_mul_one_div]
  · -- summability of the shifted term sequence
    have hsum : LSeriesSummable (etaCoeff ·) s :=
      ZMod.LSeriesSummable_of_one_lt_re etaCoeff hs
    exact (summable_nat_add_iff 1).mpr hsum

#print axioms etaCoeff_sum_zero
#print axioms etaLFunction_differentiable
#print axioms etaLFunction_analytic
#print axioms etaCoeff_natCast
/-- The factor-times-zeta function, analytic on `{1}ᶜ`. -/
theorem zeta_factor_analytic :
    AnalyticOnNhd ℂ (fun s => (1 - 2 * (2 : ℂ) ^ (-s)) * riemannZeta s) {(1 : ℂ)}ᶜ := by
  apply AnalyticOnNhd.mul
  · have hd : Differentiable ℂ (fun s : ℂ => 1 - 2 * (2 : ℂ) ^ (-s)) := by fun_prop
    exact (analyticOnNhd_univ_iff_differentiable.mpr hd).mono (Set.subset_univ _)
  · exact analyticOn_riemannZeta

/-- STAGE 2c: the continued eta-zeta identity. On `{1}ᶜ` (hence on the strip),
`LFunction etaCoeff s = (1 - 2·2^(-s))·ζ(s)`. -/
theorem etaLFunction_eq_factor_zeta {s : ℂ} (hs : s ≠ 1) :
    ZMod.LFunction etaCoeff s = (1 - 2 * (2 : ℂ) ^ (-s)) * riemannZeta s := by
  have hU : IsPreconnected ({(1 : ℂ)}ᶜ) :=
    (isConnected_compl_singleton_of_one_lt_rank (by simp) _).isPreconnected
  have hagree : Set.EqOn (ZMod.LFunction etaCoeff)
      (fun s => (1 - 2 * (2 : ℂ) ^ (-s)) * riemannZeta s) {s : ℂ | 1 < s.re} := by
    intro z hz
    rw [etaLFunction_eq_etaSeries hz, ← eta_zeta_identity hz]
  have hz2 : (2 : ℂ) ∈ {s : ℂ | 1 < s.re} := by
    rw [Set.mem_setOf_eq]
    norm_num
  have hopen : IsOpen {s : ℂ | 1 < s.re} := isOpen_lt continuous_const continuous_re
  have heq : Set.EqOn (ZMod.LFunction etaCoeff)
      (fun s => (1 - 2 * (2 : ℂ) ^ (-s)) * riemannZeta s) {(1 : ℂ)}ᶜ := by
    refine AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq
      (etaLFunction_analytic.mono (Set.subset_univ _)) zeta_factor_analytic hU
      (z₀ := 2) ?_ ?_
    · -- 2 ∈ {1}ᶜ
      simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
      norm_num
    · exact hagree.eventuallyEq_of_mem (hopen.mem_nhds hz2)
  exact heq hs

#print axioms etaTerm_succ
#print axioms etaLFunction_eq_etaSeries
#print axioms zeta_factor_analytic
#print axioms etaLFunction_eq_factor_zeta

end RHFormalization
