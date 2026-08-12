/-
DENSE SCHEDULE — Brick D3b: THE SHARP MASS (Lemma 1 complete).
`S1mass R ≤ 6(log4+4)·√(2^(K+1))` whenever `e^R ≤ 2^(K+1)`.
Route: S1mass (codes) = pairs-sum of weightReal; weightReal = Λ(natValue)/√natValue
on valid pairs; natValue injects the active set into Ioc 1 (2^(K+1));
extend by nonnegativity; apply D3a (cumulative_weighted_shell_bound).
Replaces the weak `S1mass_le : ≤ 2(e^R+2)` with the √-rate the dense
defect (D4) and dense window (D5) require. No PNT.
-/

import RHFormalization.DenseCumulativeMass
import RHFormalization.AdmissibleS1MassBound
import RHFormalization.AdaptiveStageMassBridge

set_option autoImplicit false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace RHFormalization

noncomputable section

open ArithmeticFunction Finset Real
open scoped BigOperators Classical

/-- On valid pairs the frozen weight is exactly `Λ(natValue)/√natValue`. -/
theorem weightReal_eq_vonMangoldt_div_sqrt (q : PrimePowerPair)
    (hq : IsPrimePowerPair q) :
    q.weightReal = vonMangoldt q.natValue / Real.sqrt (q.natValue : ℝ) := by
  have hΛ : vonMangoldt q.natValue = Real.log q.p := by
    simp only [PrimePowerPair.natValue]
    rw [ArithmeticFunction.vonMangoldt_apply_pow hq.2.ne',
        ArithmeticFunction.vonMangoldt_apply_prime hq.1]
  unfold PrimePowerPair.weightReal
  rw [if_pos hq, hΛ]

/-- Codes-sum to pairs-sum (mirror of `adaptiveStageMass_eq_S1mass`'s move). -/
theorem S1mass_eq_pairs_sum (R : ℝ) :
    S1mass R = ∑ q ∈ activePrimePowerPairsCenterBelow R, q.weightReal := by
  classical
  have hcodes : activePrimePowerCodesCenterBelow R
      = (activePrimePowerPairsCenterBelow R).image ppCode := rfl
  unfold S1mass
  rw [hcodes, Finset.sum_image]
  · refine Finset.sum_congr rfl (fun q _hq => ?_)
    simp [ppWeightReal, ppDecode_ppCode, PrimePowerPair.weightC]
  · intro a _ b _ h
    have h2 := congrArg ppDecode h
    simpa [ppDecode_ppCode] using h2

/-- **D3b — THE SHARP MASS.** -/
theorem S1mass_le_cumulative (R : ℝ) (K : ℕ)
    (hRK : Real.exp R ≤ (2:ℝ)^(K+1)) :
    S1mass R ≤ 6 * (Real.log 4 + 4) * Real.sqrt ((2:ℝ)^(K+1)) := by
  classical
  rw [S1mass_eq_pairs_sum]
  -- rewrite each valid term as Λ(natValue)/√natValue
  have hterms : ∀ q ∈ activePrimePowerPairsCenterBelow R,
      q.weightReal = vonMangoldt q.natValue / Real.sqrt (q.natValue : ℝ) := by
    intro q hq
    rw [activePrimePowerPairsCenterBelow_mem] at hq
    exact weightReal_eq_vonMangoldt_div_sqrt q hq.1
  rw [Finset.sum_congr rfl hterms]
  -- push through the natValue injection into Ioc 1 (2^(K+1))
  have hinj : ∀ a ∈ activePrimePowerPairsCenterBelow R,
      ∀ b ∈ activePrimePowerPairsCenterBelow R,
      a.natValue = b.natValue → a = b := by
    intro a ha b hb hval
    rw [activePrimePowerPairsCenterBelow_mem] at ha hb
    have hva : IsPrimePowerPair a := ha.1
    have hvb : IsPrimePowerPair b := hb.1
    simp only [PrimePowerPair.natValue] at hval
    have hpp : a.p = b.p := by
      have h1 : a.p ∣ b.p ^ b.m := by
        rw [← hval]; exact dvd_pow_self a.p hva.2.ne'
      have h2 : a.p ∣ b.p := hva.1.dvd_of_dvd_pow h1
      exact (Nat.prime_dvd_prime_iff_eq hva.1 hvb.1).mp h2
    have hmm : a.m = b.m := by
      apply Nat.pow_right_injective hva.1.two_le
      show a.p ^ a.m = a.p ^ b.m
      rw [hval, hpp]
    first
      | exact Prod.ext hpp hmm
      | exact Prod.ext_iff.mpr ⟨hpp, hmm⟩
      | (obtain ⟨ap, am⟩ := a; obtain ⟨bp, bm⟩ := b;
         simp_all [PrimePowerPair.p, PrimePowerPair.m])
  have himg : ∑ q ∈ activePrimePowerPairsCenterBelow R,
        vonMangoldt q.natValue / Real.sqrt (q.natValue : ℝ)
      = ∑ m ∈ (activePrimePowerPairsCenterBelow R).image
          (fun q => q.natValue),
          vonMangoldt m / Real.sqrt (m : ℝ) := by
    rw [Finset.sum_image hinj]
  rw [himg]
  -- the image sits inside Ioc 1 (2^(K+1))
  have hsub : (activePrimePowerPairsCenterBelow R).image
      (fun q : PrimePowerPair => q.natValue) ⊆ Finset.Ioc 1 (2^(K+1)) := by
    intro m hm
    rw [Finset.mem_image] at hm
    obtain ⟨q, hq, rfl⟩ := hm
    rw [activePrimePowerPairsCenterBelow_mem] at hq
    have hvalid : IsPrimePowerPair q := hq.1
    have hcenter : q.center ≤ R := hq.2
    have h2 : (2 : ℕ) ≤ q.natValue := by
      simp only [PrimePowerPair.natValue]
      calc (2 : ℕ) ≤ q.p := hvalid.1.two_le
        _ ≤ q.p ^ q.m := Nat.le_self_pow hvalid.2.ne' q.p
    have hpos : (0 : ℝ) < ((q.natValue : ℕ) : ℝ) := by
      have h0 : 0 < q.natValue := lt_of_lt_of_le (by norm_num) h2
      exact_mod_cast h0
    have hlog : Real.log ((q.natValue : ℕ) : ℝ) ≤ R := by
      first
        | exact hcenter
        | simpa [PrimePowerPair.center] using hcenter
    have hpow_le : ((q.natValue : ℕ) : ℝ) ≤ Real.exp R := by
      calc ((q.natValue : ℕ) : ℝ)
          = Real.exp (Real.log ((q.natValue : ℕ) : ℝ)) := (Real.exp_log hpos).symm
        _ ≤ Real.exp R := Real.exp_le_exp.mpr hlog
    have hle : ((q.natValue : ℕ) : ℝ) ≤ ((2:ℝ))^(K+1) :=
      le_trans hpow_le hRK
    rw [Finset.mem_Ioc]
    constructor
    · omega
    · have h2K : ((2:ℝ))^(K+1) = (((2:ℕ)^(K+1) : ℕ) : ℝ) := by push_cast; ring
      rw [h2K] at hle
      exact_mod_cast hle
  have hext : ∑ m ∈ (activePrimePowerPairsCenterBelow R).image
        (fun q : PrimePowerPair => q.natValue),
        vonMangoldt m / Real.sqrt (m : ℝ)
      ≤ ∑ m ∈ Finset.Ioc 1 (2^(K+1)), vonMangoldt m / Real.sqrt (m : ℝ) := by
    apply Finset.sum_le_sum_of_subset_of_nonneg hsub
    intro m _ _
    apply div_nonneg vonMangoldt_nonneg (Real.sqrt_nonneg _)
  exact le_trans hext (cumulative_weighted_shell_bound K)

#print axioms weightReal_eq_vonMangoldt_div_sqrt
#print axioms S1mass_eq_pairs_sum
#print axioms S1mass_le_cumulative

end

end RHFormalization
