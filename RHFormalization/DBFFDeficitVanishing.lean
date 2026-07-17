import RHFormalization.DBFFDeficitCompactBound
import RHFormalization.AdmissibleS1MassBound

/-!
# DBFFDeficitVanishing — D.MR.5 window sector closed on Ω-compacts

ROUTE CARD
1. Target: D.MR.5 for the corrected provider (window deficit → 0 uniformly on
   Ω-compacts — the parabola-side extension of Brick A). Consumer: provider
   ε-field / D.MASTER-RESIDUAL assembly.
2. Objects: deficitWeightMass, S1mass (banked S1mass_le ≤ 2(e^R+2)).
3-5. No raw B on Ω; true outright. 6. D.CANONICAL-WINDOW/D.MR.5.
7. Consumer: corrected-provider instantiation.
-/

set_option autoImplicit false

namespace RHFormalization

noncomputable section

open Complex Filter

open scoped Topology BigOperators

/-- The deficit weight mass obeys the elementary count bound: each weight is
at most 2 (mirror of `abs_ppWeightReal_le_two` on the pairs side), and the
active pair count is at most `⌈e^R⌉ + 1`. -/
theorem deficitWeightMass_le (n : ℕ) :
    deficitWeightMass n ≤ 2 * (Real.exp (admR n) + 2) := by
  classical
  have hterm : ∀ q ∈ activePrimePowerPairsCenterBelow (admR n),
      ‖q.weightC‖ ≤ (2 : ℝ) := by
    intro q hq
    have h1 : ‖q.weightC‖ = |ppWeightReal (ppCode q)| := by
      rw [norm_weightC_eq_abs_weightReal]
      congr 1
      show q.weightReal = ppWeightReal (ppCode q)
      unfold ppWeightReal
      rw [ppDecode_ppCode]
      first
        | rfl
        | (rw [show ((q.weightC).re) = q.weightReal from by
             unfold PrimePowerPair.weightC
             simp])
        | (unfold PrimePowerPair.weightC
           simp)
    rw [h1]
    exact abs_ppWeightReal_le_two (ppCode q)
  have hsum : deficitWeightMass n
      ≤ ((activePrimePowerPairsCenterBelow (admR n)).card : ℝ) * 2 := by
    unfold deficitWeightMass
    have h := Finset.sum_le_sum hterm
    simpa [Finset.sum_const, nsmul_eq_mul] using h
  have hcard : ((activePrimePowerPairsCenterBelow (admR n)).card : ℝ)
      ≤ Real.exp (admR n) + 2 := by
    have h1 : (activePrimePowerPairsCenterBelow (admR n)).card
        ≤ ⌈Real.exp (admR n)⌉₊ + 1 := by
      calc (activePrimePowerPairsCenterBelow (admR n)).card
          = (concretePrimePowerBelowCutoff (admR n)).card := by
            rw [activePairs_eq_concrete]
        _ ≤ ⌈Real.exp (admR n)⌉₊ + 1 := card_concretePrimePowerBelowCutoff_le _
    have h2 : ((⌈Real.exp (admR n)⌉₊ : ℕ) : ℝ) < Real.exp (admR n) + 1 :=
      Nat.ceil_lt_add_one (Real.exp_pos _).le
    have h3 : ((activePrimePowerPairsCenterBelow (admR n)).card : ℝ)
        ≤ ((⌈Real.exp (admR n)⌉₊ + 1 : ℕ) : ℝ) := by exact_mod_cast h1
    push_cast at h3
    linarith
  have hm0 : (0:ℝ) ≤ deficitWeightMass n :=
    Finset.sum_nonneg fun q _ => norm_nonneg _
  calc deficitWeightMass n
      ≤ ((activePrimePowerPairsCenterBelow (admR n)).card : ℝ) * 2 := hsum
    _ ≤ (Real.exp (admR n) + 2) * 2 :=
        mul_le_mul_of_nonneg_right hcard (by norm_num)
    _ = 2 * (Real.exp (admR n) + 2) := by ring

/-- exp(admR n) = √(n+2). -/
theorem exp_admR (n : ℕ) : Real.exp (admR n) = Real.sqrt ((n : ℝ) + 2) := by
  show Real.exp (Real.log ((n : ℝ) + 2) / 2) = Real.sqrt ((n : ℝ) + 2)
  have hp : (0 : ℝ) < (n : ℝ) + 2 := by positivity
  rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos hp]
  ring_nf

/-- **D.MR.5 closed**: the window deficit vanishes uniformly on Ω-compacts. -/
theorem BcorrWin_vanishes_on_compacts
    (K : Set ℂ) (hK : IsCompact K) (hKO : K ⊆ Ω) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop, ∀ s ∈ K, ‖BcorrWin n s‖ ≤ ε := by
  obtain ⟨C, hC, hbound⟩ := BcorrWin_norm_le_on_compact K hK hKO
  intro ε hε
  have hten : Tendsto (fun n : ℕ =>
      admR n / (2 * admL n) * deficitWeightMass n * C) atTop (𝓝 0) := by
    have h0 : ∀ n : ℕ, (0:ℝ) ≤ admR n / (2 * admL n) * deficitWeightMass n * C := by
      intro n
      have hL2 : (0 : ℝ) < 2 * admL n := by have := admL_pos' n; linarith
      have hm0 : (0:ℝ) ≤ deficitWeightMass n :=
        Finset.sum_nonneg fun q _ => norm_nonneg _
      have := div_nonneg (admR_pos n).le hL2.le
      positivity
    have hb : ∀ᶠ n in atTop, admR n / (2 * admL n) * deficitWeightMass n * C
        ≤ 8 * C / ((n : ℝ) + 2) := by
      filter_upwards with n
      have hp : (0 : ℝ) < (n : ℝ) + 2 := by positivity
      have hL2 : (0 : ℝ) < 2 * admL n := by have := admL_pos' n; linarith
      have hmass : deficitWeightMass n ≤ 2 * (Real.sqrt ((n:ℝ)+2) + 2) := by
        have := deficitWeightMass_le n
        rwa [exp_admR] at this
      have hsq : Real.sqrt ((n:ℝ)+2) ≤ (n:ℝ) + 2 := by
        have h2 : (1:ℝ) ≤ (n:ℝ) + 2 := by
          have : (0:ℝ) ≤ (n:ℝ) := Nat.cast_nonneg n
          linarith
        calc Real.sqrt ((n:ℝ)+2) ≤ Real.sqrt (((n:ℝ)+2)^2) := by
              apply Real.sqrt_le_sqrt
              nlinarith
          _ = (n:ℝ) + 2 := Real.sqrt_sq hp.le
      have hmass2 : deficitWeightMass n ≤ 4 * ((n:ℝ) + 2) := by
        have h2 : (2:ℝ) ≤ (n:ℝ) + 2 := by
          have : (0:ℝ) ≤ (n:ℝ) := Nat.cast_nonneg n
          linarith
        nlinarith [hmass, hsq]
      have hratio : admR n / (2 * admL n) ≤ 2 / ((n:ℝ)+2)^2 := by
        show Real.log ((n:ℝ)+2) / 2 / (2 * ((n:ℝ)+2)^3) ≤ 2 / ((n:ℝ)+2)^2
        have hlog : Real.log ((n:ℝ)+2) ≤ (n:ℝ)+2 := by
          first
            | exact Real.log_le_self hp.le
            | (have h := Real.log_le_sub_one_of_pos hp; linarith)
        first
          | (rw [div_le_div_iff₀ (by positivity) (by positivity)]
             nlinarith [mul_le_mul_of_nonneg_right hlog (sq_nonneg ((n:ℝ)+2)),
               sq_nonneg ((n:ℝ)+2), hp.le,
               mul_pos (mul_pos hp hp) hp])
          | (rw [div_le_div_iff (by positivity) (by positivity)]
             nlinarith [mul_le_mul_of_nonneg_right hlog (sq_nonneg ((n:ℝ)+2)),
               sq_nonneg ((n:ℝ)+2), hp.le,
               mul_pos (mul_pos hp hp) hp])
      have hm0 : (0:ℝ) ≤ deficitWeightMass n :=
        Finset.sum_nonneg fun q _ => norm_nonneg _
      calc admR n / (2 * admL n) * deficitWeightMass n * C
          ≤ (2 / ((n:ℝ)+2)^2) * (4 * ((n:ℝ)+2)) * C := by
            apply mul_le_mul_of_nonneg_right _ hC.le
            apply mul_le_mul hratio hmass2 hm0 (by positivity)
        _ = 8 * C / ((n:ℝ)+2) := by field_simp; ring
    have hlim : Tendsto (fun n : ℕ => 8 * C / ((n : ℝ) + 2)) atTop (𝓝 0) := by
      have h1 : Tendsto (fun n : ℕ => (n : ℝ) + 2) atTop atTop := by
        apply tendsto_atTop_add_const_right
        first
          | exact tendsto_natCast_atTop_atTop
          | exact tendsto_nat_cast_atTop_atTop
      simpa using h1.inv_tendsto_atTop.const_mul (8 * C)
    exact squeeze_zero' (Filter.Eventually.of_forall h0) hb hlim
  have := (Metric.tendsto_atTop.mp hten) ε hε
  obtain ⟨N, hN⟩ := this
  filter_upwards [Filter.eventually_ge_atTop N] with n hn
  intro s hs
  have h1 := hbound n s hs
  have h2 := hN n hn
  rw [Real.dist_eq, sub_zero] at h2
  have h3 : admR n / (2 * admL n) * deficitWeightMass n * C < ε := by
    have := abs_lt.mp h2
    linarith [this.2]
  linarith

#print axioms deficitWeightMass_le
#print axioms exp_admR
#print axioms BcorrWin_vanishes_on_compacts

end

end RHFormalization
