import RHFormalization.AdmissibleFirstOrderDiagonal
import RHFormalization.AdmissibleResolventWeightSum
import RHFormalization.AdmissibleColumnNormBound
import RHFormalization.AdmissibleS1MassBound
import RHFormalization.AdmissibleEigenvalueFloor
import RHFormalization.GalerkinFConvergence

/-!
# Gate 2 (RESOLVED BY VANISHING): the FirstOrderWindow limit is 0

Via brick 4a's diagonal form, the entry bound 4b-iii(b), and the
resolvent-weight sum 4b-iii(a):

`‖FirstOrderWindow n s‖ ≤ (1/2L)·((2/L)S₁)·(C₀²L) = C₀²·S₁/L ≤ 6C₀²/(n+2)²`

so at the slow cutoff the density-normalized first-order trace tends to 0
uniformly on Ω-compacts.  The manuscript anchor `S(t,R)/(2L)` is not merely
bounded along the admissible schedule — it vanishes.  Consequence:
`FHadm = FHadmFree`; the arithmetic content of the overlap identity is
carried by the B-slot (`admissible_hB`, banked) and Front R.
-/

set_option autoImplicit false

namespace RHFormalization

noncomputable section

open Complex

open scoped BigOperators Classical

/-- **Gate 2, pointwise master bound**: the first-order window is controlled
by `(1/2L)·((2/L)S₁)·(C₀²L)`. -/
theorem FirstOrderWindow_norm_le (n : ℕ) (s : ℂ) {C₀ : ℝ} (hC₀ : 0 ≤ C₀)
    (hbound : ∀ lam : ℝ, 0 ≤ lam →
        ‖(s + (SupVConst : ℂ) + (lam : ℂ))⁻¹‖ ≤ C₀ * (1 + lam)⁻¹) :
    ‖FirstOrderWindow n s‖
      ≤ 1 / (2 * admL n)
          * (2 / admL n * S1mass (admR n) * (C₀ ^ 2 * admL n)) := by
  have hL : (0 : ℝ) < admL n := admL_pos n
  have h2L : (0 : ℝ) < 2 * admL n := by positivity
  have hdens : ‖admDensityC n‖ = 1 / (2 * admL n) := by
    unfold admDensityC
    first
      | rw [Complex.norm_real, Real.norm_eq_abs,
            abs_of_pos (one_div_pos.mpr h2L)]
      | rw [Complex.norm_ofReal, abs_of_pos (one_div_pos.mpr h2L)]
  rw [FirstOrderWindow_eq_diag_sum n s, norm_neg, norm_mul, hdens]
  refine mul_le_mul_of_nonneg_left ?_ (le_of_lt (one_div_pos.mpr h2L))
  have hentry : ∀ m : Fin (admN n),
      ‖(galerkinVC (N := admN n) 1
          (activePrimePowerCodesCenterBelow (admR n)) ppWeightReal
          (admL n)) m m‖
        ≤ 2 / admL n * S1mass (admR n) := by
    intro m
    have hVC : (galerkinVC (N := admN n) 1
          (activePrimePowerCodesCenterBelow (admR n)) ppWeightReal
          (admL n)) m m
        = ((galerkinV (N := admN n) 1
            (activePrimePowerCodesCenterBelow (admR n)) ppWeightReal
            (admL n) m m : ℝ) : ℂ) := rfl
    rw [hVC]
    first
      | (rw [Complex.norm_real]
         exact abs_galerkinV_entry_le_S1 (admR n) (admL n) hL m m)
      | (rw [Complex.norm_real, Real.norm_eq_abs]
         exact abs_galerkinV_entry_le_S1 (admR n) (admL n) hL m m)
      | (rw [Complex.norm_ofReal]
         exact abs_galerkinV_entry_le_S1 (admR n) (admL n) hL m m)
  have hres := freeMu_resolvent_sq_sum_le (admN n) (admL n) hL
      (s + (SupVConst : ℂ)) C₀ hC₀ hbound
  have hstep : ∀ m : Fin (admN n),
      ‖(galerkinVC (N := admN n) 1
          (activePrimePowerCodesCenterBelow (admR n)) ppWeightReal
          (admL n)) m m
        * (((s + (SupVConst : ℂ))
            + ((galerkinFreeMu (admN n) (admL n) m : ℝ) : ℂ))⁻¹) ^ 2‖
      ≤ 2 / admL n * S1mass (admR n)
          * ‖((s + (SupVConst : ℂ))
              + ((galerkinFreeMu (admN n) (admL n) m : ℝ) : ℂ))⁻¹‖ ^ 2 := by
    intro m
    rw [norm_mul, norm_pow]
    exact mul_le_mul_of_nonneg_right (hentry m) (by positivity)
  refine le_trans (norm_sum_le _ _) ?_
  refine le_trans (Finset.sum_le_sum (fun m _ => hstep m)) ?_
  rw [← Finset.mul_sum]
  exact mul_le_mul_of_nonneg_left hres
    (mul_nonneg (by positivity) (S1mass_nonneg _))

/-- Pure algebra: the Gate 2 master RHS collapses to `6c²/x`. -/
theorem fow_master_collapse (x S c : ℝ) (hx1 : 1 ≤ x) (hc : 0 ≤ c)
    (hS0 : 0 ≤ S) (hS : S ≤ 6 * x) :
    1 / (2 * x ^ 3) * (2 / x ^ 3 * S * (c ^ 2 * x ^ 3)) ≤ 6 * c ^ 2 / x := by
  have hx : (0 : ℝ) < x := lt_of_lt_of_le one_pos hx1
  have hxne : x ≠ 0 := ne_of_gt hx
  have heq : 1 / (2 * x ^ 3) * (2 / x ^ 3 * S * (c ^ 2 * x ^ 3))
      = S * c ^ 2 / x ^ 3 := by
    first
      | (field_simp; ring)
      | field_simp
      | (field_simp; ring_nf)
  rw [heq]
  have hA : (0 : ℝ) ≤ (6 * x - S) * (c ^ 2 * x) :=
    mul_nonneg (sub_nonneg.mpr hS) (mul_nonneg (sq_nonneg c) hx.le)
  have hB : (0 : ℝ) ≤ 6 * c ^ 2 * (x ^ 2 * (x - 1)) :=
    mul_nonneg (by positivity) (mul_nonneg (sq_nonneg x) (sub_nonneg.mpr hx1))
  have h1 : S * c ^ 2 * x ≤ 6 * c ^ 2 * x ^ 2 := by nlinarith [hA]
  have h2 : 6 * c ^ 2 * x ^ 2 ≤ 6 * c ^ 2 * x ^ 3 := by nlinarith [hB]
  first
    | (rw [div_le_div_iff (by positivity) hx]; nlinarith [h1, h2])
    | (rw [div_le_div_iff₀ (by positivity) hx]; nlinarith [h1, h2])

/-- Schedule form of the S₁ bound, linear version: `S₁(admR n) ≤ 6(n+2)`. -/
theorem S1mass_admR_le_linear (n : ℕ) :
    S1mass (admR n) ≤ 6 * ((n : ℝ) + 2) := by
  have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  have h12 : (1 : ℝ) ≤ (n : ℝ) + 2 := by linarith
  have hlog0 : (0 : ℝ) ≤ Real.log ((n : ℝ) + 2) := Real.log_nonneg h12
  have hR : admR n ≤ Real.log ((n : ℝ) + 2) := by
    first
      | (unfold admR; linarith)
      | (simp only [admR]; linarith)
  have hexp : Real.exp (admR n) ≤ (n : ℝ) + 2 := by
    calc Real.exp (admR n)
        ≤ Real.exp (Real.log ((n : ℝ) + 2)) := Real.exp_le_exp.mpr hR
      _ = (n : ℝ) + 2 := Real.exp_log (by linarith)
  have h1 := S1mass_le (admR n)
  linarith

/-- **Gate 2, K-uniform decay**: `‖FirstOrderWindow n s‖ ≤ C/(n+2)` on
every Ω-compact. -/
theorem FirstOrderWindow_uniform_bound
    (K : Set ℂ) (hK : IsCompact K) (hKO : K ⊆ Ω) :
    ∃ C : ℝ, 0 < C ∧ ∀ (n : ℕ), ∀ s ∈ K,
      ‖FirstOrderWindow n s‖ ≤ C / ((n : ℝ) + 2) := by
  obtain ⟨C₀, hC₀pos, hC₀⟩ := inv_norm_le_on_compact K hK hKO
  refine ⟨6 * C₀ ^ 2, by positivity, fun n s hs => ?_⟩
  have hbound' : ∀ lam : ℝ, 0 ≤ lam →
      ‖(s + (SupVConst : ℂ) + (lam : ℂ))⁻¹‖ ≤ C₀ * (1 + lam)⁻¹ := by
    intro lam hlam
    have h1 := hC₀ s hs (SupVConst + lam)
      (add_nonneg SupVConst_nonneg_adm hlam)
    have hcast : s + ((SupVConst + lam : ℝ) : ℂ)
        = s + (SupVConst : ℂ) + (lam : ℂ) := by
      push_cast
      ring
    rw [hcast] at h1
    refine le_trans h1 (mul_le_mul_of_nonneg_left ?_ hC₀pos.le)
    have hpos : (0 : ℝ) < 1 + lam := by linarith
    have hle : (1 : ℝ) + lam ≤ 1 + (SupVConst + lam) := by
      have hsv := SupVConst_nonneg_adm
      linarith
    first
      | gcongr
      | exact inv_le_inv_of_le hpos hle
  refine le_trans (FirstOrderWindow_norm_le n s hC₀pos.le hbound') ?_
  have hLeq : admL n = ((n : ℝ) + 2) ^ 3 := by
    first
      | rfl
      | (unfold admL; ring)
      | simp [admL]
  rw [hLeq]
  have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  exact fow_master_collapse ((n : ℝ) + 2) (S1mass (admR n)) C₀
    (by linarith) hC₀pos.le (S1mass_nonneg _) (S1mass_admR_le_linear n)

/-- **GATE 2 CLOSED (by vanishing), eps-N form**: the first-order window
tends to 0 uniformly on Ω-compacts along the admissible schedule. -/
theorem FirstOrderWindow_epsN
    (K : Set ℂ) (hK : IsCompact K) (hKO : K ⊆ Ω) :
    ∀ ε : ℝ, 0 < ε → ∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n → ∀ s ∈ K,
      ‖FirstOrderWindow n s‖ ≤ ε := by
  intro ε hε
  obtain ⟨C, hCpos, hC⟩ := FirstOrderWindow_uniform_bound K hK hKO
  refine ⟨⌈C / ε⌉₊, fun n hn s hs => ?_⟩
  refine le_trans (hC n s hs) ?_
  have hx2 : (0 : ℝ) < (n : ℝ) + 2 := by positivity
  have h1 : C / ε ≤ (⌈C / ε⌉₊ : ℝ) := Nat.le_ceil _
  have h2 : ((⌈C / ε⌉₊ : ℕ) : ℝ) ≤ (n : ℝ) := Nat.cast_le.mpr hn
  have h3 : C / ε ≤ (n : ℝ) := le_trans h1 h2
  have h4 : C ≤ (n : ℝ) * ε := by
    first
      | exact (div_le_iff hε).mp h3
      | exact (div_le_iff₀ hε).mp h3
  first
    | (rw [div_le_iff hx2]; nlinarith [hε.le])
    | (rw [div_le_iff₀ hx2]; nlinarith [hε.le])

#print axioms FirstOrderWindow_norm_le
#print axioms fow_master_collapse
#print axioms S1mass_admR_le_linear
#print axioms FirstOrderWindow_uniform_bound
#print axioms FirstOrderWindow_epsN

end

end RHFormalization
