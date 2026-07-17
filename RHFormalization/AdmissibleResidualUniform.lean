import RHFormalization.AdmissibleResidualAssembly
import RHFormalization.AdmissibleEigenvalueFloor
import RHFormalization.GalerkinFConvergence

/-!
# Brick 4b-iv (uniform form) — BRICK 4b CLOSED

K-uniform decay of the second-resolvent residual along the admissible
schedule: `‖SecondResolventResidual n s‖ ≤ C(K)/(n+2)` for all `s ∈ K`,
hence `→ 0` uniformly on Ω-compacts (eps-N form).  Hypotheses of the
pointwise master bound are discharged from `inv_norm_le_on_compact`,
`exists_uniform_lower_bound_on_compact`, and the admissible eigenvalue
floor; the schedule collapse uses `exp(admR n)² = n+2`.
-/

set_option autoImplicit false

namespace RHFormalization

noncomputable section

open Complex

open scoped BigOperators Classical

/-- Schedule form of the S₁ bound: `S₁(admR n)² ≤ 36·(n+2)`. -/
theorem S1mass_admR_sq_le (n : ℕ) :
    (S1mass (admR n)) ^ 2 ≤ 36 * ((n : ℝ) + 2) := by
  have h1 := S1mass_le (admR n)
  have hS0 := S1mass_nonneg (admR n)
  have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  have h12 : (1 : ℝ) ≤ (n : ℝ) + 2 := by linarith
  have hlog : (0 : ℝ) ≤ Real.log ((n : ℝ) + 2) := Real.log_nonneg h12
  have hR0 : 0 ≤ admR n := by
    first
      | (unfold admR; linarith)
      | (simp only [admR]; linarith)
  have hexp1 : 1 ≤ Real.exp (admR n) := by
    first
      | exact Real.one_le_exp hR0
      | exact Real.one_le_exp_iff.mpr hR0
      | (rw [show (1 : ℝ) = Real.exp 0 from Real.exp_zero.symm]
         exact Real.exp_le_exp.mpr hR0)
  have hexpsq : Real.exp (admR n) ^ 2 = (n : ℝ) + 2 := by
    rw [sq, ← Real.exp_add]
    have hh : admR n + admR n = Real.log ((n : ℝ) + 2) := by
      unfold admR; ring
    rw [hh, Real.exp_log (by positivity)]
  have hS6 : S1mass (admR n) ≤ 6 * Real.exp (admR n) := by
    linarith
  have hint1 : (0 : ℝ) ≤ (6 * Real.exp (admR n) - S1mass (admR n))
      * S1mass (admR n) :=
    mul_nonneg (sub_nonneg.mpr hS6) hS0
  have hint2 : (0 : ℝ) ≤ (6 * Real.exp (admR n) - S1mass (admR n))
      * Real.exp (admR n) :=
    mul_nonneg (sub_nonneg.mpr hS6) (Real.exp_pos (admR n)).le
  have hfin : (S1mass (admR n)) ^ 2 ≤ 36 * (Real.exp (admR n)) ^ 2 := by
    nlinarith [hint1, hint2]
  calc (S1mass (admR n)) ^ 2
      ≤ 36 * (Real.exp (admR n)) ^ 2 := hfin
    _ = 36 * ((n : ℝ) + 2) := by rw [hexpsq]

/-- Pure algebra: the master RHS at the schedule collapses to
`72·d⁻¹·c²/x` once `S² ≤ 36x`. -/
theorem residual_master_collapse (x S d c : ℝ) (hx : 0 < x) (hd : 0 < d)
    (hc : 0 ≤ c) (hS : 0 ≤ S) (hSsq : S ^ 2 ≤ 36 * x) :
    1 / (2 * x ^ 3) * (d⁻¹ * (c ^ 2 * x ^ 3 * (x ^ 4 * ((2 / x ^ 3) * S) ^ 2)))
      ≤ 72 * d⁻¹ * c ^ 2 / x := by
  have hxne : x ≠ 0 := ne_of_gt hx
  have hdne : d ≠ 0 := ne_of_gt hd
  have heq : 1 / (2 * x ^ 3)
        * (d⁻¹ * (c ^ 2 * x ^ 3 * (x ^ 4 * ((2 / x ^ 3) * S) ^ 2)))
      = 2 * d⁻¹ * c ^ 2 * (S ^ 2 / x ^ 2) := by
    first
      | (field_simp; ring)
      | (field_simp [hxne, hdne]; ring)
      | (field_simp [hxne, hdne])
      | field_simp
  rw [heq]
  have hA : S ^ 2 / x ^ 2 ≤ 36 * x / x ^ 2 := by
    rw [div_eq_mul_inv, div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_right hSsq (inv_nonneg.mpr (by positivity))
  have hB : 36 * x / x ^ 2 = 36 / x := by
    first
      | (field_simp [hxne]; ring)
      | (field_simp [hxne])
      | (field_simp; ring)
      | field_simp
  have hnn : (0 : ℝ) ≤ 2 * d⁻¹ * c ^ 2 :=
    mul_nonneg (mul_nonneg (by norm_num) (inv_pos.mpr hd).le) (sq_nonneg c)
  calc 2 * d⁻¹ * c ^ 2 * (S ^ 2 / x ^ 2)
      ≤ 2 * d⁻¹ * c ^ 2 * (36 / x) :=
        mul_le_mul_of_nonneg_left (le_trans hA (le_of_eq hB)) hnn
    _ = 72 * d⁻¹ * c ^ 2 / x := by ring

/-- **BRICK 4b-iv, uniform form.** On every compact `K ⊆ Ω` there is a
single constant with `‖SecondResolventResidual n s‖ ≤ C/(n+2)` for all
stages and all `s ∈ K`. -/
theorem SecondResolventResidual_uniform_bound
    (K : Set ℂ) (hK : IsCompact K) (hKO : K ⊆ Ω) :
    ∃ C : ℝ, 0 < C ∧ ∀ (n : ℕ), ∀ s ∈ K,
      ‖SecondResolventResidual n s‖ ≤ C / ((n : ℝ) + 2) := by
  obtain ⟨δ, hδpos, hδ⟩ := exists_uniform_lower_bound_on_compact K hK hKO
  obtain ⟨C₀, hC₀pos, hC₀⟩ := inv_norm_le_on_compact K hK hKO
  refine ⟨72 * δ⁻¹ * C₀ ^ 2,
    mul_pos (mul_pos (by norm_num) (inv_pos.mpr hδpos)) (pow_pos hC₀pos 2),
    fun n s hs => ?_⟩
  have hlow' : ∀ i, δ ≤ ‖s + (SupVConst : ℂ)
      + ((admPerturbedLam n i : ℝ) : ℂ)‖ := by
    intro i
    have hnn : 0 ≤ admPerturbedLam n i := by
      unfold admPerturbedLam
      refine admissibleEigenvalue_nonneg (admL n) (admL_pos n) _ _
        (fun k => ?_) i
      first
        | exact galerkinFreeMu_nonneg _ _ k
        | (unfold galerkinFreeMu; positivity)
        | exact sq_nonneg _
    have hlam : (0 : ℝ) ≤ SupVConst + admPerturbedLam n i :=
      add_nonneg SupVConst_nonneg_adm hnn
    have h := hδ s hs (SupVConst + admPerturbedLam n i) hlam
    have hcast : s + ((SupVConst + admPerturbedLam n i : ℝ) : ℂ)
        = s + (SupVConst : ℂ) + ((admPerturbedLam n i : ℝ) : ℂ) := by
      push_cast
      ring
    rw [hcast] at h
    exact h
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
  refine le_trans
    (SecondResolventResidual_norm_le n s hδpos hC₀pos.le hlow' hbound') ?_
  have hL : admL n = ((n : ℝ) + 2) ^ 3 := by
    first
      | rfl
      | (unfold admL; ring)
      | simp [admL]
  have hN : (admN n : ℝ) = ((n : ℝ) + 2) ^ 4 := by
    first
      | (unfold admN; push_cast; ring)
      | (unfold admN; push_cast)
      | (simp only [admN]; push_cast; ring)
  rw [hL, hN]
  exact residual_master_collapse ((n : ℝ) + 2) (S1mass (admR n)) δ C₀
    (by positivity) hδpos hC₀pos.le (S1mass_nonneg _) (S1mass_admR_sq_le n)

/-- **BRICK 4b, eps-N form (DONE)**: the second-resolvent residual tends
to 0 uniformly on Ω-compacts along the admissible schedule — the shape
the three-epsilon prime-layer assembly consumes. -/
theorem SecondResolventResidual_epsN
    (K : Set ℂ) (hK : IsCompact K) (hKO : K ⊆ Ω) :
    ∀ ε : ℝ, 0 < ε → ∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n → ∀ s ∈ K,
      ‖SecondResolventResidual n s‖ ≤ ε := by
  intro ε hε
  obtain ⟨C, hCpos, hC⟩ := SecondResolventResidual_uniform_bound K hK hKO
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
  have hgoal : C ≤ ε * ((n : ℝ) + 2) := by nlinarith [hε.le]
  first
    | (rw [div_le_iff hx2]; nlinarith [hε.le])
    | (rw [div_le_iff₀ hx2]; nlinarith [hε.le])

#print axioms S1mass_admR_sq_le
#print axioms residual_master_collapse
#print axioms SecondResolventResidual_uniform_bound
#print axioms SecondResolventResidual_epsN

end

end RHFormalization
