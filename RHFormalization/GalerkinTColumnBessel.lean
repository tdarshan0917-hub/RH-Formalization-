import RHFormalization.BddMeasMulIntegrable
import RHFormalization.DirichletEigenfunOrthogonal
import RHFormalization.DirichletEigenfunNorm
import RHFormalization.GreenBesselFinite
import RHFormalization.GalerkinDisplacementKernel

/-!
# RHFormalization.GalerkinTColumnBessel
**Ledger item 3a: the N-free column ℓ² bound for the translation matrix.**
`Σ_{m∈S} TmatrixElement(1,a,m+1,n)² ≤ 1/2`, uniform in N, a, n.
Route: T-column entries are the sine coefficients of the windowed
translate `g = φ_n^{win}(·−a)`; Bessel via `0 ≤ ∫(g − Σ 2c_m φ_{m+1})²`,
orthogonality + `∫φ² = 1/2` + `‖g‖² ≤ 1`. Integrability: the banked
windowed primitive + the product primitive.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace RHFormalization

noncomputable section

open Real intervalIntegral MeasureTheory

/-- The column generator at L=1. -/
noncomputable def tColGen (a : ℝ) (n : ℕ) (x : ℝ) : ℝ :=
  dirichletEigenfunWindowed n 1 (x - a)

theorem tColGen_meas (a : ℝ) (n : ℕ) : Measurable (tColGen a n) := by
  have hcomp : tColGen a n
      = (dirichletEigenfunWindowed n 1) ∘ (fun x : ℝ => x - a) := rfl
  rw [hcomp]
  exact (measurable_dirichletEigenfunWindowed n 1).comp (by fun_prop)

theorem tColGen_abs_le (a : ℝ) (n : ℕ) (x : ℝ) : |tColGen a n x| ≤ 1 :=
  dirichletEigenfunWindowed_abs_le n 1 (x - a)

/-- Coefficient identity: the T-entry is the pairing with the generator. -/
theorem TmatrixElement_eq_pair (a : ℝ) (m n : ℕ) :
    TmatrixElement 1 a m n
      = ∫ x in (0:ℝ)..1, dirichletEigenfun m 1 x * tColGen a n x := rfl

/-- **Item 3a.** -/
theorem TmatrixElement_column_sumSq_le (a : ℝ) (n : ℕ) (S : Finset ℕ) :
    ∑ m ∈ S, TmatrixElement 1 a (m + 1) n ^ 2 ≤ 1 / 2 := by
  set g : ℝ → ℝ := tColGen a n with hgdef
  set c : ℕ → ℝ := fun m => TmatrixElement 1 a (m + 1) n with hcdef
  set P : ℝ → ℝ :=
    fun x => ∑ m ∈ S, 2 * c m * dirichletEigenfun (m + 1) 1 x with hPdef
  have hgm : Measurable g := tColGen_meas a n
  have hgb : ∀ x, |g x| ≤ 1 := tColGen_abs_le a n
  have hPc : Continuous P := by
    rw [hPdef]
    apply continuous_finset_sum
    intro m _
    exact continuous_const.mul (dirichletEigenfun_continuous (m + 1) 1)
  -- integrabilities
  have hg2 : IntervalIntegrable (fun x => g x ^ 2)
      MeasureTheory.volume 0 1 := by
    apply IntervalIntegrable.mono_fun' (g := fun _ : ℝ => (1:ℝ))
    · exact _root_.intervalIntegrable_const
    · exact ((hgm.pow_const 2)).aestronglyMeasurable
    · filter_upwards [self_mem_ae_restrict measurableSet_uIoc] with x _
      rw [Real.norm_eq_abs, abs_pow, sq_abs]
      have h := hgb x
      nlinarith [abs_nonneg (g x), sq_abs (g x),
        mul_le_mul h h (abs_nonneg (g x)) zero_le_one]
  have hPg : IntervalIntegrable (fun x => P x * g x)
      MeasureTheory.volume 0 1 :=
    continuous_mul_bddMeas_intervalIntegrable P g hPc hgm 1 hgb 0 1
  have hP2 : IntervalIntegrable (fun x => P x ^ 2)
      MeasureTheory.volume 0 1 := (hPc.pow 2).intervalIntegrable 0 1
  -- ∫ P·g = 2·Σ c²  (termwise coefficient identity)
  have hPgEq : (∫ x in (0:ℝ)..1, P x * g x) = 2 * ∑ m ∈ S, c m ^ 2 := by
    have hpt : ∀ x : ℝ, P x * g x
        = ∑ m ∈ S, (2 * c m) * (dirichletEigenfun (m + 1) 1 x * g x) := by
      intro x
      rw [hPdef]
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl fun m _ => ?_
      ring
    have hterm_int : ∀ m ∈ S, IntervalIntegrable
        (fun x => (2 * c m) * (dirichletEigenfun (m + 1) 1 x * g x))
        MeasureTheory.volume 0 1 := by
      intro m _
      exact (continuous_mul_bddMeas_intervalIntegrable
        (dirichletEigenfun (m + 1) 1) g
        (dirichletEigenfun_continuous (m + 1) 1) hgm 1 hgb 0 1).const_mul _
    simp_rw [hpt]
    rw [intervalIntegral.integral_finset_sum hterm_int]
    have hterm : ∀ m ∈ S,
        (∫ x in (0:ℝ)..1,
            (2 * c m) * (dirichletEigenfun (m + 1) 1 x * g x))
          = 2 * c m ^ 2 := by
      intro m _
      rw [intervalIntegral.integral_const_mul]
      have : (∫ x in (0:ℝ)..1, dirichletEigenfun (m + 1) 1 x * g x)
          = c m := (TmatrixElement_eq_pair a (m + 1) n).symm
      rw [this]
      ring
    rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum]
  -- ∫ P² = 2·Σ c²  (orthogonality + norm)
  have hP2Eq : (∫ x in (0:ℝ)..1, P x ^ 2) = 2 * ∑ m ∈ S, c m ^ 2 := by
    have hpt : ∀ x : ℝ, P x ^ 2
        = ∑ m ∈ S, ∑ k ∈ S, (2 * c m * (2 * c k))
            * (dirichletEigenfun (m + 1) 1 x * dirichletEigenfun (k + 1) 1 x) := by
      intro x
      rw [hPdef, pow_two, Finset.sum_mul_sum]
      refine Finset.sum_congr rfl fun m _ => Finset.sum_congr rfl fun k _ => ?_
      ring
    have houter : ∀ m ∈ S, IntervalIntegrable
        (fun x => ∑ k ∈ S, (2 * c m * (2 * c k))
            * (dirichletEigenfun (m + 1) 1 x * dirichletEigenfun (k + 1) 1 x))
        MeasureTheory.volume 0 1 := by
      intro m _
      apply Continuous.intervalIntegrable
      apply continuous_finset_sum
      intro k _
      exact continuous_const.mul
        ((dirichletEigenfun_continuous (m + 1) 1).mul
          (dirichletEigenfun_continuous (k + 1) 1))
    simp_rw [hpt]
    rw [intervalIntegral.integral_finset_sum houter]
    have hinner : ∀ m ∈ S,
        (∫ x in (0:ℝ)..1, ∑ k ∈ S, (2 * c m * (2 * c k))
            * (dirichletEigenfun (m + 1) 1 x * dirichletEigenfun (k + 1) 1 x))
          = 2 * c m ^ 2 := by
      intro m hm
      have hin : ∀ k ∈ S, IntervalIntegrable
          (fun x => (2 * c m * (2 * c k))
              * (dirichletEigenfun (m + 1) 1 x * dirichletEigenfun (k + 1) 1 x))
          MeasureTheory.volume 0 1 := by
        intro k _
        exact (continuous_const.mul
          ((dirichletEigenfun_continuous (m + 1) 1).mul
            (dirichletEigenfun_continuous (k + 1) 1))).intervalIntegrable 0 1
      rw [intervalIntegral.integral_finset_sum hin]
      have hzero : ∀ k ∈ S, k ≠ m →
          (∫ x in (0:ℝ)..1, (2 * c m * (2 * c k))
              * (dirichletEigenfun (m + 1) 1 x * dirichletEigenfun (k + 1) 1 x))
            = 0 := by
        intro k _ hkm
        rw [intervalIntegral.integral_const_mul,
            eigenfun_orthogonal (m + 1) (k + 1) 1 one_ne_zero (by omega),
            mul_zero]
      rw [Finset.sum_eq_single_of_mem m hm hzero,
          intervalIntegral.integral_const_mul]
      have hsq : (∫ x in (0:ℝ)..1,
          dirichletEigenfun (m + 1) 1 x * dirichletEigenfun (m + 1) 1 x)
            = 1 / 2 := by
        simp_rw [← pow_two]
        have := integral_dirichletEigenfun_sq (m + 1) 1 one_pos (by omega)
        simpa using this
      rw [hsq]
      ring
    rw [Finset.sum_congr rfl hinner, ← Finset.mul_sum]
  -- ∫ g² ≤ 1
  have hg2le : (∫ x in (0:ℝ)..1, g x ^ 2) ≤ 1 := by
    have hle : (∫ x in (0:ℝ)..1, g x ^ 2) ≤ ∫ _ in (0:ℝ)..1, (1:ℝ) := by
      apply intervalIntegral.integral_mono_on (by norm_num) hg2
        _root_.intervalIntegrable_const
      intro x _
      have h := hgb x
      nlinarith [sq_abs (g x), abs_nonneg (g x)]
    simpa using hle
  -- expand 0 ≤ ∫(g−P)²
  have h0 : (0:ℝ) ≤ ∫ x in (0:ℝ)..1, (g x - P x) ^ 2 := by
    apply intervalIntegral.integral_nonneg (by norm_num)
    intro x _
    exact sq_nonneg _
  have hgP2 : IntervalIntegrable (fun x => 2 * (P x * g x))
      MeasureTheory.volume 0 1 := hPg.const_mul 2
  have hexp : ∀ x : ℝ, (g x - P x) ^ 2
      = g x ^ 2 - 2 * (P x * g x) + P x ^ 2 := by
    intro x
    ring
  have hsplit : (∫ x in (0:ℝ)..1, (g x - P x) ^ 2)
      = (∫ x in (0:ℝ)..1, g x ^ 2)
        - (∫ x in (0:ℝ)..1, 2 * (P x * g x))
        + (∫ x in (0:ℝ)..1, P x ^ 2) := by
    simp_rw [hexp]
    rw [intervalIntegral.integral_add (hg2.sub hgP2) hP2,
        intervalIntegral.integral_sub hg2 hgP2]
  rw [hsplit, intervalIntegral.integral_const_mul, hPgEq, hP2Eq, ] at h0
  linarith [hg2le]

/-- The `galerkinT` column sum-of-squares bound: ≤ 2, N-free. -/
theorem galerkinT_column_sumSq_le {N : ℕ} (a : ℝ) (n : Fin N) :
    ∑ m : Fin N, galerkinT (N := N) 1 a m n ^ 2 ≤ 2 := by
  unfold galerkinT
  have h := TmatrixElement_column_sumSq_le a ((n : ℕ) + 1)
    ((Finset.univ : Finset (Fin N)).image (fun m : Fin N => (m : ℕ)))
  calc ∑ m : Fin N, ((2 / 1) * TmatrixElement 1 a ((m : ℕ) + 1) ((n : ℕ) + 1)) ^ 2
      = 4 * ∑ m : Fin N, TmatrixElement 1 a ((m : ℕ) + 1) ((n : ℕ) + 1) ^ 2 := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun m _ => ?_
        norm_num
        ring
    _ ≤ 4 * (1 / 2) := by
        apply mul_le_mul_of_nonneg_left _ (by norm_num)
        rw [show (∑ m : Fin N,
            TmatrixElement 1 a ((m : ℕ) + 1) ((n : ℕ) + 1) ^ 2)
          = ∑ m ∈ (Finset.univ : Finset (Fin N)).image
              (fun m : Fin N => (m : ℕ)),
              TmatrixElement 1 a (m + 1) ((n : ℕ) + 1) ^ 2 from by
          rw [Finset.sum_image (fun x _ y _ h => Fin.val_injective h)]]
        exact h
    _ = 2 := by norm_num

#print axioms TmatrixElement_column_sumSq_le
#print axioms galerkinT_column_sumSq_le

end

end RHFormalization
