import RHFormalization.PrimeOperatorArithmeticWeights
import RHFormalization.GalerkinFormBound

/-!
# RHFormalization.AdmissibleWeightNonneg

**Brick 1 of the admissible F-front.** The frozen arithmetic weights
`w(q) = Λ(q)/√q` are nonnegative, hence the position-space prime potential is
pointwise nonnegative for every width, code set, and window. This kills the
need for any SupV-style shift on the admissible net: the perturbation form is
nonneg, so the admissible eigenvalues sit above the free Dirichlet spectrum.
Fully generic in δ, qs, w, L — nothing pinned to the L = 1 box.
-/

set_option autoImplicit false

namespace RHFormalization

noncomputable section

open Real

/-- The frozen prime-power weight is nonnegative. -/
theorem PrimePowerPair.weightReal_nonneg (q : PrimePowerPair) :
    0 ≤ q.weightReal := by
  unfold PrimePowerPair.weightReal
  split_ifs with h
  · apply div_nonneg
    · apply Real.log_nonneg
      have hp2 : 2 ≤ q.p := h.1.two_le
      have : (2 : ℝ) ≤ ((q.p : ℕ) : ℝ) := by exact_mod_cast hp2
      linarith
    · exact Real.sqrt_nonneg _
  · exact le_refl 0

/-- The coded arithmetic weight is nonnegative. -/
theorem ppWeightReal_nonneg (k : ℕ) : 0 ≤ ppWeightReal k := by
  unfold ppWeightReal
  have h := PrimePowerPair.weightReal_nonneg (ppDecode k)
  rw [show ((ppDecode k).weightC).re = (ppDecode k).weightReal from by
    unfold PrimePowerPair.weightC
    exact Complex.ofReal_re _]
  exact h

/-- **Pointwise nonnegativity of the prime potential** — every width δ > 0,
every code set, every point. The admissible-net replacement for supV. -/
theorem primePotentialFn_nonneg
    (δ : ℝ) (hδ : 0 < δ) (qs : Finset ℕ) (x : ℝ) :
    0 ≤ primePotentialFn δ qs ppWeightReal x := by
  unfold primePotentialFn
  apply Finset.sum_nonneg
  intro q _
  exact mul_nonneg (ppWeightReal_nonneg q)
    (le_of_lt (gaussBump_pos δ hδ _))

/-- The L-generic Galerkin trial function on the box `[0, L]`. -/
def galerkinTrialL (L : ℝ) {N : ℕ} (a : Fin N → ℝ) (x : ℝ) : ℝ :=
  ∑ m : Fin N, a m * dirichletEigenfun ((m : ℕ) + 1) L x

theorem continuous_galerkinTrialL (L : ℝ) {N : ℕ} (a : Fin N → ℝ) :
    Continuous (galerkinTrialL L a) := by
  unfold galerkinTrialL
  apply continuous_finsetSum
  intro m _
  exact (continuous_dirichletEigenfun _ L).const_mul _

#print axioms PrimePowerPair.weightReal_nonneg
#print axioms ppWeightReal_nonneg
#print axioms primePotentialFn_nonneg
#print axioms continuous_galerkinTrialL

/-- Continuity of the prime potential at every width (δ ≠ 0). -/
theorem continuous_primePotentialFn_gen (δ : ℝ) (hδ : δ ≠ 0) (qs : Finset ℕ) :
    Continuous (primePotentialFn δ qs ppWeightReal) := by
  unfold primePotentialFn
  apply continuous_finsetSum
  intro q _
  unfold gaussBump
  have hden : Real.sqrt (2 * Real.pi * δ ^ 2) ≠ 0 := by
    apply Real.sqrt_ne_zero'.mpr
    positivity
  fun_prop

/-- **The L-generic form identity** (port of the banked L = 1 proof):
the Galerkin bump form equals the position-space integral on `[0, L]`. -/
theorem galerkinV_form_eq_integral_L
    {N : ℕ} (L : ℝ) (hL : 0 < L) (qs : Finset ℕ) (a : Fin N → ℝ) :
    ∑ m : Fin N, ∑ n : Fin N, a m * a n * galerkinV (N := N) 1 qs ppWeightReal L m n
      = (2 / L) * ∫ x in (0:ℝ)..L,
          primePotentialFn 1 qs ppWeightReal x * (galerkinTrialL L a x) ^ 2 := by
  have hint : ∀ (g : ℝ → ℝ), Continuous g →
      IntervalIntegrable g MeasureTheory.volume 0 L :=
    fun g hg => hg.intervalIntegrable 0 L
  have hexp : ∀ x : ℝ,
      primePotentialFn 1 qs ppWeightReal x * (galerkinTrialL L a x) ^ 2
        = ∑ m : Fin N, ∑ n : Fin N,
            a m * a n * (dirichletEigenfun ((m:ℕ)+1) L x
              * primePotentialFn 1 qs ppWeightReal x
              * dirichletEigenfun ((n:ℕ)+1) L x) := by
    intro x
    unfold galerkinTrialL
    rw [sq, Finset.sum_mul_sum]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro m _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro n _
    ring
  calc ∑ m : Fin N, ∑ n : Fin N,
        a m * a n * galerkinV (N := N) 1 qs ppWeightReal L m n
      = (2 / L) * ∑ m : Fin N, ∑ n : Fin N, a m * a n
          * ∫ x in (0:ℝ)..L,
              dirichletEigenfun ((m:ℕ)+1) L x
                * primePotentialFn 1 qs ppWeightReal x
                * dirichletEigenfun ((n:ℕ)+1) L x := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl; intro m _
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl; intro n _
        rw [galerkinV_apply]
        show a m * a n * (2 / L * VmatrixElement 1 qs ppWeightReal L (↑m + 1) (↑n + 1)) = _
        first
          | (rw [show VmatrixElement 1 qs ppWeightReal L (↑m + 1) (↑n + 1)
                = ∫ x in (0:ℝ)..L,
                    dirichletEigenfun ((m:ℕ)+1) L x
                      * primePotentialFn 1 qs ppWeightReal x
                      * dirichletEigenfun ((n:ℕ)+1) L x from rfl]
             ring)
          | (unfold VmatrixElement; ring)
    _ = (2 / L) * ∑ m : Fin N, ∑ n : Fin N,
          ∫ x in (0:ℝ)..L, a m * a n
            * (dirichletEigenfun ((m:ℕ)+1) L x
              * primePotentialFn 1 qs ppWeightReal x
              * dirichletEigenfun ((n:ℕ)+1) L x) := by
        congr 1
        apply Finset.sum_congr rfl; intro m _
        apply Finset.sum_congr rfl; intro n _
        rw [intervalIntegral.integral_const_mul]
    _ = (2 / L) * ∫ x in (0:ℝ)..L, ∑ m : Fin N, ∑ n : Fin N, a m * a n
          * (dirichletEigenfun ((m:ℕ)+1) L x
            * primePotentialFn 1 qs ppWeightReal x
            * dirichletEigenfun ((n:ℕ)+1) L x) := by
        congr 1
        rw [intervalIntegral.integral_finsetSum]
        · apply Finset.sum_congr rfl; intro m _
          rw [intervalIntegral.integral_finsetSum]
          intro n _
          apply hint
          apply Continuous.const_mul
          exact ((continuous_dirichletEigenfun _ L).mul
            (continuous_primePotentialFn_gen 1 one_ne_zero qs)).mul
            (continuous_dirichletEigenfun _ L)
        · intro m _
          apply hint
          apply continuous_finsetSum
          intro n _
          apply Continuous.const_mul
          exact ((continuous_dirichletEigenfun _ L).mul
            (continuous_primePotentialFn_gen 1 one_ne_zero qs)).mul
            (continuous_dirichletEigenfun _ L)
    _ = (2 / L) * ∫ x in (0:ℝ)..L,
          primePotentialFn 1 qs ppWeightReal x * (galerkinTrialL L a x) ^ 2 := by
        congr 1
        apply intervalIntegral.integral_congr
        intro x _
        exact (hexp x).symm

/-- **The admissible-net keystone**: the Galerkin bump form is NONNEGATIVE at
every window — nonneg weights make the shift machinery unnecessary. -/
theorem galerkinV_form_nonneg_L
    {N : ℕ} (L : ℝ) (hL : 0 < L) (qs : Finset ℕ) (a : Fin N → ℝ) :
    0 ≤ ∑ m : Fin N, ∑ n : Fin N,
        a m * a n * galerkinV (N := N) 1 qs ppWeightReal L m n := by
  rw [galerkinV_form_eq_integral_L L hL qs a]
  have hpt : ∀ x ∈ Set.Icc (0:ℝ) L,
      0 ≤ primePotentialFn 1 qs ppWeightReal x * (galerkinTrialL L a x) ^ 2 :=
    fun x _ => mul_nonneg (primePotentialFn_nonneg 1 one_pos qs x) (sq_nonneg _)
  refine mul_nonneg (by positivity) ?_
  first
    | exact intervalIntegral.intervalIntegral_nonneg hpt (le_of_lt hL)
    | exact intervalIntegral.integral_nonneg (le_of_lt hL) hpt
    | exact intervalIntegral.integral_nonneg (le_of_lt hL)
        (fun x hx => hpt x hx)
    | (apply intervalIntegral.integral_nonneg (le_of_lt hL)
       intro x hx
       exact hpt x hx)

#print axioms continuous_primePotentialFn_gen
#print axioms galerkinV_form_eq_integral_L
#print axioms galerkinV_form_nonneg_L

end

end RHFormalization
