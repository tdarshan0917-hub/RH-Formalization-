-- SENTINEL: dmr-ftail-omega-bound-v7
import RHFormalization.DMRRStageHalfplaneBound
import RHFormalization.DTailPerturbedTraceDomination
import RHFormalization.DTailUniformBound
import RHFormalization.GalerkinTailHolo
import Mathlib

/-! # Step 3a: closed F-tail bounded on ALL Ω-compacts (D.TAIL-DENSITY payoff).
Instantiates the banked `dTail_uniform_bound` engine at the admissible stage:
λ := admMu (≥ 0, banked), h_fk from `h_fk_perturbed_galerkin` with the
SupV-shift absorbed by `exp(−t₀·SupV) ≤ 1`, δ-gap and |Re|-max from the
banked compact providers. Kills the `0 < Re s` guard. Hypothesis-free. -/

set_option autoImplicit false

namespace RHFormalization

noncomputable section

open Complex MeasureTheory Set
open scoped BigOperators Classical

/-- The two free-spectrum functions coincide. -/
theorem galerkinFreeMu_eq_galerkinLam (N : ℕ) (L : ℝ) :
    galerkinFreeMu N L = fun i : Fin N => galerkinLam L (i : ℕ) := by
  funext i
  first
    | rfl
    | (unfold galerkinFreeMu galerkinLam)
    | (unfold galerkinFreeMu galerkinLam; rfl)

/-- FK domination at the SHIFTED eigenvalues `admMu`. -/
theorem h_fk_admMu (n : ℕ) :
    (1 / (2 * admL n)) * (∑ i : Fin (admN n),
        Real.exp (-spikeT0 * admMu n i)) ≤ freeHeatDiagonal spikeT0 := by
  have hV := galerkinVC_isHermitian (N := admN n) 1
    (activePrimePowerCodesCenterBelow (admR n)) ppWeightReal (admL n)
  have hfk := h_fk_perturbed_galerkin (N := admN n)
    (activePrimePowerCodesCenterBelow (admR n)) (admL n) spikeT0
    (admL_pos n) spikeT0_pos hV
  have hPL : ∀ i : Fin (admN n), admPerturbedLam n i
      = perturbedEigenvalues
          (fun i : Fin (admN n) => galerkinLam (admL n) (i : ℕ)) hV i := by
    intro i
    unfold admPerturbedLam
    rw [← galerkinFreeMu_eq_galerkinLam]
  have hcoef : (0:ℝ) ≤ 1 / (2 * admL n) := by
    have := admL_pos n; positivity
  have hshift : ∀ i : Fin (admN n),
      Real.exp (-spikeT0 * admMu n i)
        ≤ Real.exp (-spikeT0 * admPerturbedLam n i) := by
    intro i
    apply Real.exp_le_exp.mpr
    have hsv := SupVConst_nonneg_adm
    have ht0 := spikeT0_pos
    have hmu : admMu n i = admPerturbedLam n i + SupVConst := rfl
    first
      | (rw [hmu]; nlinarith)
      | (rw [hmu])
      | nlinarith
  calc (1 / (2 * admL n)) * (∑ i : Fin (admN n),
        Real.exp (-spikeT0 * admMu n i))
      ≤ (1 / (2 * admL n)) * (∑ i : Fin (admN n),
          Real.exp (-spikeT0 * admPerturbedLam n i)) := by
        exact mul_le_mul_of_nonneg_left
          (Finset.sum_le_sum (fun i _ => hshift i)) hcoef
    _ = (1 / (2 * admL n)) * (∑ i : Fin (admN n),
          Real.exp (-spikeT0 * perturbedEigenvalues
            (fun i : Fin (admN n) => galerkinLam (admL n) (i : ℕ)) hV i)) := by
        first
          | rfl
          | (congr 1)
          | (congr 1
             exact Finset.sum_congr rfl (fun i _ => by rw [hPL i]))
          | (exact congrArg _ (Finset.sum_congr rfl (fun i _ => by rw [hPL i])))
    _ ≤ freeHeatDiagonal spikeT0 := hfk

/-- **STEP 3a: closed F-tail bounded on ALL Ω-compacts, uniform in n.** -/
theorem galFTailClosed_omega_uniform_bound
    (K : Set ℂ) (hK : IsCompact K) (hKO : K ⊆ Ω) (hne : K.Nonempty) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ, ∀ s ∈ K, ‖galFTailClosed n s‖ ≤ C := by
  obtain ⟨δ, hδpos, hδ⟩ := exists_uniform_lower_bound_on_compact K hK hKO
  obtain ⟨s0, hs0, hmax⟩ := hK.exists_isMaxOn hne
    (Complex.continuous_re.abs.continuousOn)
  set M : ℝ := |s0.re| with hMdef
  have hMK : ∀ s ∈ K, |s.re| ≤ M := fun s hs => hmax hs
  have hfhd : (0:ℝ) ≤ freeHeatDiagonal spikeT0 := by
    unfold freeHeatDiagonal
    positivity
  refine ⟨Real.exp (spikeT0 * M) * ((1 / δ) * freeHeatDiagonal spikeT0),
    by
      have h1 : (0:ℝ) ≤ 1 / δ := by positivity
      have h2 : (0:ℝ) ≤ Real.exp (spikeT0 * M) := (Real.exp_pos _).le
      exact mul_nonneg h2 (mul_nonneg h1 hfhd),
    fun n s hs => ?_⟩
  have hgap : ∀ i : Fin (admN n), δ ≤ ‖s + ((admMu n i : ℝ) : ℂ)‖ :=
    fun i => hδ s hs (admMu n i) (admMu_nonneg n i)
  have hM := hMK s hs
  have hmain := dTail_uniform_bound (n := admN n) spikeT0 (admL n)
    spikeT0_pos.le (admL_pos n) s (admMu n) (admMu_nonneg n)
    δ M hδpos hgap hM (h_fk_admMu n)
  -- reshape galFTailClosed into the engine's normal form
  have hdens : ‖admDensityC n‖ = 1 / (2 * admL n) := by
    unfold admDensityC
    have h2L : (0:ℝ) < 2 * admL n := by
      have := admL_pos n; positivity
    first
      | rw [Complex.norm_real, Real.norm_eq_abs,
            abs_of_pos (one_div_pos.mpr h2L)]
      | rw [Complex.norm_ofReal, abs_of_pos (one_div_pos.mpr h2L)]
      | simp [Real.norm_eq_abs, abs_of_pos (one_div_pos.mpr h2L)]
  have hsumeq : (∑ i : Fin (admN n),
        Complex.exp (-(s + ((admMu n i : ℝ) : ℂ)) * (spikeT0:ℂ))
          / (s + ((admMu n i : ℝ) : ℂ)))
      = ∑ i : Fin (admN n),
        Complex.exp (-(spikeT0 : ℂ) * (s + ((admMu n i : ℝ) : ℂ)))
          / (s + ((admMu n i : ℝ) : ℂ)) := by
    refine Finset.sum_congr rfl (fun i _ => ?_)
    congr 1
    congr 1
    ring
  calc ‖galFTailClosed n s‖
      = ‖admDensityC n‖ * ‖∑ i : Fin (admN n),
          Complex.exp (-(s + ((admMu n i : ℝ) : ℂ)) * (spikeT0:ℂ))
            / (s + ((admMu n i : ℝ) : ℂ))‖ := by
        unfold galFTailClosed
        rw [norm_mul]
    _ = (1 / (2 * admL n)) * ‖∑ i : Fin (admN n),
          Complex.exp (-(spikeT0 : ℂ) * (s + ((admMu n i : ℝ) : ℂ)))
            / (s + ((admMu n i : ℝ) : ℂ))‖ := by
        rw [hdens, hsumeq]
    _ ≤ Real.exp (spikeT0 * M) * ((1 / δ) * freeHeatDiagonal spikeT0) := hmain

/-- **THE Ω-CORE NORMAL FAMILY**: `head + closed F-tail`, uniformly bounded
on every Ω-compact, uniformly in `n`. The operator-side Ω-core of the
sector residual. -/
theorem galOmegaCore_uniform_bound
    (K : Set ℂ) (hK : IsCompact K) (hKO : K ⊆ Ω) (hne : K.Nonempty) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ, ∀ s ∈ K,
      ‖galHead n s + galFTailClosed n s‖ ≤ C := by
  obtain ⟨_, C1, hC10, hC1⟩ := galHead_normal_family K hK hne
  obtain ⟨C2, hC20, hC2⟩ := galFTailClosed_omega_uniform_bound K hK hKO hne
  refine ⟨C1 + C2, by linarith, fun n s hs => ?_⟩
  calc ‖galHead n s + galFTailClosed n s‖
      ≤ ‖galHead n s‖ + ‖galFTailClosed n s‖ := norm_add_le _ _
    _ ≤ C1 + C2 := add_le_add (hC1 n s hs) (hC2 n s hs)

#print axioms h_fk_admMu
#print axioms galFTailClosed_omega_uniform_bound
#print axioms galOmegaCore_uniform_bound

end

end RHFormalization
