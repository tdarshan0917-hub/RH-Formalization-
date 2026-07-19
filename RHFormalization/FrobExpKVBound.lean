-- SENTINEL: frob-exp-kv-bound-v3
import RHFormalization.FrobDiagBounds
import RHFormalization.RealSpectralTraceBridge
import RHFormalization.DTailPerturbedTraceDomination
import RHFormalization.DMRFTailOmegaBound
import Mathlib

/-! # Core brick 6c-iii — `frobSq (exp (s•(−(K+V)))) ≤ N` at the stage. -/

set_option autoImplicit false

namespace RHFormalization

noncomputable section

open Matrix
open scoped BigOperators

attribute [local instance]
  Matrix.linftyOpNormedAddCommGroup
  Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing
  Matrix.linftyOpNormedAlgebra

variable {N : ℕ}

theorem isSymm_smul_neg_KV (qs : Finset ℕ) (L s : ℝ) :
    (s • (-(galerkinK (N := N) L
        + galerkinV (N := N) 1 qs ppWeightReal L))).IsSymm := by
  have h := galerkinKV_isSymm (N := N) 1 qs ppWeightReal L
  first
    | exact (h.neg).smul s
    | exact (h.neg.smul s)
    | (unfold Matrix.IsSymm at *
       rw [Matrix.transpose_smul, Matrix.transpose_neg, h])

theorem frobSq_exp_neg_KV_le (qs : Finset ℕ) (L : ℝ) (hL : 0 < L)
    (s : ℝ) (hs : 0 ≤ s) :
    frobSq (NormedSpace.exp (s • (-(galerkinK (N := N) L
        + galerkinV (N := N) 1 qs ppWeightReal L)))) ≤ (N : ℝ) := by
  have hV := galerkinVC_isHermitian (N := N) 1 qs ppWeightReal L
  rw [frobSq_exp_symm_eq_trace_exp_double _ (isSymm_smul_neg_KV qs L s)]
  have hdouble : (s • (-(galerkinK (N := N) L
        + galerkinV (N := N) 1 qs ppWeightReal L)))
      + (s • (-(galerkinK (N := N) L
        + galerkinV (N := N) 1 qs ppWeightReal L)))
      = (2 * s) • (-(galerkinK (N := N) L
        + galerkinV (N := N) 1 qs ppWeightReal L)) := by
    rw [← add_smul]
    congr 1
    ring
  rw [hdouble]
  rw [trace_exp_neg_KV_eq_eigen_sum (N := N) 1 qs ppWeightReal L (2 * s)]
  have h2s : (0:ℝ) ≤ 2 * s := by linarith
  have hdom := perturbedHeatSum_le_freeHeatSum (galerkinFreeMu N L) qs L hL
    hV (2 * s) h2s
  have hfree := freeHeatSum_eq_entrySum
    (fun i : Fin N => galerkinLam L (i : ℕ))
    (galerkinLamFin_monotone L hL) (2 * s)
  have hmu : galerkinFreeMu N L = fun i : Fin N => galerkinLam L (i : ℕ) :=
    galerkinFreeMu_eq_galerkinLam N L
  rw [hmu] at hdom
  have hentry : (∑ i : Fin N,
        Real.exp (-(2 * s) * freeEigenvalues
          (fun i : Fin N => galerkinLam L (i : ℕ)) i))
      ≤ (N : ℝ) := by
    rw [hfree]
    have hcard := sum_heatWeight_le_card (N := N) L (2 * s) h2s
    refine le_trans ?_ hcard
    refine Finset.sum_le_sum (fun i _ => ?_)
    unfold heatWeight
    rw [abs_of_nonneg (le_of_lt (Real.exp_pos _))]
    apply le_of_eq
    congr 1
    ring
  exact le_trans hdom hentry

#print axioms isSymm_smul_neg_KV
#print axioms frobSq_exp_neg_KV_le

end

end RHFormalization
