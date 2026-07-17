import RHFormalization.DTailFreeHeatTraceBound
import RHFormalization.CoordSpanMinMax
import RHFormalization.FinitePerturbedSpectrum
import RHFormalization.AdmissibleEigenvalueFloor

/-!
# DTailPerturbedTraceDomination — the perturbed half of h_fk

ROUTE CARD
1. Target: h_fk, the D.TAIL-DENSITY heat-trace domination — the last analytic
   input of the RH chain. Perturbed heat trace ≤ free heat trace via Weyl
   (form-positivity + Courant–Fischer), then chain with the banked free half.
2. Objects: `eigenvalues_mono` (banked Weyl), `galerkinVC_re_form_nonneg_L`
   (banked positivity), `freeEigenvalues_eq_rev_of_monotone` (banked reindex),
   `h_fk_free_galerkin` (banked free half).
3. Raw B on Ω? NO. 4. R = F − raw B? NO. 5. True outright.
6. Manuscript: D.TAIL-DENSITY (p179–180), Feynman–Kac/KLMN domination —
   realized here at the finite Galerkin stage by eigenvalue monotonicity.
7. Consumer: `dTail_uniform_bound`'s h_fk slot; stage wiring next turn.
-/

set_option autoImplicit false

namespace RHFormalization

noncomputable section

open Complex RCLike Real
open scoped BigOperators

variable {N : ℕ}

/-- Form comparison: the free diagonal form is dominated by the perturbed form,
since the galerkin potential is form-nonnegative. -/
theorem free_form_le_perturbed_form
    (μ : Fin N → ℝ) (qs : Finset ℕ) (L : ℝ) (hL : 0 < L)
    (x : EuclideanSpace ℂ (Fin N)) :
    RCLike.re (inner ℂ x (freeDiagOp μ x))
      ≤ RCLike.re (inner ℂ x
          (perturbedOp μ (galerkinVC (N := N) 1 qs ppWeightReal L) x)) := by
  have hsplit : perturbedOp μ (galerkinVC (N := N) 1 qs ppWeightReal L) x
      = freeDiagOp μ x + pertOp (galerkinVC (N := N) 1 qs ppWeightReal L) x := by
    rw [perturbedOp_eq_add]
    rfl
  rw [hsplit, inner_add_right, map_add]
  have hnn := galerkinVC_re_form_nonneg_L (N := N) L hL qs x
  linarith

/-- **Weyl step**: every sorted free eigenvalue is ≤ the corresponding sorted
perturbed eigenvalue. -/
theorem freeEigenvalues_le_perturbed
    (μ : Fin N → ℝ) (qs : Finset ℕ) (L : ℝ) (hL : 0 < L)
    (hV : (galerkinVC (N := N) 1 qs ppWeightReal L).IsHermitian) (k : Fin N) :
    freeEigenvalues μ k ≤ perturbedEigenvalues μ hV k := by
  unfold freeEigenvalues perturbedEigenvalues
  exact eigenvalues_mono (freeDiagOp_isSymmetric μ)
    (perturbedOp_isSymmetric μ hV) perturbedOp_finrank
    (fun x => free_form_le_perturbed_form μ qs L hL x) k

/-- **Trace step**: the perturbed heat trace is dominated by the free heat
trace (exp is antitone, applied index-by-index to the sorted spectra). -/
theorem perturbedHeatSum_le_freeHeatSum
    (μ : Fin N → ℝ) (qs : Finset ℕ) (L : ℝ) (hL : 0 < L)
    (hV : (galerkinVC (N := N) 1 qs ppWeightReal L).IsHermitian)
    (t : ℝ) (ht : 0 ≤ t) :
    (∑ i : Fin N, Real.exp (-t * perturbedEigenvalues μ hV i))
      ≤ ∑ i : Fin N, Real.exp (-t * freeEigenvalues μ i) := by
  apply Finset.sum_le_sum
  intro i _
  apply Real.exp_le_exp.mpr
  rw [neg_mul, neg_mul]
  exact neg_le_neg (mul_le_mul_of_nonneg_left
    (freeEigenvalues_le_perturbed μ qs L hL hV i) ht)

/-- **Reindex step**: for a monotone entry vector, the free heat sum over the
sorted spectrum equals the heat sum over the entries (Fin.rev is a bijection). -/
theorem freeHeatSum_eq_entrySum
    (μ : Fin N → ℝ) (hmono : Monotone μ) (t : ℝ) :
    (∑ i : Fin N, Real.exp (-t * freeEigenvalues μ i))
      = ∑ i : Fin N, Real.exp (-t * μ i) := by
  have hterm : ∀ i : Fin N,
      Real.exp (-t * freeEigenvalues μ i) = Real.exp (-t * μ (Fin.rev i)) := by
    intro i
    rw [freeEigenvalues_eq_rev_of_monotone μ hmono i]
  rw [Finset.sum_congr rfl (fun i _ => hterm i)]
  first
    | exact Fin.sum_rev (fun i => Real.exp (-t * μ i))
    | exact Fin.sum_rev _
    | exact Equiv.sum_comp Fin.revPerm (fun i => Real.exp (-t * μ i))
    | exact Fintype.sum_equiv
        ⟨Fin.rev, Fin.rev, fun x => Fin.rev_rev x, fun x => Fin.rev_rev x⟩
        _ _ (fun x => rfl)

/-- The galerkin free entry vector is monotone in the index. -/
theorem galerkinLamFin_monotone (L : ℝ) (hL : 0 < L) :
    Monotone (fun i : Fin N => galerkinLam L (i : ℕ)) := by
  intro i j hij
  have hnat : (i : ℕ) ≤ (j : ℕ) := by
    first
      | exact hij
      | exact Fin.le_def.mp hij
      | exact Fin.val_le_val.mpr hij
  unfold galerkinLam
  have hb : ((i : ℕ) : ℝ) + 1 ≤ ((j : ℕ) : ℝ) + 1 := by
    have : ((i : ℕ) : ℝ) ≤ ((j : ℕ) : ℝ) := by exact_mod_cast hnat
    linarith
  have hpiL : (0:ℝ) ≤ Real.pi / L := by positivity
  have hbase : (((i : ℕ) : ℝ) + 1) * Real.pi / L
      ≤ (((j : ℕ) : ℝ) + 1) * Real.pi / L := by
    calc (((i : ℕ) : ℝ) + 1) * Real.pi / L
        = (((i : ℕ) : ℝ) + 1) * (Real.pi / L) := by rw [mul_div_assoc]
      _ ≤ (((j : ℕ) : ℝ) + 1) * (Real.pi / L) :=
          mul_le_mul_of_nonneg_right hb hpiL
      _ = (((j : ℕ) : ℝ) + 1) * Real.pi / L := by rw [mul_div_assoc]
  have h0 : (0:ℝ) ≤ (((i : ℕ) : ℝ) + 1) * Real.pi / L := by positivity
  have h0j : (0:ℝ) ≤ (((j : ℕ) : ℝ) + 1) * Real.pi / L := by positivity
  first
    | exact pow_le_pow_left₀ h0 hbase 2
    | exact pow_le_pow_left h0 hbase 2
    | exact sq_le_sq' (by linarith) hbase
    | nlinarith [h0, h0j, hbase]

/-- **h_fk, perturbed form — THE D.TAIL-DENSITY HEAT-TRACE DOMINATION.**
The density-normalized heat trace of the perturbed galerkin operator is
bounded by the free heat diagonal `(4πt)^{-1/2}`, uniformly in the cutoff
data `qs` and the window `L`. -/
theorem h_fk_perturbed_galerkin
    (qs : Finset ℕ) (L t : ℝ) (hL : 0 < L) (ht : 0 < t)
    (hV : (galerkinVC (N := N) 1 qs ppWeightReal L).IsHermitian) :
    (1 / (2 * L)) * (∑ i : Fin N,
        Real.exp (-t * perturbedEigenvalues
          (fun i : Fin N => galerkinLam L (i : ℕ)) hV i))
      ≤ freeHeatDiagonal t := by
  have hstep1 := perturbedHeatSum_le_freeHeatSum
    (fun i : Fin N => galerkinLam L (i : ℕ)) qs L hL hV t ht.le
  have hstep2 := freeHeatSum_eq_entrySum
    (fun i : Fin N => galerkinLam L (i : ℕ)) (galerkinLamFin_monotone L hL) t
  have hfree := h_fk_free_galerkin (N := N) L t hL ht
  have hcoef : (0:ℝ) ≤ 1 / (2 * L) := by positivity
  calc (1 / (2 * L)) * (∑ i : Fin N,
        Real.exp (-t * perturbedEigenvalues
          (fun i : Fin N => galerkinLam L (i : ℕ)) hV i))
      ≤ (1 / (2 * L)) * ∑ i : Fin N,
          Real.exp (-t * freeEigenvalues
            (fun i : Fin N => galerkinLam L (i : ℕ)) i) :=
        mul_le_mul_of_nonneg_left hstep1 hcoef
    _ = (1 / (2 * L)) * ∑ i : Fin N,
          Real.exp (-t * galerkinLam L (i : ℕ)) := by rw [hstep2]
    _ ≤ freeHeatDiagonal t := hfree

#print axioms free_form_le_perturbed_form
#print axioms freeEigenvalues_le_perturbed
#print axioms perturbedHeatSum_le_freeHeatSum
#print axioms freeHeatSum_eq_entrySum
#print axioms galerkinLamFin_monotone
#print axioms h_fk_perturbed_galerkin

end

end RHFormalization
