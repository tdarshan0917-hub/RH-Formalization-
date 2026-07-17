import RHFormalization.MinMaxBrick8
import Mathlib.Algebra.Polynomial.AlgebraMap

namespace RHFormalization
noncomputable section
open RCLike Polynomial BigOperators

variable {𝕜 : Type*} [RCLike 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E]
variable {n : ℕ} {B : E →ₗ[𝕜] E}

theorem shiftOp_eq_sub (c : ℝ) : shiftOp B c = B - ((-c : 𝕜)) • (1 : E →ₗ[𝕜] E) := by
  rw [shiftOp]; ext x
  simp only [LinearMap.add_apply, LinearMap.smul_apply, LinearMap.id_apply,
    Module.End.one_apply, neg_smul, sub_neg_eq_add]

/-- The characteristic polynomial of `shiftOp B c` is `∏ᵢ (X - C(λᵢ + c))`. -/
theorem charpoly_shiftOp (hB : B.IsSymmetric) (hn : Module.finrank 𝕜 E = n) (c : ℝ) :
    (shiftOp B c).charpoly = ∏ i, (X - C ((hB.eigenvalues hn i : 𝕜) + (c:𝕜))) := by
  rw [shiftOp_eq_sub, LinearMap.charpoly_sub_smul, hB.charpoly_eq hn, prod_comp]
  apply Finset.prod_congr rfl
  intro i _
  rw [sub_comp, X_comp, C_comp, map_add, map_neg]
  ring

theorem roots_prod_eigen (μ : Fin n → 𝕜) :
    (∏ i, (X - C (μ i))).roots = Finset.univ.val.map μ := by
  have h : (∏ i, (X - C (μ i))) = ((Finset.univ.val.map μ).map (fun a => X - C a)).prod := by
    rw [Multiset.map_map, ← Finset.prod_eq_multiset_prod]; rfl
  rw [h, roots_multiset_prod_X_sub_C]

theorem sort_map_antitone (g : Fin n → ℝ) (hg : Antitone g) :
    ((Finset.univ.val.map (fun i => g i)).sort (· ≥ ·)) = List.ofFn g := by
  rw [Fin.univ_val_map, Multiset.coe_sort]
  convert List.mergeSort_of_pairwise ?_
  simp_rw [decide_eq_true_eq, ← List.sortedGE_iff_pairwise]
  exact hg.sortedGE_ofFn

theorem shifted_antitone (hB : B.IsSymmetric) (hn : Module.finrank 𝕜 E = n) (c : ℝ) :
    Antitone (fun i => hB.eigenvalues hn i + c) :=
  fun i j hij => by simp only; linarith [hB.eigenvalues_antitone hn hij]

/-- **Shift-eigenvalue equality.** The `k`-th eigenvalue of `B + c·I` is `λ_k(B) + c`. -/
theorem eigenvalues_shiftOp (hB : B.IsSymmetric) (hn : Module.finrank 𝕜 E = n) (c : ℝ)
    (k : Fin n) :
    (shiftOp_symm hB c).eigenvalues hn k = hB.eigenvalues hn k + c := by
  have hlist : List.ofFn ((shiftOp_symm hB c).eigenvalues hn)
      = List.ofFn (fun i => hB.eigenvalues hn i + c) := by
    rw [← (shiftOp_symm hB c).sort_roots_charpoly_eq_eigenvalues hn, charpoly_shiftOp hB hn c,
      roots_prod_eigen, Multiset.map_map,
      show (RCLike.re ∘ fun i => ((hB.eigenvalues hn i : 𝕜) + (c:𝕜)))
          = fun i => hB.eigenvalues hn i + c from by
        funext i; simp only [Function.comp_apply, ← RCLike.ofReal_add, RCLike.ofReal_re]]
    exact sort_map_antitone _ (shifted_antitone hB hn c)
  exact congrFun (List.ofFn_inj.mp hlist) k

#print axioms eigenvalues_shiftOp
end
end RHFormalization
