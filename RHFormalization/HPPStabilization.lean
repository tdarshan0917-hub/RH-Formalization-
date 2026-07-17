import RHFormalization.PairPoleIsolation

/-!
# RHFormalization.HPPStabilization

Installment 2 of the h_pp-from-convergence campaign.

* the default exhaustion is MONOTONE (the truncation regions are nested);
* both members of the reflection pair are in every late stage;
* at late stages the partial pole series splits as
  (sum over the other zeros) + pairCoeff/(s − s0);
* the other-zeros sum is holomorphic on the isolation ball.
-/

namespace RHFormalization

noncomputable section

open Complex Set Topology Filter Metric
open scoped Classical

/-- The truncation regions are nested. -/
theorem zetaStripRegion_mono {m n : ℕ} (h : m ≤ n) :
    zetaStripRegion m ⊆ zetaStripRegion n := by
  intro s hs
  obtain ⟨hball, hre1, hre2⟩ := hs
  have hmn : (m : ℝ) + 2 ≤ (n : ℝ) + 2 := by exact_mod_cast by omega
  have hpos_m : (0 : ℝ) < (m : ℝ) + 2 := by positivity
  have hpos_n : (0 : ℝ) < (n : ℝ) + 2 := by positivity
  have hinv : 1 / ((n : ℝ) + 2) ≤ 1 / ((m : ℝ) + 2) :=
    one_div_le_one_div_of_le hpos_m hmn
  refine ⟨?_, ?_, ?_⟩
  · rw [mem_closedBall_zero_iff] at hball ⊢
    linarith
  · linarith
  · linarith

/-- The default exhaustion is monotone. -/
theorem defaultZeroExhaustion_mono {m n : ℕ} (h : m ≤ n) :
    defaultZeroExhaustion.zeroSet m ⊆ defaultZeroExhaustion.zeroSet n := by
  intro ρ hρ
  have h1 := (zetaZeros_region_finite m).mem_toFinset.mp hρ
  exact (zetaZeros_region_finite n).mem_toFinset.mpr
    ⟨h1.1, zetaStripRegion_mono h h1.2⟩

/-- Both members of the reflection pair are in every late stage. -/
theorem pair_eventually_in (W : ZeroWitness) :
    ∃ N : ℕ, ∀ n, N ≤ n →
      W.ρ ∈ defaultZeroExhaustion.zeroSet n ∧
      (1 - W.ρ) ∈ defaultZeroExhaustion.zeroSet n := by
  obtain ⟨N1, hN1⟩ := defaultZeroExhaustion.h_eventually_contains W.ρ W.h_zero
  obtain ⟨N2, hN2⟩ := defaultZeroExhaustion.h_eventually_contains (1 - W.ρ)
    (reflected_zero W.ρ W.h_zero)
  refine ⟨max N1 N2, fun n hn => ⟨?_, ?_⟩⟩
  · exact defaultZeroExhaustion_mono ((le_max_left N1 N2).trans hn) hN1
  · exact defaultZeroExhaustion_mono ((le_max_right N1 N2).trans hn) hN2

/-- The reflection pair as a Finset. -/
def pairFinset (W : ZeroWitness) : Finset ℂ := {W.ρ, 1 - W.ρ}

/-- At a stage containing the pair, the partial pole series splits off the
pair singular part. -/
theorem zeroPolePartial_stabilized
    (M : ZeroMultiplicityData) (W : ZeroWitness) (n : ℕ)
    (h1 : W.ρ ∈ defaultZeroExhaustion.zeroSet n)
    (h2 : (1 - W.ρ) ∈ defaultZeroExhaustion.zeroSet n)
    (s : ℂ) :
    zeroPolePartial M defaultZeroExhaustion n s =
      finiteZeroPoleSeries M
        (defaultZeroExhaustion.zeroSet n \ pairFinset W) s +
      (groupedResidueCoeff M (pairGroupedPoleClass M W)) / (s - W.s0) := by
  have hsub : pairFinset W ⊆ defaultZeroExhaustion.zeroSet n := by
    rw [pairFinset, Finset.insert_subset_iff, Finset.singleton_subset_iff]
    exact ⟨h1, h2⟩
  unfold zeroPolePartial finiteZeroPoleSeries
  rw [← Finset.sum_sdiff hsub]
  congr 1
  rw [pairFinset, Finset.sum_pair (offCritical_ne_reflection W)]
  have hd1 : zeroPoleDenom W.ρ s = s - W.s0 := by
    rw [W.hs0_def]; unfold zeroPoleDenom polePoint; ring
  have hd2 : zeroPoleDenom (1 - W.ρ) s = s - W.s0 := by
    rw [W.hs0_def]; unfold zeroPoleDenom polePoint; ring
  unfold zeroPoleSummand
  rw [hd1, hd2, pairGroupedPoleClass_coeff]
  push_cast
  ring

/-- The other-zeros sum is holomorphic on the isolation ball. -/
theorem remainder_differentiableOn
    (M : ZeroMultiplicityData) (W : ZeroWitness) (n : ℕ)
    (r : ℝ) (hr : 0 < r)
    (hiso : ∀ ρ' : ℂ, IsNontrivialZetaZero ρ' →
      ρ' ≠ W.ρ → ρ' ≠ 1 - W.ρ → r ≤ dist (polePoint ρ') W.s0) :
    DifferentiableOn ℂ
      (fun s => finiteZeroPoleSeries M
        (defaultZeroExhaustion.zeroSet n \ pairFinset W) s)
      (Metric.ball W.s0 r) := by
  unfold finiteZeroPoleSeries
  have hterm : ∀ ρ' ∈ defaultZeroExhaustion.zeroSet n \ pairFinset W,
      DifferentiableOn ℂ (fun s => zeroPoleSummand M ρ' s)
        (Metric.ball W.s0 r) := by
    intro ρ' hρ'
    rw [Finset.mem_sdiff] at hρ'
    have hz' := defaultZeroExhaustion.h_all_zeros n ρ' hρ'.1
    have hne1 : ρ' ≠ W.ρ := by
      intro h; exact hρ'.2 (by rw [pairFinset, h]; exact Finset.mem_insert_self _ _)
    have hne2 : ρ' ≠ 1 - W.ρ := by
      intro h; exact hρ'.2 (by
        rw [pairFinset, h]
        exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _))
    intro s hs
    have hden : zeroPoleDenom ρ' s ≠ 0 := by
      have hd : zeroPoleDenom ρ' s = s - polePoint ρ' := by
        unfold zeroPoleDenom polePoint; ring
      rw [hd, sub_ne_zero]
      intro hcontra
      have hdist := hiso ρ' hz' hne1 hne2
      rw [← hcontra] at hdist
      rw [Metric.mem_ball] at hs
      linarith
    refine DifferentiableAt.differentiableWithinAt ?_
    unfold zeroPoleSummand zeroPoleDenom
    unfold zeroPoleDenom at hden
    first
      | exact (differentiableAt_const _).div
          (differentiableAt_id'.add (differentiableAt_const _)) hden
      | exact (differentiableAt_const _).div
          (differentiableAt_id.add (differentiableAt_const _)) hden
      | fun_prop (disch := assumption)
  first
    | exact DifferentiableOn.sum hterm
    | exact DifferentiableOn.fun_sum hterm
    | (induction (defaultZeroExhaustion.zeroSet n \ pairFinset W) using
        Finset.induction_on with
       | empty => simpa using differentiableOn_const 0
       | insert a s ha ih =>
         simp only [Finset.sum_insert ha]
         exact (hterm a (Finset.mem_insert_self a s)).add
           (ih (fun i hi => hterm i (Finset.mem_insert_of_mem hi))))

#print axioms zeroPolePartial_stabilized
#print axioms remainder_differentiableOn
#print axioms pair_eventually_in

end

end RHFormalization
