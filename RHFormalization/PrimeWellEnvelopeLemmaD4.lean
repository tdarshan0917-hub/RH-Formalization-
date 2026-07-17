import RHFormalization.PrimeWellEnvelopeLemmaD3

namespace RHFormalization

open Real Filter Asymptotics Finset

noncomputable def latticeTerm (α c : ℝ) (k : ℕ) : ℝ :=
  Real.exp (-((k : ℝ) * Real.log 2 - c)^2 / (2 * α))

theorem latticeTerm_nonneg (α c : ℝ) (k : ℕ) : 0 ≤ latticeTerm α c k := Real.exp_nonneg _

theorem latticeTerm_le_one (α c : ℝ) (hα : 0 < α) (k : ℕ) : latticeTerm α c k ≤ 1 := by
  unfold latticeTerm
  rw [Real.exp_le_one_iff]
  apply div_nonpos_of_nonpos_of_nonneg
  · exact neg_nonpos_of_nonneg (sq_nonneg _)
  · positivity

theorem latticeTerm_le_major (α c : ℝ) (hα : 0 < α) (k : ℕ) (m : ℤ)
    (hm : m = round (c / Real.log 2)) :
    latticeTerm α c k ≤ (if (k : ℤ) = m then 1 else gaussTailW α ((k : ℤ) - m).natAbs) := by
  by_cases hkm : (k : ℤ) = m
  · simp [hkm, latticeTerm_le_one α c hα k]
  · simp only [hkm, if_false]
    exact latticeTerm_le_gaussTailW α c hα k m hm hkm

theorem sum_gaussTailW_comp_le (α : ℝ) (hα : 0 < α) (u : Finset ℕ) (φ : ℕ → ℕ)
    (hφ : Set.InjOn φ u) :
    ∑ k ∈ u, gaussTailW α (φ k) ≤ ∑' d, gaussTailW α d := by
  rw [← Finset.sum_image hφ]
  exact Summable.sum_le_tsum _ (fun i _ => gaussTailW_nonneg α i) (gaussTailW_summable α hα)

theorem injOn_lo (m : ℤ) (u : Finset ℕ) :
    Set.InjOn (fun k : ℕ => (m - (k:ℤ)).natAbs)
      (↑(u.filter (fun k : ℕ => (k:ℤ) < m)) : Set ℕ) := by
  intro a ha b hb hab
  rw [Finset.mem_coe, Finset.mem_filter] at ha hb
  simp only at hab
  omega

theorem injOn_hi (m : ℤ) (u : Finset ℕ) :
    Set.InjOn (fun k : ℕ => ((k:ℤ) - m).natAbs)
      (↑(u.filter (fun k : ℕ => m < (k:ℤ))) : Set ℕ) := by
  intro a ha b hb hab
  rw [Finset.mem_coe, Finset.mem_filter] at ha hb
  simp only at hab
  omega

theorem nonpeak_sum_le (α : ℝ) (hα : 0 < α) (u : Finset ℕ) (m : ℤ) :
    ∑ k ∈ u, (if (k : ℤ) = m then (0:ℝ) else gaussTailW α ((k : ℤ) - m).natAbs)
      ≤ 2 * ∑' d, gaussTailW α d := by
  classical
  have hsymm : ∀ k : ℕ, ((k:ℤ) - m).natAbs = (m - (k:ℤ)).natAbs := by
    intro k; omega
  have hpt : ∀ k ∈ u,
      (if (k : ℤ) = m then (0:ℝ) else gaussTailW α ((k : ℤ) - m).natAbs)
      ≤ (if (k:ℤ) < m then gaussTailW α (m - (k:ℤ)).natAbs else 0)
        + (if m < (k:ℤ) then gaussTailW α ((k:ℤ) - m).natAbs else 0) := by
    intro k _
    rcases lt_trichotomy (k:ℤ) m with h | h | h
    · rw [if_neg (ne_of_lt h), if_pos h, if_neg (not_lt.mpr (le_of_lt h)), add_zero, hsymm]
    · rw [if_pos h, if_neg (by omega : ¬ (k:ℤ) < m), if_neg (by omega : ¬ m < (k:ℤ))]
      simp
    · rw [if_neg (ne_of_gt h), if_neg (not_lt.mpr (le_of_lt h)), if_pos h, zero_add]
  calc ∑ k ∈ u, (if (k : ℤ) = m then (0:ℝ) else gaussTailW α ((k : ℤ) - m).natAbs)
      ≤ ∑ k ∈ u, ((if (k:ℤ) < m then gaussTailW α (m - (k:ℤ)).natAbs else 0)
          + (if m < (k:ℤ) then gaussTailW α ((k:ℤ) - m).natAbs else 0)) :=
        Finset.sum_le_sum hpt
    _ = (∑ k ∈ u.filter (fun k : ℕ => (k:ℤ) < m), gaussTailW α (m - (k:ℤ)).natAbs)
        + (∑ k ∈ u.filter (fun k : ℕ => m < (k:ℤ)), gaussTailW α ((k:ℤ) - m).natAbs) := by
        rw [Finset.sum_add_distrib, Finset.sum_filter, Finset.sum_filter]
    _ ≤ (∑' d, gaussTailW α d) + (∑' d, gaussTailW α d) := by
        gcongr
        · exact sum_gaussTailW_comp_le α hα _ (fun k : ℕ => (m - (k:ℤ)).natAbs) (injOn_lo m u)
        · exact sum_gaussTailW_comp_le α hα _ (fun k : ℕ => ((k:ℤ) - m).natAbs) (injOn_hi m u)
    _ = 2 * ∑' d, gaussTailW α d := by ring

theorem latticeTerm_finset_sum_le (α c : ℝ) (hα : 0 < α) (u : Finset ℕ) :
    ∑ k ∈ u, latticeTerm α c k ≤ 1 + 2 * ∑' d, gaussTailW α d := by
  classical
  set m : ℤ := round (c / Real.log 2) with hm
  have hstep1 : ∑ k ∈ u, latticeTerm α c k
      ≤ ∑ k ∈ u, (if (k:ℤ) = m then (1:ℝ) else gaussTailW α ((k:ℤ) - m).natAbs) :=
    Finset.sum_le_sum (fun k _ => latticeTerm_le_major α c hα k m hm)
  have hpoint : ∀ k : ℕ,
      (if (k:ℤ) = m then (1:ℝ) else gaussTailW α ((k:ℤ) - m).natAbs)
      = (if (k:ℤ) = m then (1:ℝ) else 0)
        + (if (k:ℤ) = m then (0:ℝ) else gaussTailW α ((k:ℤ) - m).natAbs) := by
    intro k; by_cases h : (k:ℤ) = m <;> simp [h]
  have hsplit : ∑ k ∈ u, (if (k:ℤ) = m then (1:ℝ) else gaussTailW α ((k:ℤ) - m).natAbs)
      = (∑ k ∈ u, (if (k:ℤ) = m then (1:ℝ) else 0))
        + ∑ k ∈ u, (if (k:ℤ) = m then (0:ℝ) else gaussTailW α ((k:ℤ) - m).natAbs) := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun k _ => hpoint k)
  have hpeak : ∑ k ∈ u, (if (k:ℤ) = m then (1:ℝ) else 0) ≤ 1 := by
    calc ∑ k ∈ u, (if (k:ℤ) = m then (1:ℝ) else 0)
        = ∑ k ∈ u.filter (fun k : ℕ => (k:ℤ) = m), (1:ℝ) := by rw [Finset.sum_filter]
      _ = (u.filter (fun k : ℕ => (k:ℤ) = m)).card := by
          rw [Finset.sum_const, nsmul_eq_mul, mul_one]
      _ ≤ 1 := by
          have hc : (u.filter (fun k : ℕ => (k:ℤ) = m)).card ≤ 1 := by
            apply Finset.card_le_one.mpr
            intro a ha b hb
            rw [Finset.mem_filter] at ha hb
            have : (a:ℤ) = (b:ℤ) := by rw [ha.2, hb.2]
            exact_mod_cast this
          exact_mod_cast hc
  calc ∑ k ∈ u, latticeTerm α c k
      ≤ ∑ k ∈ u, (if (k:ℤ) = m then (1:ℝ) else gaussTailW α ((k:ℤ) - m).natAbs) := hstep1
    _ = (∑ k ∈ u, (if (k:ℤ) = m then (1:ℝ) else 0))
        + ∑ k ∈ u, (if (k:ℤ) = m then (0:ℝ) else gaussTailW α ((k:ℤ) - m).natAbs) := hsplit
    _ ≤ 1 + 2 * ∑' d, gaussTailW α d := by linarith [nonpeak_sum_le α hα u m, hpeak]

theorem latticeSum_le (α c : ℝ) (hα : 0 < α) :
    ∑' k, latticeTerm α c k ≤ 1 + 2 * ∑' d, gaussTailW α d := by
  apply Real.tsum_le_of_sum_le (fun k => latticeTerm_nonneg α c k)
  intro u
  exact latticeTerm_finset_sum_le α c hα u

noncomputable def shellEnvelopeConst (α : ℝ) : ℝ :=
  Real.exp (α/8) * (1 + 2 * ∑' d, gaussTailW α d)

theorem shellEnvelopeConst_nonneg (α : ℝ) (hα : 0 < α) : 0 ≤ shellEnvelopeConst α := by
  unfold shellEnvelopeConst
  apply mul_nonneg (Real.exp_nonneg _)
  have : 0 ≤ ∑' d, gaussTailW α d := tsum_nonneg (fun d => gaussTailW_nonneg α d)
  linarith

/-- **Lemma D (shell-sum bound).** `∑'_k shellTerm α u k ≤ Θ(α)·e^(u/2)`, uniform in `u`. -/
theorem shellSum_le (α u : ℝ) (hα : 0 < α) :
    ∑' k, shellTerm α u k ≤ shellEnvelopeConst α * Real.exp (u/2) := by
  have hαne : α ≠ 0 := ne_of_gt hα
  have hterm : ∀ k, shellTerm α u k
      = (Real.exp (u/2) * Real.exp (α/8)) * latticeTerm α (u + α/2) k := by
    intro k
    rw [shellTerm_completeSquare α u k hα]
    unfold latticeTerm
    rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
    congr 1
    field_simp
    ring
  have hsum : ∑' k, shellTerm α u k
      = (Real.exp (u/2) * Real.exp (α/8)) * ∑' k, latticeTerm α (u + α/2) k := by
    rw [← tsum_mul_left]
    exact tsum_congr hterm
  rw [hsum]
  have hlat := latticeSum_le α (u + α/2) hα
  have hconst_pos : 0 ≤ Real.exp (u/2) * Real.exp (α/8) := by positivity
  calc (Real.exp (u/2) * Real.exp (α/8)) * ∑' k, latticeTerm α (u + α/2) k
      ≤ (Real.exp (u/2) * Real.exp (α/8)) * (1 + 2 * ∑' d, gaussTailW α d) :=
        mul_le_mul_of_nonneg_left hlat hconst_pos
    _ = shellEnvelopeConst α * Real.exp (u/2) := by
        unfold shellEnvelopeConst; ring

#print axioms shellSum_le

end RHFormalization
