import RHFormalization.DenseSealEndpoint
import RHFormalization.MeromorphyAwayFromPoles

namespace RHFormalization

noncomputable section

open Complex

/-- Riemann zeta does not vanish at a negative odd integer. -/
private theorem riemannZeta_neg_odd_ne_zero (k : ℕ) :
    riemannZeta (-(2 * k + 1 : ℕ) : ℂ) ≠ 0 := by
  let t : ℂ := (2 * (k + 1) : ℕ)
  have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have ht_re : 1 ≤ t.re := by
    simp [t]
    linarith
  have ht_re_pos : 0 < t.re := by
    simp [t]
    linarith
  have ht_zeta : riemannZeta t ≠ 0 :=
    riemannZeta_ne_zero_of_one_le_re ht_re
  have ht_gamma : Gamma t ≠ 0 :=
    Gamma_ne_zero_of_re_pos ht_re_pos
  have ht_cpow : (2 * (Real.pi : ℂ)) ^ (-t) ≠ 0 := by
    exact cpow_ne_zero_iff.mpr (Or.inl
      (mul_ne_zero (by norm_num) (by exact_mod_cast Real.pi_ne_zero)))
  have ht_cos : cos ((Real.pi : ℂ) * t / 2) ≠ 0 := by
    have harg : (Real.pi : ℂ) * t / 2 = (k + 1 : ℕ) * (Real.pi : ℂ) := by
      simp [t]
      ring
    rw [harg, ← ofReal_natCast, ← ofReal_mul, ← ofReal_cos,
      Real.cos_nat_mul_pi, ofReal_pow, ofReal_neg, ofReal_one]
    exact pow_ne_zero _ (by norm_num)
  have ht_not_neg_nat : ∀ n : ℕ, t ≠ -(n : ℂ) := by
    intro n h
    have hn_nonpos : (-(n : ℂ)).re ≤ 0 := by simp
    exact (not_lt_of_ge hn_nonpos) (h ▸ ht_re_pos)
  have ht_ne_one : t ≠ 1 := by
    intro h
    have htgt1 : 1 < t.re := by
      simp [t]
      linarith
    rw [h] at htgt1
    norm_num at htgt1
  have hfe := riemannZeta_one_sub ht_not_neg_nat ht_ne_one
  have hleft : (1 - t : ℂ) = -(2 * k + 1 : ℕ) := by
    simp [t]
    ring
  rw [hleft] at hfe
  rw [hfe]
  exact mul_ne_zero
    (mul_ne_zero
      (mul_ne_zero
        (mul_ne_zero (by norm_num) ht_cpow)
        ht_gamma)
      ht_cos)
    ht_zeta

/-- A zeta zero that is neither a Mathlib-packaged trivial zero nor the pole
value lies in the open critical strip. -/
theorem zeta_zero_mem_open_critical_strip
    (s : ℂ)
    (hz : riemannZeta s = 0)
    (htriv : ¬ ∃ n : ℕ, s = -2 * ((n : ℂ) + 1))
    (hs1 : s ≠ 1) :
    0 < s.re ∧ s.re < 1 := by
  have hlt1 : s.re < 1 := by
    by_contra h
    have hge : 1 ≤ s.re := le_of_not_gt h
    exact (riemannZeta_ne_zero_of_one_le_re hge) hz
  refine ⟨?_, hlt1⟩
  by_contra hpos
  have hle0 : s.re ≤ 0 := le_of_not_gt hpos
  by_cases hneg : ∃ n : ℕ, s = -(n : ℂ)
  · obtain ⟨n, rfl⟩ := hneg
    have hn0 : n ≠ 0 := by
      intro hn
      subst n
      simpa [riemannZeta_zero] using hz
    rcases n.even_or_odd with heven | hodd
    · obtain ⟨m, hm⟩ := heven
      have hm0 : m ≠ 0 := by
        intro hmzero
        subst m
        simp at hm
        exact hn0 hm
      obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hm0
      apply htriv
      refine ⟨k, ?_⟩
      simp [hm]
      ring
    · obtain ⟨k, rfl⟩ := hodd
      exact (riemannZeta_neg_odd_ne_zero k) hz
  · have hz_reflected : riemannZeta (1 - s) = 0 := by
      rw [riemannZeta_one_sub (by simpa using hneg) hs1, hz, mul_zero]
    have hre_reflected : 1 ≤ (1 - s).re := by
      simp [Complex.sub_re, Complex.one_re]
      linarith
    exact (riemannZeta_ne_zero_of_one_le_re hre_reflected) hz_reflected

/-- The project and Mathlib formulations of RH have the same content. -/
theorem RH_semantic_lock :
    RHFormalization.RiemannHypothesis ↔
    _root_.RiemannHypothesis := by
  constructor
  · intro h s hz htriv hs1
    exact h s ⟨hz, zeta_zero_mem_open_critical_strip s hz htriv hs1⟩
  · intro h s hs
    obtain ⟨hz, hs0, hslt1⟩ := hs
    apply h s hz
    · rintro ⟨n, rfl⟩
      have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
      norm_num at hs0
      linarith
    · intro hs_eq
      subst s
      norm_num at hslt1

/-- The dense paired-transform endpoint with Mathlib's root-level RH codomain. -/
theorem RH_from_pairedTransform_only_dense_mathlib
    (hP :
      ∀ K : Set ℂ,
        IsCompact K →
        K ⊆ Ω →
        ∃ Cp : ℝ,
          ∀ n,
          ∀ s ∈ K,
            ‖(2 : ℂ) * RHFormalization.denseFreePairedTransform n s
                - RHFormalization.compensatorM n s‖ ≤ Cp) :
    _root_.RiemannHypothesis := by
  exact RH_semantic_lock.mp
    (RHFormalization.RH_from_pairedTransform_only_dense hP)

#print RHFormalization.IsNontrivialZetaZero
#print RHFormalization.RiemannHypothesis
#print _root_.RiemannHypothesis
#print axioms RHFormalization.RH_from_pairedTransform_only_dense
#print axioms RHFormalization.RH_semantic_lock
#print axioms RHFormalization.RH_from_pairedTransform_only_dense_mathlib

end

end RHFormalization
