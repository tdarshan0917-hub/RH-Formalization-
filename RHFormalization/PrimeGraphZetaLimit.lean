import RHFormalization.PrimeGraphZetaLink
import Mathlib

/-!
# PrimeGraphZetaLimit — PG-9c: the graph's Euler part converges to −ζ'/ζ

`truncTerm s P n` is the von Mangoldt L-series term restricted to powers of primes `≤ P`.
* `truncTerm_eq`: only the prime `n.minFac` can contribute;
* `truncTerm_dichotomy`: `truncTerm = term` or `truncTerm = 0`;
* `truncTerm_eq_of_le`: `truncTerm s P n = term s n` once `n ≤ P`;
* `graphEuler_tendsto_logDeriv_zeta` (PG-9c): for `Re s > 1`,
  `Σ_{p ≤ P} log p · p^{-s}/(1-p^{-s}) → −ζ'(s)/ζ(s)` (Tannery / dominated convergence).
-/

set_option autoImplicit false

namespace RHFormalization

open Filter Topology
open scoped BigOperators

noncomputable def truncTerm (s : ℂ) (P n : ℕ) : ℂ :=
  ∑ p ∈ (Finset.range (P + 1)).filter Nat.Prime,
    Set.indicator (Set.range fun k : ℕ => p ^ (k + 1))
      (LSeries.term (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) s) n

theorem mem_range_primePow_minFac {p n : ℕ} (hp : p.Prime)
    (h : n ∈ Set.range fun k : ℕ => p ^ (k + 1)) : n.minFac = p := by
  obtain ⟨k, rfl⟩ := h
  exact hp.pow_minFac (Nat.succ_ne_zero k)

theorem truncTerm_eq (s : ℂ) (P n : ℕ) :
    truncTerm s P n = if n.minFac ∈ (Finset.range (P + 1)).filter Nat.Prime then
      Set.indicator (Set.range fun k : ℕ => n.minFac ^ (k + 1))
        (LSeries.term (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) s) n else 0 := by
  rw [truncTerm]
  have hterm : ∀ p ∈ (Finset.range (P + 1)).filter Nat.Prime,
      Set.indicator (Set.range fun k : ℕ => p ^ (k + 1))
          (LSeries.term (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) s) n
        = if p = n.minFac then Set.indicator (Set.range fun k : ℕ => p ^ (k + 1))
            (LSeries.term (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) s) n else 0 := by
    intro p hp
    by_cases h : p = n.minFac
    · rw [if_pos h]
    · rw [if_neg h]
      have hn : n ∉ Set.range fun k : ℕ => p ^ (k + 1) := fun hmem =>
        h (mem_range_primePow_minFac (Finset.mem_filter.mp hp).2 hmem).symm
      first
        | exact Set.indicator_of_notMem hn _
        | exact Set.indicator_of_not_mem hn _
        | simp [Set.indicator_apply, hn]
  rw [Finset.sum_congr rfl hterm]
  first
    | exact Finset.sum_ite_eq' _ _ _
    | simp only [Finset.sum_ite_eq, Finset.sum_ite_eq']

theorem truncTerm_dichotomy (s : ℂ) (P n : ℕ) :
    truncTerm s P n = LSeries.term (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) s n
      ∨ truncTerm s P n = 0 := by
  rw [truncTerm_eq]
  split_ifs
  · by_cases hm : n ∈ Set.range fun k : ℕ => n.minFac ^ (k + 1)
    · left
      exact Set.indicator_of_mem hm _
    · right
      first
        | exact Set.indicator_of_notMem hm _
        | exact Set.indicator_of_not_mem hm _
        | simp [Set.indicator_apply, hm]
  · right
    rfl

theorem truncTerm_eq_of_le {s : ℂ} {P n : ℕ} (hn : n ≤ P) :
    truncTerm s P n = LSeries.term (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) s n := by
  by_cases hpp : IsPrimePow n
  · obtain ⟨q, j, hq, hj, rfl⟩ := (isPrimePow_nat_iff n).mp hpp
    have hmin : (q ^ j).minFac = q := hq.pow_minFac (by omega)
    have hmem : (q ^ j).minFac ∈ (Finset.range (P + 1)).filter Nat.Prime := by
      rw [hmin]
      refine Finset.mem_filter.mpr ⟨Finset.mem_range.mpr ?_, hq⟩
      have hle : q ≤ q ^ j := by
        have h := Nat.minFac_le (pow_pos hq.pos j)
        rwa [hmin] at h
      omega
    rw [truncTerm_eq, if_pos hmem, hmin]
    apply Set.indicator_of_mem
    refine ⟨j - 1, ?_⟩
    show q ^ (j - 1 + 1) = q ^ j
    rw [Nat.sub_add_cancel hj]
  · have hf0 : LSeries.term (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) s n = 0 := by
      rw [LSeries.term_def]
      split_ifs
      · rfl
      · simp [ArithmeticFunction.vonMangoldt_eq_zero_iff.mpr hpp]
    rcases truncTerm_dichotomy s P n with h | h <;> rw [h, hf0]

/-- **PG-9c — the graph's Euler part converges to −ζ'/ζ on `Re s > 1`.** -/
theorem graphEuler_tendsto_logDeriv_zeta {s : ℂ} (hs : 1 < s.re) :
    Tendsto (fun P : ℕ => ∑ p ∈ (Finset.range (P + 1)).filter Nat.Prime,
        (Real.log p : ℂ) * ((p : ℂ) ^ (-s) / (1 - (p : ℂ) ^ (-s))))
      atTop (𝓝 (-deriv riemannZeta s / riemannZeta s)) := by
  have hs0 : 0 < s.re := by linarith
  have hsum : Summable (LSeries.term (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) s) :=
    ArithmeticFunction.LSeriesSummable_vonMangoldt hs
  have hnorm : Summable (fun n =>
      ‖LSeries.term (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) s n‖) :=
    summable_norm_iff.mpr hsum
  have hval : ∀ P : ℕ, ∑ p ∈ (Finset.range (P + 1)).filter Nat.Prime,
      (Real.log p : ℂ) * ((p : ℂ) ^ (-s) / (1 - (p : ℂ) ^ (-s))) = ∑' n, truncTerm s P n :=
    fun P => ((truncated_vonMangoldt_hasSum _
      (fun p hp => (Finset.mem_filter.mp hp).2) hs0).tsum_eq).symm
  rw [← vonMangoldt_LSeries_eq_logDeriv_zeta hs]
  refine (tendsto_congr hval).mpr ?_
  exact tendsto_tsum_of_dominated_convergence hnorm
    (fun n => tendsto_const_nhds.congr'
      (Filter.eventually_atTop.mpr ⟨n, fun P hP => (truncTerm_eq_of_le hP).symm⟩))
    (Filter.Eventually.of_forall (fun P n => by
      rcases truncTerm_dichotomy s P n with h | h
      · exact le_of_eq (by rw [h])
      · rw [h, norm_zero]
        exact norm_nonneg _))

#print axioms truncTerm_eq_of_le
#print axioms graphEuler_tendsto_logDeriv_zeta

end RHFormalization
