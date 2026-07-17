/-
AlmostAntitoneLimit.lean

GENERIC ALMOST-ANTITONE CONVERGENCE: a real sequence with a_{n+1} <= a_n
+ eps_n for a summable nonneg error sequence, bounded below, converges.
Proof: b_n := a_n + (tail sum of eps from n) is genuinely antitone and
bounded below, hence converges (banked ciInf engine); the tail vanishes;
a = b - tail converges.

Engine for the diagonal spectrum limit of Front F (dim step is a pure
decrease, code step is a summable drift).
-/
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Mathlib.Topology.Order.MonotoneConvergence
import Mathlib.Topology.Instances.Real.Lemmas

namespace RHFormalization

open Filter Topology

/-- Tail sums of a summable nonneg sequence, as a function of the start. -/
noncomputable def tailSum (eps : ℕ → ℝ) (n : ℕ) : ℝ :=
  ∑' m, eps (m + n)

theorem tailSum_nonneg (eps : ℕ → ℝ) (h0 : ∀ n, 0 ≤ eps n) (n : ℕ) :
    0 ≤ tailSum eps n :=
  tsum_nonneg fun m => h0 (m + n)

theorem tailSum_succ (eps : ℕ → ℝ) (hsum : Summable eps) (n : ℕ) :
    tailSum eps n = eps n + tailSum eps (n + 1) := by
  unfold tailSum
  have hs : Summable (fun m => eps (m + n)) := by
    first
      | exact (summable_nat_add_iff n).mpr hsum
      | exact hsum.comp_injective (add_left_injective n)
  have hshift : (fun m => eps (m + (n + 1))) = fun m => eps ((m + 1) + n) := by
    funext m
    congr 1
    omega
  first
    | { rw [hs.tsum_eq_zero_add]
        congr 1
        · rw [zero_add]
        · rw [hshift] }
    | { rw [tsum_eq_zero_add hs]
        congr 1
        · rw [zero_add]
        · rw [hshift] }


theorem tailSum_tendsto_zero (eps : ℕ → ℝ) (hsum : Summable eps) :
    Tendsto (tailSum eps) atTop (nhds 0) := by
  unfold tailSum
  first
    | exact tendsto_sum_nat_add eps
    | exact hsum.tendsto_sum_nat_add
    | simpa using tendsto_sum_nat_add eps

/-- **ALMOST-ANTITONE CONVERGENCE.** -/
theorem exists_tendsto_of_almost_antitone (a eps : ℕ → ℝ)
    (h0 : ∀ n, 0 ≤ eps n) (hsum : Summable eps)
    (hstep : ∀ n, a (n + 1) ≤ a n + eps n)
    (c : ℝ) (hbdd : ∀ n, c ≤ a n) :
    ∃ L : ℝ, c ≤ L ∧ Tendsto a atTop (nhds L) := by
  set b : ℕ → ℝ := fun n => a n + tailSum eps n with hb
  have hbanti : Antitone b := by
    apply antitone_nat_of_succ_le
    intro n
    have h1 := hstep n
    have h2 := tailSum_succ eps hsum n
    show a (n + 1) + tailSum eps (n + 1) ≤ a n + tailSum eps n
    linarith
  have hbbdd : BddBelow (Set.range b) := by
    refine ⟨c, ?_⟩
    rintro x ⟨n, rfl⟩
    have := tailSum_nonneg eps h0 n
    show c ≤ a n + tailSum eps n
    linarith [hbdd n]
  have hbconv : Tendsto b atTop (nhds (⨅ n, b n)) :=
    tendsto_atTop_ciInf hbanti hbbdd
  refine ⟨⨅ n, b n, ?_, ?_⟩
  · apply le_ciInf
    intro n
    have := tailSum_nonneg eps h0 n
    show c ≤ a n + tailSum eps n
    linarith [hbdd n]
  · have haeq : a = fun n => b n - tailSum eps n := by
      funext n
      show a n = (a n + tailSum eps n) - tailSum eps n
      ring
    rw [haeq]
    have := hbconv.sub (tailSum_tendsto_zero eps hsum)
    simpa using this

#print axioms tailSum_succ
#print axioms tailSum_tendsto_zero
#print axioms exists_tendsto_of_almost_antitone

end RHFormalization
