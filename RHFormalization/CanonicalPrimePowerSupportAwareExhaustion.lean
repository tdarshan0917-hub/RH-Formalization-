import RHFormalization.CanonicalPrimePowerIndexExhaustion

/-!
# Support-aware partial-sum convergence

Replaces full-type finset exhaustion (`Tendsto I atTop atTop`) by the honest
statement: the index sets eventually contain every *valid* prime power, and
`weightC` vanishes off the valid prime powers, so partial sums still converge
to the tsum.
-/

namespace RHFormalization

noncomputable section

open Complex Topology Filter
open scoped BigOperators

/--
Support-aware partial-sum convergence: if `f` vanishes off valid prime powers
and the finsets eventually contain every valid prime power, the partial sums
converge to the tsum.
-/
theorem finite_sum_tendsto_of_hasSum_valid_exhaustion
    (I : ℕ → Finset PrimePowerPair)
    (f : PrimePowerPair → ℂ)
    (hf_zero : ∀ q : PrimePowerPair, ¬ IsPrimePowerPair q → f q = 0)
    (hmem : ∀ q : PrimePowerPair, IsPrimePowerPair q →
      ∃ N : ℕ, ∀ n : ℕ, N ≤ n → q ∈ I n)
    (hsum : HasSum f (∑' q, f q)) :
    Tendsto
      (fun n : ℕ => (I n).sum f)
      Filter.atTop
      (𝓝 (∑' q, f q)) := by
  classical
  -- HasSum means: net of partial sums over ALL finsets converges.
  -- We show our sequence of partial sums is eventually inside any
  -- neighborhood, using that for any finset S, the sum over (I n) eventually
  -- agrees with the sum over (I n ∪ S-valid-part), and invalid elements of S
  -- contribute zero.
  rw [HasSum] at hsum
  have hsum' :
      Tendsto (fun T : Finset PrimePowerPair => T.sum f) Filter.atTop
        (𝓝 (∑' q, f q)) := by
    simpa using hsum
  rw [tendsto_atTop'] at hsum' ⊢
  intro U hU
  rcases hsum' U hU with ⟨S, hS⟩
  -- S : Finset PrimePowerPair such that every finset ⊇ S lands in U.
  -- Split S into valid and invalid parts.
  set Sval : Finset PrimePowerPair := S.filter (fun q => IsPrimePowerPair q) with hSval
  -- Each valid element of S is eventually in I n; take the max threshold.
  have hN : ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ q ∈ Sval, q ∈ I n := by
    have : ∀ q ∈ Sval, ∃ N : ℕ, ∀ n : ℕ, N ≤ n → q ∈ I n := by
      intro q hq
      have hqval : IsPrimePowerPair q := by
        simpa [hSval] using (Finset.mem_filter.mp hq).2
      exact hmem q hqval
    -- choose a threshold for each q in the finite set Sval, take the max
    choose Nq hNq using this
    refine ⟨Sval.attach.sup (fun q => Nq q.1 q.2), ?_⟩
    intro n hn q hq
    have hle :
        Nq q hq ≤ Sval.attach.sup (fun r => Nq r.1 r.2) :=
      Finset.le_sup (f := fun r : {x // x ∈ Sval} => Nq r.1 r.2)
        (Finset.mem_attach Sval ⟨q, hq⟩)
    exact hNq q hq n (le_trans hle hn)
  rcases hN with ⟨N, hNall⟩
  refine ⟨N, ?_⟩
  intro n hn
  -- Key: sum over (I n) = sum over (I n ∪ S), because the added elements of S
  -- are either valid (already in I n by hNall) or invalid (f = 0).
  have hsum_eq :
      (I n).sum f = ((I n) ∪ S).sum f := by
    rw [Finset.sum_union_eq_left]
    intro q hqS hqnotI
    by_cases hqval : IsPrimePowerPair q
    · exact absurd (hNall n hn q (Finset.mem_filter.mpr ⟨hqS, hqval⟩)) hqnotI
    · exact hf_zero q hqval
  rw [hsum_eq]
  exact hS ((I n) ∪ S) Finset.subset_union_right

/--
Support-aware version of the finite-to-tsum convergence helper.

Same conclusion as `finiteCanonical_tendsto_tsum_of_kernel_error_tendsto_zero`,
but the exhaustion input only requires eventual containment of VALID prime
powers — the honest, satisfiable statement.
-/
theorem finiteCanonical_tendsto_tsum_of_kernel_error_tendsto_zero_valid
    (I : ℕ → Finset PrimePowerPair)
    (Kstage : ℕ → CanonicalKernelC)
    (Kshared : CanonicalKernelC)
    (s : ℂ)
    (hmem : ∀ q : PrimePowerPair, IsPrimePowerPair q →
      ∃ N : ℕ, ∀ n : ℕ, N ≤ n → q ∈ I n)
    (hsummable :
      Summable
        (fun q : PrimePowerPair => q.weightC * Kshared q.center s))
    (herror :
      Tendsto
        (fun n : ℕ =>
          finiteCanonicalPrimePowerPackage (I n) (Kstage n) s
            -
          (I n).sum
            (fun q : PrimePowerPair => q.weightC * Kshared q.center s))
        Filter.atTop
        (𝓝 0)) :
    Tendsto
      (fun n : ℕ =>
        finiteCanonicalPrimePowerPackage (I n) (Kstage n) s)
      Filter.atTop
      (𝓝
        (∑' q : PrimePowerPair,
          q.weightC * Kshared q.center s)) := by
  have hf_zero :
      ∀ q : PrimePowerPair, ¬ IsPrimePowerPair q →
        q.weightC * Kshared q.center s = 0 := by
    intro q hq
    have : q.weightC = 0 := by
      simp [PrimePowerPair.weightC, PrimePowerPair.weightReal, hq]
    simp [this]
  have hpartial :=
    finite_sum_tendsto_of_hasSum_valid_exhaustion
      I
      (fun q : PrimePowerPair => q.weightC * Kshared q.center s)
      hf_zero
      hmem
      hsummable.hasSum
  have hsum := hpartial.add herror
  simpa [finiteCanonicalPrimePowerPackage, sub_eq_add_neg,
    add_assoc, add_left_comm, add_comm] using hsum

end

end RHFormalization
