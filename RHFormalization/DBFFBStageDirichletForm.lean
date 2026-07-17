import RHFormalization.ShiftedLaplaceLogDerivIdentity
import RHFormalization.DBFFBcorrWindowHolo

/-!
# DBFFBStageDirichletForm — B_stage as a ψ-shaped Dirichlet partial sum

ROUTE CARD
1. Target: D.OP.2 discrete bridge — the live B_stage equals
   (2√(s+1/4))⁻¹ · Σ_{k ≤ ⌊e^R⌋} Λ(k)·k^{−(√(s+1/4)+1/2)}. With the banked
   main-term pivot, B_stage − M is then the discrete (★) object and
   `abel_transfer_uniform`'s hE slot IS O3, stated in Lean.
2. Objects: `laplace_term_eq_vonMangoldt_term` (banked),
   `natValue_injOn_valid`, `vonMangoldt_term_support_subset_range`,
   `finiteCanonicalPrimePowerPackage_eq_weighted_sum` (all banked).
3. Raw B on Ω? NO — finite identity per stage, valid for ALL s (both sides
   carry the same (2√)⁻¹ factor; no continuation claim).
4. R = F − raw B forced? NO. 5. True outright.
6. Manuscript: D.OP-BOUND, Lemma D.OP.2 (discrete form of (★)).
7. Consumer: (★)-restatement brick; O3's Lean-named hypothesis slot.
-/

set_option autoImplicit false

namespace RHFormalization

noncomputable section

open Complex Finset ArithmeticFunction

/-- **D.OP.2 discrete bridge.** The finite prime-power package below cutoff `R`
is exactly the von Mangoldt Dirichlet partial sum up to `⌊e^R⌋`, normalized by
`(2√(s+1/4))⁻¹`. Valid for every `s : ℂ`. -/
theorem finitePackage_eq_vonMangoldt_partial_sum (R : ℝ) (s : ℂ) :
    finiteCanonicalPrimePowerPackage (activePrimePowerPairsCenterBelow R)
        shiftedLaplaceHeatKernelC s
      = (1 / (2 * Complex.sqrt (s + (1/4:ℂ)))) *
          ∑ k ∈ Finset.Ioc 0 ⌊Real.exp R⌋₊,
            LSeries.term (fun m => (ArithmeticFunction.vonMangoldt m : ℂ))
              (Complex.sqrt (s + (1/4:ℂ)) + (1/2:ℂ)) k := by
  classical
  set c : ℂ := 1 / (2 * Complex.sqrt (s + (1/4:ℂ))) with hc
  set T : ℕ → ℂ := fun k =>
    LSeries.term (fun m => (ArithmeticFunction.vonMangoldt m : ℂ))
      (Complex.sqrt (s + (1/4:ℂ)) + (1/2:ℂ)) k with hT
  -- membership unpacking (green donor route via mem_toFinset)
  have hmem : ∀ q ∈ activePrimePowerPairsCenterBelow R,
      IsPrimePowerPair q ∧ q.center ≤ R := by
    intro q hq
    first
      | exact (valid_primePower_center_le_finite R).mem_toFinset.mp hq
      | simpa using (valid_primePower_center_le_finite R).mem_toFinset.mp hq
  -- step 1: termwise banked identity
  have hstep1 : finiteCanonicalPrimePowerPackage
        (activePrimePowerPairsCenterBelow R) shiftedLaplaceHeatKernelC s
      = ∑ q ∈ activePrimePowerPairsCenterBelow R, c * T q.natValue := by
    rw [finiteCanonicalPrimePowerPackage_eq_weighted_sum]
    refine Finset.sum_congr rfl ?_
    intro q hq
    have hvalid : IsPrimePowerPair q := (hmem q hq).1
    simpa [hc, hT] using laplace_term_eq_vonMangoldt_term q hvalid s
  -- step 2: pull the constant out
  have hstep2 : (∑ q ∈ activePrimePowerPairsCenterBelow R, c * T q.natValue)
      = c * ∑ q ∈ activePrimePowerPairsCenterBelow R, T q.natValue := by
    rw [Finset.mul_sum]
  -- step 3: reindex along natValue (injective on valid pairs)
  have hstep3 : (∑ k ∈ (activePrimePowerPairsCenterBelow R).image
        PrimePowerPair.natValue, T k)
      = ∑ q ∈ activePrimePowerPairsCenterBelow R, T q.natValue := by
    refine Finset.sum_image ?_
    intro a ha b hb hab
    exact natValue_injOn_valid (hmem a ha).1 (hmem b hb).1 hab
  -- step 4a: image ⊆ Ioc 0 ⌊e^R⌋
  have hsub : (activePrimePowerPairsCenterBelow R).image PrimePowerPair.natValue
      ⊆ Finset.Ioc 0 ⌊Real.exp R⌋₊ := by
    intro k hk
    obtain ⟨q, hqmem, rfl⟩ := Finset.mem_image.mp hk
    obtain ⟨hvalid, hcenter⟩ := hmem q hqmem
    have h2 : (2 : ℕ) ≤ q.natValue := by
      calc (2 : ℕ) ≤ q.p := hvalid.1.two_le
        _ ≤ q.p ^ q.m := Nat.le_self_pow hvalid.2.ne' q.p
        _ = q.natValue := rfl
    have hpos : (0 : ℝ) < ((q.natValue : ℕ) : ℝ) := by
      have : (2:ℝ) ≤ ((q.natValue : ℕ) : ℝ) := by exact_mod_cast h2
      linarith
    have hle_exp : ((q.natValue : ℕ) : ℝ) ≤ Real.exp R := by
      have hexp := Real.exp_le_exp.mpr hcenter
      rwa [PrimePowerPair.center, Real.exp_log hpos] at hexp
    refine Finset.mem_Ioc.mpr ⟨by omega, ?_⟩
    first
      | exact Nat.le_floor hle_exp
      | exact (Nat.le_floor_iff (Real.exp_pos R).le).mpr hle_exp
      | exact Nat.le_floor_iff'.mpr hle_exp
  -- step 4b: terms on Ioc outside the image vanish
  have hzero : ∀ k ∈ Finset.Ioc 0 ⌊Real.exp R⌋₊,
      k ∉ (activePrimePowerPairsCenterBelow R).image PrimePowerPair.natValue
      → T k = 0 := by
    intro k hk hnot
    by_contra hTne
    obtain ⟨q, hq⟩ := vonMangoldt_term_support_subset_range k hTne
    obtain ⟨hk0, hkfl⟩ := Finset.mem_Ioc.mp hk
    have hkpos : (0:ℝ) < (k:ℝ) := by exact_mod_cast hk0
    have hkle : (k:ℝ) ≤ Real.exp R := by
      calc (k:ℝ) ≤ ((⌊Real.exp R⌋₊ : ℕ) : ℝ) := by exact_mod_cast hkfl
        _ ≤ Real.exp R := Nat.floor_le (Real.exp_pos R).le
    have hlog : Real.log (k:ℝ) ≤ R := by
      first
        | exact (Real.log_le_iff_le_exp hkpos).mpr hkle
        | (rw [← Real.log_exp R]; exact Real.log_le_log hkpos hkle)
        | (rw [← Real.log_exp R]
           exact (Real.log_le_log_iff hkpos (Real.exp_pos R)).mpr hkle)
    have hcenter : q.1.center ≤ R := by
      first
        | (simp only [PrimePowerPair.center, hq]; exact hlog)
        | (unfold PrimePowerPair.center; rw [hq]; exact hlog)
        | (simpa [PrimePowerPair.center, hq] using hlog)
    have hqmem : q.1 ∈ activePrimePowerPairsCenterBelow R := by
      first
        | exact (valid_primePower_center_le_finite R).mem_toFinset.mpr ⟨q.2, hcenter⟩
        | simpa using
            (valid_primePower_center_le_finite R).mem_toFinset.mpr ⟨q.2, hcenter⟩
    exact hnot (Finset.mem_image.mpr ⟨q.1, hqmem, hq⟩)
  -- assemble
  rw [hstep1, hstep2, ← hstep3, Finset.sum_subset hsub hzero]

/-- **Live-chain form**: the galerkin `B_stage` along the admissible net is the
ψ-shaped Dirichlet partial sum. -/
theorem galerkin_B_stage_eq_vonMangoldt_partial_sum (n : ℕ) (s : ℂ) :
    galerkinStagePackage.B_stage (admissibleGalerkinStageSeq n) s
      = (1 / (2 * Complex.sqrt (s + (1/4:ℂ)))) *
          ∑ k ∈ Finset.Ioc 0 ⌊Real.exp ((admissibleGalerkinStageSeq n).R)⌋₊,
            LSeries.term (fun m => (ArithmeticFunction.vonMangoldt m : ℂ))
              (Complex.sqrt (s + (1/4:ℂ)) + (1/2:ℂ)) k := by
  have h := finitePackage_eq_vonMangoldt_partial_sum
    ((admissibleGalerkinStageSeq n).R) s
  first
    | exact h
    | simpa [galerkinStagePackage] using h
    | (show finiteCanonicalPrimePowerPackage
          (activePrimePowerPairsCenterBelow ((admissibleGalerkinStageSeq n).R))
          shiftedLaplaceHeatKernelC s = _
       exact h)

#print axioms finitePackage_eq_vonMangoldt_partial_sum
#print axioms galerkin_B_stage_eq_vonMangoldt_partial_sum

end

end RHFormalization
