import RHFormalization.AppendixDPrimePowerPairCode
import RHFormalization.CanonicalPrimePowerHeatKernelGaussianCoreSummability

/-!
# RHFormalization.AppendixDGuardedCenterCutoffFinite

Finite guarded center-cutoff set for Appendix-D structural stage witnesses.

This proves directly that the valid prime-power pairs with center at most a real
cutoff `R` form a finite set. This is the unconditional finite set needed for the
`DFiniteStage` diagonal-spike active indices.
-/

namespace RHFormalization

noncomputable section

/--
Valid prime-power pairs below a real center cutoff form a finite set.
-/
lemma valid_primePower_center_le_finite (R : ℝ) :
    {q : PrimePowerPair | IsPrimePowerPair q ∧ q.center ≤ R}.Finite := by
  classical
  let N : ℕ := Nat.ceil (Real.exp R) + 1
  refine (valid_primePower_natValue_lt_finite N).subset ?_
  intro q hq
  simp only [Set.mem_setOf_eq] at hq ⊢
  rcases hq with ⟨hvalid, hcenter⟩
  refine ⟨hvalid, ?_⟩

  have hnat_pos : 0 < q.natValue := by
    rcases q with ⟨p, m⟩
    rcases hvalid with ⟨hp, _hm⟩
    simp [PrimePowerPair.natValue, PrimePowerPair.p, PrimePowerPair.m]
    exact Nat.pow_pos hp.pos

  have hnat_real_pos : 0 < ((q.natValue : ℕ) : ℝ) := by
    exact_mod_cast hnat_pos

  have hle_exp : ((q.natValue : ℕ) : ℝ) ≤ Real.exp R := by
    have hlog : Real.log ((q.natValue : ℕ) : ℝ) ≤ R := by
      simpa [PrimePowerPair.center] using hcenter
    exact (Real.log_le_iff_le_exp hnat_real_pos).1 hlog

  have hlt_ceil_succ :
      ((q.natValue : ℕ) : ℝ) <
        ((Nat.ceil (Real.exp R) + 1 : ℕ) : ℝ) := by
    have hceil_ge : Real.exp R ≤ (Nat.ceil (Real.exp R) : ℝ) :=
      Nat.le_ceil (Real.exp R)
    have hceil_lt_succ :
        (Nat.ceil (Real.exp R) : ℝ) <
          ((Nat.ceil (Real.exp R) + 1 : ℕ) : ℝ) := by
      exact_mod_cast Nat.lt_succ_self (Nat.ceil (Real.exp R))
    exact lt_of_le_of_lt (le_trans hle_exp hceil_ge) hceil_lt_succ

  change q.natValue < Nat.ceil (Real.exp R) + 1
  exact_mod_cast hlt_ceil_succ

end

end RHFormalization
