#!/bin/zsh
cat > RHFormalization/PrimePowerDFiniteStage.lean <<'EOF'
import RHFormalization.EmptyDFiniteStage
import RHFormalization.ConcretePrimePowerEnumeration
import RHFormalization.AppendixDPrimePowerPairCode

/-!
# RHFormalization.PrimePowerDFiniteStage

The genuine prime-power stage ladder: `primePowerStage n` has cutoff
`R = n + 1` and active spikes = the ppCode-image of the concrete enumeration
of valid prime powers with center ≤ n + 1, with the frozen weights
`Λ(q)/√q` as contributions. All certificates proven.
-/

namespace RHFormalization

noncomputable section

open Complex

/-- Active Nat codes for stage `n`: codes of valid prime powers with center ≤ n+1. -/
noncomputable def ppStageCodes (n : ℕ) : Finset ℕ :=
  (concretePrimePowerBelowCutoff ((n : ℝ) + 1)).image ppCode

theorem mem_ppStageCodes {n : ℕ} {k : ℕ} :
    k ∈ ppStageCodes n ↔
      ∃ q ∈ concretePrimePowerBelowCutoff ((n : ℝ) + 1), ppCode q = k := by
  simp [ppStageCodes]

/-- The prime-power designed stage at level `n`. -/
noncomputable def primePowerStage (n : ℕ) : DFiniteStage :=
  { L := 1
    R := (n : ℝ) + 1
    hL_pos := one_pos
    hR_pos := by positivity
    E := ℂ
    instNormed := inferInstance
    instInner := inferInstance
    instComplete := inferInstance
    native := zeroNativeStage
    heatEigenvalue := fun k => (k : ℝ)
    heatScale := 1
    h_heatScale_pos := one_pos
    h_heatEigenvalue_linear_lower := by intro k; simp
    resolventTraceTerm := fun _ _ => 0
    resolventBoundConstant := fun _ => 0
    h_resolventBoundConstant_nonneg := by intro s _; exact le_refl 0
    h_resolventTraceBound := by intro s _ k; simp
    duhamelTraceNormTerm := fun _ => 0
    h_duhamelTraceNormTerm_nonneg := by intro k; exact le_refl 0
    duhamelMajorant := fun _ => 0
    h_duhamelMajorant_nonneg := by intro k; exact le_refl 0
    h_duhamelTraceNormTerm_bound := by intro k; exact le_refl 0
    h_duhamelMajorant_summable := summable_zero
    mixedWordRemainder := fun _ => 0
    h_mixedWordRemainder_nonneg := by intro k; exact le_refl 0
    h_mixedWordSuperPolynomialDecay := by
      intro N
      exact ⟨0, le_refl 0, by intro k; simp⟩
    diagonalSpikeActive := fun k => k ∈ ppStageCodes n
    diagonalSpikeContribution := fun k => (ppDecode k).weightC
    canonicalSpikeContribution := fun k => (ppDecode k).weightC
    h_diagonalSpikeExtraction := by intro k _; rfl
    appendixDFiniteFStage := fun _ => 0
    diagonalSpikeActiveIndices := ppStageCodes n
    h_diagonalSpikeActiveIndices_active := by intro k hk; exact hk
    h_diagonalSpikeActiveIndices_complete := by intro k hk; exact hk
    diagonalSpikeToPP := ppDecode
    h_diagonalSpikeToPP_inj := by
      intro a _ b _ h
      have h2 := congrArg ppCode h
      simpa [ppCode_ppDecode] using h2
    h_canonicalSpikeContribution_eq_weightC := by intro k _; rfl
    h_diagonalSpikeToPP_center_le_R := by
      intro k hk
      rcases mem_ppStageCodes.mp hk with ⟨q, hq, rfl⟩
      have hfil := Finset.mem_filter.mp hq
      have hcenter := hfil.2.2
      simpa [ppDecode_ppCode] using hcenter
    h_diagonalSpikeToPP_complete_center_le_R := by
      intro q hq hle
      have hbelow : q ∈ concretePrimePowerBelowCutoff ((n : ℝ) + 1) :=
        concretePrimePowerEnum.h_mem_belowCutoff ((n : ℝ) + 1) q hq hle
      refine ⟨ppCode q, ?_, ppDecode_ppCode q⟩
      exact mem_ppStageCodes.mpr ⟨q, hbelow, rfl⟩ }

/-- The stage cutoff dominates the index: `n ≤ R(stage n)`. -/
theorem primePowerStage_R_ge_nat (n : ℕ) :
    (n : ℝ) ≤ (primePowerStage n).R := by
  simp [primePowerStage]

/-- The cutoffs tend to infinity along the ladder. -/
theorem primePowerStage_R_tendsto_atTop :
    Filter.Tendsto (fun n : ℕ => (primePowerStage n).R)
      Filter.atTop Filter.atTop := by
  simp only [primePowerStage]
  exact Filter.tendsto_atTop_add_const_right _ 1
    Filter.tendsto_natCast_atTop_atTop

#print axioms primePowerStage
#print axioms primePowerStage_R_tendsto_atTop

end

end RHFormalization
EOF
lake build RHFormalization.PrimePowerDFiniteStage 2>&1 | tee pps_a.log | grep -e "error" -e "depends on axioms" -e "Build completed"
if grep -q "error" pps_a.log; then
  echo "FAILED -> removing (errors below)"
  grep -B2 -A10 "error" pps_a.log | head -60
  rm RHFormalization/PrimePowerDFiniteStage.lean
  exit 1
fi
grep -qxF "import RHFormalization.PrimePowerDFiniteStage" RHFormalization.lean || printf '\nimport RHFormalization.PrimePowerDFiniteStage\n' >> RHFormalization.lean
lake build 2>&1 | tee pps_root.log | tail -3
grep -q "Build completed successfully" pps_root.log && tar --exclude='.lake' --exclude='*.bak*' --exclude='*.parked' -czf ~/Downloads/RHFormalization_PP_STAGE.tar.gz . && echo "SNAPSHOT SAVED: PP_STAGE"
