#!/bin/zsh
cat > RHFormalization/EmptyDFiniteStage.lean <<'EOF'
import RHFormalization.DOperatorExport
import RHFormalization.ZeroNativeStageWitness

/-!
# RHFormalization.EmptyDFiniteStage

Existence proof for the designed-stage route: a fully concrete `DFiniteStage`
with no active spikes, zero transform, the zero-native operator core, and all
certificates proven. `R = 1/2 < log 2`, so prime-power completeness conditions
are vacuous at this stage.
-/

namespace RHFormalization

noncomputable section

open Complex

/-- A canonical prime-power pair to serve as the (irrelevant) value of `toPP`. -/
noncomputable def ppTwo : PrimePowerPair := default

/-- The empty designed finite stage. -/
noncomputable def emptyDFiniteStage : DFiniteStage :=
  { L := 1
    R := 1/2
    hL_pos := one_pos
    hR_pos := by norm_num
    E := ℂ
    instNormed := inferInstance
    instInner := inferInstance
    instComplete := inferInstance
    native := zeroNativeStage
    heatEigenvalue := fun n => (n : ℝ)
    heatScale := 1
    h_heatScale_pos := one_pos
    h_heatEigenvalue_linear_lower := by intro n; simp
    resolventTraceTerm := fun _ _ => 0
    resolventBoundConstant := fun _ => 0
    h_resolventBoundConstant_nonneg := by
      intro s _
      exact le_refl 0
    h_resolventTraceBound := by intro s _ n; simp
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
    diagonalSpikeActive := fun _ => False
    diagonalSpikeContribution := fun _ => 0
    canonicalSpikeContribution := fun _ => 0
    h_diagonalSpikeExtraction := by intro q hq; exact hq.elim
    appendixDFiniteFStage := fun _ => 0
    diagonalSpikeActiveIndices := ∅
    h_diagonalSpikeActiveIndices_active := by
      intro q hq; exact absurd hq (Finset.not_mem_empty q)
    h_diagonalSpikeActiveIndices_complete := by intro q hq; exact hq.elim
    diagonalSpikeToPP := fun _ => ppTwo
    h_diagonalSpikeToPP_inj := by
      intro m hm n hn _
      exact absurd hm (Finset.not_mem_empty m)
    h_canonicalSpikeContribution_eq_weightC := by
      intro n hn; exact absurd hn (Finset.not_mem_empty n) }

#print axioms emptyDFiniteStage

end

end RHFormalization
EOF
lake build RHFormalization.EmptyDFiniteStage 2>&1 | tee empty_a.log | grep -e "error" -e "depends on axioms" -e "Build completed"
if grep -q "error" empty_a.log; then
  echo "FAILED -> removing (errors below)"
  grep -B2 -A8 "error" empty_a.log | head -50
  rm RHFormalization/EmptyDFiniteStage.lean
  exit 1
fi
grep -qxF "import RHFormalization.EmptyDFiniteStage" RHFormalization.lean || printf '\nimport RHFormalization.EmptyDFiniteStage\n' >> RHFormalization.lean
lake build 2>&1 | tail -3 | tee empty_root.log
grep -q "Build completed successfully" empty_root.log && tar --exclude='.lake' --exclude='*.bak*' --exclude='*.parked' -czf ~/Downloads/RHFormalization_EMPTY_STAGE.tar.gz . && echo "SNAPSHOT SAVED: EMPTY_STAGE"
