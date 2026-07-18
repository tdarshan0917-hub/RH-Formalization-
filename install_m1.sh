#!/bin/zsh
cat > RHFormalization/MeromorphyOffCritical.lean <<'EOF'
import RHFormalization.HPPEndgame

/-!
# RHFormalization.MeromorphyOffCritical

Meromorphy campaign, installment M1: at the pole point of any OFF-CRITICAL
nontrivial zero, Zpole is MeromorphicAt — directly from the derived principal
part (h_pp_from_convergence) and Mathlib's MeromorphicAt algebra. No new
analysis; this converts the h_pp campaign's output into meromorphy currency.
-/

namespace RHFormalization

noncomputable section

open Complex Set Topology Filter Metric

/-- The model singularity is meromorphic at its pole. -/
theorem meromorphicAt_const_div_sub (c s0 : ℂ) :
    MeromorphicAt (fun s => c / (s - s0)) s0 :=
  (analyticAt_const (v := c)).meromorphicAt.div
    ((analyticAt_id.sub analyticAt_const).meromorphicAt)

/-- A function with a principal part at a point is MeromorphicAt there. -/
theorem meromorphicAt_of_hasPrincipalPart
    (f : ℂ → ℂ) (s0 c : ℂ)
    (hpp : HasPrincipalPartAtC f s0 c) :
    MeromorphicAt f s0 := by
  obtain ⟨h, hA, hev⟩ := hpp
  have hmodel : MeromorphicAt (fun s => c / (s - s0) + h s) s0 := by
    have := (meromorphicAt_const_div_sub c s0).add hA.meromorphicAt
    first
      | exact this
      | simpa [Pi.add_def] using this
  refine hmodel.congr ?_
  first
    | (filter_upwards [hev, self_mem_nhdsWithin] with w hw hne
       exact (hw hne).symm)
    | (rw [Filter.eventuallyEq_iff_exists_mem]
       refine ⟨{w | w ≠ s0 → f w = c / (w - s0) + h w} ∩ {s0}ᶜ, ?_, ?_⟩
       · exact Filter.inter_mem (nhdsWithin_le_nhds hev)
           (self_mem_nhdsWithin)
       · intro w hw
         exact (hw.1 hw.2).symm)

/-- M1: Zpole is MeromorphicAt every off-critical witness pole point. -/
theorem meromorphicAt_offcritical_pole
    (M : ZeroMultiplicityData) (Zpole : ℂ → ℂ)
    (conv : ZeroPoleLocalUniformConvergenceAPI M defaultZeroExhaustion Zpole)
    (W : ZeroWitness) :
    MeromorphicAt Zpole W.s0 :=
  meromorphicAt_of_hasPrincipalPart Zpole W.s0
    (groupedResidueCoeff M (pairGroupedPoleClass M W))
    (h_pp_from_convergence M Zpole conv W)

#print axioms meromorphicAt_const_div_sub
#print axioms meromorphicAt_of_hasPrincipalPart
#print axioms meromorphicAt_offcritical_pole

end

end RHFormalization
EOF
lake build RHFormalization.MeromorphyOffCritical 2>&1 | tee m1_a.log | grep -e "error" -e "depends on axioms" -e "Build completed"
if grep -q "error" m1_a.log; then
  echo "FAILED -> removing (errors below)"
  grep -B2 -A14 "error" m1_a.log | head -90
  rm RHFormalization/MeromorphyOffCritical.lean
  exit 1
fi
for thm in meromorphicAt_const_div_sub meromorphicAt_of_hasPrincipalPart meromorphicAt_offcritical_pole; do
  if ! grep -q "$thm' depends on axioms: \[propext, Classical.choice, Quot.sound\]" m1_a.log; then
    echo "AXIOM CHECK FAILED ($thm) -> removing"; rm RHFormalization/MeromorphyOffCritical.lean; exit 1
  fi
done
grep -qxF "import RHFormalization.MeromorphyOffCritical" RHFormalization.lean || printf '\nimport RHFormalization.MeromorphyOffCritical\n' >> RHFormalization.lean
lake build 2>&1 | tee m1_root.log | tail -3
grep -q "Build completed successfully" m1_root.log && tar --exclude='.lake' --exclude='*.bak*' --exclude='*.parked' -czf ~/Downloads/RHFormalization_MERO_M1.tar.gz . && echo "SNAPSHOT SAVED: MERO_M1"
