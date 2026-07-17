import RHFormalization.ShiftedLaplaceRepMeromorphic
import RHFormalization.ShiftedLaplaceRepSummable
import RHFormalization.PairPoleIsolation

namespace RHFormalization
noncomputable section
open Complex Filter Topology Metric

def repRestPartial (M : ZeroMultiplicityData) (ρrep : ℂ) (n : ℕ) (s : ℂ) : ℂ :=
  ∑ ρ ∈ repSubtypeStage n, (if ρ.1 = ρrep then 0 else zeroPoleSummand M ρ.1 s)

theorem repRestPartial_differentiableOn
    (M : ZeroMultiplicityData) (ρrep : ℂ) (n : ℕ) (x : ℂ) (r : ℝ)
    (hiso : ∀ ρ' : ℂ, IsNontrivialZetaZero ρ' → ρ' ≠ ρrep →
      r ≤ dist (polePoint ρ') x) :
    DifferentiableOn ℂ
      (fun s => repRestPartial M ρrep n s)
      (Metric.ball x r) := by
  unfold repRestPartial
  have hterm : ∀ ρ' ∈ repSubtypeStage n,
      DifferentiableOn ℂ
        (fun s => if ρ'.1 = ρrep then 0 else zeroPoleSummand M ρ'.1 s)
        (Metric.ball x r) := by
    intro ρ' _
    by_cases hr : ρ'.1 = ρrep
    · simp only [hr, if_pos]
      exact differentiableOn_const 0
    · simp only [if_neg hr]
      have hz' : IsNontrivialZetaZero ρ'.1 := ρ'.2.1
      intro s hs
      have hden : zeroPoleDenom ρ'.1 s ≠ 0 := by
        have hd : zeroPoleDenom ρ'.1 s = s - polePoint ρ'.1 := by
          unfold zeroPoleDenom polePoint; ring
        rw [hd, sub_ne_zero]
        intro hcontra
        have hdist := hiso ρ'.1 hz' hr
        rw [← hcontra] at hdist
        rw [Metric.mem_ball] at hs
        linarith [dist_comm s x ▸ hs]
      refine DifferentiableAt.differentiableWithinAt ?_
      unfold zeroPoleSummand zeroPoleDenom
      unfold zeroPoleDenom at hden
      first
        | exact (differentiableAt_const _).div
            (differentiableAt_id'.add (differentiableAt_const _)) hden
        | exact (differentiableAt_const _).div
            (differentiableAt_id.add (differentiableAt_const _)) hden
  have hsum := DifferentiableOn.sum hterm
  have heq : (∑ i ∈ repSubtypeStage n,
        fun s => if i.1 = ρrep then 0 else zeroPoleSummand M i.1 s)
      = (fun s => ∑ ρ ∈ repSubtypeStage n,
        if ρ.1 = ρrep then 0 else zeroPoleSummand M ρ.1 s) := by
    funext s
    rw [Finset.sum_apply]
  rw [heq] at hsum
  exact hsum

#print axioms repRestPartial_differentiableOn

end
end RHFormalization
