import RHFormalization.ShiftedLaplaceRepresentativeZpole
import RHFormalization.ZetaMultReflection

namespace RHFormalization
noncomputable section
open Complex Filter Topology

def ZpoleRepSeries (M : ZeroMultiplicityData) (s : ℂ) : ℂ :=
  ∑' ρ : {ρ : ℂ // IsNontrivialZetaZero ρ ∧ ρ.re < 1/2}, zeroPoleSummand M ρ.1 s

theorem repZpole_residue_at_witness
    (W : ZeroWitness) :
    ∃ ρrep : ℂ, IsNontrivialZetaZero ρrep ∧ ρrep.re < 1/2 ∧
      polePoint ρrep = W.s0 ∧
      zetaZeroMult ρrep = zetaZeroMult W.ρ := by
  obtain ⟨hz, h0, h1⟩ := W.h_zero
  have hoff : W.ρ.re ≠ (1/2:ℝ) := W.h_offline
  rcases lt_or_gt_of_ne hoff with hlt | hgt
  · refine ⟨W.ρ, W.h_zero, hlt, ?_, rfl⟩
    rw [W.hs0_def]
  · have hrefl : IsNontrivialZetaZero (1 - W.ρ) := reflected_zero W.ρ W.h_zero
    have hre : (1 - W.ρ).re < 1/2 := by
      simp only [Complex.sub_re, Complex.one_re]; linarith
    refine ⟨1 - W.ρ, hrefl, hre, ?_, ?_⟩
    · rw [W.hs0_def]; unfold polePoint; ring_nf
    · exact (zetaZeroMult_reflection h0 h1).symm

#print axioms ZpoleRepSeries
#print axioms repZpole_residue_at_witness

end
end RHFormalization
