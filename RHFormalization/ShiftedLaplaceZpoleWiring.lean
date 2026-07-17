import RHFormalization.ShiftedLaplaceModelPP
import RHFormalization.DefaultPoleNormalFormLayer
import RHFormalization.HSidePoleWitness

namespace RHFormalization

open Complex Filter Topology

/-- For the default singleton class, the grouped residue coefficient is `mult W.ρ`. -/
theorem groupedResidueCoeff_default_eq
    (M : ZeroMultiplicityData) (W : ZeroWitness) :
    groupedResidueCoeff M (defaultGroupedPoleClass M W) = (M.mult W.ρ : ℂ) := by
  unfold groupedResidueCoeff groupedMultiplicitySum defaultGroupedPoleClass
  simp [Finset.sum_singleton]

/-- For the default data, the coefficient is `zetaZeroMult W.ρ`. -/
theorem groupedResidueCoeff_default_eq_zetaZeroMult (W : ZeroWitness) :
    groupedResidueCoeff defaultZeroMultiplicityData (defaultGroupedPoleClass defaultZeroMultiplicityData W)
      = (zetaZeroMult W.ρ : ℂ) := by
  rw [groupedResidueCoeff_default_eq]
  rfl

/-- **Sign flip.** If `B` has principal part with residue `c` at `z`, and `A` is
holomorphic at `z`, then `A - B` has residue `-c`. -/
theorem hasPrincipalPart_holo_sub
    {A B : ℂ → ℂ} {z c : ℂ}
    (hA : AnalyticAt ℂ A z)
    (hB : HasPrincipalPartAtC B z c) :
    HasPrincipalPartAtC (fun w => A w - B w) z (-c) := by
  obtain ⟨h, hh_an, hh_eq⟩ := hB
  refine ⟨fun w => A w - h w, hA.sub hh_an, ?_⟩
  filter_upwards [hh_eq] with w hw
  intro hwz
  rw [hw hwz]
  field_simp
  ring

end RHFormalization
