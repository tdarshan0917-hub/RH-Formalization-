import RHFormalization.ShiftedLaplaceRepCorrectedHolo
import RHFormalization.HExplicitFormulaSplitChosenCshared
import RHFormalization.PoleGeometry
import RHFormalization.HMeromorphicPackage

namespace RHFormalization
noncomputable section
open Complex Filter Topology
open scoped Classical

/-- For a nontrivial zero, the pole point has strictly negative real part. -/
theorem polePoint_re_neg_of_nontrivial {ρ : ℂ} (hρ : IsNontrivialZetaZero ρ) :
    (polePoint ρ).re < 0 := by
  obtain ⟨_, h0, h1⟩ := hρ
  rw [polePoint_re_formula]
  nlinarith [sq_nonneg ρ.im, mul_pos h0 (by linarith : (0:ℝ) < 1 - ρ.re)]

/-- On a right half-plane with `0 ≤ sigma0`, there are no pole points
(witnesses have negative real part). -/
theorem notMem_zeroPoleSet_of_mem_rightHalfPlane
    {sigma0 : ℝ} (hsigma : 0 ≤ sigma0) {s : ℂ}
    (hs : s ∈ RightHalfPlane sigma0) :
    s ∉ ZeroPoleSet := by
  intro hmem
  obtain ⟨ρ, hρ, hsρ⟩ := hmem
  have hsre : sigma0 < s.re := hs
  rw [hsρ] at hsre
  have hneg := polePoint_re_neg_of_nontrivial hρ
  linarith

/-- The corrected Harch package: `Harch := repCorrectedGlobal`, holomorphic on Ω
(Brick C). This is the honest archimedean package, built from the removable-
extension holomorphy rather than the false raw-sum `h_holo`. -/
noncomputable def shiftedLaplaceRepCorrectedHarchPackage
    (sigma0 : ℝ) (ZF : ZetaZeroFacts)
    (hBpp : ∀ W : ZeroWitness,
      HasPrincipalPartAtC
        (fun s => (shiftedLaplacePrimePackageAt sigma0).Bshared s)
        W.s0 (-(zetaZeroMult W.ρ : ℂ)))
    (hZpp_rep : ∀ W : ZeroWitness,
      HasPrincipalPartAtC (ZpoleRepSeries defaultZeroMultiplicityData)
        W.s0 ((zetaZeroMult W.ρ : ℂ)))
    (h_regular : ∀ z : ℂ, z ∈ Ω → (∀ W : ZeroWitness, z ≠ W.s0) →
      HolomorphicAtC (repRaw sigma0) z) :
    HArchPackage :=
  { Harch := repCorrectedGlobal sigma0
    h_Harch_holo := repCorrectedGlobal_holomorphicOn sigma0 ZF hBpp hZpp_rep h_regular }

/-- The split for the corrected Harch package on the half-plane. On `RightHalfPlane
sigma0` (with `0 ≤ sigma0`) there are no witnesses, so `repCorrectedGlobal = raw`,
giving `Bshared = Harch - ZpoleRep`. -/
theorem shiftedLaplaceRepCorrectedHarchPackage_split
    (sigma0 : ℝ) (ZF : ZetaZeroFacts) (hsigma : 0 ≤ sigma0)
    (hBpp : ∀ W : ZeroWitness,
      HasPrincipalPartAtC
        (fun s => (shiftedLaplacePrimePackageAt sigma0).Bshared s)
        W.s0 (-(zetaZeroMult W.ρ : ℂ)))
    (hZpp_rep : ∀ W : ZeroWitness,
      HasPrincipalPartAtC (ZpoleRepSeries defaultZeroMultiplicityData)
        W.s0 ((zetaZeroMult W.ρ : ℂ)))
    (h_regular : ∀ z : ℂ, z ∈ Ω → (∀ W : ZeroWitness, z ≠ W.s0) →
      HolomorphicAtC (repRaw sigma0) z)
    (s : ℂ) (hs : s ∈ RightHalfPlane sigma0) :
    (shiftedLaplacePrimePackageAt sigma0).Bshared s =
      (shiftedLaplaceRepCorrectedHarchPackage sigma0 ZF hBpp hZpp_rep h_regular).Harch s
        - ZpoleRepSeries defaultZeroMultiplicityData s := by
  have hnp : s ∉ ZeroPoleSet := notMem_zeroPoleSet_of_mem_rightHalfPlane hsigma hs
  show (shiftedLaplacePrimePackageAt sigma0).Bshared s =
      repCorrectedGlobal sigma0 s - ZpoleRepSeries defaultZeroMultiplicityData s
  rw [repCorrectedGlobal_eq_raw_of_notMem sigma0 hnp]
  show (shiftedLaplacePrimePackageAt sigma0).Bshared s =
      ((shiftedLaplacePrimePackageAt sigma0).Bshared s
        + ZpoleRepSeries defaultZeroMultiplicityData s)
        - ZpoleRepSeries defaultZeroMultiplicityData s
  ring

#print axioms shiftedLaplaceRepCorrectedHarchPackage
#print axioms shiftedLaplaceRepCorrectedHarchPackage_split

end
end RHFormalization
