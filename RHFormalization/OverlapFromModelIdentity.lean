/-
OverlapFromModelIdentity.lean

Overlap builder: with `Bzero := Harch - ZpoleRep` (h_split = rfl), the entire
`HSideOverlapPackage` reduces to ONE identity on the overlap half-plane:

  Cshared.Bshared = shiftedLaplaceLogDerivModel  on  Re s > sigma0  (sigma0 >= 0)

via the banked pillar-(d) reduction on Fixed (witness pole points have
negative real part, so the half-plane avoids them all). V4 endpoint:
RH from (ZF, D, shared-model identity, E). Firewall intact: the identity
lives strictly inside the convergence half-plane.
-/
import RHFormalization.HonestEndpointV3
import RHFormalization.ShiftedLaplaceRepCorrectedHarch

namespace RHFormalization

noncomputable section

/-- Build the full overlap package from the single shared-model identity. -/
def overlapFromSharedModelIdentity
    (Cshared : CanonicalPrimePowerPackage)
    (sigma0 : ℝ)
    (h_nonneg : 0 ≤ sigma0)
    (h_le : Cshared.sigma0 ≤ sigma0)
    (h_model : ∀ s ∈ RightHalfPlane sigma0,
      Cshared.Bshared s = shiftedLaplaceLogDerivModel s) :
    HSideOverlapPackage
      (ZpoleRepSeries defaultZeroMultiplicityData)
      unconditionalHArchPackage.Harch where
  Bzero := fun s =>
    unconditionalHArchPackage.Harch s -
      ZpoleRepSeries defaultZeroMultiplicityData s
  sigma0 := sigma0
  Cshared := Cshared
  h_Cshared_sigma_le := h_le
  h_Bzero_matches_shared := by
    intro s hs
    have hsre : sigma0 < s.re := hs
    have hspos : 0 < s.re := lt_of_le_of_lt h_nonneg hsre
    have hΩ : s ∈ Ω := by
      first
        | exact rightHalfPlane_subset_Omega h_nonneg hs
        | exact rightHalfPlane_subset_Omega hs
        | exact rightHalfPlane_subset_Omega sigma0 h_nonneg hs
        | · rw [mem_Omega_iff]
            intro hmem
            exact absurd hmem (by simp [NonpositiveRealAxis]; linarith)
    have hnw : ∀ W : ZeroWitness, s ≠ W.s0 := by
      intro W heq
      have hneg : (polePoint W.ρ).re < 0 :=
        polePoint_re_neg_of_nontrivial W.h_zero
      rw [W.hs0_def] at heq
      rw [heq] at hspos
      linarith
    rw [h_model s hs]
    show shiftedLaplaceHarchOmegaFixed s -
        ZpoleRepSeries defaultZeroMultiplicityData s
      = shiftedLaplaceLogDerivModel s
    exact shiftedLaplaceHarchOmegaFixed_sub_Zpole_eq_model hΩ hnw
  h_split := fun _ _ => rfl

/-- V4 endpoint: pillar (d)'s Lean interface is now a single equation. -/
theorem RH_from_shared_model_identity
    (ZF : ZetaZeroFacts)
    (D : OperatorResolventBridge)
    (Cshared : CanonicalPrimePowerPackage)
    (sigma0 : ℝ)
    (h_nonneg : 0 ≤ sigma0)
    (h_le : Cshared.sigma0 ≤ sigma0)
    (h_model : ∀ s ∈ RightHalfPlane sigma0,
      Cshared.Bshared s = shiftedLaplaceLogDerivModel s)
    (E : InterfaceBridgeNonnegativeAPI D
      (unconditionalX_from_overlap
        (overlapFromSharedModelIdentity Cshared sigma0 h_nonneg h_le
          h_model)).toLegacyZeroPolePackageAPI) :
    RiemannHypothesis :=
  RH_from_overlap_D_E ZF D
    (overlapFromSharedModelIdentity Cshared sigma0 h_nonneg h_le h_model) E

#check @RH_from_shared_model_identity
#print axioms overlapFromSharedModelIdentity
#print axioms RH_from_shared_model_identity

end
end RHFormalization
