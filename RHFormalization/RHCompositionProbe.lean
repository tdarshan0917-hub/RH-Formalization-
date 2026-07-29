import RHFormalization.MainTheoremFromRealZeroFreeOmegaPunctured
import RHFormalization.EtaPositivity

/-!
# RH composition probe
Plug the PROVEN `h_real_zero_free` into the reduction, leaving only Y/X/E/OIP.
Let Lean enumerate exactly what those four still require.
-/

namespace RHFormalization
noncomputable section

-- ZF is proven; this reduces RH to exactly Y, X, E, OIP.
theorem RH_from_four_holes
    (Y : DDetailedConstructionWithOperatorLegality)
    (X : HMeromorphicWithNormalFormPoles)
    (E : InterfaceBridgeNonnegativeAPI
      Y.toOperatorResolventBridge
      X.toLegacyZeroPolePackageAPI)
    (OIP : OmegaPuncturedMeromorphicIdentityAPI) :
    RiemannHypothesis :=
  mainTheorem_from_realZeroFree_omegaPuncturedIdentity
    h_real_zero_free
    Y X E OIP

#print axioms RH_from_four_holes

end
end RHFormalization
