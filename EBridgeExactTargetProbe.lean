import RHFormalization.OmegaMeromorphicZeroPropagationClopen
import RHFormalization.InterfaceAlgebra
import RHFormalization.HMeromorphicPackage
import RHFormalization.DOperatorExport

#print RHFormalization.InterfaceBridgeAPI
#print RHFormalization.OperatorResolventBridge
#print RHFormalization.ZeroPolePackageAPI
#print RHFormalization.DDetailedConstructionWithOperatorLegality
#print RHFormalization.HMeromorphicWithNormalFormPoles
#print RHFormalization.HMeromorphicPackageLayerV2

#check RHFormalization.finalRHSpine_after_zeroPropagation
#check RHFormalization.DDetailedConstructionWithOperatorLegality.toOperatorResolventBridge
#check RHFormalization.HMeromorphicWithNormalFormPoles.toLegacyZeroPolePackageAPI

-- The exact target we need:
example
    (Y : RHFormalization.DDetailedConstructionWithOperatorLegality)
    (X : RHFormalization.HMeromorphicWithNormalFormPoles) :
    Type :=
  RHFormalization.InterfaceBridgeAPI
    Y.toOperatorResolventBridge
    X.toLegacyZeroPolePackageAPI
