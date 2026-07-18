import RHFormalization.SelectedFiniteTraceSpikePayload
import RHFormalization.CanonicalPrimePowerPackage
import RHFormalization.AppendixDSpikeSumExtraction

namespace RHFormalization

#check PrimePowerPair
#print PrimePowerPair

#check PrimePowerPair.center
#check PrimePowerPair.weightC

-- Look for possible Nat/PrimePowerPair bridge names.
#check PrimePowerPair.toNat
#check PrimePowerPair.ofNat
#check PrimePowerPair.encode
#check PrimePowerPair.decode
#check PrimePowerPair.index
#check PrimePowerPair.natIndex

#check finiteNatSpikePackage
#check finiteCanonicalPrimePowerPackage
#check finiteNatSpikePackage_eq_of_coeff_eq_on_indices

end RHFormalization
