import RHFormalization.CanonicalPrimePowerConcreteTsumPackage
import RHFormalization.CanonicalPrimePowerCutoffMassEnumeration

namespace RHFormalization

#print PrimePowerPair
#print PrimePowerPair.center
#print PrimePowerPair.weightReal
#print PrimePowerPair.weightC
#print finiteCanonicalPrimePowerPackage
#print enumeratedPrimePowerMass
#print PrimePowerWeightCutoffEnumerationData

-- sanity checks for constructing values of the reducible pair type
#check ((0, 0) : PrimePowerPair)
#check ((1, 0) : PrimePowerPair)
#check ((2, 1) : PrimePowerPair)
#check (((2, 1) : PrimePowerPair).center)
#check (((2, 1) : PrimePowerPair).weightC)

end RHFormalization
