import RHFormalization.DFiniteStageOperator

namespace RHFormalization

noncomputable section

/--
Target: the concrete finite operator layer needed for the selected D-side construction.
This is now the first real missing object.
-/
def selectedFiniteOperatorLayer :
  DFiniteStagePackageFromOperatorLayer :=
by
  refine
    {
      legality := ?legality
      traceConstruction := ?traceConstruction
      traceData := ?traceData
      h_traceData_from_legality := ?h_traceData_from_legality
      splitFromDuhamel := ?splitFromDuhamel
      spikeSumData := ?spikeSumData
    }

end

end RHFormalization
