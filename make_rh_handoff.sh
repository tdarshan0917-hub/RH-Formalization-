#!/usr/bin/env bash
set -euo pipefail

OUT="RH_ENDGAME_HANDOFF.md"

{
echo "# RH Formalization Endgame Handoff"
echo ""
echo "Generated: $(date)"
echo "Repo: $(pwd)"
echo ""
echo "## 0. Git state"
git rev-parse --abbrev-ref HEAD 2>/dev/null || true
git log --oneline -5 2>/dev/null || true
echo ""
git status --short 2>/dev/null || true

echo ""
echo "## 1. Final endpoint"
echo '```lean'
sed -n '1,70p' RHFormalization/FinalRHAssembly.lean
echo '```'

echo ""
echo "## 2. Current known strategic map"
cat <<'MAP'
FINAL TARGET:
  final_RH_assembly

It needs:
  sigma0
  Y : DDetailedConstructionWithOperatorLegality
  hYC : Y.B.Cshared = shiftedLaplacePrimePackageAt sigma0
  h_Cshared_sigma_le

Zero side:
  treated as banked inside FinalRHAssembly:
    hsum_unconditional
    h_real_zero_free
    buildEnvelopeFromZeroDensity
    buildZeroPoleLUCAPIFromEnvelope
    meromorphicOn_from_convergence
    h_pp_from_convergence
    groupedResidueCoeff_ne_zero

Main live issue:
  Build or choose a Y whose B.Cshared matches shiftedLaplacePrimePackageAt 1.

Do NOT drift into:
  designedY route
  old displacement/mass-envelope kernelID route unless explicitly chosen
  resolvent detour unless final endpoint requires it
  broad endpoint auditing

Recent banked route:
  RealPrimeShiftedLaplaceDBcanFromMajorant
  RealPrimeShiftedLaplaceMajorantFields
  RealPrimeShiftedLaplaceMajorantIndex

Meaning:
  DBcan-from-majorant route works.
  kernel agreement is banked.
  R-cutoff index wrapper is banked.
  But this route is optional unless we intentionally build the majorant data.
MAP

echo ""
echo "## 3. Recent files we created/banked"
for f in \
  RHFormalization/RealPrimeShiftedLaplaceDBcanFromMajorant.lean \
  RHFormalization/RealPrimeShiftedLaplaceMajorantFields.lean \
  RHFormalization/RealPrimeShiftedLaplaceMajorantIndex.lean \
  RHFormalization/RealPrimeRHSharp.lean \
  RHFormalization/FinalRHAssembly.lean
do
  echo ""
  echo "### $f"
  if [ -f "$f" ]; then
    grep -nE "theorem |def |#print axioms|sorry|admit|designedY" "$f" | head -80 || true
  else
    echo "MISSING"
  fi
done

echo ""
echo "## 4. Built Y candidates"
grep -rn ": DDetailedConstructionWithOperatorLegality\|def .*Y\|structure .*Y" RHFormalization/*.lean \
  | grep -v "designedY" \
  | head -120 || true

echo ""
echo "## 5. DBcan candidates"
grep -rn "shiftedLaplaceDBcanLimitSigma1\|resolventDBcanLimit\|realPrimeShiftedLaplaceDBcan_fromMajorant\|DBcanLimitData" RHFormalization/*.lean \
  | grep -E "def |theorem |:= " \
  | head -120 || true

echo ""
echo "## 6. hYC / Cshared bridge search"
grep -rn "hYC\|Cshared = shiftedLaplacePrimePackageAt\|shiftedLaplacePrimePackageAt\|Cshared_eq_model\|B.Cshared" RHFormalization/*.lean \
  | head -120 || true

echo ""
echo "## 7. Sorry/admit gate in current endgame files"
grep -nE "sorry|admit" \
  RHFormalization/FinalRHAssembly.lean \
  RHFormalization/RealPrimeRHSharp.lean \
  RHFormalization/RealPrimeY.lean \
  RHFormalization/RealPrimeShiftedLaplaceDBcanFromMajorant.lean \
  RHFormalization/RealPrimeShiftedLaplaceMajorantFields.lean \
  RHFormalization/RealPrimeShiftedLaplaceMajorantIndex.lean \
  2>/dev/null || echo "No sorry/admit in listed endgame files."

echo ""
echo "## 8. Axiom checks for recent banked terms"
lake build RHFormalization.RealPrimeShiftedLaplaceDBcanFromMajorant \
           RHFormalization.RealPrimeShiftedLaplaceMajorantFields \
           RHFormalization.RealPrimeShiftedLaplaceMajorantIndex \
  2>&1 | grep -E "error|sorry|sorryAx|Built RHFormalization.RealPrimeShiftedLaplace|depends on axioms" | tail -80 || true

echo ""
echo "## 9. Next instruction for assistant"
cat <<'NEXT'
Do not restart broad auditing.

First answer this decision:
  Which Y should feed final_RH_assembly?

Check in order:
  1. Is there already a complete non-designed Y with B.Cshared = shiftedLaplacePrimePackageAt 1?
  2. If yes, plug it into final_RH_assembly with banked providers.
  3. If no, use the shortest Y construction route:
       either realPrimeY with banked S/F/R,
       or shiftedLaplace sigma1 Y if full F/R/sectors/master exist.
  4. Only continue the RealPrimeShiftedLaplaceMajorant route if we deliberately need a new B/DBcan for realPrimeY.

Current live route if majorant path is chosen:
  Build CanonicalPrimePowerMajorantKernelSeriesData
    (primePerturbedOperatorLayerAligned μ)
  with Kshared := shiftedLaplaceHeatKernelC.
NEXT

} > "$OUT"

echo "Wrote $OUT"
