from pathlib import Path

root = Path("RHFormalization")

needles = [
    "selectedClosedPayload",
    "selectedFiniteOperatorLayer",
    "selectedH0",
    "selectedHeatKernelWeighted",
    "CanonicalPrimePowerSharpCutoffHeatKernelWeightedClosedPayload.mk",
    "DFiniteStagePackageFromOperatorLayer.mk",
    "DCanonicalWindowSharpCutoffConcreteChosenSpeedData.mk",
    "PrimePowerDWindowKernelIdentificationData.mk",
    "PrimePowerWeightCutoffEnumerationData.mk",
    "PrimePowerMassEnvelopeData.mk",
    "exactPrimePowerMassEnvelopeData",
    "buildCanonicalPrimePowerSharpCutoffHeatKernelWeightedDataFromClosedPayload",
    "buildCanonicalPrimePowerSharpCutoffHeatKernelWeightedDataClosedSummability",
    "heatKernelWeightedEnvelope_summable",
    "h_R_ge_nat",
    "h_indices_contains_of_center_le_R",
    "h_indices_subset_center_le_R",
    "h_coordSet_compact",
    "h_coord_mem",
    "hL_chosen",
]

for p in sorted(root.rglob("*.lean")):
    try:
        txt = p.read_text()
    except UnicodeDecodeError:
        continue

    hits = []
    lines = txt.splitlines()
    for i, line in enumerate(lines, start=1):
        for needle in needles:
            if needle in line:
                hits.append((i, line.strip()))
                break

    if hits:
        print(f"===== {p} =====")
        for i, line in hits[:80]:
            print(f"{i}: {line}")
        if len(hits) > 80:
            print(f"... {len(hits) - 80} more hits")
        print()
