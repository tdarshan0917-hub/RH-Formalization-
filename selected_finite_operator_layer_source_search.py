from pathlib import Path

root = Path("RHFormalization")

needles = [
    "selectedFiniteOperatorLayer",
    "DFiniteStagePackageFromOperatorLayer.mk",
    "DFiniteStageOperatorLegality.mk",
    "DFiniteTraceConstructionAPI.mk",
    "DFiniteTraceFunctionData.mk",
    "DFiniteStageSplitFromDuhamelAPI.mk",
    "DFiniteStageSpikeSumData.mk",
    "DStageSelfAdjointC",
    "DStageLowerSemiboundedC",
    "DStageShiftedNonnegativeC",
    "DStageHeatTraceClassC",
    "DStageResolventTraceLegalC",
    "DStageDuhamelTraceNormLegalC",
    "DStageDiagonalSpikeExtractionC",
    "DStageMixedWordControlC",
    "traceConstruction",
    "traceData",
    "splitFromDuhamel",
    "spikeSumData",
]

for p in sorted(root.rglob("*.lean")):
    try:
        txt = p.read_text()
    except UnicodeDecodeError:
        continue

    hits = []
    for i, line in enumerate(txt.splitlines(), start=1):
        if any(n in line for n in needles):
            hits.append((i, line.strip()))

    if hits:
        print(f"===== {p} =====")
        for i, line in hits[:80]:
            print(f"{i}: {line}")
        if len(hits) > 80:
            print(f"... {len(hits) - 80} more hits")
        print()
