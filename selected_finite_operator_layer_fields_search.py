from pathlib import Path

root = Path("RHFormalization")

needles = [
    "selectedFiniteStageOperatorLegality",
    "selectedTraceConstruction",
    "selectedTraceData",
    "selected_traceData_from_legality",
    "selectedSplitFromDuhamel",
    "selectedSpikeSumData",
    "DFiniteTraceConstructionAPI.mk",
    "DFiniteTraceFunctionData.mk",
    "DFiniteStageSplitFromDuhamelAPI.mk",
    "DFiniteStageSpikeSumData.mk",
    "DFiniteStageOperatorLegality.mk",
    "DStageHeatTraceClassC_of_pos",
    "DStageResolventTraceLegalC_of_mem_Omega",
    "DStageDuhamelTraceNormLegalC_from_majorant",
    "DStageDiagonalSpikeExtractionC_from_stage_certificate",
    "DStageMixedWordControlC_from_stage_certificate",
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
        for i, line in hits[:120]:
            print(f"{i}: {line}")
        if len(hits) > 120:
            print(f"... {len(hits) - 120} more hits")
        print()
