from pathlib import Path

root = Path("RHFormalization")

skip_files = {
    "SelectedFiniteTraceSpikePayloadInstance.lean",
    "SelectedFiniteTraceSpikePayloadFromImageBridge.lean",
    "SelectedFiniteTraceSpikePayload.lean",
    "FiniteNatPrimePowerBridge.lean",
}

needles = [
    "DFiniteTraceFunctionData.mk",
    "DFiniteStageSplitAPI.mk",
    "DFiniteStageSplitFromDuhamelAPI.mk",
    "DFiniteStageSpikeSumData.mk",
    "F_stage :=",
    "B_stage :=",
    "R_stage :=",
    "sigma0 :=",
    "activeIndices :=",
    "spikeKernel :=",
    "ppIndices :=",
    "ppKernel :=",
    "h_stage_split",
    "h_activeIndices_active",
    "h_B_stage_eq_diagonal_sum",
    "h_canonical_sum_eq_finiteCanonical",
    "h_B_stage_eq_finiteCanonical",
    "canonicalSpikeContribution",
    "diagonalSpikeContribution",
    "diagonalSpikeActive",
    "PrimePowerPair.weightC",
    ".weightC",
    ".center",
    "toPP",
    "Kcan",
    "toFiniteCanonicalPrimePowerFormula",
    "buildDFiniteStageCanonicalPrimePowerFormulaFromSpikeSums",
    "finiteCanonicalPrimePowerPackage",
    "finiteNatSpikePackage",
]

for p in sorted(root.rglob("*.lean")):
    if p.name in skip_files:
        continue

    try:
        txt = p.read_text()
    except UnicodeDecodeError:
        continue

    lines = txt.splitlines()
    hits = []
    for i, line in enumerate(lines, start=1):
        if any(needle in line for needle in needles):
            hits.append((i, line.rstrip()))

    if hits:
        print(f"===== {p} =====")
        for i, line in hits[:120]:
            print(f"{i}: {line}")
        if len(hits) > 120:
            print(f"... {len(hits) - 120} more hits")
        print()
