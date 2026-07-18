from pathlib import Path

root = Path("RHFormalization")

needles = [
    "DFiniteStage.mk",
    "DFiniteTraceFunctionData.mk",
    "DFiniteStageSpikeSumData.mk",
    "DFiniteStageCanonicalPrimePowerFormula.mk",
    "buildDFiniteStageCanonicalPrimePowerFormulaFromSpikeSums",

    "diagonalSpikeActive :=",
    "diagonalSpikeContribution :=",
    "canonicalSpikeContribution :=",

    "activeIndices :=",
    "spikeKernel :=",
    "ppIndices :=",
    "ppKernel :=",

    "h_B_stage_eq_diagonal_sum :=",
    "h_canonical_sum_eq_finiteCanonical :=",
    "h_stage_split :=",
    "F_stage :=",
    "B_stage :=",
    "R_stage :=",
    "sigma0 :=",
]

exclude = {
    "SelectedFiniteTraceSpikePayload.lean",
    "SelectedFiniteTraceSpikePayloadInstance.lean",
    "SelectedFiniteOperatorLayer.lean",
}

for p in sorted(root.rglob("*.lean")):
    if p.name in exclude:
        continue

    try:
        lines = p.read_text().splitlines()
    except UnicodeDecodeError:
        continue

    hits = []
    for i, line in enumerate(lines, start=1):
        if any(n in line for n in needles):
            hits.append((i, line.rstrip()))

    if hits:
        print(f"===== {p} =====")
        for i, line in hits[:180]:
            print(f"{i}: {line}")
        if len(hits) > 180:
            print(f"... {len(hits) - 180} more hits")
        print()
