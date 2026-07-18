from pathlib import Path

root = Path("RHFormalization")

needles = [
    "activeIndices :",
    "activeIndices :=",
    "spikeKernel :",
    "spikeKernel :=",
    "ppIndices :",
    "ppIndices :=",
    "ppKernel :",
    "ppKernel :=",
    "h_B_stage_eq_diagonal_sum",
    "h_canonical_sum_eq_finiteCanonical",
    "h_activeIndices_active",
    "diagonalSpikeActive",
    "diagonalSpikeContribution",
    "canonicalSpikeContribution",
    "finiteNatSpikePackage",
    "finiteCanonicalPrimePowerPackage",
    "selectedFiniteTraceSpikePayload",
]

exclude_files = {
    "SelectedFiniteTraceSpikePayload.lean",
    "SelectedFiniteOperatorLayer.lean",
}

for p in sorted(root.rglob("*.lean")):
    if p.name in exclude_files:
        continue
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
        for i, line in hits[:160]:
            print(f"{i}: {line}")
        if len(hits) > 160:
            print(f"... {len(hits) - 160} more hits")
        print()
