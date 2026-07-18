from pathlib import Path

root = Path("RHFormalization")

needles = [
    "CanonicalPrimePowerDWindowMassCountingSetWeightEnvelopeData.mk",
    "CanonicalPrimePowerDWindowMassCountingSetWeightEnvelopeData",
    "SelectedSharpCutoffClosedDWindowSource",
    "selectedSharpCutoffClosedDWindowSource",
    "sharpCutoffDCanonicalWindowData",
    "displacementCanonicalKernel",
    "DCanonicalWindowSharpCutoffConcreteChosenSpeedData.mk",
    "hL_chosen",
    "hW",
    "hKshared",
    "massCountingSetWeightEnvelope",
    "h_countWeight_div_denominator_tendsto_zero",
]

skip = {
    "CanonicalPrimePowerSharpCutoffClosedDWindowSource.lean",
    "CanonicalPrimePowerSharpCutoffClosedDWindowSourceInstance.lean",
}

for p in sorted(root.rglob("*.lean")):
    if ".lake" in p.parts or p.name in skip:
        continue
    txt = p.read_text(errors="ignore")
    if not any(n in txt for n in needles):
        continue

    lines = txt.splitlines()
    hits = []
    for i, line in enumerate(lines, start=1):
        if any(n in line for n in needles):
            hits.append(i)

    if not hits:
        continue

    print(f"===== {p} =====")
    printed = set()
    for i in hits:
        block = i // 35
        if block in printed:
            continue
        printed.add(block)
        lo = max(1, i - 8)
        hi = min(len(lines), i + 22)
        print(f"--- around line {i} ---")
        for j in range(lo, hi + 1):
            print(f"{j}: {lines[j-1]}")
        print()
