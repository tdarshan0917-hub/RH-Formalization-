from pathlib import Path

root = Path("RHFormalization")

skip_names = {
    "AppendixDFiniteSpikeExtractionWitness.lean",
    "AppendixDFiniteSpikeExtractionWitnessInstance.lean",
    "SelectedFiniteTraceSpikePayloadInstance.lean",
    "CorrectSelectedDSourceCheck.lean",
}

needles = [
    "DFiniteStage.mk",
    "diagonalSpikeActive :=",
    "diagonalSpikeContribution :=",
    "canonicalSpikeContribution :=",
    "h_diagonalSpikeExtraction :=",
    "activeIndices :=",
    "h_activeIndices_active",
    "h_activeIndices_complete",
    "toPP :=",
    "toPP",
    "Nat → PrimePowerPair",
    "ℕ → PrimePowerPair",
    "PrimePowerPair.weightC",
    "hcoeff",
    "hinj",
    "canonicalSpikeContribution",
    "diagonalSpikeActive",
    "selectedAppendixDFiniteSpikeExtractionWitness",
    "AppendixDFiniteSpikeExtractionWitness",
]

def print_window(path, lines, i, before=8, after=18):
    lo = max(1, i - before)
    hi = min(len(lines), i + after)
    print(f"===== {path}:{i} =====")
    for j in range(lo, hi + 1):
        print(f"{j}: {lines[j-1]}")
    print()

for p in sorted(root.rglob("*.lean")):
    if p.name in skip_names or ".lake" in p.parts:
        continue

    try:
        txt = p.read_text()
    except UnicodeDecodeError:
        continue

    if not any(n in txt for n in needles):
        continue

    lines = txt.splitlines()
    printed = set()

    for i, line in enumerate(lines, start=1):
        if any(n in line for n in needles):
            # Avoid printing the same nearby block repeatedly.
            key = (str(p), max(1, i // 30))
            if key in printed:
                continue
            printed.add(key)
            print_window(p, lines, i)
