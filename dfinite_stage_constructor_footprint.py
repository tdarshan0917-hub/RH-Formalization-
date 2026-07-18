from pathlib import Path

root = Path("RHFormalization")

needles = [
    "structure DFiniteStage",
    "DFiniteStage.mk",
    "diagonalSpikeActive :=",
    "diagonalSpikeContribution :=",
    "canonicalSpikeContribution :=",
    "h_diagonalSpikeExtraction :=",
]

for p in sorted(root.rglob("*.lean")):
    if ".lake" in p.parts:
        continue
    txt = p.read_text(errors="ignore")
    if not any(n in txt for n in needles):
        continue

    print(f"===== {p} =====")
    lines = txt.splitlines()
    for i, line in enumerate(lines, start=1):
        if any(n in line for n in needles):
            lo = max(1, i - 8)
            hi = min(len(lines), i + 22)
            print(f"--- around line {i} ---")
            for j in range(lo, hi + 1):
                print(f"{j}: {lines[j-1]}")
            print()
