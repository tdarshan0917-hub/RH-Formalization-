from pathlib import Path

root = Path("RHFormalization")
needles = [
    "ℕ → DFiniteStage",
    "Nat → DFiniteStage",
    "alpha : ℕ → DFiniteStage",
    "alpha : Nat → DFiniteStage",
    "alpha :=",
    ".alpha",
    "DFiniteStage.R",
    "h_R_ge_nat",
    "h_indices_contains_of_center_le_R",
    "h_indices_subset_center_le_R",
]

skip_fragments = [
    ".lake",
    "SelectedDWindowAlphaIndexDataInstance.lean",
]

for p in sorted(root.rglob("*.lean")):
    if any(s in str(p) for s in skip_fragments):
        continue
    try:
        txt = p.read_text()
    except UnicodeDecodeError:
        continue
    hits = []
    for i, line in enumerate(txt.splitlines(), start=1):
        if any(n in line for n in needles):
            hits.append((i, line.rstrip()))
    if hits:
        print(f"===== {p} =====")
        for i, line in hits[:80]:
            print(f"{i}: {line}")
        if len(hits) > 80:
            print(f"... {len(hits)-80} more hits")
        print()
