from pathlib import Path
import re

root = Path("RHFormalization")

patterns = [
    re.compile(r"\b(def|theorem|lemma|axiom)\b.*DFiniteStage"),
    re.compile(r"DFiniteStage\.mk"),
    re.compile(r"∃\s*α\s*:\s*DFiniteStage"),
    re.compile(r"exists.*DFiniteStage", re.IGNORECASE),
    re.compile(r"with_R", re.IGNORECASE),
    re.compile(r"R_ge", re.IGNORECASE),
    re.compile(r"h_diagonalSpikeToPP_complete_center_le_R"),
]

skip = {
    "SelectedDWindowAlphaIndexDataInstance.lean",
    "AppendixDOrderedCutoffStageSequence.lean",
}

for p in sorted(root.rglob("*.lean")):
    if ".lake" in p.parts or p.name in skip:
        continue
    txt = p.read_text(errors="ignore")
    hits = []
    for i, line in enumerate(txt.splitlines(), start=1):
        if any(pat.search(line) for pat in patterns):
            hits.append((i, line.rstrip()))
    if hits:
        print(f"===== {p} =====")
        for i, line in hits[:120]:
            print(f"{i}: {line}")
        if len(hits) > 120:
            print(f"... {len(hits)-120} more hits")
        print()
