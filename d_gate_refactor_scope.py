from pathlib import Path

root = Path("RHFormalization")

needles = [
    "spikeSumData",
    "DFiniteStageSpikeSumData",
    "buildDFiniteStageCanonicalPrimePowerFormulaFromSpikeSums",
    "toFiniteCanonicalPrimePowerFormula",
    "DFiniteStageCanonicalPrimePowerFormula",
    "h_B_stage_eq_finiteCanonical",
    "SelectedFiniteTraceSpikePayload",
    "SelectedFiniteTraceSpikePayloadInstance",
    "CertifiedSelectedFiniteTraceSpikePayload",
    "IsCertifiedFiniteAppendixDExtraction",
]

for p in sorted(root.rglob("*.lean")):
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
        for i, line in hits[:120]:
            print(f"{i}: {line}")
        if len(hits) > 120:
            print(f"... {len(hits) - 120} more hits")
        print()
