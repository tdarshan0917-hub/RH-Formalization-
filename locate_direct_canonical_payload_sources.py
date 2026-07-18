from pathlib import Path
import re

root = Path("RHFormalization")

skip_names = {
    "SelectedFiniteCanonicalPayload.lean",
    "SelectedFiniteCanonicalPayloadInstance.lean",
    "SelectedFiniteTraceSpikePayload.lean",
    "SelectedFiniteTraceSpikePayloadInstance.lean",
    "SelectedFiniteTraceSpikePayloadFromImageBridge.lean",
    "SelectedFiniteTraceSpikePayloadCertified.lean",
    "FiniteNatPrimePowerBridge.lean",
}

needles = [
    "DFiniteTraceFunctionData.mk",
    "DFiniteTraceConstructionAPI.mk",
    "DFiniteStageSplitAPI.mk",
    "DFiniteStageSplitFromDuhamelAPI.mk",
    "DFiniteStageCanonicalPrimePowerFormula.mk",
    "h_B_stage_eq_finiteCanonical",
    "finiteCanonicalPrimePowerPackage",
    "F_stage :=",
    "B_stage :=",
    "R_stage :=",
    "sigma0 :=",
    "indices :=",
    "kernel :=",
    "selectedFiniteCanonicalPayload",
    "CanonicalPayload",
    "canonicalFormula",
    "toFiniteCanonicalPrimePowerFormula",
]

print("===== SEARCHING NON-SCRATCH SOURCE FILES ONLY =====")

for p in sorted(root.rglob("*.lean")):
    if p.name in skip_names:
        continue
    if ".lake" in p.parts or ".git" in p.parts:
        continue

    try:
        txt = p.read_text()
    except UnicodeDecodeError:
        continue

    lines = txt.splitlines()
    hits = []
    for i, line in enumerate(lines, start=1):
        if any(n in line for n in needles):
            hits.append((i, line.rstrip()))

    if hits:
        print(f"===== {p} =====")
        for i, line in hits[:120]:
            print(f"{i}: {line}")
        if len(hits) > 120:
            print(f"... {len(hits) - 120} more hits")
        print()
