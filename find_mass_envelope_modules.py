from pathlib import Path

root = Path("RHFormalization")

print("===== EXACT FILE CHECK =====")
exact = root / "CanonicalPrimePowerMassEnvelope.lean"
print(f"{exact}: {'EXISTS' if exact.exists() else 'MISSING'}")
print()

print("===== FILES WITH MassEnvelope IN NAME =====")
for p in sorted(root.glob("*MassEnvelope*.lean")):
    print(p)
print()

print("===== FILES WITH CutoffMass / Enumeration IN NAME =====")
for p in sorted(root.glob("*Mass*.lean")):
    if "Cutoff" in p.name or "Enumeration" in p.name or "Envelope" in p.name:
        print(p)
print()

print("===== DEFINITIONS / STRUCTURES MENTIONING PrimePowerMassEnvelopeData =====")
for p in sorted(root.rglob("*.lean")):
    try:
        txt = p.read_text()
    except UnicodeDecodeError:
        continue
    if "PrimePowerMassEnvelopeData" in txt or "PrimePowerWeightCutoffEnumerationData" in txt:
        print(p)
        for i, line in enumerate(txt.splitlines(), start=1):
            if (
                "PrimePowerMassEnvelopeData" in line
                or "PrimePowerWeightCutoffEnumerationData" in line
                or "structure PrimePowerMassEnvelopeData" in line
                or "def " in line and "MassEnvelope" in line
            ):
                print(f"  {i}: {line.strip()}")
        print()

print("===== IMPORTS OF CanonicalPrimePowerMassEnvelope =====")
for p in sorted(root.rglob("*.lean")):
    try:
        txt = p.read_text()
    except UnicodeDecodeError:
        continue
    if "CanonicalPrimePowerMassEnvelope" in txt:
        print(p)
        for i, line in enumerate(txt.splitlines(), start=1):
            if "CanonicalPrimePowerMassEnvelope" in line:
                print(f"  {i}: {line.strip()}")
