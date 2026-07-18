from pathlib import Path

targets = {
    "RHFormalization/SelectedFiniteTraceSpikePayload.lean": [
        "structure SelectedFiniteTraceSpikePayload",
        "def buildSelectedFiniteOperatorLayerFromTraceSpikePayload",
    ],
    "RHFormalization/DFiniteStageOperator.lean": [
        "structure DFiniteStage",
        "structure DFiniteTraceFunctionData",
        "structure DFiniteStagePackageFromOperatorLayer",
    ],
    "RHFormalization/AppendixDSpikeSumExtraction.lean": [
        "structure DFiniteStageSpikeSumData",
        "def finiteNatSpikePackage",
        "def finiteCanonicalPrimePowerPackage",
        "theorem finiteNatSpikePackage_eq_of_coeff_eq_on_indices",
        "def buildDFiniteStageCanonicalPrimePowerFormulaFromSpikeSums",
    ],
    "RHFormalization/CanonicalPrimePowerConcreteTsumPackage.lean": [
        "def PrimePowerPair",
        "abbrev PrimePowerPair",
        "abbrev CanonicalKernelC",
        "def finiteCanonicalPrimePowerPackage",
    ],
}

def print_window(path: Path, line_no: int, before: int = 12, after: int = 45):
    lines = path.read_text().splitlines()
    lo = max(1, line_no - before)
    hi = min(len(lines), line_no + after)
    print(f"===== {path}:{line_no} =====")
    for j in range(lo, hi + 1):
        print(f"{j}: {lines[j-1]}")
    print()

for file_name, needles in targets.items():
    p = Path(file_name)
    if not p.exists():
        print(f"===== MISSING FILE: {file_name} =====")
        continue

    lines = p.read_text().splitlines()
    seen = set()
    for needle in needles:
        for i, line in enumerate(lines, start=1):
            if needle in line and (file_name, i) not in seen:
                seen.add((file_name, i))
                print_window(p, i)
                break
