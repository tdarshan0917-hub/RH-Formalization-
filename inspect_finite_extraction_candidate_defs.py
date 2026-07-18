from pathlib import Path

files = [
    "RHFormalization/CanonicalPrimePowerConcreteTsumPackage.lean",
    "RHFormalization/CanonicalPrimePowerKernelSeries.lean",
    "RHFormalization/CanonicalPrimePowerDWindowKernelIdentification.lean",
    "RHFormalization/CanonicalPrimePowerIndexExhaustion.lean",
    "RHFormalization/AppendixDSpikeSumExtraction.lean",
    "RHFormalization/DFiniteStageOperator.lean",
]

needles = [
    "def ",
    "theorem ",
    "lemma ",
    "structure ",
    "abbrev ",
    "class ",
    "noncomputable def ",
]

focus = [
    "DFiniteTraceFunctionData",
    "DFiniteStageSplitAPI",
    "DFiniteStageSplitFromDuhamelAPI",
    "DFiniteStageSpikeSumData",
    "DFiniteStageCanonicalPrimePowerFormula",
    "buildDFiniteStageCanonicalPrimePowerFormulaFromSpikeSums",
    "finiteNatSpikePackage",
    "finiteCanonicalPrimePowerPackage",
    "h_B_stage_eq_finiteCanonical",
    "h_B_stage_eq_diagonal_sum",
    "h_canonical_sum_eq_finiteCanonical",
    "toFiniteCanonicalPrimePowerFormula",
    "ConcreteTsum",
    "Kshared",
    "sigma0",
    "indices",
    "kernel",
    "PrimePowerPair",
    "weightC",
    "center",
]

def print_window(path, lines, i, before=8, after=28):
    lo = max(1, i - before)
    hi = min(len(lines), i + after)
    print(f"===== {path}:{i} =====")
    for j in range(lo, hi + 1):
        print(f"{j}: {lines[j-1]}")
    print()

for fname in files:
    p = Path(fname)
    if not p.exists():
        print(f"===== MISSING {fname} =====")
        continue

    lines = p.read_text().splitlines()
    printed = set()

    for i, line in enumerate(lines, start=1):
        stripped = line.strip()
        is_decl = any(stripped.startswith(n) for n in needles)
        is_focus = any(f in line for f in focus)

        if is_decl and is_focus:
            key = (fname, i)
            if key not in printed:
                printed.add(key)
                print_window(fname, lines, i)

    print(f"===== END {fname} =====")
    print()
