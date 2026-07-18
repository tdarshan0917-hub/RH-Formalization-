from pathlib import Path

root = Path("RHFormalization")

# Only inspect files likely to contain the closed D-window / heat-kernel / mass data.
name_filters = [
    "CanonicalPrimePower",
    "DCanonicalWindow",
    "DWindow",
    "HeatKernel",
    "MassEnvelope",
    "CutoffMass",
]

needles = [
    "selectedClosedPayload",
    "selectedH0",
    "selectedFiniteOperatorLayer",
    "CanonicalPrimePowerSharpCutoffHeatKernelWeightedClosedPayload",
    "CanonicalPrimePowerSharpCutoffHeatKernelWeightedClosedPayload.mk",
    "DCanonicalWindowSharpCutoffConcreteChosenSpeedData.mk",
    "PrimePowerDWindowKernelIdentificationData.mk",
    "PrimePowerWeightCutoffEnumerationData.mk",
    "exactPrimePowerMassEnvelopeData",
    "sharpCutoffDCanonicalWindowData",
    "displacementCanonicalKernel",
    "alpha : ℕ → DFiniteStage",
    "alpha := ",
    "Lstage := ",
    "sharpSpeed := ",
    "kernelID := ",
    "coordSet := ",
    "massEnum := ",
    "massEnvelopeData := ",
    "h_R_ge_nat",
    "h_indices_contains_of_center_le_R",
    "h_indices_subset_center_le_R",
    "h_coordSet_compact",
    "h_coord_mem",
    "hL_chosen",
    "h_stage_kernel_eq_window",
    "h_shared_kernel_eq_limit",
    "hL_pos",
    "compactRadius",
    "Gbound",
]

def interesting(path: Path) -> bool:
    s = str(path)
    return (
        ".lake" not in path.parts
        and path.suffix == ".lean"
        and any(f in s for f in name_filters)
    )

def print_window(path: Path, lines, i, before=8, after=18):
    lo = max(1, i - before)
    hi = min(len(lines), i + after)
    print(f"===== {path}:{i} =====")
    for j in range(lo, hi + 1):
        print(f"{j}: {lines[j-1]}")
    print()

for p in sorted(root.rglob("*.lean")):
    if not interesting(p):
        continue

    txt = p.read_text(errors="ignore")
    if not any(n in txt for n in needles):
        continue

    lines = txt.splitlines()
    printed_blocks = set()

    for i, line in enumerate(lines, start=1):
        if any(n in line for n in needles):
            # Avoid dumping the same nearby block repeatedly.
            key = (str(p), i // 35)
            if key in printed_blocks:
                continue
            printed_blocks.add(key)
            print_window(p, lines, i)
