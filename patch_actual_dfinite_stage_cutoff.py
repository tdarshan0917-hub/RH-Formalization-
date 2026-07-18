from pathlib import Path
import sys

root = Path("RHFormalization")

candidates = []
for p in sorted(root.rglob("*.lean")):
    txt = p.read_text(errors="ignore")
    if "structure DFiniteStage" in txt:
        candidates.append(p)

print("DFiniteStage source candidates:")
for p in candidates:
    print("  ", p)

if len(candidates) != 1:
    print("ERROR: expected exactly one source file defining `structure DFiniteStage`.")
    sys.exit(1)

p = candidates[0]
text = p.read_text()
print(f"Using source file: {p}")

if "h_diagonalSpikeToPP_center_le_R" in text:
    print("Cutoff compatibility fields already present.")
else:
    lines = text.splitlines()
    marker_idx = None
    for i, line in enumerate(lines):
        if "h_canonicalSpikeContribution_eq_weightC" in line:
            marker_idx = i
            break

    if marker_idx is None:
        print("ERROR: source file has DFiniteStage but no h_canonicalSpikeContribution_eq_weightC marker.")
        print("Nearby canonicalSpike lines:")
        for i, line in enumerate(lines, start=1):
            if "canonicalSpike" in line or "diagonalSpikeToPP" in line:
                lo = max(1, i - 3)
                hi = min(len(lines), i + 5)
                for j in range(lo, hi + 1):
                    print(f"{j}: {lines[j-1]}")
                print()
        sys.exit(1)

    # Move to the end of the existing h_canonicalSpikeContribution_eq_weightC field.
    insert_at = marker_idx + 1
    while insert_at < len(lines):
        line = lines[insert_at]
        if "weightC" in line:
            insert_at += 1
            break
        insert_at += 1

    insert = [
        "",
        "  /--",
        "  Every selected diagonal-spike prime-power lies below the stage `R` cutoff.",
        "  This is the stage-level cutoff soundness certificate needed by the",
        "  selected D-window alpha/index package.",
        "  -/",
        "  h_diagonalSpikeToPP_center_le_R :",
        "    ∀ n : ℕ,",
        "      n ∈ diagonalSpikeActiveIndices →",
        "        (diagonalSpikeToPP n).center ≤ R",
        "",
        "  /--",
        "  Every prime-power pair below the stage `R` cutoff is represented by one",
        "  selected diagonal-spike index.",
        "  This is the stage-level cutoff completeness certificate needed by the",
        "  selected D-window alpha/index package.",
        "  -/",
        "  h_diagonalSpikeToPP_complete_center_le_R :",
        "    ∀ q : PrimePowerPair,",
        "      q.center ≤ R →",
        "        ∃ n : ℕ,",
        "          n ∈ diagonalSpikeActiveIndices ∧",
        "            diagonalSpikeToPP n = q",
    ]

    lines[insert_at:insert_at] = insert
    p.write_text("\n".join(lines) + "\n")
    print("Inserted cutoff compatibility fields into DFiniteStage.")

module = ".".join(p.with_suffix("").parts)
Path(".dfinite_stage_module").write_text(module + "\n")
print(f"MODULE={module}")
