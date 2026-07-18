from pathlib import Path

here = Path.cwd().resolve()
roots = [here, here.parent]

# Also search sibling RHFormalization iterations in the parent directory.
for p in here.parent.iterdir():
    if p.is_dir() and ("RHFormalization" in p.name or "LeanCompanion" in p.name or "Iteration" in p.name):
        roots.append(p.resolve())

# Deduplicate while preserving order.
seen = set()
dedup_roots = []
for r in roots:
    if r not in seen:
        seen.add(r)
        dedup_roots.append(r)

exact_needles = [
    "def selectedFiniteTraceSpikePayload",
    "noncomputable def selectedFiniteTraceSpikePayload",
    "theorem selectedFiniteTraceSpikePayload",
    "selectedFiniteTraceSpikePayload : SelectedFiniteTraceSpikePayload",
]

support_needles = [
    "SelectedFiniteTraceSpikePayload",
    "h_B_stage_eq_diagonal_sum",
    "h_canonical_sum_eq_finiteCanonical",
    "buildSelectedFiniteOperatorLayerFromTraceSpikePayload",
]

print("===== SEARCH ROOTS =====")
for r in dedup_roots:
    print(r)
print()

exact_hits = []
support_hits = []

for root in dedup_roots:
    if not root.exists():
        continue
    for p in sorted(root.rglob("*.lean")):
        parts = set(p.parts)
        if ".lake" in parts or ".git" in parts:
            continue
        try:
            txt = p.read_text()
        except UnicodeDecodeError:
            continue

        lines = txt.splitlines()
        local_exact = []
        local_support = []

        for i, line in enumerate(lines, start=1):
            stripped = line.strip()
            if any(n in stripped for n in exact_needles):
                local_exact.append((i, stripped))
            elif any(n in stripped for n in support_needles):
                local_support.append((i, stripped))

        if local_exact:
            exact_hits.append((p, local_exact))
        elif local_support:
            support_hits.append((p, local_support[:20]))

print("===== EXACT selectedFiniteTraceSpikePayload DEFINITIONS =====")
if not exact_hits:
    print("NO EXACT selectedFiniteTraceSpikePayload DEFINITION FOUND")
else:
    for p, hits in exact_hits:
        print(f"FILE: {p}")
        for i, line in hits:
            print(f"  {i}: {line}")
        print()

print("===== SUPPORTING TRACE/SPIKE PAYLOAD FILES =====")
if not support_hits:
    print("NO SUPPORT FILES FOUND")
else:
    for p, hits in support_hits[:80]:
        print(f"FILE: {p}")
        for i, line in hits:
            print(f"  {i}: {line}")
        print()
