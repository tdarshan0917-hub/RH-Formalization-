#!/bin/zsh
lake build RHFormalization.SphereUniformConvergence 2>&1 | tee sph_a.log | grep -e "error" -e "depends on axioms" -e "Build completed"
if grep -q "error" sph_a.log; then
  echo "FAILED -> removing (errors below)"
  grep -B2 -A14 "error" sph_a.log | head -100
  rm RHFormalization/SphereUniformConvergence.lean
  exit 1
fi
for thm in isOpen_Omega_proved tendstoUniformlyOn_of_tlu_isCompact sphere_uniform_from_API; do
  if ! grep -q "$thm' depends on axioms: \[propext, Classical.choice, Quot.sound\]" sph_a.log; then
    echo "AXIOM CHECK FAILED ($thm) -> removing"; rm RHFormalization/SphereUniformConvergence.lean; exit 1
  fi
done
grep -qxF "import RHFormalization.SphereUniformConvergence" RHFormalization.lean || printf '\nimport RHFormalization.SphereUniformConvergence\n' >> RHFormalization.lean
lake build 2>&1 | tee sph_root.log | tail -3
grep -q "Build completed successfully" sph_root.log && tar --exclude='.lake' --exclude='*.bak*' --exclude='*.parked' -czf ~/Downloads/RHFormalization_SPHERE.tar.gz . && echo "SNAPSHOT SAVED: SPHERE"
