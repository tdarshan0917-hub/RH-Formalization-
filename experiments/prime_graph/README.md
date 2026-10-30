# Prime quantum star graph — experiment scripts

One bond per prime p <= P, length (1/2) log p. Quantum map U(k) = diag(p^{ik}) @ sigma,
sigma = B x B unitary central scattering. Levels: real k with det(I - U(k)) = 0.
Smoothed density (exact): d(T; eps) = L/pi + (1/pi) Re Tr(Lambda U (I - U)^{-1}) at k = T + i*eps,
Lambda = diag(log p). Compared against the first 400 zeta zeros (zeros.json, mpmath dps 20).

Requirements: Python 3, numpy, scipy (mpmath only to regenerate zeros.json).
Run from this folder.

| Script | What it does | Output |
|---|---|---|
| graph.py | primes, quantum map, level finder, unitary with prescribed diagonal (alternating projection) | library |
| g1.py | level-spacing statistics (variance, fraction < 0.3) vs zeros / GUE / Kirchhoff / random unitary | prints |
| g2.py | smoothed oscillating densities on axis k = T; correlation with the zeros' density | library + prints |
| g3.py | sigma with diag = -p^{-1/2}, suppress mixed 2-cycles sigma_pq*sigma_qp | sigma_opt_P{P}.npy |
| g4.py | decompose density by orbit order: prime-power part vs mixed (composite) part | prints |
| g5.py | sign test: diag = +p^{-1/2} gives one consistent sign (absorption mirror) | sigma_plus_P{P}.npy |
| g6.py | suppress ALL composite orbits: Riemannian gradient descent on U(B); objective uses primes only | sigma_all_P{P}.npy, g6_results_{P}.json |
| g7.py | holes: N most prominent dips (N from counting law) vs each zero, with random / midpoint nulls | g7_results_P{P}.json, g7_dist_P{P}.npy |
| g7b.py | ceiling: explicit formula truncated to primes <= P, same hole metric | g7b_ceiling_{P}.json |

Usage: `python3 g6.py 300` then `python3 g7.py 300` (P = 1000: g6 takes ~12 min on one CPU).

Key results (P = 1000, 168 bonds): mixed-orbit energy 0.136 -> 0.018; density correlation with zeros
-0.852 / -0.973 / -0.9996 at eps = 0.15 / 0.3 / 0.7 (ceilings 0.881 / 0.976 / 0.9997);
median zero-to-dip distance 0.042 mean spacings; 84% of zeros within 0.1 spacing
(ceiling 90%, random-point null 20%, midpoint null 7%).

Lean counterpart: RHFormalization/PrimeGraphTrace.lean (PG-1).
