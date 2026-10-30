# Sign test: self-scattering +p^{-1/2} makes every prime-power orbit carry the explicit-formula
# weight with ONE consistent sign (opposite to the zeros): graph levels = "absorption" picture.
import numpy as np, math, time
from scipy.linalg import polar
from graph import primes_upto, unitary_with_diagonal
from g2 import graph_density, zeta_density_osc, theory_prime_powers, Tg
from g3 import two_cycle_weight
def optimize_d(ps, d, eps=0.3, iters=6000, eta=0.5, seed=2):
    B = len(ps); lp = np.log(ps.astype(float))
    W = (lp[:, None]+lp[None, :])**2*np.exp(-2*eps*(lp[:, None]+lp[None, :])); W /= W.max()
    s = unitary_with_diagonal(d, seed=seed, iters=500)
    for it in range(iters):
        G = W*s*(np.abs(s.T)**2); np.fill_diagonal(G, 0)
        s = s - eta*G; s[np.diag_indices(B)] = d; s, _ = polar(s)
    for _ in range(300):
        s[np.diag_indices(B)] = d; s, _ = polar(s)
    return s
for P in [100, 300]:
    ps = primes_upto(P); B = len(ps); d = +1/np.sqrt(ps.astype(float))
    t = time.time()
    s0 = unitary_with_diagonal(d, seed=2); s1 = optimize_d(ps, d)
    np.save("sigma_plus_P%d.npy" % P, s1)
    for name, s in [("diag +p^-1/2 generic", s0), ("diag +p^-1/2 optimized", s1)]:
        line = "P=%d %-24s diag err %.1e |" % (P, name, np.max(np.abs(np.diag(s)-d)))
        for eps in [0.15, 0.3, 0.7]:
            z = zeta_density_osc(Tg, eps); th = theory_prime_powers(ps, Tg, eps)
            line += "  eps=%.2f corr %+.3f (ceiling %.3f)" % (eps, np.corrcoef(graph_density(ps, s, Tg, eps), z)[0,1], np.corrcoef(th, z)[0,1])
        print(line)
    print("  (%.0fs)" % (time.time()-t))
