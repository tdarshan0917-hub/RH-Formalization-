# Decompose the graph density by orbit order m: prime-power (single-bond) part vs mixed (composite) part.
import numpy as np, math
from graph import primes_upto, unitary_with_diagonal
from g2 import Tg
T = Tg[::6]
for P in [300]:
    ps = primes_upto(P); lp = np.log(ps.astype(float)); d = -1/np.sqrt(ps.astype(float))
    for name, s in [("generic", unitary_with_diagonal(d, seed=2)), ("2-cycle-optimized", np.load("sigma_opt_P%d.npy" % P))]:
        for eps in [0.3, 0.7]:
            k = T + 1j*eps
            D = np.exp(1j*np.outer(k, lp)); U = D[:, :, None]*s[None]
            Um = np.repeat(np.eye(len(ps))[None], len(T), 0).astype(complex)
            line = "%-18s eps=%.1f  RMS per order m (prime-power | mixed):" % (name, eps)
            tot_pp = tot_mx = 0
            for m in range(1, 9):
                Um = Um @ U
                full = np.real(np.einsum('b,nbb->n', lp, Um))/math.pi
                diag = np.real(np.sum(lp[None]*(d[None]*D)**m, axis=1))/math.pi
                mixed = full - diag
                line += "  m%d %.3f|%.3f" % (m, np.std(diag), np.std(mixed))
            print(line)
