# Search unitary sigma with diag = -p^{-1/2} that suppresses mixed 2-cycles sigma_pq*sigma_qp.
import numpy as np, json, math, time, sys
from scipy.linalg import polar
from graph import primes_upto, unitary_with_diagonal, random_unitary
from g2 import graph_density, zeta_density_osc, theory_prime_powers, Tg

def two_cycle_weight(s, W):
    A = np.abs(s)**2
    M = A*A.T; np.fill_diagonal(M, 0)
    return float(np.sum(W*M)/2), float(np.sqrt(M.max()))

def optimize(ps, eps=0.3, iters=6000, eta=0.5, seed=2):
    d = -1/np.sqrt(ps.astype(float)); B = len(ps)
    lp = np.log(ps.astype(float))
    W = (lp[:, None] + lp[None, :])**2 * np.exp(-2*eps*(lp[:, None] + lp[None, :]))
    W /= W.max()
    s = unitary_with_diagonal(d, seed=seed, iters=500)
    for it in range(iters):
        G = W*s*(np.abs(s.T)**2)                    # d f / d conj(sigma)
        np.fill_diagonal(G, 0)
        s = s - eta*G
        s[np.diag_indices(B)] = d
        s, _ = polar(s)
        if it % 50 == 0:                             # re-impose diagonal more tightly
            for _ in range(5):
                s[np.diag_indices(B)] = d; s, _ = polar(s)
    for _ in range(200):
        s[np.diag_indices(B)] = d; s, _ = polar(s)
    return s, W

if __name__ == "__main__":
    for P in [100, 300]:
        ps = primes_upto(P); B = len(ps); d = -1/np.sqrt(ps.astype(float))
        t = time.time()
        s0 = unitary_with_diagonal(d, seed=2)
        s1, W = optimize(ps)
        print("P=%d B=%d  (%.0fs)" % (P, B, time.time()-t))
        for name, s in [("before (generic)", s0), ("after optimization", s1)]:
            tw, mx = two_cycle_weight(s, W)
            derr = np.max(np.abs(np.diag(s) - d)); uerr = np.max(np.abs(s.conj().T@s - np.eye(B)))
            line = "  %-20s 2-cycle weight %.4f  max|s_pq s_qp| %.4f  diag err %.1e unitarity err %.1e |" % (name, tw, mx, derr, uerr)
            for eps in [0.3, 0.7]:
                z = zeta_density_osc(Tg, eps)
                line += "  corr(eps=%.1f) %.3f" % (eps, np.corrcoef(graph_density(ps, s, Tg, eps), z)[0,1])
            print(line)
        for eps in [0.3, 0.7]:
            print("  ceiling (prime-power terms only) eps=%.1f: %.3f" % (eps, np.corrcoef(theory_prime_powers(ps, Tg, eps), zeta_density_osc(Tg, eps))[0,1]))
        np.save("sigma_opt_P%d.npy" % P, s1)
