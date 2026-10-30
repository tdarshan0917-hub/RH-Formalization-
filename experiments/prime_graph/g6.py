# Step 1: suppress ALL composite (mixed) orbits by gradient descent on the unitary group.
# Objective uses only prime data: J = mean_T [graph_osc(T) - pp_target(T)]^2, where pp_target is the
# graph's own single-bond (prime-power) part. No zeta zeros are used in the optimization.
import numpy as np, math, time, sys, json
from scipy.linalg import polar, expm
from graph import primes_upto, unitary_with_diagonal
from g2 import graph_density, zeta_density_osc, theory_prime_powers, Tg

def pp_part(ps, d, T, eps):
    lp = np.log(ps.astype(float)); k = T + 1j*eps
    y = d[None]*np.exp(1j*np.outer(k, lp))
    return np.real(np.sum(lp[None]*y/(1-y), axis=1))/math.pi

def objective_and_grad(s, ps, d, T, eps):
    lp = np.log(ps.astype(float)); B = len(ps); I = np.eye(B)
    k = T + 1j*eps
    D = np.exp(1j*np.outer(k, lp))                      # (n,B)
    U = D[:, :, None]*s[None]
    R = np.linalg.inv(I[None] - U)                      # (n,B,B)
    X = R - I[None]
    f = np.real(np.einsum('b,nbb->n', lp, X))/math.pi
    fm = f - pp_part(ps, d, T, eps)                     # mixed-orbit part
    J = np.mean(fm**2)
    # d Tr(Lam X) = Tr(R Lam R D dsigma)  ->  holomorphic gradient G = (R Lam R D)^T
    RL = R*lp[None, None, :]                            # R @ diag(lp)
    M = np.einsum('nij,njk->nik', RL, R) * D[:, None, :]   # (R Lam R) @ diag(D)
    G = np.transpose(M, (0, 2, 1))
    grad = np.mean(fm[:, None, None]*np.conj(G), axis=0)/math.pi   # dJ/d conj(sigma) (up to factor)
    return J, grad

def optimize_all(ps, d, s, eps=0.15, iters=300, nT=600, lr=0.05, seed=0, log=True):
    rng = np.random.default_rng(seed); B = len(ps)
    for it in range(iters):
        T = rng.uniform(20, 640, nT)
        J, g = objective_and_grad(s, ps, d, T, eps)
        g[np.diag_indices(B)] = 0
        # Riemannian step on U(B): skew-Hermitian direction
        A = s.conj().T @ g; A = (A - A.conj().T)/2
        s = s @ expm(-lr*A/ (np.linalg.norm(A)+1e-12))
        for _ in range(3):
            s[np.diag_indices(B)] = d; s, _ = polar(s)
        if log and it % 50 == 0: print("   it %d  mixed-energy %.5f" % (it, J), flush=True)
    for _ in range(200):
        s[np.diag_indices(B)] = d; s, _ = polar(s)
    return s

if __name__ == "__main__":
    out = {}
    for P in [int(a) for a in sys.argv[1:]] or [300]:
        ps = primes_upto(P); B = len(ps); d = 1/np.sqrt(ps.astype(float))
        t = time.time()
        try: s = np.load("sigma_plus_P%d.npy" % P)
        except Exception: s = unitary_with_diagonal(d, seed=2, iters=800)
        Tev = np.random.default_rng(99).uniform(20, 640, 800)
        J0, _ = objective_and_grad(s, ps, d, Tev, 0.15)
        s = optimize_all(ps, d, s, iters=300 if B < 100 else 150, nT=600 if B < 100 else 250)
        J1, _ = objective_and_grad(s, ps, d, Tev, 0.15)
        np.save("sigma_all_P%d.npy" % P, s)
        res = dict(P=P, B=B, mixed_before=J0, mixed_after=J1, time=time.time()-t,
                   diag_err=float(np.max(np.abs(np.diag(s)-d))),
                   unit_err=float(np.max(np.abs(s.conj().T@s-np.eye(B)))))
        for eps in [0.15, 0.3, 0.7]:
            z = zeta_density_osc(Tg, eps)
            res["corr_%.2f" % eps] = float(np.corrcoef(graph_density(ps, s, Tg, eps), z)[0,1])
            res["ceil_%.2f" % eps] = float(np.corrcoef(theory_prime_powers(ps, Tg, eps), z)[0,1])
        print(json.dumps(res), flush=True)
        out[P] = res
    json.dump(out, open("g6_results_%s.json" % "_".join(map(str, out.keys())), "w"))
