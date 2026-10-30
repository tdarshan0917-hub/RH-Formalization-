# Smoothed oscillating densities on the common axis k = T, compared with the zeta zeros.
import numpy as np, json, math, time
from graph import *
GAM = np.array(json.load(open("zeros.json")))
Tg = np.linspace(20, 640, 12000)

def graph_density(ps, sigma, T, eps):
    """exact Lorentzian-smoothed level density via d = L/pi + (1/pi) Re Tr(Lam U (I-U)^-1) at k=T+i eps"""
    logp = np.log(ps.astype(float)); B = len(ps); I = np.eye(B); out = np.empty(len(T))
    for i0 in range(0, len(T), 2000):
        k = T[i0:i0+2000] + 1j*eps
        D = np.exp(1j*np.outer(k, logp))
        U = D[:, :, None]*sigma[None]
        X = np.linalg.solve(I[None] - U, U)                     # U (I-U)^-1 == (I-U)^-1 U
        out[i0:i0+2000] = np.real(np.einsum('b,nbb->n', logp, X))/math.pi
    return out                                                  # oscillating part only

def zeta_density_osc(T, eps):
    d = np.sum(eps/((T[:, None]-GAM[None, :])**2 + eps**2), axis=1)/math.pi
    return d - np.log(T/(2*math.pi))/(2*math.pi)

def theory_prime_powers(ps, T, eps, sign_alt=False):
    # zeta's explicit-formula terms restricted to the graph's primes: -(1/pi) sum log p p^{-m/2-m eps} cos(mT log p)
    out = np.zeros(len(T))
    for p in ps:
        lp = math.log(p)
        for m in range(1, 40):
            a = p**(-m/2 - m*eps)
            if a < 1e-12: break
            out -= lp*a*np.cos(m*T*lp)/math.pi
    return out

# consistency check (P=30): Lorentzian density from roots vs trace formula
ps = primes_upto(30); sig = unitary_with_diagonal(-1/np.sqrt(ps.astype(float)), seed=2)
r, L = spectrum(ps, sig, 700.0)
Tc = np.linspace(100, 110, 50); e = 0.5
dr = np.sum(e/((Tc[:, None]-r[None, :])**2+e**2), axis=1)/math.pi - L/math.pi
dt = graph_density(ps, sig, Tc, e)
print("check: roots vs trace-formula density, max abs diff %.2e (density scale %.2f)" % (np.max(np.abs(dr-dt)), np.std(dr)))

for P in [30, 100, 300]:
    ps = primes_upto(P); B = len(ps)
    t = time.time()
    sigs = {"diag -p^-1/2": unitary_with_diagonal(-1/np.sqrt(ps.astype(float)), seed=2)}
    rng = np.random.default_rng(5)
    sigs["diag shuffled (null)"] = unitary_with_diagonal(-1/np.sqrt(rng.permutation(ps).astype(float)), seed=2)
    sigs["random unitary (null)"] = random_unitary(B, 3)
    for eps in [0.3, 0.7, 1.5]:
        z = zeta_density_osc(Tg, eps)
        th = theory_prime_powers(ps, Tg, eps)
        line = "P=%3d eps=%.1f  theory(prime-power terms only) corr %+.3f |" % (P, eps, np.corrcoef(th, z)[0,1])
        for name, s in sigs.items():
            g = graph_density(ps, s, Tg, eps)
            line += "  %s %+.3f" % (name, np.corrcoef(g, z)[0,1])
        print(line)
    print("   (%.1fs)" % (time.time()-t))
