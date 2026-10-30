# Quantum star graph: one bond per prime p, length l_p = (1/2) log p, so a round trip on bond p
# has phase p^{ik}.  Quantum map U(k) = diag(p^{ik}) @ sigma  (sigma = central-vertex scattering).
# Spectrum: real k with det(I - U(k)) = 0.
import numpy as np, json, math
from scipy.linalg import polar

def primes_upto(P):
    s = np.ones(P+1, bool); s[:2] = False
    for i in range(2, int(P**0.5)+1):
        if s[i]: s[i*i::i] = False
    return np.nonzero(s)[0]

def unitary_with_diagonal(d, seed=0, iters=3000):
    """unitary sigma whose diagonal is (approximately) d, via alternating projections"""
    rng = np.random.default_rng(seed); B = len(d)
    M = (rng.normal(size=(B,B)) + 1j*rng.normal(size=(B,B)))/np.sqrt(2)
    Q, _ = np.linalg.qr(M)
    for _ in range(iters):
        Q[np.diag_indices(B)] = d
        Q, _ = polar(Q)
    return Q

def random_unitary(B, seed):
    rng = np.random.default_rng(seed)
    M = (rng.normal(size=(B,B)) + 1j*rng.normal(size=(B,B)))/np.sqrt(2)
    Q, R = np.linalg.qr(M); return Q * (np.diag(R)/np.abs(np.diag(R)))

def spectrum(ps, sigma, kmax, dk=None):
    logp = np.log(ps.astype(float)); B = len(ps)
    Ltot = logp.sum()/2.0                      # total bond length; mean density = Ltot/pi
    if dk is None: dk = (math.pi/Ltot)/25
    phi_s = np.angle(np.linalg.det(sigma))
    ks = np.arange(1e-6, kmax, dk)
    out = []
    CH = 4000
    I = np.eye(B)
    for i0 in range(0, len(ks), CH):
        k = ks[i0:i0+CH]
        D = np.exp(1j*np.outer(k, logp))                       # (n,B): p^{ik}
        U = D[:, :, None] * sigma[None, :, :]
        det = np.linalg.det(I[None] - U)
        ph = (k*logp.sum() + phi_s)/2                          # half of arg det U
        f = np.real(det*np.exp(-1j*ph)/(-2j)**B)               # = prod sin(theta_j/2), real
        out.append(f)
    f = np.concatenate(out)
    idx = np.nonzero(np.sign(f[:-1]) != np.sign(f[1:]))[0]
    # linear interpolation for roots
    roots = ks[idx] - f[idx]*(ks[idx+1]-ks[idx])/(f[idx+1]-f[idx])
    return roots, Ltot

def spacing_stats(levels, Ltot):
    x = np.sort(levels)*Ltot/math.pi                            # unfolded (constant density)
    s = np.diff(x); s = s/s.mean()
    return s.var(), np.mean(s < 0.3)
