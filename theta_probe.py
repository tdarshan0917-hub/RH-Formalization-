import numpy as np
from numpy.linalg import eigvalsh
from scipy.fft import dst

# ---------- parameters you can tweak ----------
delta = 1.0                 # Gaussian width
theta_list = [0.25, 0.5, 0.75]
Ns = [32, 64, 96, 128, 192]  # try increasing
L_of_N = lambda N: int(round((N**0.75)))  # rough inverse of N≈(n+2)^4 vs L≈(n+2)^3

# ---------- prime powers up to R ----------
def prime_powers(R):
    # generate primes up to exp(R)
    import math
    maxp = int(np.floor(np.exp(R)))
    sieve = np.ones(maxp+1, dtype=bool)
    sieve[:2] = False
    for p in range(2, int(maxp**0.5)+1):
        if sieve[p]:
            sieve[p*p:maxp+1:p] = False
    primes = np.where(sieve)[0]

    qs = []
    ws = []
    for p in primes:
        m = 1
        while True:
            q = p**m
            if np.log(q) <= R:
                qs.append(q)
                ws.append(np.log(p)/np.sqrt(q))
                m += 1
            else:
                break
    return np.array(qs, dtype=float), np.array(ws, dtype=float)

# ---------- Gaussian bump ----------
def gauss(x, mu, delta):
    return np.exp(-0.5*((x-mu)/delta)**2) / (np.sqrt(2*np.pi)*delta)

# ---------- potential V(x) ----------
def Vx(x, qs, ws, delta):
    if len(qs)==0:
        return np.zeros_like(x)
    centers = np.log(qs)
    V = np.zeros_like(x)
    for (c, w) in zip(centers, ws):
        V += w * gauss(x, c, delta)
    return V

# ---------- Galerkin via DST-I (orthonormal) ----------
def apply_V(a, Vvals):
    # DST-I is orthonormal with norm='ortho'
    u = dst(a, type=1, norm='ortho')
    u = Vvals * u
    return dst(u, type=1, norm='ortho')

# ---------- build K diagonal ----------
def K_diag(N, L):
    m = np.arange(1, N+1)
    return ((m*np.pi)/L)**2

# ---------- power iteration for largest eigenvalue ----------
def max_eig_linear_op(apply, N, iters=200):
    x = np.random.randn(N)
    x /= np.linalg.norm(x)
    for _ in range(iters):
        y = apply(x)
        nrm = np.linalg.norm(y)
        if nrm == 0:
            return 0.0
        x = y / nrm
    # Rayleigh quotient
    y = apply(x)
    return float(x @ y)

# ---------- main loop ----------
def run():
    print("N   L    R       theta0(K^-1/2 V K^-1/2)   C0(theta=0.5)   rho(c=1)")
    for N in Ns:
        L = max(4, L_of_N(N))
        # use the manuscript-style R ~ (1/2) log(n+2); we emulate via N↔n
        n_est = int(round(N**0.25 - 2))
        R = 0.5*np.log(max(2, n_est+2))

        qs, ws = prime_powers(R)

        # quadrature grid for DST-I
        M = max(4*N, 4096)
        j = np.arange(1, M+1)
        x = L * j/(M+1)
        Vvals = Vx(x, qs, ws, delta)

        Kd = K_diag(N, L)

        # operators
        def apply_Vop(a):
            return apply_V(a, Vvals)

        def apply_Kinv_sqrt_V_Kinv_sqrt(a):
            # y = K^{-1/2} a
            y = a / np.sqrt(Kd)
            y = apply_Vop(y)
            y = y / np.sqrt(Kd)
            return y

        # theta0 (C0=0 test)
        theta0 = max_eig_linear_op(apply_Kinv_sqrt_V_Kinv_sqrt, N)

        # C0(theta) for theta=0.5
        theta = 0.5
        def apply_V_minus_thetaK(a):
            return apply_Vop(a) - theta*(Kd*a)
        C0 = max_eig_linear_op(apply_V_minus_thetaK, N)

        # shifted contraction rho(c) with c=1
        c = 1.0
        def apply_shifted(a):
            y = a / np.sqrt(Kd + c)
            y = apply_Vop(y)
            y = y / np.sqrt(Kd + c)
            return y
        rho = max_eig_linear_op(apply_shifted, N)

        print(f"{N:<3d} {L:<4d} {R:6.3f}     {theta0:10.4f}                 {C0:10.4f}      {rho:8.4f}")

if __name__ == "__main__":
    run()
