import numpy as np, json, math, time
from graph import *
GAM = np.array(json.load(open("zeros.json")))
for P in [30, 100]:
    ps = primes_upto(P); B = len(ps)
    kir = 2.0/B*np.ones((B,B)) - np.eye(B)
    t = time.time()
    for name, sig in [("Kirchhoff (real, TR-symmetric)", kir),
                      ("random unitary (TR broken)", random_unitary(B, 1)),
                      ("diag = -p^-1/2 (TR broken)", unitary_with_diagonal(-1/np.sqrt(ps.astype(float)), seed=2))]:
        r, L = spectrum(ps, sig, 120.0)
        v, f = spacing_stats(r, L)
        print("P=%3d B=%2d %-32s levels %5d  spacing var %.3f  frac(s<0.3) %.3f" % (P, B, name, len(r), v, f))
    print("   (%.1fs)" % (time.time()-t))
print("reference: zeta zeros var 0.139 frac 0.010 ; GUE ~0.178/0.011 ; GOE ~0.286/0.067 ; Poisson 1.0/0.26")
