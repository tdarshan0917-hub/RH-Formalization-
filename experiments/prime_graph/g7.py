# Step 2: the "holes". Locate dips of the graph density and measure distance to each zeta zero.
import numpy as np, json, math, sys
from scipy.signal import find_peaks
from graph import primes_upto
from g2 import graph_density
GAM = np.array(json.load(open("zeros.json")))
P = int(sys.argv[1]) if len(sys.argv) > 1 else 300
ps = primes_upto(P); s = np.load("sigma_all_P%d.npy" % P)
eps = 0.15
T = np.arange(20, 640, 0.005)
g = graph_density(ps, s, T, eps)
mirror = -g                                           # zeros should appear as peaks of -g
pk, prop = find_peaks(mirror, prominence=0.0)
prom = prop["prominences"]
Z = GAM[(GAM > 25) & (GAM < 635)]
spacing = lambda t: 2*math.pi/np.log(t/(2*math.pi))
def nearest(pos, cand):
    i = np.searchsorted(cand, pos); i = np.clip(i, 1, len(cand)-1)
    return np.minimum(np.abs(cand[i]-pos), np.abs(cand[i-1]-pos))
res = {}
# keep the N most prominent dips, N = number of zeros in range (no zero info used beyond the count)
order = np.argsort(-prom)
for label, N in [("top-N dips (N = #zeros)", len(Z)), ("all dips", len(pk))]:
    dips = np.sort(T[pk[order[:N]]])
    dz = nearest(Z, dips)/spacing(Z)                  # zero -> nearest dip, in local spacings
    rng = np.random.default_rng(3)
    rnd = rng.uniform(25, 635, 20000); dr = nearest(rnd, dips)/spacing(rnd)
    half = Z + 0.5*spacing(Z); dh = nearest(half, dips)/spacing(half)
    # dip -> nearest zero (precision of the dips)
    dd = nearest(dips, np.sort(GAM))/spacing(dips)
    r = dict(n_dips=int(len(dips)), n_zeros=int(len(Z)),
             zero_to_dip_median=float(np.median(dz)), zero_to_dip_p90=float(np.percentile(dz, 90)),
             frac_zeros_within_0_1=float(np.mean(dz < 0.1)), frac_zeros_within_0_25=float(np.mean(dz < 0.25)),
             null_random_median=float(np.median(dr)), null_random_frac_0_1=float(np.mean(dr < 0.1)),
             null_midpoints_median=float(np.median(dh)), null_midpoints_frac_0_1=float(np.mean(dh < 0.1)),
             dip_to_zero_median=float(np.median(dd)), frac_dips_within_0_1=float(np.mean(dd < 0.1)))
    res[label] = r
    print(label, json.dumps(r, indent=1))
# per-height breakdown for the top-N dips
dips = np.sort(T[pk[order[:len(Z)]]]); dz = nearest(Z, dips)/spacing(Z)
for lo, hi in [(25,150),(150,300),(300,450),(450,635)]:
    m = (Z>=lo)&(Z<hi)
    print("  T in [%d,%d): zeros %3d  median dist %.3f spacing  frac<0.1 %.2f" % (lo, hi, m.sum(), np.median(dz[m]), np.mean(dz[m]<0.1)))
json.dump(res, open("g7_results_P%d.json" % P, "w"))
np.save("g7_dist_P%d.npy" % P, dz)
