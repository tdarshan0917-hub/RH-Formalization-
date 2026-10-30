import numpy as np, json, math
from scipy.signal import find_peaks
from graph import primes_upto
from g2 import theory_prime_powers
GAM = np.array(json.load(open("zeros.json")))
import sys; PP_ = int(sys.argv[1]) if len(sys.argv)>1 else 300; ps = primes_upto(PP_); T = np.arange(20, 640, 0.005)
ideal = theory_prime_powers(ps, T, 0.15)            # truncated explicit formula: peaks at zeros
pk, prop = find_peaks(ideal, prominence=0.0); order = np.argsort(-prop["prominences"])
Z = GAM[(GAM > 25) & (GAM < 635)]
sp = lambda t: 2*math.pi/np.log(t/(2*math.pi))
def nearest(pos, cand):
    i = np.clip(np.searchsorted(cand, pos), 1, len(cand)-1)
    return np.minimum(np.abs(cand[i]-pos), np.abs(cand[i-1]-pos))
d = nearest(Z, np.sort(T[pk[order[:len(Z)]]]))/sp(Z)
print("ceiling (truncated explicit formula, primes<=%d)" % PP_ + ": median %.3f  frac<0.1 %.3f  frac<0.25 %.3f" % (np.median(d), np.mean(d<0.1), np.mean(d<0.25)))
json.dump(dict(median=float(np.median(d)), f01=float(np.mean(d<0.1)), f025=float(np.mean(d<0.25))), open("g7b_ceiling_%d.json" % PP_,"w"))
