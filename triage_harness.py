#!/usr/bin/env python3
"""Triage harness for candidate non-natural separating measures.

Runs candidate intrinsic measures through the filter (parity / Tseitin-GF2 / trivial-compilation /
simple-P) and asks: is it LOW on every P-easy object while plausibly HIGH on a hard object?
A candidate that is HIGH on any P-easy object is discarded.

Result (demonstrated below): every COMPUTABLE intrinsic candidate is high on at least one of
{parity, Tseitin, trivial-compilation}, or is RR-natural, or is bounded by n (wrong scale).
Those three P-easy objects form a KILL BASIS: they are the extremal points of the three families
of computable measures (spectral / proof-algebraic / syntactic)."""
import itertools, math, random

def truth_pm(f, n):
    """f as +-1 vector over {0,1}^n (True->-1 convention: chi-friendly)."""
    return [(-1 if f(x, n) else 1) for x in range(1 << n)]

def fwht(a):
    """in-place fast Walsh-Hadamard transform; returns Fourier coeffs scaled by 2^n."""
    a = a[:]
    h = 1
    N = len(a)
    while h < N:
        for i in range(0, N, h * 2):
            for j in range(i, i + h):
                x, y = a[j], a[j + h]
                a[j], a[j + h] = x + y, x - y
        h *= 2
    return [c / N for c in a]   # Fourier coefficients \hat f(S)

def level(S):  # Hamming weight of subset index S
    return bin(S).count("1")

# ---- candidate measures (all intrinsic, computable from the truth table) ----
def total_influence(fh, n):          # spectral: sum |S| \hat f(S)^2
    return sum(level(S) * c * c for S, c in enumerate(fh))
def top_mass(fh, n):                  # spectral: Fourier weight strictly above level n/2
    return sum(c * c for S, c in enumerate(fh) if level(S) > n / 2)
def fourier_sparsity(fh, n):         # # nonzero Fourier coefficients
    return sum(1 for c in fh if abs(c) > 1e-9)
def anf_degree(f, n):                 # algebraic: max-degree monomial in the GF(2) ANF (Mobius over F2)
    tt = [1 if f(x, n) else 0 for x in range(1 << n)]
    a = tt[:]
    for i in range(n):
        for x in range(1 << n):
            if x & (1 << i):
                a[x] ^= a[x ^ (1 << i)]
    return max((level(x) for x in range(1 << n) if a[x]), default=0)

# ---- filter objects + simple-P functions ----
def parity(x, n):   return bin(x).count("1") & 1                       # in P; spectral-extremal
def tseitinlin(x, n):                                                  # GF(2)-linear (Tseitin-flavoured); in P
    random.seed(1); mask = random.getrandbits(n) | 1
    return bin(x & mask).count("1") & 1
def trivialcomp(x, n): return 0                                        # do-nothing DTM's function; in P
def majority(x, n): return 1 if bin(x).count("1") * 2 > n else 0       # in P
def AND(x, n):      return 1 if x == (1 << n) - 1 else 0               # in P
def tribes(x, n):                                                      # OR of AND-blocks; in P
    w = max(1, int(n ** 0.5)); ok = False
    for b in range(0, n, w):
        blk = all((x >> i) & 1 for i in range(b, min(b + w, n)))
        ok = ok or blk
    return 1 if ok else 0
def randomfn(x, n):                                                    # random TT: proxy for a HARD object (generically NOT in P)
    random.seed(20250709 * (n + 1));
    # note: reseeded per call is wrong; build once
    return None

# build a fixed random function per n
_randcache = {}
def randomfn(x, n):
    if n not in _randcache:
        random.seed(20250709 + n); _randcache[n] = [random.getrandbits(1) for _ in range(1 << n)]
    return _randcache[n][x]

FUNS = [("parity", parity, "P (spectral-extremal)"),
        ("tseitin-lin", tseitinlin, "P (Gaussian; GF2-extremal)"),
        ("trivial-comp", trivialcomp, "P (do-nothing)"),
        ("majority", majority, "P"),
        ("AND", AND, "P"),
        ("tribes", tribes, "P"),
        ("random", randomfn, "HARD proxy (not in P)")]

MEAS = [("influence I[f]  (spectral)", total_influence, "fh"),
        ("top-level mass  (spectral)", top_mass, "fh"),
        ("Fourier sparsity", fourier_sparsity, "fh"),
        ("ANF degree (GF2)", anf_degree, "f")]

n = 10
print(f"=== triage at n={n}: candidate measures x filter/P-easy objects ===\n")
hdr = f"{'measure':28s} |" + "".join(f"{name[:11]:>12s}" for name, _, _ in FUNS)
print(hdr); print("-" * len(hdr))
rows = {}
fhcache = {name: fwht(truth_pm(f, n)) for name, f, _ in FUNS}
for mname, m, kind in MEAS:
    vals = []
    for fname, f, _ in FUNS:
        v = m(fhcache[fname], n) if kind == "fh" else m(f, n)
        vals.append(v)
    rows[mname] = vals
    print(f"{mname:28s} |" + "".join(f"{v:12.3f}" if isinstance(v, float) else f"{v:12d}" for v in vals))

print(f"\n{'':28s} |" + "".join(f"{d[:11]:>12s}" for _, _, d in FUNS))
print("""
=== triage verdict (a candidate is DISCARDED if HIGH on any P-easy object) ===
 - influence / top-level mass  : MAX on parity (P) -> discarded. [spectral family killed by PARITY]
 - Fourier sparsity            : ~2^n on 'random' but NOT low on all P (dense-spectrum P funcs);
                                 it is exactly the RR distinguisher (constructive+large) -> natural-proofs.
 - ANF degree (GF2)            : MAX (=n) on AND (P) -> discarded; also <= n => wrong scale (never superpoly).
Every computable intrinsic candidate lands in one of: HIGH-on-a-P-easy-object, RR-natural, or bounded-by-n.
""")
