#!/usr/bin/env python3
"""G4-b: exact ranks of the paper's Def. 12 SPDP measure (drop / reduce conventions)
versus the Lean strict measure `mlBlockedSpdpRank` (discrete blocks), for easy Boolean
functions, random functions and the SAT characteristic polynomial of the 21921958 branch.

All polynomials here are multilinear (multilinear extensions / characteristic polynomials
chi_f of Boolean f, paper Def. 13), with integer coefficients (Moebius transform).
For multilinear p:
  * d^tau p = 0 whenever some tau_i >= 2, so only tau = 1_S, |S| = kappa, matter;
  * d_S p = sum_{T disjoint S} c[T u S] x^T;
  * drop:  a shift u with an exponent >= 2 gives drop(u * q) = 0; for multilinear u = x^U,
           drop(x^U q) = x^U * (part of q on monomials disjoint from U);
  * reduce: red(u * q) = red(red(u) * q), so only multilinear u = x^U matter and
           red(x^U q) = sum_T c'[T] x^{T u U};
  * Lean strict (discrete blocks): S nodup, |S| = kappa, shift m with vars(m) subset S,
           deg m <= l, then mlProj (= drop). Since d_S p has no S-variable, only multilinear
           m = x^U, U subset S, |U| <= l, survive.
Columns: multilinear monomials of degree <= D = max(0, deg p - kappa + l) (Def. 12);
every row already lies there (checked by assertion).
Rank: exact over Q with FLINT fmpz_mat.rank() when the matrix is small enough ('exact');
otherwise rank over GF(P), P = 2^61-1 ('modp'), which is a LOWER bound on the rank over Q
(integer matrix), and is exact when it meets the column/row ceiling.
"""
import itertools, math, random, sys, json
import numpy as np
import flint

P = (1 << 61) - 1

def popcount(m): return bin(m).count("1")

def mle(f, N):
    """Integer coefficients c[mask] of chi_f (Moebius transform of the truth table)."""
    c = [int(f(a)) for a in range(1 << N)]   # a: bit i = x_i
    for i in range(N):
        b = 1 << i
        for m in range(1 << N):
            if m & b:
                c[m] -= c[m ^ b]
    return c

def degree(c):
    d = -1
    for m, v in enumerate(c):
        if v: d = max(d, popcount(m))
    return d  # -1 for p = 0

def subsets_upto(N, l):
    out = []
    for j in range(l + 1):
        for comb in itertools.combinations(range(N), j):
            out.append(sum(1 << i for i in comb))
    return out

def rows(c, N, kappa, l, conv):
    """Yield rows as dicts mask -> int."""
    supp = [(m, v) for m, v in enumerate(c) if v]
    shifts_all = subsets_upto(N, l)
    for S in itertools.combinations(range(N), kappa):
        Sm = sum(1 << i for i in S)
        dS = [(m ^ Sm, v) for m, v in supp if m & Sm == Sm]   # d_S p, monomials disjoint from S
        if not dS: continue
        if conv == "lean":
            shifts = [U for U in shifts_all if U & ~Sm == 0]
        else:
            shifts = shifts_all
        for U in shifts:
            r = {}
            for T, v in dS:
                if conv in ("lean", "drop"):
                    if T & U: continue
                    key = T | U
                elif conv == "reduce":
                    key = T | U
                r[key] = r.get(key, 0) + v
            r = {k: v for k, v in r.items() if v}
            if r: yield r

def rank_of(rowlist, D, N, exact_limit=4_000_000):
    cols = sorted({k for r in rowlist for k in r})
    for k in cols: assert popcount(k) <= D, "row outside Def.12 column range"
    if not rowlist: return 0, "exact"
    idx = {k: i for i, k in enumerate(cols)}
    nr, nc = len(rowlist), len(cols)
    if nr * nc <= exact_limit:
        M = flint.fmpz_mat(nr, nc)
        for i, r in enumerate(rowlist):
            for k, v in r.items(): M[i, idx[k]] = v
        return M.rank(), "exact"
    M = flint.nmod_mat(nr, nc, P)
    for i, r in enumerate(rowlist):
        for k, v in r.items(): M[i, idx[k]] = v % P
    return M.rank(), "modp"

def gamma(c, N, kappa, l, conv):
    d = degree(c)
    if d < 0: return 0, "exact", 0
    D = max(0, d - kappa + l)
    if d - kappa + l < 0: return 0, "exact", D
    rl = list(rows(c, N, kappa, l, conv))
    # dedupe identical rows (does not change rank)
    seen = {}
    for r in rl: seen[tuple(sorted(r.items()))] = r
    r, how = rank_of(list(seen.values()), D, N)
    return r, how, D

# ---------------- functions ----------------
def bit(a, i): return (a >> i) & 1

def f_and(N): return lambda a: a == (1 << N) - 1
def f_or(N): return lambda a: a != 0
def f_parity(N): return lambda a: popcount(a) % 2
def f_thr(N, t): return lambda a: popcount(a) >= t
def f_maj(N): return f_thr(N, (N + 1) // 2)
def f_ip(N):
    h = N // 2
    return lambda a: sum(bit(a, i) & bit(a, i + h) for i in range(h)) % 2
def f_scanner(N):
    # easyLanguage (21921958 GodMoveLinearTimeRankObstruction): accept iff first false bit
    # has even index (word [a_0, ..., a_{N-1}]; implicit false after the end).
    def f(a):
        for i in range(N):
            if not bit(a, i): return i % 2 == 0
        return N % 2 == 0
    return f
def f_mux(N):
    # addressing: k address bits select one of the remaining bits (k max with k + 2^k <= N)
    k = 0
    while (k + 1) + (1 << (k + 1)) <= N: k += 1
    def f(a):
        addr = sum(bit(a, i) << i for i in range(k))
        j = k + addr
        return bit(a, j) if j < N else 0
    return f
def f_random(N, seed):
    rnd = random.Random(seed); tt = [rnd.randrange(2) for _ in range(1 << N)]
    return lambda a: tt[a]

# ---- SAT language of the branch (CookLevinEmitCodec coordinate codec), exact port ----
def decodeNat(bs):
    n = 0
    while bs and bs[0]:
        n += 1; bs = bs[1:]
    if bs: bs = bs[1:]          # consume the terminating false (if any)
    return n, bs

def npair(a, b):  # Mathlib Nat.pair
    return b * b + a if a < b else a * a + a + b

def decodeVar(bs):
    t, r = decodeNat(bs); p, r = decodeNat(r); tag, r = decodeNat(r)
    return 3 * npair(t, p) + tag, r

def decodeLit(bs):
    v, r = decodeVar(bs)
    s = r[0] if r else False
    return (v, s), r[1:]

def decodeLits(k, bs):
    out = []
    for _ in range(k):
        l, bs = decodeLit(bs); out.append(l)
    return out, bs

def decodeClause(bs):
    k, r = decodeNat(bs); return decodeLits(k, r)

def decodeFormula(bs):
    k, r = decodeNat(bs)
    cl = []
    for _ in range(k):
        c, r = decodeClause(r); cl.append(c)
    return cl

def satisfiable(phi):
    vs = sorted({v for c in phi for (v, _) in c})
    if any(len(c) == 0 for c in phi): return False
    for vals in itertools.product([False, True], repeat=len(vs)):
        a = dict(zip(vs, vals))
        if all(any(a[v] == s for (v, s) in c) for c in phi): return True
    return False

def f_sat(N):
    # languageCharacteristic SATLang N: word = [a 0, ..., a (N-1)] (wordOfFin)
    return lambda a: satisfiable(decodeFormula([bool(bit(a, i)) for i in range(N)]))

def unitSourceLength(n):
    def encNat(k): return k + 1
    def encVar(v):
        q = v // 3
        # Nat.unpair
        s = math.isqrt(q)
        a, b = (q - s * s, s) if q - s * s < s else (s, q - s * s - s)
        return encNat(a) + encNat(b) + encNat(v % 3)
    L = encNat(n + n)  # encodeNat (phi.length + n), phi = unitFormula n has n clauses
    for i in range(n): L += encNat(1) + encVar(i) + 1   # encodeClause' [(i,true)]
    for i in range(n): L += encNat(1) + encVar(i) + 1   # unitTemplate i
    return L

def ceilings(N, kappa, l, D):
    cols = sum(math.comb(N, j) for j in range(D + 1))
    rows_def12 = math.comb(N, kappa) * sum(math.comb(N, j) for j in range(l + 1))
    rows_lean = math.comb(N, kappa) * sum(math.comb(kappa, j) for j in range(min(l, kappa) + 1))
    return cols, rows_def12, rows_lean

FUNCS = {
    "AND": f_and, "OR": f_or, "PARITY": f_parity, "MAJ": f_maj, "IP": f_ip,
    "SCANNER": f_scanner, "MUX": f_mux, "THR2": lambda N: f_thr(N, 2),
    "RAND0": lambda N: f_random(N, 0), "RAND1": lambda N: f_random(N, 1),
    "SAT": f_sat,
}

def main():
    Ns = [int(x) for x in sys.argv[1].split(",")] if len(sys.argv) > 1 else [4, 5, 6, 7, 8]
    ks = [int(x) for x in sys.argv[2].split(",")] if len(sys.argv) > 2 else [0, 1, 2, 3]
    names = sys.argv[3].split(",") if len(sys.argv) > 3 else list(FUNCS)
    for N in Ns:
        for kappa in ks:
            if kappa > N: continue
            l = kappa
            for name in names:
                c = mle(FUNCS[name](N), N)
                d = degree(c)
                res = {"N": N, "kappa": kappa, "l": l, "f": name, "deg": d}
                for conv in ("lean", "drop", "reduce"):
                    r, how, D = gamma(c, N, kappa, l, conv)
                    res[conv] = r; res[conv + "_how"] = how; res["D"] = D
                cols, rd, rl = ceilings(N, kappa, l, res["D"])
                res.update(cols=cols, rows_def12=rd, rows_lean=rl)
                print(json.dumps(res), flush=True)

if __name__ == "__main__":
    main()
