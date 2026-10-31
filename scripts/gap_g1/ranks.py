#!/usr/bin/env python3
"""SPDP ranks of compiled tableau polynomials (ACC = always-accept, AND) - see tableau.py.

Conventions (as in scripts/spdp_obstruction/spdp_rank.py):
  LEAN-drop     : MultilinearSPDP.mlBlockedSpdpSubspace (singleton blocks = compilerBlockPartition):
                  rows mlProj(m * d^S p), S distinct vars |S| = kappa, m monomial deg <= ell, vars(m) in S,
                  mlProj DROPS non-multilinear monomials.  Computed EXACTLY (Fraction) or mod 2^31-1.
  PAPER-reduce  : Def. 12 of the v5 paper: u ANY monomial of degree <= ell, ambient space mod <x^2 - x>.
                  A multilinear polynomial is determined by its values on {0,1}^N, so
                  Gamma = rank of the matrix [ (u * d^tau p)(a) ]_{rows, a in {0,1}^N}.
                  We use a SUBSET of rows (distinct-variable tau) and a SUBSET of points a, so the
                  computed number is a rigorous LOWER BOUND on the Def.-12 rank (rank mod p <= rank over Q).
Output: JSON lines to stdout.
"""
import itertools, json, math, random, sys, time
import numpy as np
from fractions import Fraction
from tableau import Tableau, ev, deg, pmul, padd, X, ONE

P = 2**31 - 1
WSHIFT = 30
NRAND = 400

def rank_modp(M):
    """Rank of an integer matrix modulo P (numpy int64; entries < 2^31 so products fit)."""
    A = np.array(M, dtype=np.int64) % P
    r = 0; rows, cols = A.shape
    for c in range(cols):
        if r == rows: break
        piv = np.nonzero(A[r:, c])[0]
        if piv.size == 0: continue
        k = r + piv[0]
        if k != r: A[[r, k]] = A[[k, r]]
        inv = pow(int(A[r, c]), P - 2, P)
        A[r] = (A[r] * inv) % P
        nz = np.nonzero(A[:, c])[0]
        nz = nz[nz != r]
        if nz.size:
            A[nz] = (A[nz] - (A[nz, c][:, None] * A[r][None, :]) % P) % P
        r += 1
    return r

# ---------------------------------------------------------------- symbolic LEAN-drop
def deriv(p, v):
    r = {}
    for m, c in p.items():
        d = dict(m)
        if v in d:
            e = d[v]; c2 = c * e
            if e == 1: del d[v]
            else: d[v] = e - 1
            k = tuple(sorted(d.items())); r[k] = r.get(k, 0) + c2
    return {k: c for k, c in r.items() if c}

def ml_drop(p):
    return {frozenset(v for v, _ in m): c for m, c in p.items() if all(e == 1 for _, e in m)}

class Basis:
    def __init__(self, exact):
        self.piv = {}; self.exact = exact
    def add(self, row):
        r = {k: (Fraction(v) if self.exact else v % P) for k, v in row.items()}
        r = {k: v for k, v in r.items() if v}
        while r:
            k = min(r, key=lambda m: (len(m), sorted(m)))
            if k in self.piv:
                b = self.piv[k]; f = r[k]
                for kk, vv in b.items():
                    nv = r.get(kk, 0) - f * vv
                    if not self.exact: nv %= P
                    if nv: r[kk] = nv
                    else: r.pop(kk, None)
            else:
                inv = (1 / r[k]) if self.exact else pow(r[k], P - 2, P)
                self.piv[k] = {kk: (vv * inv if self.exact else vv * inv % P) for kk, vv in r.items()}
                return True
        return False

def lean_rank(p, kappa, ell, candidate_sets, exact=True):
    """LEAN-drop rank; candidate_sets must contain every kappa-set S with d^S p != 0."""
    B = Basis(exact); nrows = 0
    for S in candidate_sets:
        d = p
        for v in S:
            d = deriv(d, v)
            if not d: break
        if not d: continue
        for k in range(ell + 1):
            for u in itertools.combinations_with_replacement(S, k):
                mono = {}
                for v in u: mono[v] = mono.get(v, 0) + 1
                q = pmul(d, {tuple(sorted(mono.items())): 1})
                q = ml_drop(q); nrows += 1
                if q: B.add(q)
    return len(B.piv), nrows

def support_sets(tab, kappa, with_pad):
    """All kappa-sets S that can have d^S(V) != 0 or d^S(Y*V) != 0 (locality: S_tab inside one constraint)."""
    out = set()
    supports = {frozenset(v for m in c for v, _ in m) for _, c in tab.C}
    pad = tab.pad if with_pad else []
    for sup in supports:
        for j in range(0, min(kappa, len(sup)) + 1):
            if kappa - j > len(pad): continue
            for St in itertools.combinations(sorted(sup), j):
                for Sp in itertools.combinations(pad, kappa - j):
                    out.add(tuple(sorted(St + Sp)))
    return sorted(out)

def V_of(tab):
    V = {}
    for _, c in tab.C: V = padd(V, pmul(c, c))
    return V

def Y_of(tab):
    Y = ONE
    for y in tab.pad: Y = pmul(Y, X(y))
    return Y

# ---------------------------------------------------------------- PAPER-reduce lower bounds by evaluation
def sample_points(tab, rng, n_rand, flips=(1, 2, 3)):
    pts = []
    base = []
    for x in itertools.product((0, 1), repeat=tab.n):
        a, _ = tab.run(x); base.append(a); pts.append(a)
    allv = tab.tab_vars + tab.pad
    for a in base:
        for v in tab.tab_vars:
            a2 = dict(a); a2[v] ^= 1; pts.append(a2)
    while len(pts) < len(base) * (len(tab.tab_vars) + 1) + n_rand:
        a = dict(rng.choice(base)); k = rng.choice(flips)
        for v in rng.sample(tab.tab_vars, k): a[v] ^= 1
        pts.append(a)
    for a in pts:
        for y in tab.pad: a.setdefault(y, rng.randint(0, 1))
    return pts

def prod_row_values(tab, S, pts_info):
    """(d^S prod_C (1-C))(a) mod P for each point, via dual numbers in eps_S (S distinct vars)."""
    k = len(S); full = (1 << k) - 1
    pos = {v: j for j, v in enumerate(S)}
    touching = sorted({ci for v in S for ci in tab.var2c.get(v, [])})
    out = []
    for a, fvals, zeros, prodnz in pts_info:
        # scalar part: product of factors not touching S
        z_touch = sum(1 for ci in touching if fvals[ci] == 0)
        if zeros - z_touch > 0:
            out.append(0); continue
        num = prodnz
        for ci in touching:
            if fvals[ci] != 0: num = num * pow(fvals[ci], P - 2, P) % P
        acc = [0] * (1 << k); acc[0] = 1
        for ci in touching:
            f = [0] * (1 << k)          # (1 - C)(a + eps), truncated multilinear in eps
            for m, c in tab.oneminus[ci].items():
                g = [0] * (1 << k); g[0] = c % P
                for v, e in m:
                    if v in pos:
                        bit = 1 << pos[v]; av = a[v]
                        h = [0] * (1 << k)
                        for msk, val in enumerate(g):
                            if not val: continue
                            h[msk] = (h[msk] + val * pow(av, e, P)) % P
                            if not msk & bit:
                                h[msk | bit] = (h[msk | bit] + val * e * pow(av, e - 1, P)) % P
                        g = h
                    else:
                        av = a[v]
                        if av == 0: g = [0] * (1 << k); break
                for msk in range(1 << k): f[msk] = (f[msk] + g[msk]) % P
            new = [0] * (1 << k)
            for m1 in range(1 << k):
                if not acc[m1]: continue
                rest = full ^ m1; m2 = rest
                while True:
                    if f[m2]: new[m1 | m2] = (new[m1 | m2] + acc[m1] * f[m2]) % P
                    if m2 == 0: break
                    m2 = (m2 - 1) & rest
            acc = new
        out.append(acc[full] * num % P)
    return out

def prepare_prod(tab, pts):
    tab.oneminus = [padd(ONE, c, -1) for _, c in tab.C]
    tab.var2c = {}
    for ci, (_, c) in enumerate(tab.C):
        for v in {v for m in c for v, _ in m}: tab.var2c.setdefault(v, []).append(ci)
    info = []
    for a in pts:
        fvals = [ev(f, a, P) for f in tab.oneminus]
        zeros = sum(1 for x in fvals if x == 0)
        prodnz = 1
        for x in fvals:
            if x: prodnz = prodnz * x % P
        info.append((a, fvals, zeros, prodnz))
    return info

def emit(d):
    print(json.dumps(d), flush=True)

def main(which):
    rng = random.Random(2026)
    if 'lean' in which:     # exact LEAN-drop ranks of SOS and Y*V
        for n in (4, 5, 6, 8):
            kappa = max(1, int(math.log2(n))); ell = kappa
            for M in ('ACC', 'AND'):
                t0 = time.time()
                tab = Tableau(n, M, kappa)
                V = V_of(tab)
                sos = padd(ONE, V, -1)
                r1, rows1 = lean_rank(sos, kappa, ell, support_sets(tab, kappa, False), exact=(n <= 5))
                YV = pmul(Y_of(tab), V)
                r2, rows2 = lean_rank(YV, kappa, ell, support_sets(tab, kappa, True), exact=(n <= 5))
                emit(dict(test='LEAN-drop', machine=M, n=n, N_tab=len(tab.tab_vars), kappa=kappa, ell=ell,
                          deg_SOS=deg(sos), rank_SOS=r1, deg_YV=deg(YV), rank_YV=r2,
                          NP_bound_C_n3_k=math.comb(n // 3, kappa), C_n_k=math.comb(n, kappa),
                          exact=(n <= 5), secs=round(time.time() - t0, 1)))
    if 'yv' in which:       # PAPER-reduce, rows tau = all padding vars, all shifts u of degree <= ell
        for n in (4, 5):
            kappa = max(1, int(math.log2(n))); ell = kappa
            for M in ('ACC', 'AND'):
                t0 = time.time()
                tab = Tableau(n, M, kappa); V = V_of(tab)
                allv = tab.tab_vars + tab.pad
                # rows: tau = all padding vars, shifts u = multilinear monomials of degree <= ell in a
                # subset W' of WSHIFT tableau variables (a sub-family of Def.-12 rows -> lower bound)
                Wp = tab.tab_vars[-WSHIFT:]
                shifts = [u for k in range(ell + 1) for u in itertools.combinations(Wp, k)]
                npts = int(len(shifts) * 1.3) + 50
                pts = [{v: rng.randint(0, 1) for v in allv} for _ in range(npts)]
                Vv = [ev(V, a, P) for a in pts]
                Mx = [[(Vv[j] if all(pts[j][v] for v in u) else 0) for j in range(npts)] for u in shifts]
                r = rank_modp(Mx)
                emit(dict(test='PAPER-reduce Y*V, rows (tau=padding, u)', machine=M, n=n, N=tab.N, kappa=kappa,
                          ell=ell, rank_lower_bound=r, rows=len(shifts), points=npts,
                          shift_vars=len(Wp), full_rank_of_subfamily=len(shifts),
                          analytic_lower_bound_full_family=sum(math.comb(tab.N - 1, j) for j in range(ell + 1)),
                          NP_bound_C_n3_k=math.comb(n // 3, kappa), C_n_k=math.comb(n, kappa),
                          secs=round(time.time() - t0, 1)))
    if 'prod' in which:     # PAPER-reduce, ell = 0, rows d^S prod(1-C) for ALL distinct kappa-sets S
        for n in (4, 5):
            kappa = max(1, int(math.log2(n)))
            for M in ('ACC', 'AND'):
                t0 = time.time()
                tab = Tableau(n, M, 0)
                Ss = list(itertools.combinations(tab.tab_vars, kappa))
                pts = sample_points(tab, rng, n_rand=NRAND)
                info = prepare_prod(tab, pts)
                rows = [prod_row_values(tab, S, info) for S in Ss]
                rows = [r for r in rows if any(r)]
                r = rank_modp(rows) if rows else 0
                inS = list(itertools.combinations(tab.inputs, kappa))
                rows_in = [prod_row_values(tab, S, info) for S in inS]
                r_in = rank_modp(rows_in)
                emit(dict(test='PAPER-reduce PROD, ell=0', machine=M, n=n, N=tab.N, kappa=kappa,
                          rank_lower_bound_all_S=r, nonzero_rows=len(rows), rows_total=len(Ss), points=len(pts),
                          rank_lower_bound_S_in_inputs=r_in, C_n_k=math.comb(n, kappa),
                          NP_bound_C_n3_k=math.comb(n // 3, kappa), secs=round(time.time() - t0, 1)))

if __name__ == '__main__':
    main(sys.argv[1:] or ['lean', 'yv', 'prod'])
