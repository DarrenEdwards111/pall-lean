#!/usr/bin/env python3
"""Gap G1 experiments: SPDP ranks of COMPILED TABLEAU polynomials of trivial machines.

Tableau = paper v5 Sec. 17.1 (time x tape, variables b[t][i], h[t][i], s[t][q]), radius-1 constraints,
each constraint C is a polynomial that is 0/1-valued on the Boolean cube and 0 iff satisfied.
Machines (single tape, binary, head always moves right, clocked to T = n steps):
  ACC : always accept   (q0 -> qacc on any symbol, then stay)
  AND : accept iff x_1 = ... = x_n = 1  (q0 reads 1 -> q0; reads 0 -> qrej)
Encodings of the compiled polynomial:
  PROD : prod_C (1 - C)          (paper's first definition, Lean `CookLevinDefs.compiledPoly` shape)
  SOS  : 1 - sum_C C^2           (paper's 'from now on' P_{M,n}, Thm 92 / Thm 218, constant degree)
  YV   : y_1...y_kappa * sum_C C^2  (Lemma 39 padding; Lean `TuringMachine.compiledPoly`)
Polynomials: dict {monomial: int}, monomial = tuple of sorted (var, exp) pairs.
"""
import itertools

def padd(p, q, s=1):
    r = dict(p)
    for m, c in q.items():
        r[m] = r.get(m, 0) + s * c
        if r[m] == 0: del r[m]
    return r

def mmul(m1, m2):
    d = dict(m1)
    for v, e in m2: d[v] = d.get(v, 0) + e
    return tuple(sorted(d.items()))

def pmul(p, q):
    r = {}
    for m1, c1 in p.items():
        for m2, c2 in q.items():
            m = mmul(m1, m2); r[m] = r.get(m, 0) + c1 * c2
    return {m: c for m, c in r.items() if c}

ONE = {(): 1}
def X(v): return {((v, 1),): 1}
def neg1(v): return padd(ONE, X(v), -1)            # 1 - x
def lit(v, a): return X(v) if a else neg1(v)       # [x = a]
def xor(u, v): return padd(padd(X(u), X(v)), pmul(X(u), X(v)), -2)
def deg(p): return max((sum(e for _, e in m) for m in p), default=-1)

class Tableau:
    def __init__(self, n, machine, kappa=0):
        self.n, self.T, self.L = n, n, n + 1
        self.machine = machine
        self.Q = 3  # 0 = q0, 1 = acc, 2 = rej
        idx = itertools.count()
        T, L = self.T, self.L
        self.b = [[next(idx) for i in range(L + 1)] for t in range(T + 1)]   # index i = 1..L used
        self.h = [[next(idx) for i in range(L + 1)] for t in range(T + 1)]
        self.s = [[next(idx) for q in range(3)] for t in range(T + 1)]
        # drop unused column 0
        used = set()
        for t in range(T + 1):
            for i in range(1, L + 1): used |= {self.b[t][i], self.h[t][i]}
            used |= set(self.s[t])
        self.tab_vars = sorted(used)
        self.inputs = [self.b[0][i] for i in range(1, n + 1)]
        top = max(used) + 1
        self.pad = list(range(top, top + kappa))
        self.N = len(self.tab_vars) + kappa
        self.C = self._constraints()

    def delta(self, q, a):
        if self.machine == 'ACC':
            return (1 if q == 0 else q), a
        if self.machine == 'AND':
            if q == 0: return (0, 1) if a == 1 else (2, 0)
            return q, a
        raise ValueError

    def _constraints(self):
        T, L, b, h, s = self.T, self.L, self.b, self.h, self.s
        C = []
        for v in self.tab_vars:                                  # booleanity
            C.append(('bool', pmul(X(v), neg1(v))))
        C.append(('init', neg1(s[0][0]))); C.append(('init', X(s[0][1]))); C.append(('init', X(s[0][2])))
        C.append(('init', neg1(h[0][1])))
        for i in range(2, L + 1): C.append(('init', X(h[0][i])))
        C.append(('init', X(b[0][L])))                            # cell n+1 starts 0
        for t in range(T + 1):                                    # state one-hot
            for q, r in itertools.combinations(range(3), 2):
                C.append(('onehot', pmul(X(s[t][q]), X(s[t][r]))))
            C.append(('onehot', pmul(pmul(neg1(s[t][0]), neg1(s[t][1])), neg1(s[t][2]))))
        for t in range(T):
            C.append(('head', X(h[t + 1][1])))                    # head moves right
            for i in range(2, L + 1): C.append(('head', xor(h[t + 1][i], h[t][i - 1])))
            for i in range(1, L + 1):
                C.append(('frame', pmul(neg1(h[t][i]), xor(b[t][i], b[t + 1][i]))))
                for q in range(3):
                    for a in (0, 1):
                        q2, a2 = self.delta(q, a)
                        pre = pmul(pmul(X(s[t][q]), X(h[t][i])), lit(b[t][i], a))
                        C.append(('trans', pmul(pre, neg1(s[t + 1][q2]))))
                        C.append(('trans', pmul(pre, padd(ONE, lit(b[t + 1][i], a2), -1))))
        C.append(('accept', X(s[T][2])))
        return C

    def run(self, x):
        """Assignment {var: 0/1} of the (unique) computation tableau on input x, and acceptance."""
        T, L = self.T, self.L
        a = {v: 0 for v in self.tab_vars}
        tape = [0] + list(x) + [0]
        q, pos = 0, 1
        for t in range(T + 1):
            for i in range(1, L + 1): a[self.b[t][i]] = tape[i]
            a[self.h[t][pos]] = 1
            a[self.s[t][q]] = 1
            if t < T:
                q2, a2 = self.delta(q, tape[pos]); tape[pos] = a2; q = q2; pos += 1
        return a, q != 2

def ev(p, a, P=None):
    tot = 0
    for m, c in p.items():
        t = c
        for v, e in m:
            t *= a[v] ** e
            if t == 0: break
        tot += t
    return tot % P if P else tot

def sanity(tab):
    import random
    rnd = random.Random(1)
    for x in itertools.product((0, 1), repeat=tab.n):
        a, acc = tab.run(x)
        viol = [k for k, c in tab.C if ev(c, a) != 0]
        assert all(ev(c, a) in (0, 1) for _, c in tab.C)
        assert (viol == []) == acc, (x, viol, acc)
        assert viol in ([], ['accept']), viol
        for _ in range(20):           # random single flips break validity
            v = rnd.choice(tab.tab_vars); a2 = dict(a); a2[v] ^= 1
            assert any(ev(c, a2) != 0 for _, c in tab.C)
    return True
