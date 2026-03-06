#!/usr/bin/env python3
"""
Algebraic (non-multilinear) partial trace channel.

Key insight: SPDP works with the ACTUAL polynomial, not its multilinear extension.
The partial trace of the algebraic polynomial preserves non-multilinear structure
that encodes coupling through state variables.

We use a sparse monomial representation for efficiency.
"""
from collections import defaultdict
from itertools import combinations, product as cart_product
from math import comb
import time

class SparsePoly:
    """Sparse polynomial over integer variables. Monomial = tuple of (var, power) pairs."""
    def __init__(self, terms=None):
        # terms: dict { monomial_key: coefficient }
        # monomial_key: frozenset of (var_index, power) or tuple sorted
        self.terms = defaultdict(int)
        if terms:
            for k, v in terms.items():
                if v != 0:
                    self.terms[k] = v
    
    @staticmethod
    def var(i):
        p = SparsePoly()
        p.terms[((i, 1),)] = 1
        return p
    
    @staticmethod
    def const(c):
        p = SparsePoly()
        if c != 0:
            p.terms[()] = c
        return p
    
    def __add__(self, other):
        if isinstance(other, (int, float)):
            other = SparsePoly.const(other)
        result = SparsePoly()
        for k, v in self.terms.items():
            result.terms[k] += v
        for k, v in other.terms.items():
            result.terms[k] += v
        # Clean zeros
        result.terms = defaultdict(int, {k: v for k, v in result.terms.items() if v != 0})
        return result
    
    def __radd__(self, other):
        return self.__add__(other)
    
    def __sub__(self, other):
        return self + (other * (-1))
    
    def __neg__(self):
        return self * (-1)
    
    def __mul__(self, other):
        if isinstance(other, (int, float)):
            result = SparsePoly()
            for k, v in self.terms.items():
                result.terms[k] = v * other
            result.terms = defaultdict(int, {k: v for k, v in result.terms.items() if v != 0})
            return result
        
        result = SparsePoly()
        for k1, v1 in self.terms.items():
            for k2, v2 in other.terms.items():
                # Multiply monomials: merge (var, power) pairs
                merged = defaultdict(int)
                for (var, pow_) in k1:
                    merged[var] += pow_
                for (var, pow_) in k2:
                    merged[var] += pow_
                key = tuple(sorted(merged.items()))
                result.terms[key] += v1 * v2
        result.terms = defaultdict(int, {k: v for k, v in result.terms.items() if v != 0})
        return result
    
    def __rmul__(self, other):
        return self.__mul__(other)
    
    def __pow__(self, n):
        if n == 0:
            return SparsePoly.const(1)
        result = self
        for _ in range(n - 1):
            result = result * self
        return result
    
    def subs(self, var_idx, value):
        """Substitute var_idx = value (integer)."""
        result = SparsePoly()
        for monom, coeff in self.terms.items():
            new_monom = []
            multiplier = coeff
            for (var, pow_) in monom:
                if var == var_idx:
                    multiplier *= value ** pow_
                else:
                    new_monom.append((var, pow_))
            key = tuple(sorted(new_monom))
            result.terms[key] += multiplier
        result.terms = defaultdict(int, {k: v for k, v in result.terms.items() if v != 0})
        return result
    
    def coeff_mass_on_vars(self, var_set):
        """Sum of |coeff| for monomials using ONLY variables in var_set."""
        total = 0
        for monom, coeff in self.terms.items():
            if len(monom) == 0:
                continue  # skip constant
            vars_used = {var for (var, _) in monom}
            if vars_used <= var_set:
                total += abs(coeff)
        return total
    
    def n_terms(self):
        return len(self.terms)

def partial_trace(poly, state_var_indices):
    """Sum poly over all {0,1} assignments to state vars. LINEAR in poly."""
    n_state = len(state_var_indices)
    result = SparsePoly.const(0)
    for bits in cart_product([0, 1], repeat=n_state):
        p = poly
        for i, var_idx in enumerate(state_var_indices):
            p = p.subs(var_idx, bits[i])
        result = result + p
    return result

def build_models(nc, cs=2):
    """Build models. Content vars: 0..nc*cs-1, state vars: 1000..1000+nc-1"""
    n_content = nc * cs
    content = list(range(n_content))
    state = list(range(1000, 1000 + nc))
    
    x = [SparsePoly.var(i) for i in content]
    s = [SparsePoly.var(i) for i in state]
    
    # Gates: G_i = x_{2i} * x_{2i+1}
    gates = [x[i*cs] * x[i*cs+1] for i in range(nc)]
    
    # Pure product: Π(1 - G_i)
    pure_product = SparsePoly.const(1)
    for g in gates:
        pure_product = pure_product * (SparsePoly.const(1) + g * (-1))
    
    # Pure sum
    pure_sum = SparsePoly.const(0)
    for g in gates:
        pure_sum = pure_sum + g
    
    # TM violation: Σ c_t²
    c0 = s[0] + gates[0] * (-1)
    violations = [c0 ** 2]
    for t in range(1, nc):
        # c_t = s_t - s_{t-1}*(1-G_t) - G_t
        ct = s[t] + (s[t-1] * (SparsePoly.const(1) + gates[t] * (-1))) * (-1) + gates[t] * (-1)
        violations.append(ct ** 2)
    tm_violation = SparsePoly.const(0)
    for v in violations:
        tm_violation = tm_violation + v
    
    # TM product: Π(1 - c_t²)
    tm_product = SparsePoly.const(1)
    for v in violations:
        tm_product = tm_product * (SparsePoly.const(1) + v * (-1))
    
    return {
        'pure_product': (pure_product, False),
        'pure_sum': (pure_sum, False),
        'tm_violation': (tm_violation, True),
        'tm_product': (tm_product, True),
    }, content, state

def mobius_analysis(poly, nc, cs=2):
    """Compute Möbius mass at levels 0,1,2,3 for clause structure."""
    clause_var_sets = [set(range(i*cs, (i+1)*cs)) for i in range(nc)]
    
    # f_S for all subsets up to size min(3, nc)
    f_cache = {}
    def get_f(clause_set):
        key = frozenset(clause_set)
        if key not in f_cache:
            var_set = set()
            for c in clause_set:
                var_set |= clause_var_sets[c]
            f_cache[key] = poly.coeff_mass_on_vars(var_set)
        return f_cache[key]
    
    results = {}
    for level in range(min(4, nc+1)):
        total = 0
        for T in combinations(range(nc), level):
            fhat = 0
            for r in range(level + 1):
                for S in combinations(T, r):
                    sign = (-1) ** (level - r)
                    fhat += sign * get_f(S)
            total += abs(fhat)
        results[level] = total
    return results

def run(nc):
    t0 = time.time()
    models, content, state = build_models(nc)
    
    print(f"\nn={nc}, C(n,2)={comb(nc,2)}, C(n,3)={comb(nc,3)}")
    
    for name, (poly, has_state) in models.items():
        t1 = time.time()
        if has_state:
            traced = partial_trace(poly, state)
            tag = "partial_tr"
        else:
            traced = poly
            tag = "direct"
        
        mob = mobius_analysis(traced, nc)
        elapsed = time.time() - t1
        
        m_str = "  ".join(f"|T|={k}→{v}" for k, v in sorted(mob.items()))
        print(f"  {name:20s} ({tag:10s}): {m_str}  [{traced.n_terms()} terms, {elapsed:.1f}s]")
    
    print(f"  Total time: {time.time()-t0:.1f}s")

for nc in [2, 3, 4, 5, 6]:
    try:
        run(nc)
    except Exception as e:
        print(f"\nn={nc}: ERROR {e}")
        import traceback; traceback.print_exc()
        break
