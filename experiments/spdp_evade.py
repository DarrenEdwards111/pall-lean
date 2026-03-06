#!/usr/bin/env python3
"""
Find an observable that violation-counting CAN'T evade.

The problem: ∑G_i (violation count) and ∏(1-G_i) (AND indicator)
have the same zero set on {0,1}^n but different Möbius mass.
A solver can use violation counting to correctly decide SAT
without producing high Möbius mass.

What properties MUST any correct encoding share?

Key insight: the DECISION FUNCTION is f(x) = [∑G_i(x) = 0].
This is a {0,1}-valued function. Its multilinear extension is UNIQUE:
  f_ML(x) = ∏(1-G_i)
So the multilinear extension of the decision function has high Möbius mass.

But the solver doesn't compute f_ML directly — it computes ∑G_i and
then applies the nonlinear test "= 0?".

Question: is there an observable of ∑G_i that MUST be high because
it encodes the same decision as ∏(1-G_i)?

Candidates:
A. Schwartz-Zippel style: evaluate at random field points
B. Resultant/discriminant: algebraic invariant of the zero set
C. Hilbert function of the zero ideal
D. Polynomial identity testing: any polynomial agreeing on {0,1}
E. Derivative of the INDICATOR (not the polynomial)
F. Spectral norm of the boolean function
"""
import numpy as np
from itertools import combinations, product as cartprod
from collections import defaultdict

def poly_mul(p1,p2):
    r=defaultdict(int)
    for m1,c1 in p1.items():
        for m2,c2 in p2.items():
            if m1&m2:continue
            r[m1|m2]+=c1*c2
    return {m:c for m,c in r.items() if c}

def poly_add(p1,p2):
    r=defaultdict(int)
    for m,c in p1.items():r[m]+=c
    for m,c in p2.items():r[m]+=c
    return {m:c for m,c in r.items() if c}

def poly_neg(p): return {m:-c for m,c in p.items()}
def X(i): return {frozenset([i]):1}
def C(c): return {frozenset():c} if c else {}

def pderiv(p,v):
    r=defaultdict(int)
    for m,c in p.items():
        if v in m: r[m-{v}]+=c
    return {m:c for m,c in r.items() if c}

def poly_eval(p, assignment):
    result = 0
    for m, c in p.items():
        val = c
        for v in m:
            val *= assignment.get(v, 0)
        result += val
    return result

def G(i):
    return poly_mul(X(2*i), X(2*i+1))

# Build key polynomials
def build_and(n):
    """∏(1-G_i) = AND indicator"""
    p = C(1)
    for i in range(n):
        p = poly_mul(p, poly_add(C(1), poly_neg(G(i))))
    return p

def build_count(n):
    """∑G_i = violation count"""
    p = {}
    for i in range(n):
        p = poly_add(p, G(i))
    return p

def build_negcount(n):
    """1 - ∑G_i = 1 when satisfied, negative otherwise"""
    return poly_add(C(1), poly_neg(build_count(n)))

# === Observable A: Boolean function spectral properties ===
# The decision function f(x) = [p(x) = 0] is the same for both
# representations. Its Fourier spectrum is fixed.
# Fourier coefficients: f̂(S) = E_x[f(x)·χ_S(x)]

def fourier_spectrum(decision_fn, n):
    """Compute Fourier spectrum of a {0,1}-valued function on {0,1}^n."""
    coeffs = {}
    for size in range(n+1):
        for S in combinations(range(n), size):
            S_set = set(S)
            fhat = 0
            for bits in cartprod([0,1], repeat=n):
                x = {i: bits[i] for i in range(n)}
                fx = decision_fn(x)
                chi = 1
                for i in S_set:
                    chi *= (1 - 2*bits[i])  # ±1 basis
                fhat += fx * chi
            fhat /= 2**n
            if abs(fhat) > 1e-10:
                coeffs[frozenset(S)] = fhat
    return coeffs

print("=" * 70)
print("OBSERVABLES THAT VIOLATION-COUNTING CAN'T EVADE")
print("=" * 70)

# === Test A: Fourier spectrum of the DECISION function ===
print("\n--- A: Fourier spectrum of DECISION function f(x) = [all satisfied] ---")
print("This is representation-independent (property of the boolean function).")
print()

for n in [2, 3, 4, 5]:
    def decision(x, n=n):
        return 1 if all(x.get(2*i,0) * x.get(2*i+1,0) == 0 for i in range(n)) else 0
    
    # This is the AND of NOT(G_i): satisfied when G_i = 0 for all i
    spec = fourier_spectrum(decision, 2*n)
    
    nonzero_by_level = defaultdict(int)
    total_energy_by_level = defaultdict(float)
    for S, c in spec.items():
        nonzero_by_level[len(S)] += 1
        total_energy_by_level[len(S)] += c**2
    
    print(f"  n={n}:")
    for level in sorted(nonzero_by_level.keys()):
        print(f"    level {level}: {nonzero_by_level[level]} nonzero coeffs, energy={total_energy_by_level[level]:.4f}")

# === Test B: Spectral concentration ===
print("\n--- B: Spectral energy at level k (Fourier weight) ---")
print("W_k = ∑_{|S|=k} f̂(S)²")
print("This is the same for ANY polynomial computing the same boolean function.")
print()
print(f"{'n':>3}", end="")
for k in range(6):
    print(f"  W_{k:>1}      ", end="")
print()

for n in [2, 3, 4]:
    def decision(x, n=n):
        return 1 if all(x.get(2*i,0) * x.get(2*i+1,0) == 0 for i in range(n)) else 0
    
    spec = fourier_spectrum(decision, 2*n)
    weights = defaultdict(float)
    for S, c in spec.items():
        weights[len(S)] += c**2
    
    print(f"{n:>3}", end="")
    for k in range(min(6, 2*n+1)):
        print(f"  {weights[k]:.4f}", end="")
    print()

# === Test C: Decision complexity measures ===
print("\n--- C: Decision complexity measures ---")
print("These are properties of f(x) = [all G_i = 0], not of any polynomial.")
print()

for n in [2, 3, 4, 5]:
    def decision(x, n=n):
        return 1 if all(x.get(2*i,0) * x.get(2*i+1,0) == 0 for i in range(n)) else 0
    
    spec = fourier_spectrum(decision, 2*n)
    
    # Total influence: I(f) = ∑_i Pr[f changes when x_i flips]
    total_influence = 0
    for i in range(2*n):
        changes = 0
        total = 0
        for bits in cartprod([0,1], repeat=2*n):
            x = {j: bits[j] for j in range(2*n)}
            fx = decision(x)
            x_flip = dict(x)
            x_flip[i] = 1 - x[i]
            fx_flip = decision(x_flip)
            if fx != fx_flip:
                changes += 1
            total += 1
        total_influence += changes / total
    
    # Spectral degree: max |S| with f̂(S) ≠ 0
    spec_degree = max((len(S) for S, c in spec.items()), default=0)
    
    # Number of satisfying assignments
    sat_count = sum(1 for bits in cartprod([0,1], repeat=2*n) 
                    if decision({j: bits[j] for j in range(2*n)}))
    
    print(f"  n={n}: influence={total_influence:.2f}  spec_degree={spec_degree}  #sat={sat_count}/{2**(2*n)}")

# === Test D: THE KEY — multilinear extension is UNIQUE ===
print("\n" + "=" * 70)
print("KEY OBSERVATION: Multilinear Extension")
print("=" * 70)
print("""
The multilinear extension of f: {0,1}^n → {0,1} is UNIQUE.
For f = "all satisfied" = ∏_i(1 - G_i), the ML extension IS the product.

ANY polynomial p that agrees with f on {0,1}^n differs from the ML
extension only by elements of the ideal (x_i² - x_i).

So: p = ∏(1-G_i) + ∑_i (x_i² - x_i) · h_i(x)

The violation count ∑G_i does NOT agree with ∏(1-G_i) on {0,1}^n!
  ∑G_i gives the COUNT (0,1,2,...,n)
  ∏(1-G_i) gives the INDICATOR (0 or 1)

These are DIFFERENT boolean functions. The solver uses ∑G_i to 
COMPUTE the answer, but the answer itself (yes/no) corresponds to
a DIFFERENT function whose ML extension is ∏(1-G_i).

The bridge question becomes: can we force the solver to produce
a polynomial computing the INDICATOR function (not just the count)?
""")

# Verify: violation count vs AND indicator on {0,1}^n
print("--- Verification: count vs indicator values ---")
for n in [3]:
    count_p = build_count(n)
    and_p = build_and(n)
    
    print(f"  n={n}:")
    for bits in cartprod([0,1], repeat=2*n):
        a = {j: bits[j] for j in range(2*n)}
        cv = poly_eval(count_p, a)
        av = poly_eval(and_p, a)
        sat = all(bits[2*i]*bits[2*i+1] == 0 for i in range(n))
        if cv <= 1:  # show interesting cases
            print(f"    x={''.join(str(b) for b in bits)}  count={cv}  AND={av}  sat={sat}")

# === Test E: What if we use the INDICATOR observable? ===
print("\n--- E: Indicator-based observable ---")
print("Define I(p) = multilinear extension of [p(x) = 0]")
print("This transforms ANY polynomial into the unique ML indicator.")
print("The ML indicator of ∑G_i = 0 IS ∏(1-G_i).")
print("So I(∑G_i) = ∏(1-G_i), which has high Möbius mass.")
print()
print("But: computing I(p) from p is EXPONENTIAL (requires evaluating")
print("p on all 2^n boolean inputs to build the truth table).")
print("So I is not a polynomial-time computable observable.")
print()
print("HOWEVER: we don't need to COMPUTE I(p) efficiently.")
print("We just need to prove that rank(I(p)) is superpolynomial.")
print("And since I(p) = ∏(1-G_i) whenever p correctly encodes SAT,")
print("this is already proved (NP-side lower bound).")

# === Test F: The ACTUAL bridge ===
print("\n" + "=" * 70)
print("THE ACTUAL BRIDGE ARGUMENT")
print("=" * 70)
print("""
Here is the argument that might work:

1. If P=NP, there exists poly-time M* solving SAT.
2. M* compiled polynomial P_{M*} has polynomial SPDP rank (P-side). ✓
3. P_{M*}, restricted to correct computation trace on input Φ,
   gives a polynomial r(x) in content variables.
4. r(x) = 0 ⟺ Φ is satisfiable (by correctness of M*).

5. The INDICATOR function I(x) = [r(x) = 0] has a unique
   multilinear extension: ∏(1-G_i).
6. rank(∏(1-G_i)) ≥ superpolynomial (NP-side). ✓

7. KEY QUESTION: Is rank(∏(1-G_i)) ≤ rank(r)?
   i.e., does the indicator's rank bound the encoding's rank?

8. If YES: superpoly ≤ rank(∏(1-G_i)) ≤ rank(r) ≤ rank(P_{M*}) ≤ poly.
   Contradiction.

The question is step 7: does the zero-set indicator polynomial
have SPDP rank bounded by the encoding polynomial?

This is NOT obvious. The indicator [r=0] involves a nonlinear
operation (testing equality with zero). There's no reason the
indicator's rank should be ≤ the encoding's rank.

In fact, counterexample:
  r(x) = x₁ + x₂ (linear, rank 1)
  [r=0] indicator ML = 1 - x₁ - x₂ + 2x₁x₂ (has cross-term, rank > 1)

So the indicator can have HIGHER rank than the encoding.
Step 7 fails in the wrong direction!

We need rank(indicator) ≤ rank(encoding), but the indicator
can be MORE complex than the encoding.
""")

# Verify the counterexample
print("--- Counterexample verification ---")
r = poly_add(X(0), X(1))  # r = x₁ + x₂
# Indicator: [r=0] on {0,1}² 
# r(0,0)=0 → I=1; r(0,1)=1 → I=0; r(1,0)=1 → I=0; r(1,1)=2 → I=0
# ML of I: f(0,0)=1, f(0,1)=0, f(1,0)=0, f(1,1)=0
# = 1 - x₁ - x₂ + x₁x₂ = (1-x₁)(1-x₂)
ind = poly_mul(poly_add(C(1), poly_neg(X(0))), poly_add(C(1), poly_neg(X(1))))

from itertools import combinations as combs
def spdp_rank(poly, variables, kappa):
    derivs = []
    for combo in combs(variables, kappa):
        d = poly
        for v in combo:
            d = pderiv(d, v)
            if not d: break
        if d: derivs.append(d)
    if not derivs: return 0
    all_m = sorted(set().union(*(d.keys() for d in derivs)), key=lambda s:(len(s),tuple(sorted(s))))
    mi = {m:i for i,m in enumerate(all_m)}
    mat = np.zeros((len(derivs),len(all_m)))
    for i,d in enumerate(derivs):
        for m,c in d.items(): mat[i,mi[m]]=c
    return int(np.linalg.matrix_rank(mat))

print(f"  r = x₀+x₁: rank(κ=1) = {spdp_rank(r, [0,1], 1)}")
print(f"  I = (1-x₀)(1-x₁): rank(κ=1) = {spdp_rank(ind, [0,1], 1)}")
print(f"  Indicator has HIGHER rank than encoding.")
print()

# But wait — we need rank(indicator) ≤ rank(encoding).
# The indicator is MORE complex. So the inequality goes the WRONG way.
# 
# UNLESS... we reverse the argument:
# rank(encoding) ≥ rank(indicator) ≥ superpolynomial
# This would say the ENCODING must be at least as complex as the indicator.
# Is this true?

print("=== REVERSED ARGUMENT ===")
print("What if: rank(encoding) ≥ rank(indicator)?")
print("i.e., any polynomial whose zero set = SAT solutions")
print("must have rank ≥ rank of the AND indicator?")
print()

# Test: for various polynomials with same zero set, compare ranks
print("--- Polynomials with same zero set {(0,0)} on {0,1}² ---")
# Zero set: {(0,0)} = only (0,0) satisfies
# Indicator: (1-x₀)(1-x₁)
# Other reps: x₀+x₁ (zero at (0,0) but also at... no, x₀+x₁=0 only at (0,0))
# Wait: x₀+x₁ at (0,0)=0, (0,1)=1, (1,0)=1, (1,1)=2. Zero set = {(0,0)}. ✓
# Also: x₀+x₁+x₀x₁ at (0,0)=0, (0,1)=1, (1,0)=1, (1,1)=3. Zero set = {(0,0)}. ✓
# Also: x₀²+x₁² = x₀+x₁ (multilinear). Same.

test_polys = [
    ("x₀+x₁", poly_add(X(0), X(1))),
    ("x₀·x₁", poly_mul(X(0), X(1))),  # zero set: {(0,0),(0,1),(1,0)} ≠ {(0,0)}
    ("x₀+x₁+x₀x₁", poly_add(poly_add(X(0), X(1)), poly_mul(X(0), X(1)))),
    ("(1-x₀)(1-x₁)", ind),
    ("2x₀+3x₁", poly_add(poly_scale(X(0),2), poly_scale(X(1),3))),
]

print(f"  {'poly':>20} {'zero_set':>20} {'rank_1':>7}")
for name, p in test_polys:
    zs = []
    for bits in cartprod([0,1], repeat=2):
        a = {0: bits[0], 1: bits[1]}
        if poly_eval(p, a) == 0:
            zs.append(bits)
    r1 = spdp_rank(p, [0,1], 1)
    print(f"  {name:>20} {str(zs):>20} {r1:>7}")

print()
print("x₀+x₁ and (1-x₀)(1-x₁) have DIFFERENT zero sets!")
print("x₀+x₁ = 0 only at (0,0)")  
print("(1-x₀)(1-x₁) = 0 at (0,1), (1,0), (1,1)")
print()
print("So they're not encoding the same decision problem.")
print("The indicator [p=0] and p itself have different zero sets.")
print()
print("For SAT: the solver computes a polynomial r(x) where")
print("r(x)=0 ⟺ x is satisfying. The zero set of r IS the sat set.")
print("But the indicator [r≠0] has zero set = complement of sat set.")
print("These are different functions with potentially different ranks.")
