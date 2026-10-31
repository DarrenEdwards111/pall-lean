#!/usr/bin/env python3
"""HAL 9000's sanity suite for the observer-visible DYNAMIC HYPERCUBE SPDP measure.

The candidate hard-witness for the hypercube costume is 'persistent boundary / expansion /
identity-minor growth of the level set on the Boolean hypercube'. The exact, poly-computable
incarnation of 'hypercube boundary of f' is the TOTAL INFLUENCE (average sensitivity):
    I[f] = (# bichromatic edges) * 2 / 2^n ,   0 <= I[f] <= n.
This IS the edge-boundary / expansion of the level set f^{-1}(1) on the hypercube graph.

Test #2 (parity) is the decisive one: parity MAXIMISES the hypercube boundary (I = n, every edge
is a boundary edge) yet parity is TRIVIALLY in P. So 'high dynamic hypercube boundary' is HIGH on
the easiest possible object => it is not a hardness witness. Same collapse shape as do-nothing
(SPDP grid junk) and Tseitin (Gaussian elimination)."""

def total_influence(f, n):
    boundary = 0                       # bichromatic edges, counted once (y>x)
    for x in range(1 << n):
        fx = f(x, n)
        for i in range(n):
            y = x ^ (1 << i)
            if y > x and fx != f(y, n):
                boundary += 1
    return boundary, 2.0 * boundary / (1 << n)   # (#boundary edges, total influence I[f])

def parity(x, n):   return bin(x).count("1") & 1
def AND(x, n):      return 1 if x == (1 << n) - 1 else 0
def OR(x, n):       return 0 if x == 0 else 1
def majority(x, n): return 1 if bin(x).count("1") * 2 > n else 0
def dictator(x, n): return (x >> 0) & 1
def const0(x, n):   return 0

fns = [("parity", parity), ("majority", majority), ("dictator", dictator),
       ("OR", OR), ("AND", AND), ("const-0", const0)]
inP = {name: True for name, _ in fns}     # every one of these is trivially in P

print("=== Observer sanity suite: 'hypercube boundary' (total influence) vs 'is it in P?' ===")
print("Candidate hard-witness = edge-boundary/expansion of the level set on the hypercube.\n")
hdr = f"{'function':>9} |" + "".join(f"  I[f] n={n:<2}" for n in (6, 8, 10, 12)) + " |  in P?"
print(hdr); print("-" * len(hdr))
for name, f in fns:
    row = f"{name:>9} |"
    for n in (6, 8, 10, 12):
        _, I = total_influence(f, n)
        row += f"   {I:6.2f} "
    row += f" |  {'YES' if inP[name] else 'no'}"
    print(row)

print("""
=== Verdict on the four sanity tests ===
  1. do-nothing DTM : raw compiled SPDP rank ~ 2^638536 (spdp_blowup.py) -- grid junk, HIGH. [fails L1]
  2. parity         : hypercube boundary I[f] = n = MAXIMAL, and parity is in P. [fails L2 -- HIGH on easiest]
  3. Tseitin gadget : resolution/expansion HIGH, but Gaussian elimination decides it (tseitin_in_P.py). [in P]
  4. expander Tseitin: same, more so -- still a GF(2) linear system, still in P. [in P]

The 'hard witness' is HIGH on parity, Tseitin, expander-Tseitin -- all in P. And I[f] itself is
poly(2^n)-computable from the truth table and bounded by n: a 'natural', efficiently-checkable,
large property => Razborov-Rudich territory. So the hypercube-boundary witness is either high on
P-easy objects (restricted-model collapse) or a natural property (RR barrier). No branch reaches
NP-hardness-against-P. The observer constraint does not fix this -- it relocates it. """)
