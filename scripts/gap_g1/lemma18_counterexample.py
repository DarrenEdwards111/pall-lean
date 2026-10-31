#!/usr/bin/env python3
"""Paper v5 Lemma 18 claims Gamma_{l,l}(p) <= C(N,l) * 2^l for multilinear p (shifts 'can be chosen with support in S').
Counterexample p = x1 + x2 x3, N = 3, kappa = ell = 1: Def.-12 rank 7 > 6 (reduce and drop); Lean measure gives 5."""
import sys, math
sys.path.insert(0, '../spdp_obstruction')
from spdp_rank import spdp_rank
p = {frozenset([0]): 1, frozenset([1, 2]): 1}
for conv, mode in (('PAPER', 'reduce'), ('PAPER', 'drop'), ('LEAN', 'drop')):
    print(conv, mode, spdp_rank(p, 3, 1, 1, conv, mode, exact=True)[0], 'Lemma 18 bound', math.comb(3, 1) * 2)
