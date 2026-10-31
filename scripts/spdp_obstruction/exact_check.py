"""Exact (Fraction) cross-check of the modular ranks for small cases."""
from spdp_rank import *
for name, p, n in [('prod', p_prod(7), 7), ('parity', p_parity(7), 7), ('point', p_point(7), 7), ('esym', p_esym(7,3), 7), ('det3', p_det(3), 9)]:
    k = int(math.log2(n))
    for conv, mode in (('LEAN','drop'),('PAPER','reduce'),('PAPER','drop')):
        a = spdp_rank(p, n, k, k, conv, mode, exact=False)[0]
        b = spdp_rank(p, n, k, k, conv, mode, exact=True)[0]
        print(name, n, conv, mode, a, b, 'OK' if a == b else 'MISMATCH')
