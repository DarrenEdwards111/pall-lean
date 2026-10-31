"""Kill-loop plugin (external; does not modify the Einstein repo): exact SPDP measures of the
multilinear extension chi_f of a Boolean function, at the paper's parameters kappa = ell = max(1, floor(log2 n)),
singleton blocks.  Rank over Q computed with the kill loop's own exact `rank_q`.
  spdp_lean_logn         : MultilinearSPDP.mlBlockedSpdpRank (shifts with vars in S, mlProj drops)
  spdp_def12_reduce_logn : paper v5 Def. 12 (any shift monomial of degree <= ell, x_i^2 -> x_i)
Load with: PYTHONPATH=<this dir> python -m killloop --plugins killloop_spdp_plugin --spec ...
"""
import itertools
from killloop.representations import register_measure
from killloop.exact import rank_q


def _kappa(n):
    return max(1, n.bit_length() - 1)


def _rows(poly, n, conv):
    k = _kappa(n); ell = k
    p = {m: c for m, c in poly.items()}                # mask -> int coeff (multilinear)
    rows = []
    for S in itertools.combinations(range(n), k):
        smask = sum(1 << i for i in S)
        d = {m ^ smask: c for m, c in p.items() if m & smask == smask}
        if not d:
            continue
        shift_vars = S if conv == 'lean' else range(n)
        for deg in range(ell + 1):
            for u in itertools.combinations_with_replacement(shift_vars, deg):
                umask = 0; ml = True
                for v in u:
                    if umask >> v & 1: ml = False
                    umask |= 1 << v
                row = {}
                for m, c in d.items():
                    if conv == 'lean':
                        if not ml or (m & umask):
                            continue
                    k2 = m | umask
                    row[k2] = row.get(k2, 0) + c
                row = {a: b for a, b in row.items() if b}
                if row:
                    rows.append(row)
    return rows


def _rank(rows):
    if not rows:
        return 0
    uniq = {tuple(sorted(r.items())): r for r in rows}
    cols = sorted({m for r in uniq.values() for m in r})
    idx = {m: i for i, m in enumerate(cols)}
    mat = []
    for r in uniq.values():
        v = [0] * len(cols)
        for m, c in r.items():
            v[idx[m]] = c
        mat.append(v)
    return rank_q(mat)


register_measure('spdp_lean_logn', 'multilinear_q', lambda p, f, **k: _rank(_rows(p, f.n, 'lean')),
                 'Lean mlBlockedSpdpRank of chi_f, singleton blocks, kappa=ell=floor(log2 n)', max_n=8)
register_measure('spdp_def12_reduce_logn', 'multilinear_q', lambda p, f, **k: _rank(_rows(p, f.n, 'def12')),
                 'paper Def. 12 (any shift, x^2->x) SPDP rank of chi_f, kappa=ell=floor(log2 n)', max_n=7)
