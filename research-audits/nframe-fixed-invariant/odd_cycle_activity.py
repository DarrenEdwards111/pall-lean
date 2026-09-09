"""Exact integer checks of the existing local energy, alpha=beta=1."""
import json
from itertools import product
from math import prod
from pathlib import Path

def energies(x):
    n = len(x)
    phi = [x[i] * x[(i+1) % n] for i in range(n)]
    edge = [(phi[i] - phi[(i+1) % n])**2 for i in range(n)]
    penalty = [1 + a for a in phi]  # charge -1, signed phi
    local = [edge[(i-1) % n] + edge[i] + penalty[i] for i in range(n)]
    return phi, penalty, local

checked = 0
for n in range(3, 14, 2):
    for x in product((-1, 1), repeat=n):
        phi, penalty, local = energies(x)
        assert prod(phi) == 1
        assert sum(penalty) >= 2
        assert max(local) >= 2
        checked += 1

for n in range(3, 1002, 2):
    x = [(-1)**i for i in range(n)]
    phi, penalty, local = energies(x)
    assert phi == [-1]*(n-1) + [1]
    assert sum(penalty) == 2
    assert sum(local) == 18
    assert sum(e > 0 for e in local) == 3

result = {
    "exhaustive_signed_assignments": checked,
    "exhaustive_odd_sizes": list(range(3, 14, 2)),
    "constructive_sizes_checked": 500,
    "maximum_constructive_size": 1001,
    "alpha": 1, "beta": 1,
    "constructed_total_local_energy": 18,
    "constructed_positive_energy_vertices": 3,
    "scope": "finite exact checks; general algebra explained in accompanying note; no runtime lower bound"
}
print(json.dumps(result, indent=2))
