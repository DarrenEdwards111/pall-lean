"""Exact signed incidence construction; energy matches localEnergy, alpha=beta=1."""
import json
from pathlib import Path
from random import Random
from math import prod

def check(n, edges):
    assert n >= 3 and n % 2 == 1
    edges = sorted(set(tuple(sorted(e)) for e in edges))
    assert all(a != b for a,b in edges)
    adj = [[] for _ in range(n)]
    for i,(a,b) in enumerate(edges):
        adj[a].append((b,i)); adj[b].append((a,i))
    parent = {0: None}; order = [0]
    for v in order:
        for w,i in adj[v]:
            if w not in parent:
                parent[w] = (v,i); order.append(w)
    assert len(order) == n
    target = [1] + [-1]*(n-1)
    residual = target[:]; labels = [1]*len(edges)
    for v in reversed(order[1:]):
        w,i = parent[v]
        labels[i] = residual[v]
        residual[w] *= residual[v]
    assert residual[0] == 1
    field = [prod(labels[i] for _,i in adj[v]) for v in range(n)]
    assert field == target
    energy = [sum((field[v]-field[w])**2 for w,_ in adj[v]) + 1+field[v] for v in range(n)]
    assert sum(energy) == 8*len(adj[0])+2
    assert sum(e > 0 for e in energy) == len(adj[0])+1
    return len(edges), len(adj[0]), sum(energy)

rng = Random(20260909)
counts = {"cycles": 0, "four_regular_circulants": 0, "complete_graphs": 0, "random_connected": 0}
for n in range(3, 102, 2):
    cycle = [(i,(i+1)%n) for i in range(n)]
    check(n,cycle); counts["cycles"] += 1
    if n >= 5:
        result = check(n,cycle+[(i,(i+2)%n) for i in range(n)])
        assert result[1:] == (4,34)
        counts["four_regular_circulants"] += 1
    if n <= 31:
        check(n,[(i,j) for i in range(n) for j in range(i+1,n)])
        counts["complete_graphs"] += 1
    for _ in range(10):
        tree = [(i,rng.randrange(i)) for i in range(1,n)]
        extra = [(i,j) for i in range(n) for j in range(i+1,n) if rng.random()<0.08]
        check(n,tree+extra); counts["random_connected"] += 1
print(json.dumps({"cases":counts,"total":sum(counts.values()),"all_passed":True,
    "energy_identity":"8*degree(root)+2 at alpha=beta=1",
    "scope":"Exact finite checks of tree construction; no claim tested circulants are expanders"},indent=2))
