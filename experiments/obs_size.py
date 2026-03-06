#!/usr/bin/env python3
"""observableSize(productPoly) vs observableSize(sumPoly)"""
from itertools import combinations
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

def eval_zero(p): return p.get(frozenset(),0)

def observableSize(p, variables, k):
    """Count of k-tuples where ∂_{i1}...∂_{ik} p |_{x=0} ≠ 0"""
    count=0
    total=0
    for combo in combinations(variables, k):
        total+=1
        d=p
        for v in combo:
            d=pderiv(d,v)
            if not d: break
        if d and eval_zero(d)!=0:
            count+=1
    return count, total

# Product: ∏(1-z_i·G_i)
def productPoly(n):
    p=C(1)
    for i in range(n):
        g=poly_add(X(2*i),X(2*i+1))
        p=poly_mul(p, poly_add(C(1), poly_neg(poly_mul(X(1000+i),g))))
    return p, sorted(list(range(2*n))+list(range(1000,1000+n)))

# Sum: ∑G_i²
def sumPoly(n):
    p={}
    for i in range(n):
        g=poly_add(X(2*i),X(2*i+1))
        p=poly_add(p,poly_mul(g,g))
    return p, list(range(2*n))

print(f"{'n':>3} {'k':>3} | {'prod_obs':>9} {'prod_tot':>9} | {'sum_obs':>8} {'sum_tot':>8}")
print("-"*55)
for n in range(2,8):
    for k in [1,2,3,4]:
        pp,pv=productPoly(n)
        sp,sv=sumPoly(n)
        po,pt=observableSize(pp,pv,k)
        so,st=observableSize(sp,sv,k)
        print(f"{n:>3} {k:>3} | {po:>9} {pt:>9} | {so:>8} {st:>8}")
    print()
