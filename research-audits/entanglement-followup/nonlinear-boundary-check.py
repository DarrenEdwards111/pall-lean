import itertools,json
n=3
pool=[frozenset((s*i,t*j)) for i,j in itertools.combinations(range(1,n+1),2) for s,t in itertools.product((-1,1),repeat=2)]
def evaluate(cs,a): return all(any(a[abs(l)]==(l>0) for l in c) for c in cs)
def eliminate(cs,v):
 pos=[c-{v} for c in cs if v in c]; neg=[c-{-v} for c in cs if -v in c]
 out={c for c in cs if v not in c and -v not in c}
 for p in pos:
  for q in neg:
   r=p|q
   if not any(-l in r for l in r):out.add(frozenset(r))
 assert all(len(c)<=2 for c in out)
 return out
checks=0
for mask in range(1<<len(pool)):
 cs={c for i,c in enumerate(pool) if mask>>i&1}
 for v in range(1,n+1):
  out=eliminate(cs,v);others=[i for i in range(1,n+1) if i!=v]
  for bits in itertools.product((False,True),repeat=2):
   a=dict(zip(others,bits))
   assert evaluate(out,a)==any(evaluate(cs,a|{v:b}) for b in (False,True))
   checks+=1
 cur=cs
 for v in range(1,n+1):cur=eliminate(cur,v)
 assert (frozenset() not in cur)==any(evaluate(cs,dict(zip(range(1,n+1),bits))) for bits in itertools.product((False,True),repeat=n))
print(json.dumps({'formulas':1<<len(pool),'pointwise_elimination_checks':checks,'full_decision_checks':1<<len(pool),'passed':True},indent=2))
