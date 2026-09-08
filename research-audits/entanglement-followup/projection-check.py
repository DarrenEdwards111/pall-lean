import itertools,json
out=[]
for n in range(2,8):
 clauses=[]
 # x indices 0..n-1, prefix parity p indices n..2n-1
 # p0=x0; pi=p(i-1) XOR xi; last prefix parity must be true.
 clauses += [[(n,False),(0,True)],[(n,True),(0,False)]]
 for i in range(1,n):
  ids=[n+i-1,i,n+i]
  for bits in itertools.product((False,True),repeat=3):
   if (bits[0]^bits[1])!=bits[2]: clauses.append([(j,not b) for j,b in zip(ids,bits)])
 clauses.append([(2*n-1,True)])
 def sat(x,p):
  a=list(x)+list(p)
  return all(any(a[j]==b for j,b in c) for c in clauses)
 for x in itertools.product((False,True),repeat=n):
  assert any(sat(x,p) for p in itertools.product((False,True),repeat=n))==(sum(x)%2==1)
 # Count all non-tautological implicate clauses; omission/positive/negative per var.
 implicates=[]
 odds=[x for x in itertools.product((False,True),repeat=n) if sum(x)%2]
 for signs in itertools.product((0,1,-1),repeat=n):
  if all(any(s and x[i]==(s==1) for i,s in enumerate(signs)) for x in odds):
   assert all(signs)
   implicates.append(signs)
 assert len(implicates)==2**(n-1)
 out.append(dict(n=n,extension_clauses=len(clauses),boundary_implicates=len(implicates),passed=True))
print(json.dumps(out,indent=2))
