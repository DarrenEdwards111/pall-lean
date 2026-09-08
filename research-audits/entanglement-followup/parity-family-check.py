import itertools,json
out=[]
for name,v,edges in [('K4',4,list(itertools.combinations(range(4),2))),('K33',6,[(i,j) for i in range(3) for j in range(3,6)])]:
 incident=[[e for e,pair in enumerate(edges) if a in pair] for a in range(v)]
 total=0
 for charge in range(1<<v):
  clauses=[]
  for a,ids in enumerate(incident):
   for pattern in range(1<<len(ids)):
    if pattern.bit_count()%2 != (charge>>a)&1:
     clauses.append([(e,1-((pattern>>j)&1)) for j,e in enumerate(ids)])
  solutions=0
  for assignment in range(1<<len(edges)):
   cnf=all(any(((assignment>>e)&1)==value for e,value in c) for c in clauses)
   xor=all(sum((assignment>>e)&1 for e in ids)%2==((charge>>a)&1) for a,ids in enumerate(incident))
   assert cnf==xor
   solutions+=cnf
   total+=1
  assert (solutions>0)==(charge.bit_count()%2==0)
 out.append(dict(graph=name,vertices=v,edges=len(edges),clauses=len(clauses),cases=total,passed=True))
print(json.dumps(out,indent=2))
