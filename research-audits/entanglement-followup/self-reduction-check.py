import json
results=[]
for n in range(5):
 count=0
 for truth in range(1<<(1<<n)):
  def exists(prefix,length):
   return any((truth>>x)&1 for x in range(1<<n) if x>>(n-length)==prefix)
  calls=1
  if not exists(0,0):
   assert truth==0
  else:
   prefix=0
   for length in range(1,n+1):
    calls+=1
    prefix=2*prefix if exists(2*prefix,length) else 2*prefix+1
    assert exists(prefix,length)
   assert (truth>>prefix)&1
  assert calls<=n+1
  count+=1
 results.append(dict(variables=n,truth_tables=count,max_oracle_calls=n+1))
print(json.dumps({'results':results,'scope':'exhaustive abstract predicate checks; oracle evaluation cost not counted as constant runtime'},indent=2))
