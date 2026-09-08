import itertools,json
cases=0
# Every ordered pair of NAND gates: first reads input wires 0,1;
# second reads inputs or first gate output. Fresh ancilla for each gate.
for a,b in itertools.product(range(2),repeat=2):
 for c,d in itertools.product(range(3),repeat=2):
  gates=[(a,b,2),(c,d,3)]
  for x,y,z in itertools.product(range(2),repeat=3):
   state=[x,y,0,0,z]
   def step(a,b,t): state[t]^=1^(state[a]&state[b])
   for gate in gates: step(*gate)
   answer=state[3]
   state[4]^=answer
   for gate in reversed(gates): step(*gate)
   assert state==[x,y,0,0,z^answer]
   cases+=1
print(json.dumps({'cases':cases,'passed':True,'construction':'compute, XOR copy, uncompute; each NAND-target XOR is self-inverse','scope':'finite sanity check, not a SAT runtime lower bound'},indent=2))
