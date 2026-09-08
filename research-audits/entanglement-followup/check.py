import json
from fractions import Fraction
rows=[]
for n in range(1,9):
    size=2**n
    # CNF: each pair contributes (not x_i or y_i) and (x_i or not y_i).
    def sat(x,y):
        return all(((not ((x>>i)&1)) or ((y>>i)&1)) and (((x>>i)&1) or (not ((y>>i)&1))) for i in range(n))
    count=0
    for x in range(size):
        for y in range(size):
            value=sat(x,y)
            assert value == (x==y)
            count+=value
    assert sat(0,0)
    assert count==size
    # Exact coefficient matrix is I/sqrt(size); its singular values
    # are all 1/sqrt(size), hence rank=size and entropy=log2(size)=n.
    rows.append(dict(n=n,variables=2*n,clauses=2*n,assignments_checked=size*size,
        satisfying_assignments=count,schmidt_rank=size,entropy_bits=n,
        postselection_probability=str(Fraction(count,size*size)),
        known_preparation_H_gates=n,known_preparation_CNOT_gates=n))
print(json.dumps({'method':'exhaustive CNF evaluation; exact identity-matrix spectrum argument','results':rows},indent=2))
