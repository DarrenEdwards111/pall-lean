import json
rows=[]
for q in range(2,13):
    cuts=[m for m in range(1,1<<q) if m&1 and m!=(1<<q)-1]
    affected=sum(not (m&2) for m in cuts)
    assert affected==2**(q-2)
    rows.append({'qubits':q,'unordered_cuts':len(cuts),'cuts_entangled_by_one_CNOT':affected,'sum_log_rank_after':affected})
print(json.dumps(rows,indent=2))
