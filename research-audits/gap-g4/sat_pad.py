import sys, itertools
sys.path.insert(0, '/workspace/pvsnp/wt-g4/scripts/gap_g4')
import def12_rank as d
bad=0; tot=0
for n in range(0, 17):
    for t in itertools.product([0,1], repeat=n):
        w=list(t); tot+=1
        a=d.satisfiable(d.decodeFormula(w)); b=d.satisfiable(d.decodeFormula(w+[0]))
        if bool(a)!=bool(b):
            bad+=1
            if bad<5: print("MISMATCH", w)
print("words", tot, "mismatches", bad)
