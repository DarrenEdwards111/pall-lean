import sys, math, json
sys.path.insert(0, '/workspace/pvsnp/wt-g4/scripts/gap_g4')
import def12_rank as d
def contLang(bits):
    i=0
    while True:
        c = bits[i] if i < len(bits) else 0
        if not c: return 1
        x = bits[i+1] if i+1 < len(bits) else 0
        y = bits[i+2] if i+2 < len(bits) else 0
        if y and not x: return 0
        i += 3
def f_cont(N): return lambda a: contLang([(a>>i)&1 for i in range(N)])
out=[]
for N in range(3, 13):
    m = N//3
    c = d.mle(f_cont(N), N)
    for kappa in range(0, min(m,3)+1):
        for l in range(0, 3):
            for conv in ("drop","reduce"):
                g = d.gamma(c, N, kappa, l, conv)
                g = g[0] if isinstance(g, tuple) else g
                lb = math.comb(m,kappa)*sum(math.comb(m,j) for j in range(l+1))
                ceil = math.comb(N,kappa)*sum(math.comb(N,j) for j in range(l+1))
                rec=dict(N=N,m=m,kappa=kappa,l=l,conv=conv,gamma=g,lower_conj=lb,ceiling=ceil,ok=(g>=lb))
                out.append(rec); print(json.dumps(rec), flush=True)
print("VIOLATIONS", sum(1 for r in out if not r["ok"]))
