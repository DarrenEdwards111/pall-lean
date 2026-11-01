#!/bin/bash
# wait for EmitPairT, then recompute missing modules, schedule (2 procs, niced), then build chain + G3 files
while pgrep -f "EmitPairT.lean" >/dev/null; do sleep 30; done
cd /workspace/pvsnp/wt-g3 && python3 - <<'PY'
import os,json
root='/workspace/pvsnp/wt-g3'
mods=open('/workspace/pvsnp/g3out/pl_mods.txt').read().split()
p=lambda m: os.path.join(root,m.replace('.','/')+'.lean'); o=lambda m: os.path.join(root,'.lake/build/lib/lean',m.replace('.','/')+'.olean')
deps={}
def v(m):
    if m in deps: return
    deps[m]=[l.split()[1] for l in open(p(m)) if l.startswith('import ') and l.split()[1].startswith('PallLean')]
    for d in deps[m]: v(d)
for m in mods: v(m)
json.dump({m:deps[m] for m in deps if not os.path.exists(o(m))},open('/workspace/pvsnp/g3out/deps.json','w'))
PY
cd /workspace/pvsnp/g3out && python3 sched.py && ./build.sh > build.log 2>&1
