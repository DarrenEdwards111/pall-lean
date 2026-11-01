import json,os,subprocess,time,sys
root='/workspace/pvsnp/wt-g3'
deps=json.load(open('/workspace/pvsnp/g3out/deps.json'))
LP=subprocess.check_output(['bash','-lc','cd %s && PATH=$HOME/.elan/bin:$PATH lake env printenv LEAN_PATH'%root]).decode().strip()
env=dict(os.environ,LEAN_PATH=LP,PATH=os.path.expanduser('~/.elan/bin')+':'+os.environ['PATH'])
def ol(m): return os.path.join(root,'.lake/build/lib/lean',m.replace('.','/'))
done=set(); running={}; todo=set(deps)
log=open('/workspace/pvsnp/g3out/sched.log','a')
while todo or running:
    for m,p in list(running.items()):
        if p.poll() is not None:
            del running[m]
            if p.returncode!=0: log.write('FAIL %s\n'%m); log.flush(); sys.exit(1)
            done.add(m); log.write('ok %s %s %d/%d\n'%(time.strftime('%T'),m,len(done),len(deps))); log.flush()
    for m in sorted(todo):
        if len(running)>=2: break
        if all(d in done or d not in deps for d in deps[m]):
            todo.discard(m); os.makedirs(os.path.dirname(ol(m)),exist_ok=True)
            running[m]=subprocess.Popen(['nice','-n','10','lean','-o',ol(m)+'.olean','-i',ol(m)+'.ilean',os.path.join(root,m.replace('.','/')+'.lean')],env=env,stdout=open('/workspace/pvsnp/g3out/mod_%s.log'%m,'w'),stderr=subprocess.STDOUT,cwd=root)
    time.sleep(2)
log.write('ALLDONE\n'); log.flush()
