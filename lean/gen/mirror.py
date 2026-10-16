from pathlib import Path as _Path
_CODE = str(_Path(__file__).resolve().parents[2] / 'code')  # the repository's code/ folder
import json, sys, collections
xb=lambda v,i:(v>>i)&1; zb=lambda v,i:(v>>(i+4))&1
def symp(u,v): return sum(xb(u,i)&zb(v,i) ^ 0 for i in range(4))%2 ^ sum(zb(u,i)&xb(v,i) for i in range(4))%2
def symp(u,v): return (sum(xb(u,i)&zb(v,i) for i in range(4))+sum(zb(u,i)&xb(v,i) for i in range(4)))%2
def Q(v): return sum(xb(v,i)&zb(v,i) for i in range(4))%2
P1={(1,0,1,1):1,(1,0,0,1):3,(1,1,1,0):3,(1,1,0,1):1,(0,1,1,0):1,(0,1,1,1):3}
def phase(u,v): return sum(P1.get((xb(u,i),zb(u,i),xb(v,i),zb(v,i)),0) for i in range(4))%4
def neg(a,b): return 1 if phase(a,b)==2 else 0
qp=lambda v: 0<v<256 and Q(v)==0
ctx=[(a,b) for a in range(256) for b in range(256) if a<b<(a^b) and qp(a) and qp(b) and qp(a^b) and symp(a,b)==0]
print(len(ctx), sum(neg(a,b) for a,b in ctx))
# compare with numpy matrices
sys.path.insert(0,_CODE); import w72
enc=lambda p: sum(p[i]<<i for i in range(8))
ref={tuple(sorted(enc(p) for p in l[:3])):l[3] for l in w72.lines}
assert all(ref[(a,b,a^b)]==neg(a,b) for a,b in ctx); print('signs agree with matrices')
d=json.load(open(sys.argv[1])); D=d['doilies']; G=d['grids']
cs=set(a*256+b for a,b in ctx)
cnt=collections.Counter(k for r in D for k in r); print(set(cnt.values()), len(cnt)==len(ctx), all(k in cs for k in cnt))
for r in D:
    for g in G:
        m=0; s=0
        for j in g:
            a,b=divmod(r[j],256); m^=(1<<a)^(1<<b)^(1<<(a^b)); s+=neg(a,b)
        assert m==0 and s%2==1
print('grids ok', collections.Counter(j for g in G for j in g))
u=json.load(open(_CODE + '/witness.json'))
W=sum(1<<enc(p) for p,xv in zip(u['points'],u['assignment']) if xv)
print('witness viol', sum(((W>>a)^(W>>b)^(W>>(a^b)))&1 != neg(a,b) for a,b in ctx), W)
