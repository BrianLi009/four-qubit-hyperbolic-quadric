import pickle, itertools, collections, sys, numpy as np, time
from scipy.optimize import milp, LinearConstraint, Bounds
Qlines, doil = pickle.load(open('doil.pkl','rb'))
def enc(p): return sum(p[i]<<i for i in range(8))
lines=[frozenset(enc(p) for p in l[:3]) for l in Qlines]
lid={l:i for i,l in enumerate(lines)}
dl=[frozenset(lid[frozenset(enc(p) for p in l[:3])] for l in ls) for _,ls in doil]
did={d:i for i,d in enumerate(dl)}
def act(perm,h,v):
    x=[(v>>i)&1 for i in range(4)]; z=[(v>>(4+i))&1 for i in range(4)]
    for i in range(4):
        if (h>>i)&1: x[i],z[i]=z[i],x[i]
    x2=[x[perm[i]] for i in range(4)]; z2=[z[perm[i]] for i in range(4)]
    return sum(x2[i]<<i for i in range(4))+sum(z2[i]<<(4+i) for i in range(4))
mode=sys.argv[1]
if mode=='had': G=[((0,1,2,3),h) for h in range(16)]
elif mode=='perm': G=[(p,0) for p in itertools.permutations(range(4))]
elif mode=='triv': G=[((0,1,2,3),0)]
elif mode=='cyc': G=[((0,1,2,3),0),((1,2,3,0),0),((2,3,0,1),0),((3,0,1,2),0)]
elif mode=='cychad': G=[(p,h) for p in [(0,1,2,3),(1,2,3,0),(2,3,0,1),(3,0,1,2)] for h in (0,15)]
lact=[[lid[frozenset(act(p,h,v) for v in l)] for l in lines] for p,h in G]
lorb=[-1]*len(lines); lo=[]
for i in range(len(lines)):
    if lorb[i]<0:
        o={la[i] for la in lact}
        for j in o: lorb[j]=len(lo)
        lo.append(sorted(o))
dorb=[-1]*len(dl); do=[]
for i in range(len(dl)):
    if dorb[i]<0:
        o={did[frozenset(la[l] for l in dl[i])] for la in lact}
        for j in o: dorb[j]=len(do)
        do.append(sorted(o))
print(len(lo),len(do),flush=True)
A=np.array([[sum(1 for d in o if lo[r][0] in dl[d]) for o in do] for r in range(len(lo))])
n=A.shape[1]
for c in [int(sys.argv[2])]:
    t=time.time()
    res=milp(c=np.zeros(n),constraints=LinearConstraint(A,c,c),integrality=np.ones(n),bounds=Bounds(0,1),options={'time_limit':3000})
    print(c,res.status,time.time()-t,flush=True)
    if res.status==0:
        y=np.round(res.x).astype(int); sel=[d for k in range(n) if y[k] for d in do[k]]
        print(len(sel)); pickle.dump(sel,open('sel_%s.pkl'%mode,'wb')); break
