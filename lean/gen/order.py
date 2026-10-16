import pickle, itertools, json, sys
Qlines, doil = pickle.load(open('doil.pkl','rb'))
sel = pickle.load(open(sys.argv[1],'rb'))
def enc(p): return sum(p[i]<<i for i in range(4)) + sum(p[4+i]<<(4+i) for i in range(4))
def lines_of(d): return [frozenset(enc(p) for p in l[:3]) for l in doil[d][1]]
def neg_of(d): return {frozenset(enc(p) for p in l[:3]): l[3] for l in doil[d][1]}
can = lines_of(sel[0])
cpts = sorted(set().union(*can))
def grids(S):
    disj=[t for t in itertools.combinations(range(15),3) if all(not(S[a]&S[b]) for a,b in itertools.combinations(t,2))]
    out=set()
    for A in disj:
        for B in disj:
            if set(A)&set(B): continue
            if all(len(S[a]&S[b])==1 for a in A for b in B): out.add(tuple(sorted(A+B)))
    return sorted(out)
G = grids(can)
assert len(G)==10
coll = lambda L: {(p,q) for l in L for p in l for q in l if p!=q}
def iso(L):
    pts = sorted(set().union(*L)); cl = coll(L); cc = coll(can)
    m = {}
    def bt(i):
        if i == 15: return True
        p = cpts[i]
        for q in pts:
            if q in m.values(): continue
            if all(((p,p2) in cc) == ((q,m[p2]) in cl) for p2 in m):
                m[p] = q
                if bt(i+1): return True
                del m[p]
        return False
    assert bt(0)
    return m
out = []
for d in sel:
    L = lines_of(d); m = iso(L); Ls = set(L)
    row = []
    for l in can:
        img = frozenset(m[p] for p in l); assert img in Ls
        a,b,c = sorted(img); assert a^b==c
        row.append(a*256+b)
    out.append(row)
cg = [[j for j in g] for g in G]
json.dump({'doilies': out, 'grids': cg}, open('order.json','w'))
print(len(out), cg)
