from pathlib import Path as _Path
_CODE = str(_Path(__file__).resolve().parents[2] / 'code')  # the repository's code/ folder
import sys, pickle, itertools, collections
sys.path.insert(0, _CODE)
import doilies as D
doil = []
for gens in D.rref_subspaces(8, 5):
    V = D.span(gens)
    sing = [v for v in V if any(v) and v in D.Q]
    if len(sing) != 15: continue
    ls = [D.lineset[frozenset(t)] for t in itertools.combinations(sing, 3) if frozenset(t) in D.lineset]
    if len(ls) != 15: continue
    deg = collections.Counter(p for l in ls for p in l[:3])
    if any(deg[p] != 3 for p in sing): continue
    doil.append((sing, ls))
pickle.dump((D.Qlines, doil), open('doil.pkl','wb'))
print(len(doil))
