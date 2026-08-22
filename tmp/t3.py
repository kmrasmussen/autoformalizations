import math
# Is sum_t ||pi_{t+1}-pi_t||_1 always finite? test many random multi-state-like single-state cases
import random
def run(r,T,eta=0.2,th0=None,seed=0):
    n=len(r); random.seed(seed)
    th=th0[:] if th0 else [random.gauss(0,3) for _ in range(n)]
    tv=0.0;prev=None
    for t in range(T):
        m=max(th); e=[math.exp(x-m) for x in th]; Z=sum(e); p=[x/Z for x in e]
        vb=sum(p[i]*r[i] for i in range(n)); A=[r[i]-vb for i in range(n)]
        if prev: tv+=sum(abs(p[i]-prev[i]) for i in range(n))
        prev=p[:]
        for i in range(n): th[i]+=eta*p[i]*A[i]
    return tv
worst=0
for s in range(40):
    random.seed(s)
    n=random.choice([3,4,5])
    r=[random.choice([0,0.3,0.5,1.0]) for _ in range(n)]
    v=run(r,200000,seed=s+100)
    worst=max(worst,v)
    if v>2.2: print("big",s,r,round(v,4))
print("worst TV",round(worst,4))
