import math,random
# TIE CASE: two actions with Abar=0. Does each pi converge? Track theta DIFFERENCE.
def run(r,T,eta=0.2,seed=0,report=()):
    n=len(r); random.seed(seed); th=[random.gauss(0,2) for _ in range(n)]
    out=[]
    for t in range(T):
        m=max(th); e=[math.exp(x-m) for x in th]; Z=sum(e); p=[x/Z for x in e]
        vb=sum(p[i]*r[i] for i in range(n)); A=[r[i]-vb for i in range(n)]
        if t in report: out.append((t,[round(x,6) for x in p],round(th[0]-th[1],6)))
        for i in range(n): th[i]+=eta*p[i]*A[i]
    return out
rep=set([10**k for k in range(2,7)])
for seed in [1,2,3,4,5]:
    print(seed, run([1.,1.,0.],4*10**6,seed=seed,report=rep))
