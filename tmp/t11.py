import math,random
# For a in Z(s) (Abar=0), is A_t(s,a) >= 0 for ALL t (or eventually)? single-state gamma=0
def run(r,T=200000,eta=0.2,seed=0):
    n=len(r); random.seed(seed); th=[random.gauss(0,2) for _ in range(n)]
    neg=[0]*n; lastneg=[-1]*n
    for t in range(T):
        m=max(th); e=[math.exp(x-m) for x in th]; Z=sum(e); p=[x/Z for x in e]
        vb=sum(p[i]*r[i] for i in range(n)); A=[r[i]-vb for i in range(n)]
        for i in range(n):
            if A[i]<-1e-12: neg[i]+=1; lastneg[i]=t
        for i in range(n): th[i]+=eta*p[i]*A[i]
    return neg,lastneg,[round(x,6) for x in A],[round(x,5) for x in p]
for seed in [1,2,5,9]:
    for r in [[1.,1.,0.],[1.,1.,0.5,0.]]:
        print(seed,r,run(r,seed=seed))
