import math,random
def run(r,T=500000,eta=0.2,seed=0):
    n=len(r); random.seed(seed); th=[random.gauss(0,3) for _ in range(n)]
    for t in range(T):
        m=max(th); e=[math.exp(x-m) for x in th]; Z=sum(e); p=[x/Z for x in e]
        vb=sum(p[i]*r[i] for i in range(n)); A=[r[i]-vb for i in range(n)]
        for i in range(n): th[i]+=eta*p[i]*A[i]
    return p,A
for s in [3,25,26,30,37,7,11]:
    random.seed(s); n=random.choice([3,4,5]); r=[random.choice([0,0.3,0.5,1.0]) for _ in range(n)]
    p,A=run(r,seed=s+100)
    zeroA=[i for i in range(len(A)) if abs(A[i])<1e-6]
    print(s,r,"p",[round(x,4) for x in p],"Abar",[round(x,5) for x in A],"#Abar=0:",len(zeroA))
