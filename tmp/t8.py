import math,random
def run(r,T,eta=0.2,seed=0):
    n=len(r); random.seed(seed); th=[random.gauss(0,2) for _ in range(n)]
    acc=[0.0]*n; thd=None
    for t in range(T):
        m=max(th); e=[math.exp(x-m) for x in th]; Z=sum(e); p=[x/Z for x in e]
        vb=sum(p[i]*r[i] for i in range(n)); A=[r[i]-vb for i in range(n)]
        for i in range(n): acc[i]+=p[i]*abs(A[i])
        for i in range(n): th[i]+=eta*p[i]*A[i]
    return [round(x,4) for x in acc],[round(x,5) for x in p],round(th[0]-th[1],5)
for T in [10**4,10**5,6*10**5]:
    print(T,"tie110",run([1.,1.,0.],T,seed=1))
