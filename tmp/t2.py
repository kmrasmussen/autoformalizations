import math
def run(r,T,eta=0.2,th0=None):
    n=len(r); th=th0[:]
    tv=0.0;gs=0.0;prev=None
    for t in range(T):
        m=max(th); e=[math.exp(x-m) for x in th]; Z=sum(e); p=[x/Z for x in e]
        vb=sum(p[i]*r[i] for i in range(n)); A=[r[i]-vb for i in range(n)]
        g=[p[i]*A[i] for i in range(n)]
        if prev: tv+=sum(abs(p[i]-prev[i]) for i in range(n))
        prev=p[:]
        gs+=math.sqrt(sum(x*x for x in g))
        for i in range(n): th[i]+=eta*g[i]
    return round(tv,6),round(gs,4)
for T in [10**4,10**5,10**6,4*10**6]:
    print(T, "10:",run([1.,0.],T,th0=[0.,0.]))
