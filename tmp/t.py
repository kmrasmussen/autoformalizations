import math,random
def run(r,T=300000,eta=0.2,seed=0,th0=None):
    n=len(r); random.seed(seed)
    th=th0[:] if th0 else [random.gauss(0,0.3) for _ in range(n)]
    tv=0.0;gs=0.0;g2=0.0;prev=None
    for t in range(T):
        m=max(th); e=[math.exp(x-m) for x in th]; Z=sum(e); p=[x/Z for x in e]
        vb=sum(p[i]*r[i] for i in range(n)); A=[r[i]-vb for i in range(n)]
        g=[p[i]*A[i] for i in range(n)]
        if prev: tv+=sum(abs(p[i]-prev[i]) for i in range(n))
        prev=p[:]
        gn=math.sqrt(sum(x*x for x in g)); gs+=gn; g2+=gn*gn
        for i in range(n): th[i]+=eta*g[i]
    return round(tv,5),round(gs,5),round(g2,6),[round(x,5) for x in p]
print("tie 110 ",run([1.,1.,0.]))
print("110 skew",run([1.,1.,0.],th0=[-8.,-8.,0.]))
print("10      ",run([1.,0.],th0=[-10.,0.]))
print("100 skew",run([1.,0.,0.],th0=[-12.,0.,0.]))
print("1 .9 0  ",run([1.,0.9,0.],th0=[-12.,0.,0.]))
