import math,random
# Do policy coords become eventually monotone? Count sign changes of p_b(t+1)-p_b(t) after t>T.
def run(r,T=400000,eta=0.2,seed=0,warm=1000):
    n=len(r); random.seed(seed); th=[random.gauss(0,3) for _ in range(n)]
    prev=None; last=[0]*n; flips=[0]*n; lastflip=[0]*n
    for t in range(T):
        m=max(th); e=[math.exp(x-m) for x in th]; Z=sum(e); p=[x/Z for x in e]
        vb=sum(p[i]*r[i] for i in range(n)); A=[r[i]-vb for i in range(n)]
        if prev:
            for i in range(n):
                d=p[i]-prev[i]
                s=(d>1e-15)-(d<-1e-15)
                if s!=0:
                    if last[i]!=0 and s!=last[i]: flips[i]+=1; lastflip[i]=t
                    last[i]=s
        prev=p[:]
        for i in range(n): th[i]+=eta*p[i]*A[i]
    return flips,lastflip
for s in [3,25,26,30,37]:
    random.seed(s); n=random.choice([3,4,5]); r=[random.choice([0,0.3,0.5,1.0]) for _ in range(n)]
    f,lf=run(r,seed=s+100)
    print(s,r,"flips",f,"lastflip",lf)
