import math,random
# Does the ADVANTAGE sign stabilize (pibar-free question)? and does logit ORDER stabilize?
def run(r,T=400000,eta=0.2,seed=0):
    n=len(r); random.seed(seed); th=[random.gauss(0,3) for _ in range(n)]
    lastsgn=[0]*n; advflip=[0]*n; lastaf=[0]*n
    ordflip=0; lastord=None; lastordt=0
    for t in range(T):
        m=max(th); e=[math.exp(x-m) for x in th]; Z=sum(e); p=[x/Z for x in e]
        vb=sum(p[i]*r[i] for i in range(n)); A=[r[i]-vb for i in range(n)]
        for i in range(n):
            s=(A[i]>1e-14)-(A[i]<-1e-14)
            if s!=0:
                if lastsgn[i]!=0 and s!=lastsgn[i]: advflip[i]+=1; lastaf[i]=t
                lastsgn[i]=s
        o=tuple(sorted(range(n),key=lambda i:th[i]))
        if lastord is not None and o!=lastord: ordflip+=1; lastordt=t
        lastord=o
        for i in range(n): th[i]+=eta*p[i]*A[i]
    return advflip,lastaf,ordflip,lastordt
for s in [3,25,26,30,37]:
    random.seed(s); n=random.choice([3,4,5]); r=[random.choice([0,0.3,0.5,1.0]) for _ in range(n)]
    print(s,r,run(r,seed=s+100))
