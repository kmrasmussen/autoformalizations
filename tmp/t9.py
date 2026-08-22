import math,random
# In tie case, is the sign of A_t(a) for a in Z eventually constant?
def run(r,T,eta=0.2,seed=0):
    n=len(r); random.seed(seed); th=[random.gauss(0,2) for _ in range(n)]
    last=[0]*n; flip=[0]*n; lastf=[0]*n
    for t in range(T):
        m=max(th); e=[math.exp(x-m) for x in th]; Z=sum(e); p=[x/Z for x in e]
        vb=sum(p[i]*r[i] for i in range(n)); A=[r[i]-vb for i in range(n)]
        for i in range(n):
            sg=(A[i]>1e-15)-(A[i]<-1e-15)
            if sg!=0:
                if last[i] and sg!=last[i]: flip[i]+=1; lastf[i]=t
                last[i]=sg
        for i in range(n): th[i]+=eta*p[i]*A[i]
    return flip,lastf,[round(x,5) for x in p],[round(x,7) for x in A]
for seed in [1,2,3,7]:
    print(seed,run([1.,1.,0.],300000,seed=seed))
