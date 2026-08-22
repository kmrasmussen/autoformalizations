import math,random
def solveV(P,r,g,pi,nS,nA,it=300):
    V=[0.0]*nS
    for _ in range(it):
        V=[sum(pi[s][a]*(r[s][a]+g*sum(P[s][a][sp]*V[sp] for sp in range(nS))) for a in range(nA)) for s in range(nS)]
    return V
def run(P,r,g,nS,nA,T,eta,seed):
    random.seed(seed); th=[[random.gauss(0,1.5) for _ in range(nA)] for _ in range(nS)]
    mu=[1.0/nS]*nS; negcount=[[0]*nA for _ in range(nS)]
    for t in range(T):
        pi=[]
        for s in range(nS):
            m=max(th[s]); e=[math.exp(x-m) for x in th[s]]; Z=sum(e); pi.append([x/Z for x in e])
        V=solveV(P,r,g,pi,nS,nA,150)
        A=[[r[s][a]+g*sum(P[s][a][sp]*V[sp] for sp in range(nS))-V[s] for a in range(nA)] for s in range(nS)]
        occ=[0.0]*nS; cur=mu[:]
        for k in range(150):
            for s in range(nS): occ[s]+=cur[s]*(g**k)
            nxt=[0.0]*nS
            for s in range(nS):
                for a in range(nA):
                    for sp in range(nS): nxt[sp]+=cur[s]*pi[s][a]*P[s][a][sp]
            cur=nxt
        for s in range(nS):
            for a in range(nA):
                if A[s][a]<-1e-10: negcount[s][a]+=1
                th[s][a]+=eta*occ[s]*pi[s][a]*A[s][a]
    return negcount,[[round(x,6) for x in row] for row in A],[[round(x,4) for x in row] for row in pi]
nS,nA=2,3
random.seed(0)
for trial in range(4):
    P=[[[random.random() for _ in range(nS)] for _ in range(nA)] for _ in range(nS)]
    for s in range(nS):
        for a in range(nA):
            z=sum(P[s][a]); P[s][a]=[x/z for x in P[s][a]]
    r=[[1.0,1.0,0.0],[0.4,0.1,0.7]]
    nc,A,pi=run(P,r,0.6,nS,nA,3000,0.15,trial)
    print(trial,"negcounts",nc,"Abar",A)
