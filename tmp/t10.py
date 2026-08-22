import math,random
# 2-state MDP, gamma>0, so ties in Abar need NOT have A_t equal at finite t.
# state s in {0,1}, actions n. P[s][a] -> distribution over s'. r[s][a].
def solveV(P,r,g,pi,nS,nA,iters=400):
    V=[0.0]*nS
    for _ in range(iters):
        V=[sum(pi[s][a]*(r[s][a]+g*sum(P[s][a][sp]*V[sp] for sp in range(nS))) for a in range(nA)) for s in range(nS)]
    return V
def run(P,r,g,nS,nA,T,eta,seed,mu=None):
    random.seed(seed)
    th=[[random.gauss(0,1.5) for _ in range(nA)] for _ in range(nS)]
    mu=mu or [1.0/nS]*nS
    diffhist=[]
    flips=0; lastsgn=0
    prevd=None
    for t in range(T):
        pi=[]
        for s in range(nS):
            m=max(th[s]); e=[math.exp(x-m) for x in th[s]]; Z=sum(e); pi.append([x/Z for x in e])
        V=solveV(P,r,g,pi,nS,nA,120)
        Q=[[r[s][a]+g*sum(P[s][a][sp]*V[sp] for sp in range(nS)) for a in range(nA)] for s in range(nS)]
        A=[[Q[s][a]-V[s] for a in range(nA)] for s in range(nS)]
        # occupancy d (approx): use mu-weighted discounted visitation
        d=[[0.0]*nS for _ in range(nS)]
        dv=[mu[s] for s in range(nS)]
        occ=[0.0]*nS
        cur=mu[:]
        for k in range(200):
            for s in range(nS): occ[s]+=cur[s]*(g**k if g>0 else (1 if k==0 else 0))
            nxt=[0.0]*nS
            for s in range(nS):
                for a in range(nA):
                    for sp in range(nS): nxt[sp]+=cur[s]*pi[s][a]*P[s][a][sp]
            cur=nxt
        for s in range(nS):
            for a in range(nA): th[s][a]+=eta*occ[s]*pi[s][a]*A[s][a]
        if t%(T//8)==0: diffhist.append((t,[round(x,5) for x in pi[0]],[round(x,6) for x in A[0]]))
    return diffhist
nS,nA=2,3
P=[[[1.0,0.0],[1.0,0.0],[0.0,1.0]],[[0.0,1.0],[0.0,1.0],[0.0,1.0]]]
r=[[1.0,1.0,0.0],[0.2,0.2,0.2]]
for seed in [1,2]:
    print("seed",seed)
    for row in run(P,r,0.5,nS,nA,4000,0.2,seed): print("  ",row)
