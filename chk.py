import random, math
random.seed(7)
def solveV(S,A,P,r,gam,pi):
    V=[0.0]*S
    for _ in range(20000):
        nV=[sum(pi[s][a]*(r[s][a]+gam*sum(P[s][a][x]*V[x] for x in range(S))) for a in range(A)) for s in range(S)]
        if max(abs(nV[i]-V[i]) for i in range(S))<1e-13: V=nV; break
        V=nV
    return V
def occ(S,A,P,gam,pi,mu):
    # d[s] = sum_t gam^t Pr(s_t=s) starting mu  (no (1-gam) factor -- repo dinf convention TBD)
    d=list(mu); cur=list(mu)
    for _ in range(4000):
        nxt=[0.0]*S
        for s in range(S):
            if cur[s]==0: continue
            for a in range(A):
                w=cur[s]*pi[s][a]
                for x in range(S): nxt[x]+=w*P[s][a][x]
        cur=[gam*v for v in nxt]
        for x in range(S): d[x]+=cur[x]
        if max(cur)<1e-15: break
    return d
def vstar(S,A,P,r,gam):
    V=[0.0]*S
    for _ in range(30000):
        nV=[max(r[s][a]+gam*sum(P[s][a][x]*V[x] for x in range(S)) for a in range(A)) for s in range(S)]
        if max(abs(nV[i]-V[i]) for i in range(S))<1e-13: V=nV; break
        V=nV
    return V
def sm(z):
    m=max(z); e=[math.exp(v-m) for v in z]; t=sum(e); return [v/t for v in e]
worst=0; wrec=None
for trial in range(120):
    S=random.randint(2,3); A=random.randint(2,3); gam=random.uniform(0,0.85)
    P=[[[random.random() for _ in range(S)] for _ in range(A)] for _ in range(S)]
    for s in range(S):
        for a in range(A):
            t=sum(P[s][a]); P[s][a]=[v/t for v in P[s][a]]
    r=[[random.uniform(-1,1) for _ in range(A)] for _ in range(S)]
    mu=[random.random()**3+1e-3 for _ in range(S)]; t=sum(mu); mu=[v/t for v in mu]
    Vs=vstar(S,A,P,r,gam)
    Q=[[r[s][a]+gam*sum(P[s][a][x]*Vs[x] for x in range(S)) for a in range(A)] for s in range(S)]
    astar=[max(range(A),key=lambda a:Q[s][a]) for s in range(S)]
    pistar=[[1.0 if a==astar[s] else 0.0 for a in range(A)] for s in range(S)]
    dstar=occ(S,A,P,gam,pistar,mu)
    m=max(dstar[s]/mu[s] for s in range(S))
    th=[[random.gauss(0,1) for _ in range(A)] for _ in range(S)]
    eta=(1-gam)**3/8
    cmin=1e9
    for t_ in range(0,600):
        pi=[sm(th[s]) for s in range(S)]
        cmin=min(cmin, min(pi[s][astar[s]] for s in range(S)))
        V=solveV(S,A,P,r,gam,pi)
        d=occ(S,A,P,gam,pi,mu)
        if t_>=1:
            lhs=sum(mu[s]*(Vs[s]-V[s]) for s in range(S))
            rhs=16*S/(cmin**2*(1-gam)**6*t_)*m
            if lhs>0 and rhs>0 and lhs/rhs>worst:
                worst=lhs/rhs; wrec=(S,A,round(gam,3),t_,round(m,3),round(cmin,5),lhs,rhs)
        for s in range(S):
            Vp=V
            for a in range(A):
                Qa=r[s][a]+gam*sum(P[s][a][x]*Vp[x] for x in range(S))
                th[s][a]+= eta*d[s]*pi[s][a]*(Qa-Vp[s])
print("worst lhs/rhs:",worst); print(wrec)
