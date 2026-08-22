import random, math
random.seed(7)
def softmax(z):
    m=max(z); e=[math.exp(x-m) for x in z]; s=sum(e); return [x/s for x in e]
def matvec_solve(Amat,b):
    n=len(b); M=[row[:]+[b[i]] for i,row in enumerate(Amat)]
    for c in range(n):
        p=max(range(c,n),key=lambda r:abs(M[r][c]))
        if abs(M[p][c])<1e-14: return None
        M[c],M[p]=M[p],M[c]
        pv=M[c][c]
        for r in range(n):
            if r!=c:
                f=M[r][c]/pv
                for k in range(c,n+1): M[r][k]-=f*M[c][k]
    return [M[i][n]/M[i][i] for i in range(n)]
def solveV(P,r,g,pi,S,A):
    Ppi=[[sum(pi[s][a]*P[s][a][t] for a in range(A)) for t in range(S)] for s in range(S)]
    rpi=[sum(pi[s][a]*r[s][a] for a in range(A)) for s in range(S)]
    Amat=[[(1.0 if s==t else 0.0)-g*Ppi[s][t] for t in range(S)] for s in range(S)]
    V=matvec_solve(Amat,rpi)
    if V is None: return None,None
    Q=[[r[s][a]+g*sum(P[s][a][t]*V[t] for t in range(S)) for a in range(A)] for s in range(S)]
    return V,Q
def dmu(P,g,pi,mu,S,A):
    Ppi=[[sum(pi[s][a]*P[s][a][t] for a in range(A)) for t in range(S)] for s in range(S)]
    Amat=[[(1.0 if s==t else 0.0)-g*Ppi[t][s] for t in range(S)] for s in range(S)]
    return matvec_solve(Amat,mu)
worst=(1e9,)
for trial in range(30000):
    S=random.randint(2,3); A=random.randint(2,3)
    g=random.uniform(0.0,0.95)
    P=[[[random.random() for _ in range(S)] for _ in range(A)] for _ in range(S)]
    for s in range(S):
        for a in range(A):
            tot=sum(P[s][a]); P[s][a]=[x/tot for x in P[s][a]]
    r=[[random.uniform(-1,1) for _ in range(A)] for _ in range(S)]
    mu=[random.random() for _ in range(S)]; tot=sum(mu); mu=[x/tot for x in mu]
    th=[[random.gauss(0,3) for _ in range(A)] for _ in range(S)]
    eta=(1-g)**2/5
    pi=[softmax(th[s]) for s in range(S)]
    V,Q=solveV(P,r,g,pi,S,A)
    if V is None: continue
    d=dmu(P,g,pi,mu,S,A)
    if d is None: continue
    th2=[[th[s][a]+eta*(d[s]*pi[s][a]*(Q[s][a]-V[s])) for a in range(A)] for s in range(S)]
    pi2=[softmax(th2[s]) for s in range(S)]
    V2,_=solveV(P,r,g,pi2,S,A)
    if V2 is None: continue
    gap=min(V2[s]-V[s] for s in range(S))
    if gap<worst[0]: worst=(gap,S,A,g)
print("min over 30000 trials of  min_s (V'(s)-V(s)),  |r|<=1, eta=(1-g)^2/5:")
print("   ",worst)
