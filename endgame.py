# Does I_+ nonempty actually persist numerically?  Run softmax GA to near-convergence
# and check whether any action ends with pi->0 but A>0.
import random, math
random.seed(11)
def softmax(z):
    m=max(z); e=[math.exp(x-m) for x in z]; s=sum(e); return [x/s for x in e]
def gauss(Amat,b):
    n=len(b); M=[r[:]+[b[i]] for i,r in enumerate(Amat)]
    for c in range(n):
        p=max(range(c,n),key=lambda r:abs(M[r][c]))
        if abs(M[p][c])<1e-15: return None
        M[c],M[p]=M[p],M[c]; pv=M[c][c]
        for r in range(n):
            if r!=c:
                f=M[r][c]/pv
                for k in range(c,n+1): M[r][k]-=f*M[c][k]
    return [M[i][n]/M[i][i] for i in range(n)]
def VQ(P,r,g,pi,S,A):
    Pp=[[sum(pi[s][a]*P[s][a][t] for a in range(A)) for t in range(S)] for s in range(S)]
    rp=[sum(pi[s][a]*r[s][a] for a in range(A)) for s in range(S)]
    V=gauss([[(1.0 if s==t else 0)-g*Pp[s][t] for t in range(S)] for s in range(S)],rp)
    Q=[[r[s][a]+g*sum(P[s][a][t]*V[t] for t in range(S)) for a in range(A)] for s in range(S)]
    return V,Q
def docc(P,g,pi,mu,S,A):
    Pp=[[sum(pi[s][a]*P[s][a][t] for a in range(A)) for t in range(S)] for s in range(S)]
    return gauss([[(1.0 if s==t else 0)-g*Pp[t][s] for t in range(S)] for s in range(S)],mu)
bad=0
for trial in range(12):
    S,A=3,3; g=0.7
    P=[[[random.random() for _ in range(S)] for _ in range(A)] for _ in range(S)]
    for s in range(S):
        for a in range(A):
            tt=sum(P[s][a]); P[s][a]=[x/tt for x in P[s][a]]
    r=[[random.uniform(-1,1) for _ in range(A)] for _ in range(S)]
    mu=[1.0/S]*S
    th=[[random.gauss(0,1) for _ in range(A)] for _ in range(S)]
    eta=(1-g)**2/5
    for it in range(40000):
        pi=[softmax(th[s]) for s in range(S)]
        V,Q=VQ(P,r,g,pi,S,A); d=docc(P,g,pi,mu,S,A)
        for s in range(S):
            for a in range(A):
                th[s][a]+=eta*d[s]*pi[s][a]*(Q[s][a]-V[s])
    pi=[softmax(th[s]) for s in range(S)]
    V,Q=VQ(P,r,g,pi,S,A)
    for s in range(S):
        for a in range(A):
            if pi[s][a]<1e-6 and Q[s][a]-V[s]>1e-6:
                bad+=1
                print("VIOLATION trial",trial,"s,a",s,a,"pi",pi[s][a],"A",Q[s][a]-V[s])
print("done; violations:",bad)
