import numpy as np
rng=np.random.default_rng(321)
def solve(nS,r,P,gam,pi):
    Ppi=np.einsum('sa,sax->sx',pi,P); rpi=np.einsum('sa,sa->s',pi,r)
    V=np.linalg.solve(np.eye(nS)-gam*Ppi,rpi); Q=r+gam*np.einsum('sax,x->sa',P,V); return V,Q,Q-V[:,None]
def occ(nS,P,pi,mu,gam):
    Ppi=np.einsum('sa,sax->sx',pi,P); return np.linalg.solve((np.eye(nS)-gam*Ppi).T,mu)
def vstar(nS,r,P,gam):
    V=np.zeros(nS)
    for _ in range(5000):
        Q=r+gam*np.einsum('sax,x->sa',P,V); Vn=Q.max(1)
        if np.max(np.abs(Vn-V))<1e-15: V=Vn;break
        V=Vn
    return V, r+gam*np.einsum('sax,x->sa',P,V)
# Candidate S1 (keeps mism live but only via  dst(s) <= mism*mu(s)  and  sub relation):
#   c*sub = c*sum_s dst(s)X(s) <= c*mism*sum_s mu(s)*X+(s)  ... then need c*sum mu X+ <= sum dpi m
# Candidate S2:  c*X(s) <= m(s)/pi_min?  no.
# Candidate S3 (THE PROMISING ONE): use  sub <= (1/(1-gam)) * max_s Delta(s) ... no.
# Candidate S4: since dst <= mism*mu <= mism*dpi, we get c*sub <= c*mism*sum_s dpi(s)*X+(s).
#   Then SUFFICES:  c*sum_s dpi(s)*X+(s) <= sum_s dpi(s)*m(s).   TEST THIS.
w=[-1e9]*3
for t in range(60000):
    nS=int(rng.integers(2,5)); nA=int(rng.integers(2,6)); gam=float(rng.uniform(0.05,0.97))
    r=rng.integers(-2,3,size=(nS,nA)).astype(float)/2
    P=rng.dirichlet(np.ones(nS)*0.4,size=(nS,nA))
    Vs,Qs=vstar(nS,r,P,gam)
    bq=Qs.max(1,keepdims=True); mask=(Qs>=bq-1e-11).astype(float)
    pistar=mask/mask.sum(1,keepdims=True)
    mu=rng.dirichlet(np.ones(nS)); th=rng.normal(0,2.5,size=(nS,nA))
    e=np.exp(th-th.max(1,keepdims=True)); pi=e/e.sum(1,keepdims=True)
    V,Q,A=solve(nS,r,P,gam,pi); dpi=occ(nS,P,pi,mu,gam); dst=occ(nS,P,pistar,mu,gam); mism=np.max(dst/mu)
    m=np.max(pi*A,axis=1)
    astar=np.array([max([a for a in range(nA) if pistar[s,a]>0],key=lambda a:pi[s,a]) for s in range(nS)])
    c=min(pi[s,astar[s]] for s in range(nS))
    X=np.array([pistar[s]@A[s] for s in range(nS)]); Xp=np.maximum(X,0)
    # S4: c*sum dpi*X+ <= sum dpi*m
    w[0]=max(w[0], c*np.sum(dpi*Xp)-np.sum(dpi*m))
    # S5: c*sum mu*X+ <= sum dpi*m
    w[1]=max(w[1], c*np.sum(mu*Xp)-np.sum(dpi*m))
    # S6 per-state: c*X+(s) <= m(s)   (this is W1 with X+; expect false)
    w[2]=max(w[2], np.max(c*Xp-m))
print("S4 c*sum dpi X+ <= sum dpi m :",w[0])
print("S5 c*sum mu  X+ <= sum dpi m :",w[1])
print("S6 per-state c*X+ <= m       :",w[2])
