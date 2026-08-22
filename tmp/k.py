import numpy as np
rng=np.random.default_rng(91)
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
    m=np.max(pi*A,axis=1); D=Vs-V
    astar=np.array([max([a for a in range(nA) if pistar[s,a]>0],key=lambda a:pi[s,a]) for s in range(nS)])
    c=min(pi[s,astar[s]] for s in range(nS))
    # K1: c*sum dst*D  <=  mism*sum dpi*m  ?
    w[0]=max(w[0], c*np.sum(dst*D)-mism*np.sum(dpi*m))
    # K2: per-state c*D(s) <= m(s)?
    w[1]=max(w[1], np.max(c*D-m))
    # K3: sub <= sum dst*D (trivial since X<=D)
    w[2]=max(w[2], (mu@Vs-mu@V)-np.sum(dst*D))
print("K1 c*sum dst*D <= mism sum dpi m :",w[0])
print("K2 per-state c*D<=m              :",w[1])
print("K3 sub<=sum dst*D                :",w[2])
