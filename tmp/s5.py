import numpy as np
rng=np.random.default_rng(999)
def solve(nS,r,P,gam,pi):
    Ppi=np.einsum('sa,sax->sx',pi,P); rpi=np.einsum('sa,sa->s',pi,r)
    V=np.linalg.solve(np.eye(nS)-gam*Ppi,rpi); Q=r+gam*np.einsum('sax,x->sa',P,V); return V,Q,Q-V[:,None]
def occ(nS,P,pi,mu,gam):
    Ppi=np.einsum('sa,sax->sx',pi,P); return np.linalg.solve((np.eye(nS)-gam*Ppi).T,mu)
def vstar(nS,r,P,gam):
    V=np.zeros(nS)
    for _ in range(8000):
        Q=r+gam*np.einsum('sax,x->sa',P,V); Vn=Q.max(1)
        if np.max(np.abs(Vn-V))<1e-15: V=Vn;break
        V=Vn
    return V, r+gam*np.einsum('sax,x->sa',P,V)
# S5 hard test + subvariants to find the PROOF
w=[-1e9]*5
for t in range(150000):
    nS=int(rng.integers(2,6)); nA=int(rng.integers(2,7)); gam=float(rng.uniform(0.01,0.99))
    r=rng.integers(-2,3,size=(nS,nA)).astype(float)/2
    P=rng.dirichlet(np.ones(nS)*0.3,size=(nS,nA))
    Vs,Qs=vstar(nS,r,P,gam)
    bq=Qs.max(1,keepdims=True); mask=(Qs>=bq-1e-11).astype(float)
    wts=rng.dirichlet(np.ones(nA))*mask
    if wts.sum(1).min()<=0: continue
    pistar=wts/wts.sum(1,keepdims=True)
    mu=rng.dirichlet(np.ones(nS)*0.5); th=rng.normal(0,3,size=(nS,nA))
    e=np.exp(th-th.max(1,keepdims=True)); pi=e/e.sum(1,keepdims=True)
    V,Q,A=solve(nS,r,P,gam,pi); dpi=occ(nS,P,pi,mu,gam)
    m=np.max(pi*A,axis=1)
    astar=np.array([max([a for a in range(nA) if pistar[s,a]>1e-14],key=lambda a:pi[s,a]) for s in range(nS)])
    c=min(pi[s,astar[s]] for s in range(nS))
    X=np.array([pistar[s]@A[s] for s in range(nS)]); Xp=np.maximum(X,0)
    w[0]=max(w[0], c*np.sum(mu*Xp)-np.sum(dpi*m))
    # S5a: even stronger, per-state with mu<=dpi:  c*mu(s)*X+(s) <= dpi(s)*m(s)  <=  needs c*X+ <= m. false
    w[1]=max(w[1], np.max(c*mu*Xp-dpi*m))
    # S5b: c*sum mu X+ <= sum mu m ?  (drop dpi>=mu)
    w[2]=max(w[2], c*np.sum(mu*Xp)-np.sum(mu*m))
    # S5c: c*X+(s) <= m(s)*(1/(1-gam))?
    w[3]=max(w[3], np.max(c*Xp-m/(1-gam)))
    # S5d: c*sum mu X+ <= sum dpi m, but using dpi >= mu only -> equivalent to S5b
    w[4]=max(w[4], c*np.sum(mu*Xp)-np.sum(dpi*m))
print("S5  c*sum mu X+ <= sum dpi m :",w[0])
print("S5a per-state c*mu X+<=dpi m :",w[1])
print("S5b c*sum mu X+ <= sum mu m  :",w[2])
print("S5c per-state c*X+<=m/(1-g)  :",w[3])
