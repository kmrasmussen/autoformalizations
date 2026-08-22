import numpy as np
rng=np.random.default_rng(4242)
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
# The KEY: is  c * X+(s) <= m(s) * (dpi(s)/mu(s)) ??  i.e. per-state with the LOCAL ratio.
# Because sum_s dst(s)*[stuff] and dst(s)<=mism*mu(s), we'd get
#   c*sum dst X+ <= mism*sum mu*X+ ... no.
# BETTER: sum_s dst(s)*c*X+(s) <= sum_s dst(s)*m(s)*(dpi(s)/mu(s))?? then
#   <= mism*sum_s mu(s)*m(s)*dpi(s)/mu(s) = mism*sum dpi*m.  EXACTLY THE GOAL!
# So test T:  c*X+(s) <= m(s)*dpi(s)/mu(s)   per state.
w=[-1e9]*3
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
    V,Q,A=solve(nS,r,P,gam,pi); dpi=occ(nS,P,pi,mu,gam); dst=occ(nS,P,pistar,mu,gam); mism=np.max(dst/mu)
    m=np.max(pi*A,axis=1)
    astar=np.array([max([a for a in range(nA) if pistar[s,a]>1e-14],key=lambda a:pi[s,a]) for s in range(nS)])
    c=min(pi[s,astar[s]] for s in range(nS))
    X=np.array([pistar[s]@A[s] for s in range(nS)]); Xp=np.maximum(X,0)
    w[0]=max(w[0], np.max(c*Xp-m*dpi/mu))                       # T per-state
    w[1]=max(w[1], c*np.sum(dst*Xp)-np.sum(dst*m*dpi/mu))       # T summed vs dst-weighted
    w[2]=max(w[2], c*np.sum(dst*Xp)-mism*np.sum(dpi*m))         # goal (control)
print("T  per-state c*X+ <= m*dpi/mu     :",w[0])
print("T' c*sum dst X+ <= sum dst m dpi/mu:",w[1])
print("goal control                       :",w[2])
