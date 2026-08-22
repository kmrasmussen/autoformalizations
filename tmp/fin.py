import numpy as np
rng=np.random.default_rng(31337)
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
# The goal's real content, isolated.  Define per state:
#   X+(s) = max(0, sum_a pistar(a|s) A(s,a)),  m(s)=max_a pi(a|s)A(s,a) >= 0
# TRUE:  c*sum_s dst(s)*X+(s)  <=  mism*sum_s dpi(s)*m(s)
# Test the "one-state" mechanism: mism = dst(s0)/mu(s0) for some s0.
# Then mism*sum dpi m >= (dst(s0)/mu(s0))*dpi(s0)*m(s0) >= (dst(s0)/mu(s0))*mu(s0)*m(s0)=dst(s0)*m(s0).
# Candidate U: c*sum_s dst(s) X+(s) <= max_s [dst(s)/mu(s)] * sum_s dpi(s) m(s)
#   equivalently: c*sum_s dst(s)X+(s) / (sum dpi m) <= mism.
# Measure: LHSratio = c*sum dst X+ / sum dpi m ; compare to mism. Where is it tight?
best=0;wit=None
for t in range(200000):
    nS=int(rng.integers(2,5)); nA=int(rng.integers(2,6)); gam=float(rng.uniform(0.01,0.99))
    r=rng.integers(-2,3,size=(nS,nA)).astype(float)/2
    P=rng.dirichlet(np.ones(nS)*0.3,size=(nS,nA))
    Vs,Qs=vstar(nS,r,P,gam)
    bq=Qs.max(1,keepdims=True); mask=(Qs>=bq-1e-11).astype(float)
    wts=rng.dirichlet(np.ones(nA))*mask
    if wts.sum(1).min()<=0: continue
    pistar=wts/wts.sum(1,keepdims=True)
    mu=rng.dirichlet(np.ones(nS)*0.5); th=rng.normal(0,3,size=(nS,nA))
    e=np.exp(th-th.max(1,keepdims=True)); pi=e/e.sum(1,keepdims=True)
    V,Q,A=solve(nS,r,P,gam,pi); dpi=occ(nS,P,pi,mu,gam); dst=occ(nS,P,pistar,mu,gam)
    ratio=dst/mu; mism=np.max(ratio)
    m=np.max(pi*A,axis=1)
    astar=np.array([max([a for a in range(nA) if pistar[s,a]>1e-14],key=lambda a:pi[s,a]) for s in range(nS)])
    c=min(pi[s,astar[s]] for s in range(nS))
    X=np.array([pistar[s]@A[s] for s in range(nS)]); Xp=np.maximum(X,0)
    den=np.sum(dpi*m)
    if den>1e-12:
        rt=c*np.sum(dst*Xp)/(mism*den)
        if rt>best:
            best=rt; wit=(nS,nA,gam,c,mism,ratio.copy(),dst.copy(),dpi.copy(),mu.copy(),m.copy(),Xp.copy())
print("max ratio LHS/RHS =",best)
nS,nA,gam,c,mism,ratio,dst,dpi,mu,m,Xp=wit
print("nS",nS,"gam",gam,"c",c,"mism",mism)
print("dst/mu ratio",ratio); print("mu",mu); print("dst",dst); print("dpi",dpi)
print("m",m); print("X+",Xp)
print("argmax ratio state:",np.argmax(ratio)," argmax m state:",np.argmax(m)," argmax X+ state:",np.argmax(Xp))
