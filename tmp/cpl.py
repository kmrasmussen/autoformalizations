import numpy as np
rng=np.random.default_rng(777)
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
# Test intermediates that DON'T route mism through dst<=mism*mu.
# I1:  c*sum dst X+  <=  sum dst m * K ?  measure needed K = c*sum dst X+ / sum dst m
# I2:  is  c*sum_s dst(s) X+(s)  <=  (1/(1-gam)) * sum_s dpi(s) m(s) ?  (mism >= 1 always)
# I3:  mism >= 1 ?  and  mism >= max_s dst/mu
w=[-1e9]*4; kmax=0
for t in range(120000):
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
    L=c*np.sum(dst*Xp)
    w[0]=max(w[0], L-np.sum(dst*m))              # I1 (needs mism)
    w[1]=max(w[1], L-(1/(1-gam))*np.sum(dpi*m))  # I2
    w[2]=max(w[2], 1-mism)                        # I3: is mism>=1
    if np.sum(dst*m)>1e-12: kmax=max(kmax,L/np.sum(dst*m))
print("I1 c*sum dst X+ <= sum dst m       :",w[0])
print("I2 c*sum dst X+ <= sum dpi m/(1-g) :",w[1])
print("I3 1-mism (<=0 means mism>=1)      :",w[2])
print("needed factor K over sum dst*m     :",kmax)
