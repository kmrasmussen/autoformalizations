import numpy as np
rng=np.random.default_rng(123)
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
worst=-1e9; wit=None
for t in range(40000):
    nS=int(rng.integers(2,4)); nA=int(rng.integers(2,4)); gam=float(rng.uniform(0.05,0.95))
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
    c=min(pi[s,astar[s]] for s in range(nS)); sub=mu@Vs-mu@V
    # Q3': c*sub <= sum_s dst(s)*m(s)
    v=c*sub-np.sum(dst*m)
    if v>worst: worst=v; wit=(c,sub,dst,m,mism,dpi,pi,A,pistar,astar,gam)
print("Q3' max violation c*sub - sum dst*m =",worst)
c,sub,dst,m,mism,dpi,pi,A,pistar,astar,gam=wit
print("c",c,"sub",sub,"sum dst*m",np.sum(dst*m))
print("GOAL slack: mism*sum dpi*m - c*sub =",mism*np.sum(dpi*m)-c*sub)
print("mism",mism,"sum dpi*m",np.sum(dpi*m))
