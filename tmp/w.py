import numpy as np
rng=np.random.default_rng(3)
def solve(nS,r,P,gam,pi):
    Ppi=np.einsum('sa,sax->sx',pi,P); rpi=np.einsum('sa,sa->s',pi,r)
    V=np.linalg.solve(np.eye(nS)-gam*Ppi,rpi)
    Q=r+gam*np.einsum('sax,x->sa',P,V); return V,Q,Q-V[:,None]
def occ(nS,P,pi,mu,gam):
    Ppi=np.einsum('sa,sax->sx',pi,P)
    return np.linalg.solve((np.eye(nS)-gam*Ppi).T,mu)
def vstar(nS,r,P,gam):
    V=np.zeros(nS)
    for _ in range(5000):
        Q=r+gam*np.einsum('sax,x->sa',P,V); Vn=Q.max(1)
        if np.max(np.abs(Vn-V))<1e-15: V=Vn;break
        V=Vn
    return V, r+gam*np.einsum('sax,x->sa',P,V)

# Candidate C1:  V*_mu - V^pi_mu <= sum_s d^pi_mu(s) * max_a A^pi(s,a)   (times mism?)
# Candidate C2:  c*(V*_mu - V^pi_mu) <= mism * sum_s d^pi_mu(s)*m(s), m(s)=max_a pi_a A_a
w1=-1e9;w2=-1e9;w3=-1e9
for t in range(50000):
    nS=int(rng.integers(2,5)); nA=int(rng.integers(2,5)); gam=float(rng.uniform(0.05,0.95))
    r=rng.integers(-2,3,size=(nS,nA)).astype(float)/2
    P=rng.dirichlet(np.ones(nS)*0.4,size=(nS,nA))
    Vs,Qs=vstar(nS,r,P,gam)
    best=Qs.max(1,keepdims=True); mask=(Qs>=best-1e-11).astype(float)
    pistar=mask/mask.sum(1,keepdims=True)
    mu=rng.dirichlet(np.ones(nS)); th=rng.normal(0,2,size=(nS,nA))
    e=np.exp(th-th.max(1,keepdims=True)); pi=e/e.sum(1,keepdims=True)
    V,Q,A=solve(nS,r,P,gam,pi)
    dpi=occ(nS,P,pi,mu,gam); dst=occ(nS,P,pistar,mu,gam); mism=np.max(dst/mu)
    m=np.max(pi*A,axis=1)
    sub=mu@Vs-mu@V
    astar=np.array([max([a for a in range(nA) if pistar[s,a]>0],key=lambda a:pi[s,a]) for s in range(nS)])
    c=min(pi[s,astar[s]] for s in range(nS))
    w1=max(w1, sub - np.sum(dst*np.max(A,axis=1)))
    w2=max(w2, c*sub - mism*np.sum(dpi*m))
    # C3: c*sub <= sum_s dst(s) * (max_a A) * c  and  c*max_a A(s,a) <= m(s)?  test
    w3=max(w3, np.max(c*np.max(A,axis=1)-m))
print("C1 sub<=sum dst maxA :",w1)
print("C2 goal              :",w2)
print("C3 c*maxA<=m         :",w3)
