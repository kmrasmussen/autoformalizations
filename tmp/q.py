import numpy as np
rng=np.random.default_rng(41)
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
# Q1: c*sub <= sum_s dpi(s)*m(s)   (WITHOUT mism!)  -- is mism actually needed?
# Q2: c*sub <= mism*sum_s mu(s)*m(s)?
# Q3: sub <= (1/(1-gam))*max_s ... 
w=[-1e9]*5
for t in range(80000):
    nS=int(rng.integers(2,5)); nA=int(rng.integers(2,5)); gam=float(rng.uniform(0.05,0.95))
    r=rng.integers(-2,3,size=(nS,nA)).astype(float)/2
    P=rng.dirichlet(np.ones(nS)*0.4,size=(nS,nA))
    Vs,Qs=vstar(nS,r,P,gam)
    best=Qs.max(1,keepdims=True); mask=(Qs>=best-1e-11).astype(float)
    pistar=mask/mask.sum(1,keepdims=True)
    mu=rng.dirichlet(np.ones(nS)); th=rng.normal(0,2.5,size=(nS,nA))
    e=np.exp(th-th.max(1,keepdims=True)); pi=e/e.sum(1,keepdims=True)
    V,Q,A=solve(nS,r,P,gam,pi); dpi=occ(nS,P,pi,mu,gam); dst=occ(nS,P,pistar,mu,gam); mism=np.max(dst/mu)
    m=np.max(pi*A,axis=1)
    astar=np.array([max([a for a in range(nA) if pistar[s,a]>0],key=lambda a:pi[s,a]) for s in range(nS)])
    c=min(pi[s,astar[s]] for s in range(nS)); sub=mu@Vs-mu@V
    w[0]=max(w[0], c*sub-np.sum(dpi*m))
    w[1]=max(w[1], c*sub-mism*np.sum(mu*m))
    # Q3: c*sum_s dst(s)*X(s) <= sum_s dst(s)*m(s)  where X=sum_a ps_a A
    X=np.array([pistar[s]@A[s] for s in range(nS)])
    w[2]=max(w[2], c*np.sum(dst*X)-np.sum(dst*m))
    # Q4: c*sum dst X <= mism * sum dpi m (the real chain after d^pistar<=mism*mu<=mism*dpi)
    w[3]=max(w[3], c*np.sum(dst*X)-mism*np.sum(dpi*m))
    # Q5: c*X(s) <= m(s) + slack; measure sum_s dst(s)*(c*X(s)-m(s)) 
    w[4]=max(w[4], np.sum(dst*(c*X-m)))
print("Q1 c*sub <= sum dpi*m        :",w[0])
print("Q2 c*sub <= mism*sum mu*m    :",w[1])
print("Q3 c*sum dst X <= sum dst m  :",w[2])
print("Q4 c*sum dst X <= mism sum dpi m:",w[3])
print("Q5 sum dst(c X - m)          :",w[4])
