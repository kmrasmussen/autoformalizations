import numpy as np
rng=np.random.default_rng(1)

def solve(nS,nA,r,P,gam,pi):
    # V^pi
    Ppi = np.einsum('sa,sax->sx',pi,P)
    rpi = np.einsum('sa,sa->s',pi,r)
    V = np.linalg.solve(np.eye(nS)-gam*Ppi, rpi)
    Q = r + gam*np.einsum('sax,x->sa',P,V)
    A = Q - V[:,None]
    return V,Q,A

def occ(nS,P,pi,mu,gam):
    Ppi = np.einsum('sa,sax->sx',pi,P)
    # d(s) = sum_{t} gam^t (mu Ppi^t)(s), unnormalized
    return np.linalg.solve((np.eye(nS)-gam*Ppi).T, mu)

def vstar(nS,nA,r,P,gam):
    V=np.zeros(nS)
    for _ in range(20000):
        Q=r+gam*np.einsum('sax,x->sa',P,V)
        Vn=Q.max(1)
        if np.max(np.abs(Vn-V))<1e-14: V=Vn;break
        V=Vn
    Q=r+gam*np.einsum('sax,x->sa',P,V)
    return V,Q

worst=-1e9; wit=None
for trial in range(200000):
    nS=rng.integers(2,4); nA=rng.integers(2,5); gam=rng.uniform(0.05,0.9)
    # tie-seeded integer rewards
    r=rng.integers(-2,3,size=(nS,nA)).astype(float)/2
    P=rng.dirichlet(np.ones(nS)*0.4,size=(nS,nA))
    Vs,Qs=vstar(nS,nA,r,P,gam)
    # pistar: uniform over argmax
    best = Qs.max(1,keepdims=True)
    mask = (Qs>=best-1e-12).astype(float)
    pistar = mask/mask.sum(1,keepdims=True)
    mu=rng.dirichlet(np.ones(nS))
    th=rng.normal(0,2,size=(nS,nA))
    e=np.exp(th-th.max(1,keepdims=True)); pi=e/e.sum(1,keepdims=True)
    V,Q,A=solve(nS,nA,r,P,gam,pi)
    dpi=occ(nS,P,pi,mu,gam); dst=occ(nS,P,pistar,mu,gam)
    mism=np.max(dst/mu)
    b=np.argmax(pi*A,axis=1)
    # astar: any action in support of pistar -> choose worst-case (min pi(astar|s)? actually c=min over s)
    # astar free among support of pistar; adversary picks to MAXIMIZE c? c multiplies LHS so adversary maximizes c
    # c = min_s pi(astar s|s); to maximize, pick astar s = argmax_{a in supp pistar} pi(a|s)
    astar=np.array([max([a for a in range(nA) if pistar[s,a]>0], key=lambda a: pi[s,a]) for s in range(nS)])
    c=min(pi[s,astar[s]] for s in range(nS))
    lhs=c*(mu@Vs - mu@V)
    rhs=mism*np.sum(np.abs(dpi*(pi[np.arange(nS),b]*A[np.arange(nS),b])))
    if rhs>0 or lhs>0:
        v=lhs-rhs
        if v>worst: worst=v; wit=(nS,nA,gam,r,P,mu,th,lhs,rhs)
print("worst lhs-rhs",worst)
