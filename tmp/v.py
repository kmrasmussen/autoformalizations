import numpy as np
rng=np.random.default_rng(3)
def solve(nS,r,P,gam,pi):
    Ppi=np.einsum('sa,sax->sx',pi,P); rpi=np.einsum('sa,sa->s',pi,r)
    V=np.linalg.solve(np.eye(nS)-gam*Ppi,rpi)
    Q=r+gam*np.einsum('sax,x->sa',P,V); return V,Q,Q-V[:,None]
def occ(nS,P,pi,mu,gam):
    Ppi=np.einsum('sa,sax->sx',pi,P); return np.linalg.solve((np.eye(nS)-gam*Ppi).T,mu)
def vstar(nS,r,P,gam):
    V=np.zeros(nS)
    for _ in range(5000):
        Q=r+gam*np.einsum('sax,x->sa',P,V); Vn=Q.max(1)
        if np.max(np.abs(Vn-V))<1e-15: V=Vn;break
        V=Vn
    return V, r+gam*np.einsum('sax,x->sa',P,V)
# Candidate C4 (per-state, with c replaced by pi(a+|s) where a+=argmax_a A):
#   is  sub <= sum_s dst(s)*maxA(s)  and then  c*dst(s)*maxA(s) <= mism*dpi(s)*m(s) ?
#   -> needs c*maxA(s) <= m(s). FALSE.
# Candidate C5: use  sum_a pistar(a|s) A(s,a) <= (1/c)*m(s)?  i.e. c*sum_a ps_a A_a <= m(s)  -- FALSE per earlier
# What saves it globally? Let's find the max of  c*sub / (mism*sum_s dpi(s)*m(s)) and see where per-state fails but global holds.
worst=-1e9; cnt=0; bad=0
for t in range(30000):
    nS=int(rng.integers(2,5)); nA=int(rng.integers(2,5)); gam=float(rng.uniform(0.05,0.95))
    r=rng.integers(-2,3,size=(nS,nA)).astype(float)/2
    P=rng.dirichlet(np.ones(nS)*0.4,size=(nS,nA))
    Vs,Qs=vstar(nS,r,P,gam)
    best=Qs.max(1,keepdims=True); mask=(Qs>=best-1e-11).astype(float)
    pistar=mask/mask.sum(1,keepdims=True)
    mu=rng.dirichlet(np.ones(nS)); th=rng.normal(0,2,size=(nS,nA))
    e=np.exp(th-th.max(1,keepdims=True)); pi=e/e.sum(1,keepdims=True)
    V,Q,A=solve(nS,r,P,gam,pi); dpi=occ(nS,P,pi,mu,gam); dst=occ(nS,P,pistar,mu,gam); mism=np.max(dst/mu)
    m=np.max(pi*A,axis=1); sub=mu@Vs-mu@V
    astar=np.array([max([a for a in range(nA) if pistar[s,a]>0],key=lambda a:pi[s,a]) for s in range(nS)])
    c=min(pi[s,astar[s]] for s in range(nS))
    # per-state form of the goal:
    ps_term = c*dst*np.array([pistar[s]@A[s] for s in range(nS)])
    rhs_term = mism*dpi*m
    if np.any(ps_term>rhs_term+1e-12): bad+=1
    cnt+=1
print("per-state violations:",bad,"/",cnt)
