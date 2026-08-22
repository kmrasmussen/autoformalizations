import numpy as np
rng=np.random.default_rng(53)
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
# Idea: PER-STATE with the mism factor kept as sup:  c*dst(s)*X(s) <= mism*dpi(s)*m(s)?  FALSE (0.3%).
# NEW: what if we use  X(s) <= (1/c_s)*m(s) with c_s = min_{a in supp ps, ps_a>0} pi(a|s)?  Note c <= pi(astar s|s)
# but astar is FREE. The ADVERSARY picks astar to MAXIMIZE c => c = min_s max_{a in supp} pi(a|s).
# Question: is  (min_s max_{a in supp ps(.|s)} pi(a|s)) * X(s) <= m(s) per state?  test
w=[-1e9]*4
viol=0;tot=0
for t in range(120000):
    nS=int(rng.integers(2,5)); nA=int(rng.integers(2,6)); gam=float(rng.uniform(0.05,0.97))
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
    c=min(pi[s,astar[s]] for s in range(nS))
    X=np.array([pistar[s]@A[s] for s in range(nS)])
    # W1: per-state c*X(s)<=m(s)
    w[0]=max(w[0],np.max(c*X-m))
    # W2: per-state pi(astar s|s)*X(s) <= m(s)  (state's own coefficient, not the min)
    w[1]=max(w[1],np.max(np.array([pi[s,astar[s]] for s in range(nS)])*X-m))
    # W3: sum_a ps_a * pi(a|s)*A(s,a) <= m(s)  (trivially true since each pi_a A_a <= m and ps sums to 1)
    w[2]=max(w[2],np.max(np.array([sum(pistar[s,a]*pi[s,a]*A[s,a] for a in range(nA)) for s in range(nS)])-m))
    # W4: c*X(s) <= sum_a ps_a pi(a|s) A(s,a) ???  needs c <= pi(a|s) for positive-A supported a
    w[3]=max(w[3],np.max(c*X-np.array([sum(pistar[s,a]*pi[s,a]*A[s,a] for a in range(nA)) for s in range(nS)])))
print("W1 c*X<=m         :",w[0])
print("W2 pi_astar*X<=m  :",w[1])
print("W3 E_ps[pi A]<=m  :",w[2])
print("W4 c*X<=E_ps[pi A]:",w[3])
