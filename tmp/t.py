import numpy as np
rng=np.random.default_rng(21)
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
# CANDIDATE H:  per-state:  c * sum_a pistar(a|s) A(s,a)  <=  mism * (dpi(s)/dst(s)) * m(s)   [what we need]
# equivalently  c * dst(s) * X(s)  <= mism*dpi(s)*m(s) where X = sum_a ps_a A_a
# TEST INSTEAD candidate:  sum_a pistar(a|s)*A(s,a) <= m(s)/c  ... false.
# NEW IDEA: use  A(s,a) <= Qstar(s,a) - V^pi(s) <= V*(s) - V^pi(s)   for a in supp pistar (Q*-tied!)
#  since Q^pi(s,a) <= Q*(s,a) = V*(s) for a in supp pistar.
#  So X(s) = sum_a ps_a A(s,a) <= V*(s)-V^pi(s).
# And: is  c*(V*(s)-V^pi(s)) <= m(s)/(1-gam)?  or  c*sum_s dst(s)(V*(s)-V^pi(s)) <= mism sum dpi m ?
w=[-1e9]*6
for t in range(60000):
    nS=int(rng.integers(2,5)); nA=int(rng.integers(2,5)); gam=float(rng.uniform(0.05,0.95))
    r=rng.integers(-2,3,size=(nS,nA)).astype(float)/2
    P=rng.dirichlet(np.ones(nS)*0.4,size=(nS,nA))
    Vs,Qs=vstar(nS,r,P,gam)
    best=Qs.max(1,keepdims=True); mask=(Qs>=best-1e-11).astype(float)
    pistar=mask/mask.sum(1,keepdims=True)
    mu=rng.dirichlet(np.ones(nS)); th=rng.normal(0,2.5,size=(nS,nA))
    e=np.exp(th-th.max(1,keepdims=True)); pi=e/e.sum(1,keepdims=True)
    V,Q,A=solve(nS,r,P,gam,pi); dpi=occ(nS,P,pi,mu,gam); dst=occ(nS,P,pistar,mu,gam); mism=np.max(dst/mu)
    m=np.max(pi*A,axis=1); sub=mu@Vs-mu@V
    astar=np.array([max([a for a in range(nA) if pistar[s,a]>0],key=lambda a:pi[s,a]) for s in range(nS)])
    c=min(pi[s,astar[s]] for s in range(nS))
    X=np.array([pistar[s]@A[s] for s in range(nS)])
    # H1: X(s) <= V*(s)-V^pi(s)
    w[0]=max(w[0],np.max(X-(Vs-V)))
    # H2: c*(V*(s)-V^pi(s)) <= m(s)/(1-gam)
    w[1]=max(w[1],np.max(c*(Vs-V)-m/(1-gam)))
    # H3: c*(V*(s)-V^pi(s)) <= m(s)*|A|  (nA)
    w[2]=max(w[2],np.max(c*(Vs-V)-m*nA))
    # H4: c*sub <= mism*sum_s dpi(s)*m(s)  (goal)
    w[3]=max(w[3],c*sub-mism*np.sum(np.abs(dpi*m)))
    # H5:  c*(V*(s)-V^pi(s)) <= sum_{s'} dinf(s->s')... skip
    # H6: max_a A(s,a) <= (V*(s)-V^pi(s))  ? 
    w[4]=max(w[4],np.max(np.max(A,axis=1)-(Vs-V)))
    # H7: c*max_a A(s,a) <= m(s)/(1-gam)?
    w[5]=max(w[5],np.max(c*np.max(A,axis=1)-m/(1-gam)))
for i,x in enumerate(w): print("H",i+1,x)
