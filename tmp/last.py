import numpy as np
rng=np.random.default_rng(60613)
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
# FINAL CANDIDATE set. Let ps=pistar(.|s). Key structural facts available in Lean:
#  (a) for a in supp ps:  A(s,a) <= Vstar(s)-Vinf(s)  [Qinf<=Qstar=Vstar on supp]
#  (b) m(s) >= pi(a|s)A(s,a) for ALL a
#  (c) c <= pi(astar s|s), astar s in supp ps
#  (d) sum_a pi(a|s) A(s,a)=0
# CANDIDATE P1: c*X+(s) <= m(s)/ (min_a in supp ps of pi(a|s) / c)... circular.
# CANDIDATE P2 (uses (b) with a=astar s):  m(s) >= pi(astar s|s)*A(s,astar s) >= c*A(s,astar s).
#   So if X(s) <= A(s,astar s) we'd get c*X+ <= m. X<=A(s,astar s) iff astar maximizes A on supp.
#   FROZEN astar is FREE => can be the MINIMIZER. So test how bad: measure  c*X+(s)-m(s) when
#   astar chosen ADVERSARIALLY (to maximize c) -- already known false (0.52).
# CANDIDATE P3: THE GLOBAL ONE. Test whether the goal follows from:
#     c*sum_s dst(s)X+(s) <= sum_s dst(s)*max(m(s), c*X+(s))  ... trivial, useless.
# CANDIDATE P4: test whether  sum_s dst(s)*X+(s) <= (V*_mu - V^pi_mu) + sum_s dst(s)*(X+(s)-X(s))
#   and whether the negative part sum_s dst(s)*(X-)(s) is controlled by sum dpi*m.
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
    V,Q,A=solve(nS,r,P,gam,pi); dpi=occ(nS,P,pi,mu,gam); dst=occ(nS,P,pistar,mu,gam)
    mism=np.max(dst/mu); m=np.max(pi*A,axis=1)
    astar=np.array([max([a for a in range(nA) if pistar[s,a]>1e-14],key=lambda a:pi[s,a]) for s in range(nS)])
    c=min(pi[s,astar[s]] for s in range(nS))
    X=np.array([pistar[s]@A[s] for s in range(nS)]); Xp=np.maximum(X,0)
    # P5: c*X+(s) <= m(s) * (dst(s)>0 ? mism*dpi(s)/dst(s) : inf)  -> per-state SUFFICIENT form
    w[0]=max(w[0], np.max(c*Xp - m*mism*dpi/dst))
    # P6: c*X+(s) <= m(s)*mism*dpi(s)/(mism*mu(s)) = m(s)*dpi(s)/mu(s)  (weaker than P5 since dst<=mism*mu)
    w[1]=max(w[1], np.max(c*Xp - m*dpi/mu))
    # P7: control
    w[2]=max(w[2], c*np.sum(dst*Xp)-mism*np.sum(dpi*m))
print("P5 per-state c*X+ <= m*mism*dpi/dst :",w[0])
print("P6 per-state c*X+ <= m*dpi/mu       :",w[1])
print("P7 goal control                     :",w[2])
