import numpy as np
rng=np.random.default_rng(31)
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
# Reduced target R:  c * sum_s dst(s)*maxA(s)  <=  mism * sum_s dpi(s)*m(s)
# (implied-by would give the goal via C1: sub <= sum dst*maxA)
# ALSO test R2: c*sum_s dpi(s)*maxA(s) <= sum_s dpi(s)*m(s)   [drop mism, use dst<=mism*mu<=mism*dpi]
w=[-1e9]*4
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
    m=np.max(pi*A,axis=1); maxA=np.max(A,axis=1)
    astar=np.array([max([a for a in range(nA) if pistar[s,a]>0],key=lambda a:pi[s,a]) for s in range(nS)])
    c=min(pi[s,astar[s]] for s in range(nS))
    w[0]=max(w[0], c*np.sum(dst*np.maximum(maxA,0))-mism*np.sum(dpi*m))
    w[1]=max(w[1], c*np.sum(dpi*np.maximum(maxA,0))-np.sum(dpi*m))
    w[2]=max(w[2], np.max(c*np.maximum(maxA,0)-m))   # per-state
    # R3: c*maxA(s) <= m(s) when the argmax action a+ has pi(a+|s) >= c ... test c<=pi(a+|s)
    ap=np.argmax(A,axis=1)
    w[3]=max(w[3], max([c-pi[s,ap[s]] for s in range(nS) if maxA[s]>0]+[-1e9]))
print("R1 c*sum dst*maxA+ <= mism*sum dpi*m :",w[0])
print("R2 c*sum dpi*maxA+ <= sum dpi*m      :",w[1])
print("R3 per-state c*maxA+ <= m            :",w[2])
print("R4 c <= pi(argmaxA|s)                :",w[3])
