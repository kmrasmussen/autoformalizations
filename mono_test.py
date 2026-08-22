import numpy as np
rng=np.random.default_rng(0)

def softmax(z):
    z=z-z.max(-1,keepdims=True); e=np.exp(z); return e/e.sum(-1,keepdims=True)

def solve(P,r,g,pi):
    S,A=r.shape
    Ppi=np.einsum('sa,sat->st',pi,P)
    rpi=(pi*r).sum(1)
    V=np.linalg.solve(np.eye(S)-g*Ppi,rpi)
    Q=r+g*np.einsum('sat,t->sa',P,V)
    return V,Q

def dmu(P,g,pi,mu):
    S=len(mu); Ppi=np.einsum('sa,sat->st',pi,P)
    return np.linalg.solve(np.eye(S)-g*Ppi.T, mu)   # unnormalized: sums to 1/(1-g)

worst=None
for trial in range(4000):
    S,A=rng.integers(2,4),rng.integers(2,4)
    g=rng.uniform(0.0,0.95)
    P=rng.random((S,A,S)); P/=P.sum(-1,keepdims=True)
    r=rng.uniform(-1,1,(S,A))          # |r|<=1  (goal's assumption)
    mu=rng.random(S); mu/=mu.sum()
    th=rng.normal(0,3,(S,A))
    eta=(1-g)**2/5
    pi=softmax(th); V,Q=solve(P,r,g,pi); Adv=Q-V[:,None]
    d=dmu(P,g,pi,mu)
    grad=d[:,None]*pi*Adv
    th2=th+eta*grad
    pi2=softmax(th2); V2,_=solve(P,r,g,pi2)
    gap=(V2-V).min()
    if worst is None or gap<worst[0]:
        worst=(gap,S,A,g,eta)
print("worst per-state V improvement over 4000 random trials (|r|<=1, eta=(1-g)^2/5):")
print("  min_s (V'(s)-V(s)) =",worst[0], " at S,A,gamma =",worst[1:4])
