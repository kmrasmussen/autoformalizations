"""CRITICAL: is seed48's collapse caused by the POINT-MASS mu, or does it happen
with FULL-SUPPORT mu too? If it happens with uniform mu as well, then it is the
ordinary softmax-PG slow/vanishing-gradient phenomenon, NOT a point-mass artifact
-- and Agarwal et al Thm 5.1 (asymptotic, full support) would still hold in the
limit while the finite-time m(t) still dips arbitrarily low.
Generalize grad to arbitrary mu-distribution."""
import numpy as np, sys
sys.path.insert(0,'/tmp/wt-g9/scratch')
from engine import *

def grad_mu(TH,P,r,gamma,muvec):
    S,A=TH.shape; V,pi,Ppi=V_of(TH,P,r,gamma)
    Q=r+gamma*np.einsum('sax,x->sa',P,V); Adv=Q-V[:,None]
    d=(1-gamma)*np.linalg.solve((np.eye(S)-gamma*Ppi).T,muvec)
    return (1.0/(1-gamma))*d[:,None]*pi*Adv, d, V

gamma=0.9; eta=(1-gamma)**3/8
rng=np.random.default_rng(10000+48)
S=rng.integers(2,4); A=rng.integers(2,4)
P=rng.random((S,A,S)); P=P**8; P/=P.sum(axis=2,keepdims=True)
r=rng.uniform(-1,1,size=(S,A)); TH0=rng.normal(scale=4.0,size=(S,A))
astar,Qstar,Vstar=optimal_policy(P,r,gamma)
print("seed48, astar=",astar)
for name,muvec in [("point mass e0",np.array([1.,0.,0.])),
                   ("UNIFORM (full support)",np.ones(3)/3)]:
    TH=TH0.copy(); mmin=np.inf; targ=0
    T=2*10**6
    for t in range(T+1):
        pi=softmax_rows(TH); m=min(pi[s,astar[s]] for s in range(S))
        if m<mmin: mmin=m;targ=t
        TH=TH+eta*grad_mu(TH,P,r,gamma,muvec)[0]
    pi=softmax_rows(TH)
    print(f"  mu={name:<24} m(0)={min(softmax_rows(TH0)[s,astar[s]] for s in range(S)):.6e}"
          f"  min_t m={mmin:.6e} at t={targ}  final m={m:.6e}")
