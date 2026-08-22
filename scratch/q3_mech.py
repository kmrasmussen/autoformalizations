"""Mechanism at s2 (seed 48): pi(a2|s2) falls though grad[s2,a2]>0.
Softmax: d/dt log pi(a|s) = grad_theta[s,a] - sum_b pi(b|s) grad_theta[s,b]
(times eta). With grad[s,b] = c*pi(b)*A(b), c=d(s)/(1-g):
   d/dt log pi(a) = c*( pi(a)A(a) - sum_b pi(b)^2 A(b) ) ... no:
Actually theta update is grad[s,b]=c*pi(b)*A(b) for each b, so
   d/dt log pi(a) = c*[ pi(a)A(a) - sum_b pi(b)*pi(b)A(b) ]  (WRONG normalization)
Let's just measure empirically: print theta[s2,:], grad[s2,:], and the
softmax drift term, to see which action is outrunning a2."""
import numpy as np, sys
sys.path.insert(0,'/tmp/wt-g9/scratch')
from engine import *
gamma=0.9; eta=(1-gamma)**3/8
rng=np.random.default_rng(10000+48)
S=rng.integers(2,4); A=rng.integers(2,4)
P=rng.random((S,A,S)); P=P**8; P/=P.sum(axis=2,keepdims=True)
r=rng.uniform(-1,1,size=(S,A)); TH0=rng.normal(scale=4.0,size=(S,A))
astar,Qstar,Vstar=optimal_policy(P,r,gamma)
np.set_printoptions(precision=10,suppress=False)
TH=TH0.copy()
print("astar=",astar,"  focus state s2, astar(s2)=2")
for t in range(4*10**6+1):
    if t in (0,10**5,10**6,4*10**6):
        g,d,V,Q,pi=grad_of(TH,P,r,gamma,0); Adv=Q-V[:,None]
        s=2
        drift = g[s]-np.dot(pi[s],g[s])   # d/dt theta[s,a] - mean, drives log pi
        print(f"\n t={t}")
        print(f"   theta[s2]={TH[s]}")
        print(f"   pi[s2]   ={pi[s]}")
        print(f"   A[s2]    ={Adv[s]}")
        print(f"   grad[s2] ={g[s]}")
        print(f"   dlogpi[s2] (grad - pi.grad) = {drift}   <-- sign for a2: {np.sign(drift[2])}")
    TH=TH+eta*grad_of(TH,P,r,gamma,0)[0]
