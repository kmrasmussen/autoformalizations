"""Q3 fixed-point argument, numerically.
Claim: with mu a POINT MASS, for every state s REACHABLE from mu we have d^pi_mu(s)>0
for all theta (since pi>0 always under softmax). The PG row is
   grad[s,:] = (d(s)/(1-g)) * pi(s,:) * A^pi(s,:)
so the row's DIRECTION is exactly the full-support-mu direction; only the
step SIZE differs. So mu can slow convergence arbitrarily but not change the
limit. Verify: (a) d(s)>0 for all reachable s over a long trajectory,
(b) how small d(s) gets, (c) whether any state ever has d(s)==0 while reachable.
"""
import numpy as np, sys
sys.path.insert(0,'/tmp/wt-g9/scratch')
from engine import *
gamma=0.9; eta=(1-gamma)**3/8
rng=np.random.default_rng(2024)
mind=np.inf; worst=None
for seed in range(150):
    S,A=3,3
    P=rng.random((S,A,S)); P=P**10; P/=P.sum(axis=2,keepdims=True)
    r=rng.uniform(-1,1,(S,A)); TH=rng.normal(scale=4.0,size=(S,A))
    for t in range(20000):
        g,d,_,_,_=grad_of(TH,P,r,gamma,0)
        if d.min()<mind: mind=d.min(); worst=(seed,t,d.copy())
        TH=TH+eta*g
print(f"min over 150 MDPs x 20k steps of min_s d^pi_mu(s): {mind:.6e}")
print(f"   (strictly positive => every state reachable in these MDPs)")
print(f"   worst at seed={worst[0]} t={worst[1]} d={worst[2]}")
