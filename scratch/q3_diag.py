"""Diagnose seed 48: m(t) decreasing at t=3e6 with A(s2,a*)=+0.25>0.
If A(s2,astar)>0 then grad[s2,astar] = d(s2)/(1-g)*pi*A > 0, so theta[s2,astar]
INCREASES. Yet pi(astar|s2) DECREASES. That can only happen if some OTHER action
at s2 has an even larger positive advantage -> i.e. astar(s2) from value-iteration
argmax is NOT the greedy action w.r.t. the CURRENT pi. Check: is astar really
optimal? Is there a tie / near-tie in Q*? Print full Q*, and full advantage row."""
import numpy as np, sys
sys.path.insert(0,'/tmp/wt-g9/scratch')
from engine import *
gamma=0.9; eta=(1-gamma)**3/8
rng=np.random.default_rng(10000+48)
S=rng.integers(2,4); A=rng.integers(2,4)
P=rng.random((S,A,S)); P=P**8; P/=P.sum(axis=2,keepdims=True)
r=rng.uniform(-1,1,size=(S,A))
TH0=rng.normal(scale=4.0,size=(S,A))
astar,Qstar,Vstar=optimal_policy(P,r,gamma)
np.set_printoptions(precision=8,suppress=True)
print("S,A =",S,A)
print("Q* =\n",Qstar)
print("V* =",Vstar," astar =",astar)
print("Q* gaps per state (best - 2nd best):")
for s in range(S):
    q=np.sort(Qstar[s])[::-1]; print(f"   s{s}: {q[0]-q[1]:.10f}")
print("\nrun and print FULL advantage row at s2 over time:")
TH=TH0.copy()
for t in range(3*10**6+1):
    if t in (0,10**5,10**6,3*10**6):
        g,d,V,Q,pi=grad_of(TH,P,r,gamma,0); Adv=Q-V[:,None]
        print(f" t={t:>8d}")
        for s in range(S):
            print(f"   s{s}: pi={np.round(pi[s],9)} A={np.round(Adv[s],8)} argmaxA={Adv[s].argmax()} astar={astar[s]} d={d[s]:.6f}")
    TH=TH+eta*grad_of(TH,P,r,gamma,0)[0]
