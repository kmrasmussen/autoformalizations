"""Is seed48 converging to a SUBOPTIMAL policy (=> inf_t m(t)=0 with astar optimal),
or infinitely-slowly recovering?
Key diagnostic: theta[s2,a2] is nearly frozen while theta[s2,a1] grows ~ log t.
If theta[s2,a1] - theta[s2,a2] -> infinity then pi(a2|s2) -> 0.
Track the GAP g(t)=theta[s2,a1]-theta[s2,a2] and J(theta_t) vs V*(mu).
Also: does J converge to V*(s0) or to a strictly smaller value?"""
import numpy as np, sys
sys.path.insert(0,'/tmp/wt-g9/scratch')
from engine import *
gamma=0.9; eta=(1-gamma)**3/8
rng=np.random.default_rng(10000+48)
S=rng.integers(2,4); A=rng.integers(2,4)
P=rng.random((S,A,S)); P=P**8; P/=P.sum(axis=2,keepdims=True)
r=rng.uniform(-1,1,size=(S,A)); TH0=rng.normal(scale=4.0,size=(S,A))
astar,Qstar,Vstar=optimal_policy(P,r,gamma)
print(f"V*(s0) = {Vstar[0]:.10f}   astar={astar}")
TH=TH0.copy()
marks=[0,10**4,10**5,10**6,4*10**6,10**7]
print(f"{'t':>10} {'J(theta_t)':>16} {'V*-J':>14} {'gap(s2)':>12} {'pi(a2|s2)':>14}")
for t in range(10**7+1):
    if t in marks:
        V,pi,_=V_of(TH,P,r,gamma)
        gap=TH[2,1]-TH[2,2]
        print(f"{t:>10d} {V[0]:>16.10f} {Vstar[0]-V[0]:>14.3e} {gap:>12.6f} {pi[2,2]:>14.6e}")
    TH=TH+eta*grad_of(TH,P,r,gamma,0)[0]
V,pi,_=V_of(TH,P,r,gamma)
print(f"\nFINAL: J={V[0]:.10f}  V*(s0)={Vstar[0]:.10f}  suboptimality={Vstar[0]-V[0]:.6e}")
print(f"pi(astar|s) final = {[float(pi[s,astar[s]]) for s in range(S)]}")
print(f"NOTE: d(s2)~0.87 (large visitation!) so this is NOT a low-visitation artifact.")
