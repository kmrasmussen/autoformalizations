"""Q3 tiny-visitation attack, rerun. mu=point mass at s0; s1 reached only w.p. eps.
theta0 at s1 adversarially favors the SUBOPTIMAL action.
Question: does pi_t(astar(s1)|s1) DECREASE toward 0, or just rise very slowly?"""
import numpy as np, sys
sys.path.insert(0,'/tmp/wt-g9/scratch')
from engine import *
gamma=0.9; eta=(1-gamma)**3/8
print(f"gamma={gamma} eta={eta:.4e}; r in [-1,1]; mu = point mass at s0")
for eps in (1e-2,1e-4,1e-6):
    P=np.zeros((2,2,2))
    P[0,0,0]=1-eps;P[0,0,1]=eps;P[0,1,0]=1-eps;P[0,1,1]=eps
    P[1,0,1]=1.0;P[1,1,1]=1.0
    r=np.array([[1.0,0.5],[-1.0,1.0]])
    astar,_,_=optimal_policy(P,r,gamma)
    TH=np.array([[0.,0.],[6.0,-6.0]])
    fde=np.abs(grad_of(TH,P,r,gamma,0)[0]-fd(TH,P,r,gamma,0)).max()
    T=10**6; marks={0,10**4,10**5,10**6}
    mmin=np.inf;targ=0
    print(f"\n eps={eps:g} astar={astar} gradFDerr={fde:.1e}")
    print(f"   {'t':>8} {'m(t)':>14} {'pi(a*|s1)':>14} {'d(s1)':>11} {'grad[s1,a*]':>13}")
    for t in range(T+1):
        pi=softmax_rows(TH); m=min(pi[s,astar[s]] for s in range(2))
        if m<mmin: mmin=m;targ=t
        if t in marks:
            g,d,_,_,_=grad_of(TH,P,r,gamma,0)
            print(f"   {t:>8d} {m:>14.6e} {pi[1,astar[1]]:>14.6e} {d[1]:>11.3e} {g[1,astar[1]]:>+13.3e}")
        TH=TH+eta*grad_of(TH,P,r,gamma,0)[0]
    print(f"   min_t m={mmin:.8e} at t={targ} -> {'DIPPED' if targ>0 else 'min at t=0, m nondecreasing'}")
