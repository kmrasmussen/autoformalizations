"""FAST decisive Q3 test: for the dipping cases, does m(t) recover or ->0?
Vectorized over time by just running fewer, longer trajectories on the
known-worst seeds from the earlier 300-seed scan (seed 48 was worst, ratio .2528)."""
import numpy as np, sys
sys.path.insert(0,'/tmp/wt-g9/scratch')
from engine import *
gamma=0.9; eta=(1-gamma)**3/8

def rebuild(seed):
    rng=np.random.default_rng(10000+seed)
    S=rng.integers(2,4); A=rng.integers(2,4)
    P=rng.random((S,A,S))
    if seed%3==0: P=P**8
    P/=P.sum(axis=2,keepdims=True)
    r=rng.uniform(-1,1,size=(S,A))
    TH0=rng.normal(scale=4.0,size=(S,A))
    return P,r,TH0

for seed in (48,):
    P,r,TH0=rebuild(seed)
    astar,_,_=optimal_policy(P,r,gamma); S,A=TH0.shape
    print(f"seed={seed} S={S} A={A} astar={astar}")
    print(f"  gradFDerr={np.abs(grad_of(TH0,P,r,gamma,0)[0]-fd(TH0,P,r,gamma,0)).max():.2e}")
    TH=TH0.copy(); T=4*10**6
    marks={0,40000,10**5,10**6,2*10**6,4*10**6}
    mmin=np.inf;targ=0
    for t in range(T+1):
        pi=softmax_rows(TH)
        m=min(pi[s,astar[s]] for s in range(S))
        if m<mmin: mmin=m;targ=t
        if t in marks:
            g,d,V,Q,_=grad_of(TH,P,r,gamma,0); Adv=Q-V[:,None]
            pv=np.array([pi[s,astar[s]] for s in range(S)])
            av=np.array([Adv[s,astar[s]] for s in range(S)])
            gv=np.array([g[s,astar[s]] for s in range(S)])
            print(f"   t={t:>8d} m={m:.6e}")
            print(f"      pi(a*|s)={np.round(pv,9)}")
            print(f"      d(s)={np.round(d,9)}  A(s,a*)={np.round(av,9)}  grad[s,a*]={np.round(gv,12)}")
        TH=TH+eta*grad_of(TH,P,r,gamma,0)[0]
    print(f"  min_t m={mmin:.8e} at t={targ}; final m={m:.8e}")
    print(f"  RECOVERING (final > min)? {m > mmin*(1+1e-9)}")
