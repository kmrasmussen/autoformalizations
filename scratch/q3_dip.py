"""The 53/300 dips: transient, or -> 0? Run the worst offenders far longer."""
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

# first re-find the dipping seeds quickly (short run), then extend the worst ones
dips=[]
for seed in range(300):
    P,r,TH0=rebuild(seed)
    astar,_,_=optimal_policy(P,r,gamma); S=TH0.shape[0]
    TH=TH0.copy()
    m0=min(softmax_rows(TH)[s,astar[s]] for s in range(S))
    mmin=m0;targ=0
    for t in range(1,40001):
        g,_,_,_,_=grad_of(TH,P,r,gamma,0); TH=TH+eta*g
        pi=softmax_rows(TH); m=min(pi[s,astar[s]] for s in range(S))
        if m<mmin: mmin=m;targ=t
    if mmin<m0*(1-1e-12): dips.append((mmin/m0,seed,m0,mmin,targ))
dips.sort()
print(f"dipping seeds: {len(dips)}/300; worst 5 ratios: {[(round(d[0],4),d[1]) for d in dips[:5]]}")

for ratio,seed,m0,mmin_s,targ_s in dips[:4]:
    P,r,TH0=rebuild(seed)
    astar,Qs,Vs=optimal_policy(P,r,gamma); S,A=TH0.shape
    TH=TH0.copy(); T=3*10**6
    marks={0,40000,10**5,10**6,3*10**6}
    mmin=np.inf;targ=0
    print(f"\n--- seed={seed} S={S} A={A} astar={astar} shortrun ratio={ratio:.4f}")
    for t in range(T+1):
        pi=softmax_rows(TH)
        m=min(pi[s,astar[s]] for s in range(S))
        if m<mmin: mmin=m;targ=t
        if t in marks:
            g,d,V,Q,_=grad_of(TH,P,r,gamma,0); Adv=Q-V[:,None]
            pv=np.array([pi[s,astar[s]] for s in range(S)])
            av=np.array([Adv[s,astar[s]] for s in range(S)])
            print(f"   t={t:>8d} m={m:.6e} pi(a*|s)={np.round(pv,8)}")
            print(f"            d={np.round(d,8)} A(s,a*)={np.round(av,8)}")
        g,_,_,_,_=grad_of(TH,P,r,gamma,0); TH=TH+eta*g
    print(f"   min_t m={mmin:.8e} at t={targ}; final m={m:.8e}; RECOVERED_ABOVE_MIN={m>mmin*1.0000001}")
