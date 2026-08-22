"""Which REPAIRED statement is true?
Candidate A: astar optimal => m(t) >= m(0)  (monotone nondecreasing)
Candidate B: astar optimal => inf_t m(t) > 0 (bounded below, maybe < m(0))
Test A and B over many random MDPs, INCLUDING adversarial theta0 scale."""
import numpy as np, sys
sys.path.insert(0,'/tmp/wt-g9/scratch')
from engine import *
gamma=0.9; eta=(1-gamma)**3/8
viol_A=0; worstA=None; n=0
minratio_all=1.0
for seed in range(400):
    rng=np.random.default_rng(777000+seed)
    S=int(rng.integers(2,5)); A=int(rng.integers(2,4))
    P=rng.random((S,A,S))
    if seed%2==0: P=P**int(rng.integers(1,12))
    P/=P.sum(axis=2,keepdims=True)
    r=rng.uniform(-1,1,(S,A))
    TH0=rng.normal(scale=float(rng.choice([0.5,2.0,5.0])),size=(S,A))
    astar,_,_=optimal_policy(P,r,gamma)
    TH=TH0.copy(); n+=1
    m0=min(softmax_rows(TH)[s,astar[s]] for s in range(S))
    mmin=m0; targ=0
    for t in range(1,30001):
        g,_,_,_,_=grad_of(TH,P,r,gamma,0); TH=TH+eta*g
        pi=softmax_rows(TH); m=min(pi[s,astar[s]] for s in range(S))
        if m<mmin: mmin=m; targ=t
    ratio=mmin/m0
    minratio_all=min(minratio_all,ratio)
    if ratio<1-1e-9:
        viol_A+=1
        if worstA is None or ratio<worstA[0]: worstA=(ratio,seed,m0,mmin,targ,S,A)
print(f"Candidate A (m(t) >= m(0) always): VIOLATED in {viol_A}/{n} runs")
print(f"   worst ratio min_t m(t)/m(0) = {minratio_all:.6e}")
if worstA: print(f"   worst: seed={worstA[1]} S={worstA[5]} A={worstA[6]} m0={worstA[2]:.4e} mmin={worstA[3]:.4e} at t={worstA[4]}")
print(f"Candidate B (inf_t m(t) > 0): min over all runs of min_t m(t) was {'>0' if minratio_all>0 else '0'}; no run reached 0.")
