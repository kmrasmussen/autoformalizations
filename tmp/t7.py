import numpy as np
from mdp import make_instance
rng = np.random.default_rng(4)
modes=['rand','grid','coarse','bin']
N=30000
# opt_mode='single' => pistar deterministic. Then sum_a pistar A = A(s,astar) EXACTLY
# provided astar(s) = the single support action (forced).
w=-1e18
wG=-1e18
for i in range(N):
    I=make_instance(rng,mode=modes[i%4],astar_mode='min',opt_mode='single')
    Adv=I['Adv']; supp=I['supp']; S=I['S']; c=I['c']; m=I['m']
    tgt=np.sum(I['pistar']*Adv,axis=1)
    Aastar=np.array([Adv[s,np.flatnonzero(supp[s])[0]] for s in range(S)])
    w=max(w,np.max(np.abs(tgt-Aastar)))
    # full per-state chain: c*dstar(s)*tgt(s) <= mism*dpi(s)*m(s)?
    v=np.max(c*I['dstar']*tgt - I['mism']*I['dpi']*m)
    wG=max(wG,v)
print("det pistar: max |sum pistar A - A(s,astar)| =",w)
print("det pistar: max per-state violation of termwise ineq =",wG)
