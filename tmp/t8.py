import numpy as np
from mdp import make_instance
rng = np.random.default_rng(5)
modes=['rand','grid','coarse','bin']
# Verify the three termwise steps separately, det pistar, astar forced = the det action.
N=60000
w1=-1e18;w2=-1e18;w3=-1e18;wneg=-1e18
for i in range(N):
    I=make_instance(rng,mode=modes[i%4],astar_mode='min',opt_mode='single')
    Adv=I['Adv']; supp=I['supp']; S=I['S']; c=I['c']; m=I['m']; pi=I['pi']
    aidx=np.array([np.flatnonzero(supp[s])[0] for s in range(S)])
    Aa=Adv[np.arange(S),aidx]; pa=pi[np.arange(S),aidx]
    # step1: c <= pa   (def of c as min)
    w1=max(w1,np.max(c-pa))
    # step2: c*Aa <= pa*Aa  requires Aa>=0 ; when Aa<0 LHS c*Aa >= pa*Aa (wrong dir)
    # so handle: we need c*Aa <= m. If Aa<0 then c*Aa<0<=m ok.
    w2=max(w2,np.max(c*Aa-m))
    # step3: c*dstar*Aa <= mism*dpi*m
    w3=max(w3,np.max(c*I['dstar']*Aa - I['mism']*I['dpi']*m))
    wneg=max(wneg,np.max(-m))
print("N",N)
print("step1 max viol (c - pi(astar|s)):",w1)
print("step2 max viol (c*A(s,astar) - m):",w2)
print("step3 max viol termwise full:",w3)
print("max(-m) (m>=0 check):",wneg)
