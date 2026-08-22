import numpy as np
from mdp import make_instance
rng = np.random.default_rng(3)
modes=['rand','grid','coarse','bin']; astars=['min','max','rand']; opts=['uniform_argmax','rand_argmax','single']
N=30000
# How often does sum_a pistar A exceed A(s,astar)? and is it bounded by m/c anyway?
cnt=0; tot=0
wE=-1e18
for i in range(N):
    I=make_instance(rng,mode=modes[i%4],astar_mode=astars[i%3],opt_mode=opts[i%3])
    Adv=I['Adv']; pi=I['pi']; supp=I['supp']; S=I['S']; c=I['c']; m=I['m']
    Aastar=np.empty(S)
    for s in range(S):
        idx=np.flatnonzero(supp[s]); j=idx[np.argmin(np.abs(pi[s,idx]-I['cvec'][s]))]
        Aastar[s]=Adv[s,j]
    tgt=np.sum(I['pistar']*Adv,axis=1)
    tot+=S; cnt+=np.sum(tgt>Aastar+1e-12)
    wE=max(wE,np.max(tgt-Aastar))
print("frac states where sum pistar A > A(s,astar):",cnt/tot,"max excess",wE)
# CRUCIAL: is A(s,a) for a in supp(pistar) all EQUAL? Q* ties -> Qpi differs though.
