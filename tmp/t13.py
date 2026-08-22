import numpy as np
from mdp import make_instance
rng=np.random.default_rng(31)
modes=['rand','grid','coarse','bin']; opts=['uniform_argmax','rand_argmax','single']; ast=['min','max','rand']
N=25000
# C3: c*gap <= mism*sum_s mu(s)*m(s)/(1-gamma)?  (weaker/stronger?)
# C8a: G with c replaced by min_s max_{a in supp} pi(a|s)  (adversarially-best astar) -> should be TRUE
# C8b: G with c replaced by min_s pi(a+(s)|s) over states with A>0
w3=-1e18; w8a=-1e18; w8b=-1e18; n8b=0
for i in range(N):
    I=make_instance(rng,mode=modes[i%4],astar_mode=ast[i%3],opt_mode=opts[i%3])
    S=I['S']; pi=I['pi']; supp=I['supp']; m=I['m']; Adv=I['Adv']
    rhs_m = I['mism']*np.sum(I['dpi']*m)
    # C3
    w3=max(w3,I['c']*I['gap'] - I['mism']*np.sum(I['mu']*m)/(1-I['gamma']))
    # C8a
    cbest=np.min([np.max(pi[s][supp[s]]) for s in range(S)])
    w8a=max(w8a,cbest*I['gap']-rhs_m)
    # C8b
    maxA=Adv.max(axis=1); ap=Adv.argmax(axis=1)
    msk=maxA>1e-12
    if msk.any():
        cp=np.min(pi[np.arange(S),ap][msk])
        v=cp*I['gap']-rhs_m
        if v>1e-9: n8b+=1
        w8b=max(w8b,v)
print("C3  max viol (c*gap - mism*sum mu*m/(1-g)):",w3)
print("C8a max viol (cbest=min_s max_supp pi):",w8a)
print("C8b max viol (c+=min pi(a+|s) over A>0 states):",w8b,"nbad",n8b,"/",N)
