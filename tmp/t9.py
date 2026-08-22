import numpy as np
from mdp import make_instance, policy_eval, occupancy
rng = np.random.default_rng(6)
modes=['rand','grid','coarse','bin']; opts=['uniform_argmax','rand_argmax']
N=20000
# CLAIM (reduction): for ANY optimal pistar (mixture), and ANY astar with pistar(astar(s)|s)>0,
# there is a DETERMINISTIC optimal policy pihat with pihat(s)=astar(s), i.e. astar itself is optimal.
# Because supp(pistar) subset of argmax Q*, and any deterministic selection from argmax Q* is optimal.
# Then d^{astar} replaces d^{pistar}, gap unchanged (both = V*), and F1 applies with astar.
w=-1e18; wm=-1e18; wg=-1e18
for i in range(N):
    I=make_instance(rng,mode=modes[i%4],astar_mode=['min','max','rand'][i%3],opt_mode=opts[i%2])
    S=I['S'];A=I['A'];gamma=I['gamma'];r=I['r'];P=I['P'];pi=I['pi'];supp=I['supp']
    # reconstruct astar actions used for c
    aidx=np.empty(S,dtype=int)
    for s in range(S):
        idx=np.flatnonzero(supp[s]); aidx[s]=idx[np.argmin(np.abs(pi[s,idx]-I['cvec'][s]))]
    # deterministic policy from astar
    ph=np.zeros((S,A)); ph[np.arange(S),aidx]=1.0
    Vh,Qh,Pph=policy_eval(S,A,gamma,r,P,ph)
    # is it optimal?
    w=max(w,np.max(np.abs(Vh-I['Vstar'])))
    dh=occupancy(S,gamma,Pph,I['mu'])
    mismh=np.max(dh/I['mu'])
    wm=max(wm,mismh-I['mism'])   # is new mism <= old mism? NOT necessarily
    # termwise with dh:
    Adv=I['Adv']; m=I['m']; c=I['c']
    Aa=Adv[np.arange(S),aidx]
    wg=max(wg,np.max(c*dh*Aa - mismh*I['dpi']*m))
print("max |V^astar - V*| (is astar optimal?):",w)
print("max (mism_astar - mism_pistar):",wm)
print("max termwise viol using d^astar & mism_astar:",wg)
