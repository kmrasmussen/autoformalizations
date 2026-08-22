import numpy as np
from mdp import make_instance, policy_eval, occupancy
rng = np.random.default_rng(7)
modes=['rand','grid','coarse','bin']; opts=['uniform_argmax','rand_argmax']
N=30000
# The DANGER: (G) uses mism = max_s d^{pistar}/mu with the GIVEN pistar.
# If we swap to d^{astar}, mism grows -> chain gives a WEAKER statement than (G).
# So test: does the termwise ineq hold with d^{astar} but the ORIGINAL mism?
w=-1e18; wit=None; nbad=0
for i in range(N):
    I=make_instance(rng,mode=modes[i%4],astar_mode=['min','max','rand'][i%3],opt_mode=opts[i%2])
    S=I['S'];A=I['A'];gamma=I['gamma'];r=I['r'];P=I['P'];pi=I['pi'];supp=I['supp']
    aidx=np.empty(S,dtype=int)
    for s in range(S):
        idx=np.flatnonzero(supp[s]); aidx[s]=idx[np.argmin(np.abs(pi[s,idx]-I['cvec'][s]))]
    ph=np.zeros((S,A)); ph[np.arange(S),aidx]=1.0
    Vh,Qh,Pph=policy_eval(S,A,gamma,r,P,ph)
    dh=occupancy(S,gamma,Pph,I['mu'])
    Adv=I['Adv']; m=I['m']; c=I['c']
    Aa=Adv[np.arange(S),aidx]
    v=np.max(c*dh*Aa - I['mism']*I['dpi']*m)
    if v>1e-9: nbad+=1
    if v>w: w=v; wit=(I,dh,aidx)
print("max termwise viol using d^astar but ORIGINAL mism:",w,"nbad",nbad,"/",N)
# And the SUMMED version (what actually matters for G):
rng2=np.random.default_rng(8); w2=-1e18; nb2=0
for i in range(N):
    I=make_instance(rng2,mode=modes[i%4],astar_mode=['min','max','rand'][i%3],opt_mode=opts[i%2])
    S=I['S'];A=I['A'];gamma=I['gamma'];r=I['r'];P=I['P'];pi=I['pi'];supp=I['supp']
    aidx=np.empty(S,dtype=int)
    for s in range(S):
        idx=np.flatnonzero(supp[s]); aidx[s]=idx[np.argmin(np.abs(pi[s,idx]-I['cvec'][s]))]
    ph=np.zeros((S,A)); ph[np.arange(S),aidx]=1.0
    Vh,Qh,Pph=policy_eval(S,A,gamma,r,P,ph)
    dh=occupancy(S,gamma,Pph,I['mu'])
    Aa=I['Adv'][np.arange(S),aidx]
    lhs=I['c']*np.sum(dh*Aa); rhs=I['mism']*np.sum(I['dpi']*I['m'])
    if lhs-rhs>1e-9: nb2+=1
    w2=max(w2,lhs-rhs)
print("max SUMMED viol (c*sum d^astar*A(astar) - mism*sum dpi*m):",w2,"nbad",nb2,"/",N)
