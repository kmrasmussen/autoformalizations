import numpy as np
from mdp import make_instance, policy_eval, occupancy
modes=['rand','grid','coarse','bin']; opts=['uniform_argmax','rand_argmax','single']; ast=['min','max','rand']
N=130000
rng=np.random.default_rng(1234)
stats={k:-1e18 for k in ['G','R1','R2','R3','R4','F3','mneg','termwise_orig']}
cnt_term=0; tot=0
tight=[]
for i in range(N):
    mode=modes[i%4]; om=opts[(i//4)%3]; am=ast[(i//12)%3]
    if i%10000==0: print("..",i,flush=True)
    I=make_instance(rng,mode=mode,astar_mode=am,opt_mode=om)
    S=I['S'];A=I['A'];gamma=I['gamma'];r=I['r'];P=I['P'];pi=I['pi'];supp=I['supp'];mu=I['mu']
    c=I['c']; m=I['m']; Adv=I['Adv']
    # G
    lhs=c*I['gap']; rhs=I['mism']*np.sum(np.abs(I['dpi']*m))
    stats['G']=max(stats['G'],lhs-rhs)
    if rhs>1e-9: tight.append((lhs/rhs,i,mode,om,am))
    stats['F3']=max(stats['F3'],np.max(np.abs(np.sum(pi*Adv,axis=1))))
    stats['mneg']=max(stats['mneg'],np.max(-m))
    aidx=np.empty(S,dtype=int)
    for s in range(S):
        idx=np.flatnonzero(supp[s]); aidx[s]=idx[np.argmin(np.abs(pi[s,idx]-I['cvec'][s]))]
    ph=np.zeros((S,A)); ph[np.arange(S),aidx]=1.0
    Vh,Qh,Pph=policy_eval(S,A,gamma,r,P,ph)
    dh=occupancy(S,gamma,Pph,mu)
    Aa=Adv[np.arange(S),aidx]
    stats['R1']=max(stats['R1'],np.max(np.abs(Vh-I['Vstar'])))
    stats['R2']=max(stats['R2'],abs(np.sum(dh*Aa)-I['gap']))
    stats['R3']=max(stats['R3'],np.max(c*Aa-m))
    mismh=np.max(dh/mu)
    stats['R4']=max(stats['R4'],c*I['gap']-mismh*np.sum(I['dpi']*m))
    # termwise with ORIGINAL pistar (known false)
    T=np.sum(I['pistar']*Adv,axis=1)
    per=c*I['dstar']*T - I['mism']*I['dpi']*m
    tot+=S; cnt_term+=np.sum(per>1e-10)
    stats['termwise_orig']=max(stats['termwise_orig'],np.max(per))
print("N =",N,flush=True)
for k,v in stats.items(): print(f"  {k}: {v:.3e}")
print("termwise-orig violating states: %d / %d = %.4f%%"%(cnt_term,tot,100*cnt_term/tot))
tight.sort(key=lambda x:-x[0])
print("top ratios lhs/rhs for G:", [f"{t[0]:.6f}({t[2]},{t[3]},{t[4]})" for t in tight[:8]])
