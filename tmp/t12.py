import numpy as np
from mdp import make_instance, policy_eval, occupancy
rng = np.random.default_rng(21)
modes=['rand','grid','coarse','bin']; opts=['uniform_argmax','rand_argmax','single']
N=40000
# KEY REDUCTION TEST (the proof route):
# Let pihat = deterministic policy s->astar(s). Facts to verify:
#  R1: pihat is optimal (V^pihat = V*)
#  R2: gap = sum_s dhat(s) * A^pi(s,astar(s))     [F1 applied to pihat]
#  R3: c*A^pi(s,astar(s)) <= m(s)  per state      [from F4 + c<=pi(astar|s), needs A>=0 OR m>=0]
#  R4: dhat(s) <= mismhat*mu(s) <= mismhat*dpi(s) [F2 for pihat]
#  => c*gap <= mismhat * sum_s dpi(s) m(s)
# Question: is mismhat <= mism? NO (t9). So (G) as stated with mism from pistar
# needs mism to be the max over the *chosen* astar occupancy, OR the sum saves it.
w1=w2=w3=w4=-1e18
for i in range(N):
    I=make_instance(rng,mode=modes[i%4],astar_mode=['min','max','rand'][i%3],opt_mode=opts[i%3])
    S=I['S'];A=I['A'];gamma=I['gamma'];r=I['r'];P=I['P'];pi=I['pi'];supp=I['supp'];mu=I['mu']
    aidx=np.empty(S,dtype=int)
    for s in range(S):
        idx=np.flatnonzero(supp[s]); aidx[s]=idx[np.argmin(np.abs(pi[s,idx]-I['cvec'][s]))]
    ph=np.zeros((S,A)); ph[np.arange(S),aidx]=1.0
    Vh,Qh,Pph=policy_eval(S,A,gamma,r,P,ph)
    dh=occupancy(S,gamma,Pph,mu)
    w1=max(w1,np.max(np.abs(Vh-I['Vstar'])))
    Aa=I['Adv'][np.arange(S),aidx]
    w2=max(w2,abs(np.sum(dh*Aa)-I['gap']))
    w3=max(w3,np.max(I['c']*Aa-I['m']))
    mismh=np.max(dh/mu)
    w4=max(w4,I['c']*I['gap']-mismh*np.sum(I['dpi']*I['m']))
print("R1 max|V^pihat-V*| :",w1)
print("R2 max|sum dhat*A(astar) - gap| :",w2)
print("R3 max (c*A(s,astar)-m) :",w3)
print("R4 final: max(c*gap - mismhat*sum dpi*m) :",w4)
