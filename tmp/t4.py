import numpy as np
from mdp import make_instance
rng = np.random.default_rng(1)
modes=['rand','grid','coarse','bin']; astars=['min','max','rand']; opts=['uniform_argmax','rand_argmax','single']
N=30000
res={}
def rec(k,v):
    if k not in res or v>res[k][0]: res[k]=(v,)
wC7=-1e18; wC7wit=None
wC2=-1e18; wC2wit=None
wC4=-1e18; wC4wit=None
wC4b=-1e18
for i in range(N):
    I=make_instance(rng,mode=modes[i%4],astar_mode=astars[i%3],opt_mode=opts[i%3])
    Adv=I['Adv']; pi=I['pi']; m=I['m']; c=I['c']; supp=I['supp']
    S=I['S']
    # C7: sum_a pistar(a|s) A(s,a) <= m(s)/c  per state
    lhsC7 = np.sum(I['pistar']*Adv,axis=1)
    v = np.max(c*lhsC7 - m)
    if v>wC7: wC7=v; wC7wit=I
    # C2: c*max_a A(s,a) <= m(s)
    maxA = Adv.max(axis=1)
    v2 = np.max(c*maxA - m)
    if v2>wC2: wC2=v2; wC2wit=I
    # C4: c <= pi(a+(s)|s) where a+ = argmax A, at states with maxA>0
    ap = Adv.argmax(axis=1)
    chat = pi[np.arange(S),ap]
    mask = maxA>1e-12
    if mask.any():
        v4=np.max(c-chat[mask])
        if v4>wC4: wC4=v4; wC4wit=I
    # C4b: restrict also to dstar>0 states
    mask2 = mask & (I['dstar']>1e-12)
    if mask2.any():
        v4b=np.max(c-chat[mask2]); wC4b=max(wC4b,v4b)
print("C7 max violation (c*sum pistar A - m):",wC7)
print("C2 max violation (c*maxA - m):",wC2)
print("C4 max violation (c - pi(a+|s)) on maxA>0:",wC4)
print("C4b same restricted dstar>0:",wC4b)
