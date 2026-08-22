import numpy as np
from mdp import make_instance
rng = np.random.default_rng(2)
modes=['rand','grid','coarse','bin']; astars=['min','max','rand']; opts=['uniform_argmax','rand_argmax','single']
N=30000
# Key structural idea: for a in supp(pistar), A(s,a) relates to m(s) how?
# m(s) >= pi(a|s) A(s,a) >= c*A(s,a) IF pi(a|s)>=c and A(s,a)>=0.
# c = min_s pi(astar(s)|s) so pi(astar(s)|s) >= c always. So for a=astar(s):
#    m(s) >= pi(astar(s)|s)*A(s,astar(s)) >= c*A(s,astar(s))  when A(s,astar(s))>=0.
# Problem: sum_a pistar(a|s)A(s,a) can exceed A(s,astar(s)) since astar is only ONE support action.
wA=-1e18; wB=-1e18
wA_wit=None
for i in range(N):
    I=make_instance(rng,mode=modes[i%4],astar_mode=astars[i%3],opt_mode=opts[i%3])
    Adv=I['Adv']; pi=I['pi']; m=I['m']; c=I['c']; supp=I['supp']; S=I['S']
    # (P1) per-state: c * A(s,astar(s)) <= m(s)  when A(s,astar(s))>=0?
    # need the actual astar used. reconstruct: astar_mode min/max/rand -> use cvec
    # find action achieving cvec
    Aastar=np.empty(S)
    for s in range(S):
        idx=np.flatnonzero(supp[s])
        j=idx[np.argmin(np.abs(pi[s,idx]-I['cvec'][s]))]
        Aastar[s]=Adv[s,j]
    v=np.max(c*np.maximum(Aastar,0)-m)
    if v>wA: wA=v; wA_wit=I
    # (P2) is sum_a pistar(a|s) A(s,a) <= max over supp of A(s,a)?  trivially yes
    # (P3) c*max_{a in supp} A(s,a) <= m(s)?
    ms=np.array([np.max(Adv[s][supp[s]]) for s in range(S)])
    v2=np.max(c*np.maximum(ms,0)-m)
    wB=max(wB,v2)
print("P1 max viol (c*A(s,astar) - m), A clipped>=0:",wA)
print("P3 max viol (c*max_supp A - m):",wB)
