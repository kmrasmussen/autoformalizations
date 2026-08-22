import numpy as np
from mdp import make_instance, policy_eval, occupancy
rng = np.random.default_rng(11)
modes=['rand','grid','coarse','bin']; opts=['uniform_argmax','rand_argmax','single']
N=40000
# FULL SELF-CONSISTENT CHAIN, using ORIGINAL pistar throughout (no swap):
# S1 (F1):    gap = sum_s dstar(s) * T(s),  T(s)=sum_a pistar(a|s)A(s,a)
# S2:         T(s) <= A(s, astar(s)) ???  -- FALSE in general (4% of states). check magnitude
# Instead the honest chain must use, per state, the astar action. Test claim:
#   c*T(s) <= m(s) is FALSE. But is  c*dstar(s)*T(s) <= mism*dpi(s)*m(s) false too (known).
# So: measure how the SUM saves it. Decompose into good/bad states.
tot_bad_mass=[]; 
w=-1e18
for i in range(N):
    I=make_instance(rng,mode=modes[i%4],astar_mode=['min','max','rand'][i%3],opt_mode=opts[i%3])
    Adv=I['Adv']; m=I['m']; c=I['c']; S=I['S']
    T=np.sum(I['pistar']*Adv,axis=1)
    per = c*I['dstar']*T - I['mism']*I['dpi']*m
    bad=per>1e-12
    if bad.any():
        tot_bad_mass.append((per[bad].sum(), -per[~bad].sum()))
    w=max(w,c*np.sum(I['dstar']*T) - I['mism']*np.sum(I['dpi']*m))
print("summed viol with ORIGINAL pistar:",w)
if tot_bad_mass:
    arr=np.array(tot_bad_mass)
    print("cases with bad states:",len(arr),"of",N)
    print("max ratio badmass/goodslack:",np.max(arr[:,0]/np.maximum(arr[:,1],1e-300)))
