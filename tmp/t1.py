import numpy as np, sys
from mdp import make_instance
rng = np.random.default_rng(0)
modes=['rand','grid','coarse','bin']
astars=['min','max','rand']
opts=['uniform_argmax','rand_argmax','single']
N=20000
worstG=-1; wit=None
ratios=[]
for i in range(N):
    mode=modes[i%4]; am=astars[i%3]; om=opts[i%3]
    I=make_instance(rng,mode=mode,astar_mode=am,opt_mode=om)
    lhs=I['c']*I['gap']; rhs=I['mism']*np.sum(np.abs(I['dpi']*I['m']))
    if rhs<=0:
        v = lhs
    else:
        v = lhs/rhs
    ratios.append(v)
    if v>worstG: worstG=v; wit=(mode,am,om,lhs,rhs,I)
ratios=np.array(ratios)
print("G max ratio lhs/rhs:", worstG)
print("frac >1:", np.mean(ratios>1+1e-9))
print("quantiles", np.quantile(ratios,[0.5,0.9,0.99,0.999,1.0]))
