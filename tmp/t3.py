import numpy as np
from mdp import make_instance
rng = np.random.default_rng(0)
modes=['rand','grid','coarse','bin']; astars=['min','max','rand']; opts=['uniform_argmax','rand_argmax','single']
N=20000
worst=-1e18; wit=None
for i in range(N):
    I=make_instance(rng,mode=modes[i%4],astar_mode=astars[i%3],opt_mode=opts[i%3])
    lhs=I['c']*I['gap']; rhs=I['mism']*np.sum(np.abs(I['dpi']*I['m']))
    d = lhs-rhs   # absolute violation
    if d>worst: worst=d; wit=(i,lhs,rhs,I)
i,lhs,rhs,I=wit
print("max ABSOLUTE violation lhs-rhs:",worst)
print("at idx",i,"lhs",lhs,"rhs",rhs,"gap",I['gap'],"c",I['c'],"mism",I['mism'],"sum m",I['m'].sum())
