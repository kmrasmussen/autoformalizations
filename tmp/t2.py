import numpy as np
from mdp import make_instance
rng = np.random.default_rng(0)
modes=['rand','grid','coarse','bin']; astars=['min','max','rand']; opts=['uniform_argmax','rand_argmax','single']
N=20000
bad=[]
for i in range(N):
    I=make_instance(rng,mode=modes[i%4],astar_mode=astars[i%3],opt_mode=opts[i%3])
    lhs=I['c']*I['gap']; rhs=I['mism']*np.sum(np.abs(I['dpi']*I['m']))
    if lhs > rhs*(1+1e-7)+1e-12:
        bad.append((lhs/max(rhs,1e-300),i,I))
bad.sort(key=lambda x:-x[0])
print("num bad:",len(bad))
for r,i,I in bad[:3]:
    print("="*60)
    print("ratio",r,"idx",i,"S",I['S'],"A",I['A'],"gamma",I['gamma'])
    print("gap V*-Vpi =",I['gap'])
    print("c",I['c'],"mism",I['mism'])
    print("m",I['m'])
    print("dpi",I['dpi']); print("dstar",I['dstar']); print("mu",I['mu'])
    print("Adv",I['Adv'])
    print("pi",I['pi'])
    print("pistar",I['pistar'])
    print("Vstar",I['Vstar'],"Vpi",I['Vpi'])
    print("Qstar",I['Qstar'])
    # check F1
    f1 = np.sum(I['dstar']*np.sum(I['pistar']*I['Adv'],axis=1))
    print("F1 check:",f1,"vs gap",I['gap'])
    print("F2 check dstar<=mism*mu:",np.max(I['dstar']-I['mism']*I['mu']), "mu<=dpi:",np.max(I['mu']-I['dpi']))
