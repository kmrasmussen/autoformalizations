import numpy as np
rng=np.random.default_rng(7)
worst=-1e9
for trial in range(300000):
    nS=int(rng.integers(2,5)); nA=int(rng.integers(2,6))
    th=rng.normal(0,2.5,size=nA); e=np.exp(th-th.max()); pi=e/e.sum()
    # A with sum_a pi_a A_a = 0
    A=rng.normal(0,1,size=nA); A-= pi@A
    ps=rng.dirichlet(np.ones(nA)*0.3)
    # astar in supp ps (all), c <= pi[astar]; c is min over states so c <= max_a in supp pi[a]
    c=max(pi[a] for a in range(nA) if ps[a]>1e-15)
    m=np.max(pi*A)
    lhs=c*(ps@A); 
    v=lhs-m
    if v>worst: worst=v; wit=(pi,A,ps,c,m,lhs)
print("worst c*sum ps A - m =",worst)
print(wit)
