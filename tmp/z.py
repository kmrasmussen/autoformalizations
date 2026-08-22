import numpy as np
rng=np.random.default_rng(11)
# per-state candidate with a *different* comparator: use that c <= pi(astar s|s) for EVERY s,
# and also c <= 1. Try: c * sum_a ps_a A_a <= m(s) + something?
# Alternative: sum_a ps_a A_a <= max_a A_a. And m = max_a pi_a A_a.
# Chain used by AKM: sum_a ps_a A_a <= max_a A_a <= m / pi(argmax) ... 
# Let's measure the true needed inequality per-state ratio distribution
worst=-1e9
for trial in range(200000):
    nA=int(rng.integers(2,6))
    th=rng.normal(0,2.5,size=nA); e=np.exp(th-th.max()); pi=e/e.sum()
    A=rng.normal(0,1,size=nA); A-= pi@A
    ps=rng.dirichlet(np.ones(nA)*0.3)
    astar=int(rng.integers(0,nA))
    if ps[astar]<=1e-15: continue
    c=pi[astar]
    m=np.max(pi*A)
    v=c*(ps@A)-m
    if v>worst: worst=v; wit=(pi,A,ps,astar,c,m)
print(worst); print(wit)
