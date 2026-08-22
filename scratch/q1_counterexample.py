"""=== THE Q1 COUNTEREXAMPLE (definitive) ===
Smallest MDP: |S|=1, |A|=2.
  S = {s0}, self-loop under both actions: P(s0|s0,a)=1
  r(s0,a0)=+1, r(s0,a1)=-1   (|r|<=1 OK)
  gamma=0.5, mu = point mass at s0, theta_0 = (0,0)
  eta = (1-gamma)^3/8 = 0.015625
  astar(s0) = a1   <-- ARBITRARY map, here the SUBOPTIMAL action
m(t) = min_s pi_t(astar(s)|s) = pi_t(a1) -> 0.
Gradient computed by generic MDP engine (matrix-inverse V, PG theorem),
cross-checked against central finite differences on J.
"""
import numpy as np, sys
sys.path.insert(0,'/tmp/wt-g9/scratch')
from engine import *

S,A,gamma,mu = 1,2,0.5,0
P = np.ones((S,A,S))
r = np.array([[1.0,-1.0]])
eta = (1-gamma)**3/8
astar = np.array([1])          # SUBOPTIMAL

# --- gradient validation
rng=np.random.default_rng(3); err=0.0
for _ in range(25):
    TT=rng.normal(scale=3.0,size=(S,A))
    err=max(err,np.abs(grad_of(TT,P,r,gamma,mu)[0]-fd(TT,P,r,gamma,mu)).max())
print(f"gradient check: max|PG-theorem - central-FD| over 25 thetas = {err:.3e}")
print(f"eta = (1-gamma)^3/8 = {eta}")

TH=np.zeros((S,A))
marks=[0,1,10,100,1000,10000,10**5,10**6]
mmin=np.inf; prev=None; mono=True
print(f"\n{'t':>9} {'pi_t(a0)':>18} {'m(t)=pi_t(a1)':>20} {'t*m(t)':>12}")
for t in range(10**6+1):
    pi=softmax_rows(TH); m=pi[0,1]
    if prev is not None and m>=prev: mono=False
    prev=m
    if m<mmin: mmin=m
    if t in marks:
        print(f"{t:>9d} {pi[0,0]:>18.12f} {m:>20.12e} {t*m:>12.6f}")
    TH=TH+eta*grad_of(TH,P,r,gamma,mu)[0]
print(f"\nstrictly decreasing for all t: {mono}")
print(f"inf_t m(t) over t<=1e6 = {mmin:.6e}  -> m(t) -> 0")
print(f"asymptotic law: m(t) ~ C/t with C = 4/((1-gamma)^2*(r0-r1)) = {4/((1-gamma)**2*2):.4f}")
