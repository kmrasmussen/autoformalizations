"""Long-horizon seed48: does pi(a2|s2) -> 0, or eventually turn around?
Tracks the theta gap at s2 and J vs V*. 3x10^7 steps."""
import numpy as np, sys
sys.path.insert(0, '/tmp/wt-g9/scratch')
from engine import *

gamma = 0.9
eta = (1 - gamma) ** 3 / 8
rng = np.random.default_rng(10000 + 48)
S = int(rng.integers(2, 4)); A = int(rng.integers(2, 4))
P = rng.random((S, A, S)); P = P ** 8; P /= P.sum(axis=2, keepdims=True)
r = rng.uniform(-1, 1, size=(S, A))
TH0 = rng.normal(scale=4.0, size=(S, A))
astar, Qs, Vs = optimal_policy(P, r, gamma)
print(f"V*(s0)={Vs[0]:.8f} astar={astar}")

I = np.eye(S)
TH = TH0.copy()
marks = {0, 10**5, 10**6, 10**7, 3 * 10**7}
print(f"{'t':>10} {'J':>14} {'V*-J':>11} {'gap(s2)':>11} {'pi(a2|s2)':>13} {'A(s2,a2)':>11}")
for t in range(3 * 10**7 + 1):
    Z = TH - TH.max(axis=1, keepdims=True)
    E = np.exp(Z); pi = E / E.sum(axis=1, keepdims=True)
    Ppi = np.einsum('sa,sax->sx', pi, P)
    rpi = np.einsum('sa,sa->s', pi, r)
    M = I - gamma * Ppi
    V = np.linalg.solve(M, rpi)
    Q = r + gamma * np.einsum('sax,x->sa', P, V)
    Adv = Q - V[:, None]
    d = (1 - gamma) * np.linalg.solve(M.T, np.array([1.0] + [0.0] * (S - 1)))
    if t in marks:
        print(f"{t:>10d} {V[0]:>14.8f} {Vs[0]-V[0]:>11.3e} "
              f"{TH[2,1]-TH[2,2]:>11.5f} {pi[2,2]:>13.5e} {Adv[2,2]:>11.6f}")
    TH = TH + eta * (1.0 / (1 - gamma)) * d[:, None] * pi * Adv
