"""Seed48 trend at moderate horizon with dense sampling, to extrapolate
whether pi(a2|s2) -> 0 or bottoms out. 3e6 steps, log-spaced marks."""
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
print(f"V*(s0)={Vs[0]:.8f} astar={astar}  Q* gap at s2 = "
      f"{np.sort(Qs[2])[::-1][0]-np.sort(Qs[2])[::-1][1]:.6f}")

I = np.eye(S)
e0 = np.array([1.0] + [0.0] * (S - 1))
TH = TH0.copy()
marks = sorted(set([0] + [int(10 ** (k / 4.0)) for k in range(0, 27)]))
marks = [m for m in marks if m <= 3 * 10**6]
print(f"{'t':>9} {'J':>13} {'V*-J':>10} {'gap(s2)':>10} {'pi(a2|s2)':>13} {'A(s2,a2)':>10}")
for t in range(3 * 10**6 + 1):
    Z = TH - TH.max(axis=1, keepdims=True)
    E = np.exp(Z); pi = E / E.sum(axis=1, keepdims=True)
    Ppi = np.einsum('sa,sax->sx', pi, P)
    rpi = np.einsum('sa,sa->s', pi, r)
    M = I - gamma * Ppi
    V = np.linalg.solve(M, rpi)
    Q = r + gamma * np.einsum('sax,x->sa', P, V)
    Adv = Q - V[:, None]
    d = (1 - gamma) * np.linalg.solve(M.T, e0)
    if t in marks:
        print(f"{t:>9d} {V[0]:>13.7f} {Vs[0]-V[0]:>10.3e} "
              f"{TH[2,1]-TH[2,2]:>10.4f} {pi[2,2]:>13.5e} {Adv[2,2]:>10.6f}")
    TH = TH + eta * (1.0 / (1 - gamma)) * d[:, None] * pi * Adv
