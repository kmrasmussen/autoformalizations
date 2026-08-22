"""FAST mu control on seed48: point-mass vs uniform (full support)."""
import numpy as np, sys
sys.path.insert(0, '/tmp/wt-g9/scratch')
from engine import *

def grad_mu(TH, P, r, gamma, muvec):
    S, A = TH.shape
    V, pi, Ppi = V_of(TH, P, r, gamma)
    Q = r + gamma * np.einsum('sax,x->sa', P, V)
    Adv = Q - V[:, None]
    d = (1 - gamma) * np.linalg.solve((np.eye(S) - gamma * Ppi).T, muvec)
    return (1.0 / (1 - gamma)) * d[:, None] * pi * Adv

gamma = 0.9
eta = (1 - gamma) ** 3 / 8
rng = np.random.default_rng(10000 + 48)
S = int(rng.integers(2, 4)); A = int(rng.integers(2, 4))
P = rng.random((S, A, S)); P = P ** 8; P /= P.sum(axis=2, keepdims=True)
r = rng.uniform(-1, 1, size=(S, A))
TH0 = rng.normal(scale=4.0, size=(S, A))
astar, Qs, Vs = optimal_policy(P, r, gamma)
m0 = min(softmax_rows(TH0)[s, astar[s]] for s in range(S))
print(f"seed48 astar={astar}  m(0)={m0:.6e}  V*(s0)={Vs[0]:.6f}")

T = 600000
for name, muvec in [("point-mass e0", np.array([1., 0., 0.])),
                    ("uniform (FULL support)", np.ones(3) / 3)]:
    TH = TH0.copy(); mmin = np.inf; targ = 0
    for t in range(T + 1):
        pi = softmax_rows(TH)
        m = min(pi[s, astar[s]] for s in range(S))
        if m < mmin:
            mmin = m; targ = t
        TH = TH + eta * grad_mu(TH, P, r, gamma, muvec)
    V, pi, _ = V_of(TH, P, r, gamma)
    print(f"  mu={name:<24} min_t m={mmin:.6e}@t={targ}  final m={m:.6e}  "
          f"J={V[0]:.6f} (V*-J={Vs[0]-V[0]:.4f})")
