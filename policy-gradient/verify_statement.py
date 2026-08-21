"""Ground-truth check for the finite-horizon policy gradient theorem.

Compares dV/dtheta computed by:
  (a) central finite differences on V itself
  (b) the exact PG formula we intend to prove in Lean
If these agree, the Lean statement is about the right object.
"""
import numpy as np
np.random.seed(0)

nS, nA, H = 3, 2, 4          # states, actions, horizon
gamma = 0.9

# random MDP
P = np.random.rand(nS, nA, nS); P /= P.sum(axis=2, keepdims=True)
r = np.random.randn(nS, nA)

# softmax policy with parameter matrix theta (nS x nA)
def policy(theta):
    e = np.exp(theta - theta.max(axis=1, keepdims=True))
    return e / e.sum(axis=1, keepdims=True)

def V_all(theta, m):
    """V[m][s] by backward recursion -- mirrors PolicyGradient/Value.lean exactly."""
    pi = policy(theta)
    V = np.zeros(nS)
    for _ in range(m):
        Q = r + gamma * P.dot(V)          # Q[s,a] = r[s,a] + g * sum_s' P[s,a,s'] V[s']
        V = (pi * Q).sum(axis=1)
        # NB: V here is V_{k+1}, built from V_k -- same indexing as the Lean def
    return V

def V_and_Q_stack(theta, m):
    """Return list V[0..m] and Q[0..m-1], V[k] = value with k steps remaining."""
    pi = policy(theta)
    Vs = [np.zeros(nS)]
    Qs = []
    for _ in range(m):
        Q = r + gamma * P.dot(Vs[-1])
        Qs.append(Q)
        Vs.append((pi * Q).sum(axis=1))
    return Vs, Qs

def visit(theta, k, s0):
    """Pr(s_k = s | s0) -- mirrors PolicyGradient/Theorem.lean `visit`."""
    pi = policy(theta)
    d = np.zeros(nS); d[s0] = 1.0
    T = np.einsum('sa,sat->st', pi, P)     # step[s,s'] = sum_a pi[s,a] P[s,a,s']
    for _ in range(k):
        d = d @ T
    return d

def dpi_dtheta(theta, s, a, si, ai):
    """d pi(a|s) / d theta[si,ai] for softmax; nonzero only when si == s."""
    if si != s: return 0.0
    pi = policy(theta)
    return pi[s, a] * ((1.0 if a == ai else 0.0) - pi[s, ai])

def pg_formula(theta, m, s0, si, ai):
    """sum_{k<m} gamma^k sum_s visit(k,s0,s) sum_a dpi(a|s) Q_{m-1-k}(s,a)"""
    Vs, Qs = V_and_Q_stack(theta, m)
    total = 0.0
    for k in range(m):
        d = visit(theta, k, s0)
        Q = Qs[m - 1 - k]                  # Q with (m-1-k) steps remaining after the action
        for s in range(nS):
            if d[s] == 0.0: continue
            for a in range(nA):
                total += (gamma**k) * d[s] * dpi_dtheta(theta, s, a, si, ai) * Q[s, a]
    return total

theta = np.random.randn(nS, nA) * 0.5
eps = 1e-6
print(f"{'s0':>3} {'si':>3} {'ai':>3} {'finite-diff':>14} {'PG formula':>14} {'abs err':>10}")
worst = 0.0
for s0 in range(nS):
    for si in range(nS):
        for ai in range(nA):
            tp = theta.copy(); tp[si, ai] += eps
            tm = theta.copy(); tm[si, ai] -= eps
            fd = (V_all(tp, H)[s0] - V_all(tm, H)[s0]) / (2 * eps)
            ex = pg_formula(theta, H, s0, si, ai)
            err = abs(fd - ex); worst = max(worst, err)
            print(f"{s0:>3} {si:>3} {ai:>3} {fd:>14.9f} {ex:>14.9f} {err:>10.2e}")
print(f"\nworst abs error: {worst:.3e}")
print("VERDICT:", "MATCH - statement is correct" if worst < 1e-6 else "MISMATCH - statement is WRONG")
