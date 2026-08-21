"""REFERENCE IMPLEMENTATION: textbook REINFORCE, written independently of our
Lean definitions, then used to ground them.

Three estimates of dJ/dtheta, computed by genuinely different routes:
  (A) REINFORCE / score-function, from SAMPLED trajectories:
          grad = E[ sum_t gamma^t * G_t * dlog pi(a_t|s_t) ]
      This is what an RL practitioner actually writes. No Bellman recursion,
      no visitation matrix -- just rollouts and log-probs.
  (B) finite differences on the true J(theta)
  (C) our Lean formula: sum_k gamma^k sum_s visit(k) sum_a dpi(a|s) Q(s,a)

If (A) ~ (B) ~ (C), our Lean definitions describe the same object that a
working REINFORCE implementation computes.
"""
import numpy as np
rng = np.random.default_rng(7)

nS, nA, H, gamma = 3, 2, 5, 0.9
P = rng.random((nS, nA, nS)); P /= P.sum(axis=2, keepdims=True)
r = rng.normal(size=(nS, nA))
s0 = 0

def policy(th):
    e = np.exp(th - th.max(axis=1, keepdims=True)); return e / e.sum(axis=1, keepdims=True)

# ---------- (A) REINFORCE from sampled trajectories ----------
def reinforce_grad(th, n_eps=400_000):
    """Standard score-function estimator. Deliberately written the 'RL way'."""
    pi = policy(th)
    grad = np.zeros_like(th)
    for _ in range(n_eps):
        states, actions, rewards = [], [], []
        s = s0
        for _ in range(H):
            a = rng.choice(nA, p=pi[s])
            states.append(s); actions.append(a); rewards.append(r[s, a])
            s = rng.choice(nS, p=P[s, a])
        # return-to-go from each step
        G = 0.0; returns = [0.0]*H
        for t in reversed(range(H)):
            G = rewards[t] + gamma*G; returns[t] = G
        for t in range(H):
            st, at = states[t], actions[t]
            # dlog pi(at|st)/dtheta[st,:] = onehot(at) - pi[st,:]
            grad[st, :] += (gamma**t) * returns[t] * (-pi[st, :])
            grad[st, at] += (gamma**t) * returns[t]
    return grad / n_eps

# ---------- (B) finite differences on true J ----------
def J(th):
    """True expected discounted return, by exact backward recursion."""
    pi = policy(th); V = np.zeros(nS)
    for _ in range(H):
        V = (pi * (r + gamma * P.dot(V))).sum(axis=1)
    return V[s0]

def fd_grad(th, eps=1e-6):
    g = np.zeros_like(th)
    for i in range(nS):
        for j in range(nA):
            tp = th.copy(); tp[i,j] += eps; tm = th.copy(); tm[i,j] -= eps
            g[i,j] = (J(tp) - J(tm)) / (2*eps)
    return g

# ---------- (C) our Lean formula ----------
def lean_grad(th):
    pi = policy(th)
    Vs=[np.zeros(nS)]; Qs=[]
    for _ in range(H):
        Q = r + gamma*P.dot(Vs[-1]); Qs.append(Q); Vs.append((pi*Q).sum(axis=1))
    step = np.einsum('sa,sat->st', pi, P)
    g = np.zeros_like(th)
    for k in range(H):
        d = np.zeros(nS); d[s0]=1.0
        for _ in range(k): d = d @ step
        Q = Qs[H-1-k]
        for s in range(nS):
            for si in range(nS):
                if si != s: continue
                for ai in range(nA):
                    dp = np.array([pi[s,a]*((1.0 if a==ai else 0.0)-pi[s,ai]) for a in range(nA)])
                    g[si,ai] += (gamma**k) * d[s] * (dp @ Q[s])
    return g

th = rng.normal(size=(nS,nA))*0.5
print(f"J(theta) = {J(th):.6f}   (horizon {H}, gamma {gamma})\n")
B = fd_grad(th); C = lean_grad(th)
print("=== (B) finite-diff   vs  (C) LEAN FORMULA  [exact methods] ===")
print(f"max |B - C| = {np.abs(B-C).max():.3e}   {'MATCH' if np.abs(B-C).max()<1e-6 else 'MISMATCH'}\n")
print("=== (A) sampled REINFORCE  vs  (B) finite-diff  [Monte Carlo, expect ~1e-2] ===")
A = reinforce_grad(th)
print("           REINFORCE      finite-diff     lean-formula")
for i in range(nS):
    for j in range(nA):
        print(f"  th[{i},{j}]  {A[i,j]:>11.6f}  {B[i,j]:>13.6f}  {C[i,j]:>14.6f}")
err = np.abs(A-B).max()
print(f"\nmax |REINFORCE - finite-diff| = {err:.4f}  (Monte Carlo noise)")
print("VERDICT:", "ALL THREE AGREE" if err < 0.02 and np.abs(B-C).max()<1e-6 else "CHECK NEEDED")
