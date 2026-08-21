"""INDEPENDENT check: does our V match the value function computed by methods
that do NOT use our backward recursion at all?

Route 1: direct linear solve  V = (I - gamma*P_pi)^{-1} r_pi   [infinite horizon]
Route 2: brute-force enumeration over ALL trajectories, weighting each by its
         probability and summing discounted rewards. This is the DEFINITION of
         expected return -- no recursion, no Bellman, no linear algebra.
Route 3: our backward recursion.

Route 2 is the real arbiter: it is literally 'sum over trajectories of
P(traj) * discounted return', i.e. what J(theta) MEANS.
"""
import sys
import numpy as np, itertools
rng = np.random.default_rng(11)
nS, nA, H, gamma = 3, 2, 4, 0.9
P = rng.random((nS,nA,nS)); P /= P.sum(axis=2,keepdims=True)
r = rng.normal(size=(nS,nA))
th = rng.normal(size=(nS,nA))*0.5
def policy(t):
    e=np.exp(t-t.max(axis=1,keepdims=True)); return e/e.sum(axis=1,keepdims=True)
pi = policy(th); s0=0

# Route 3: our backward recursion (what Value.lean defines)
V = np.zeros(nS)
for _ in range(H):
    V = (pi*(r + gamma*P.dot(V))).sum(axis=1)
ours = V[s0]

# Route 2: brute force over every trajectory of length H
total = 0.0
for actions in itertools.product(range(nA), repeat=H):
    for states in itertools.product(range(nS), repeat=H-1):
        traj_s = (s0,)+states
        p = 1.0; disc = 0.0
        for t in range(H):
            s,a = traj_s[t], actions[t]
            p *= pi[s,a]
            disc += (gamma**t)*r[s,a]
            if t < H-1:
                p *= P[s,a,traj_s[t+1]]
        total += p*disc
brute = total

print(f"Route 3 (our backward recursion):     {ours:.12f}")
print(f"Route 2 (brute-force trajectories):   {brute:.12f}")
print(f"difference: {abs(ours-brute):.3e}")
print()
print()
print("Route 2 enumerates trajectories and applies the DEFINITION of expected")
print("return directly -- no Bellman recursion, no Q, no visitation measure.")
print("It is the one check Lean cannot do for us: Lean proves the theorem")
print("follows from the definitions; this checks the definitions are right.")
print()

TOL = 1e-10
if abs(ours - brute) < TOL:
    print(f"PASS: V is the expected discounted return (diff {abs(ours-brute):.2e} < {TOL:g})")
else:
    print(f"FAIL: V does NOT match the definition (diff {abs(ours-brute):.2e} >= {TOL:g})")
    sys.exit(1)
