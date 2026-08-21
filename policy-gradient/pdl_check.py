"""Pin down the FINITE-HORIZON performance difference lemma before proving it.

Infinite horizon (Agarwal et al. Lemma 3.2):
  V^pi(s0) - V^pi'(s0) = 1/(1-g) * E_{s~d^pi} E_{a~pi} [ A^pi'(s,a) ]
with d^pi NORMALIZED. Our `visit` is UNNORMALIZED, so the 1/(1-g) should
vanish and be replaced by an explicit sum over k < m. Candidate:

  V_m^pi(s0) - V_m^pi'(s0)
      = sum_{k<m} g^k * sum_s visit^pi(k,s0,s) * sum_a pi(a|s) * A^pi'_{m-1-k}(s,a)

where A^pi'_j(s,a) = Q^pi'_j(s,a) - V^pi'_{j+1}(s).
NOTE the index on V: Q_j pairs with V_{j+1}, since Q_j(s,a)=r+g*sum P*V_j
and V_{j+1}(s)=sum_a pi(a|s) Q_j(s,a). Getting this wrong is the classic bug.
"""
import sys
import numpy as np
rng = np.random.default_rng(17)
nS, nA, gamma = 3, 2, 0.9
P = rng.random((nS,nA,nS)); P /= P.sum(axis=2,keepdims=True)
r = rng.normal(size=(nS,nA))

def mk_policy(seed):
    g = np.random.default_rng(seed)
    p = g.random((nS,nA)); return p / p.sum(axis=1,keepdims=True)

pi  = mk_policy(1)     # the "new" policy
pip = mk_policy(2)     # pi' , the "old" / comparison policy

def VQ(policy, m):
    """Vs[j] = V_j (j steps remaining), Qs[j] = Q_j."""
    Vs=[np.zeros(nS)]; Qs=[]
    for _ in range(m):
        Q = r + gamma*P.dot(Vs[-1]); Qs.append(Q); Vs.append((policy*Q).sum(axis=1))
    return Vs, Qs

def visit(policy, k, s0):
    step = np.einsum('sa,sat->st', policy, P)
    d = np.zeros(nS); d[s0]=1.0
    for _ in range(k): d = d @ step
    return d

def lhs(m, s0):
    return VQ(pi, m)[0][m][s0] - VQ(pip, m)[0][m][s0]

def rhs(m, s0):
    Vsp, Qsp = VQ(pip, m)      # pi' value/action-value stacks
    tot = 0.0
    for k in range(m):
        d = visit(pi, k, s0)
        j = m-1-k
        for s in range(nS):
            if d[s]==0: continue
            # advantage of pi' at horizon j: Q_j(s,a) - V_{j+1}(s)
            adv = Qsp[j][s] - Vsp[j+1][s]
            tot += (gamma**k) * d[s] * float((pi[s] * adv).sum())
    return tot

print(f"{'m':>2} {'s0':>3} {'LHS (V^pi - V^pi\')':>22} {'RHS (PDL)':>18} {'diff':>10}")
worst = 0.0
for m in range(1,7):
    for s0 in range(nS):
        a, b = lhs(m,s0), rhs(m,s0)
        worst = max(worst, abs(a-b))
        if m <= 3:
            print(f"{m:>2} {s0:>3} {a:>22.12f} {b:>18.12f} {abs(a-b):>10.1e}")
print(f"\nworst |LHS - RHS| over m=1..6, all s0: {worst:.3e}")
if worst < 1e-10:
    print("PASS: finite-horizon PDL confirmed, with A_j = Q_j - V_{j+1} and NO 1/(1-g)")
else:
    print("FAIL: statement is wrong")
    sys.exit(1)
