"""Confirm the exact index bookkeeping of the closed form BEFORE proving it in Lean.
Nat subtraction (m-1-k) is a classic source of off-by-one pain, so pin it down.

Claim:  dV_m(s0) = sum_{k<m} gamma^k * sum_s visit(k,s0,s) * localTerm_{m-1-k}(s)
where localTerm_j(s) = sum_a dpi(a|s) * Q_j(s,a).
"""
import numpy as np
rng = np.random.default_rng(3)
nS, nA, gamma = 3, 2, 0.9
P = rng.random((nS,nA,nS)); P /= P.sum(axis=2,keepdims=True)
r = rng.normal(size=(nS,nA))
def policy(th):
    e=np.exp(th-th.max(axis=1,keepdims=True)); return e/e.sum(axis=1,keepdims=True)

th = rng.normal(size=(nS,nA))*0.5
pi = policy(th); stepM = np.einsum('sa,sat->st', pi, P)

def Qstack(m):
    Vs=[np.zeros(nS)]; Qs=[]
    for _ in range(m):
        Q = r + gamma*P.dot(Vs[-1]); Qs.append(Q); Vs.append((pi*Q).sum(axis=1))
    return Vs,Qs

def localTerm(j, s, si, ai):
    """sum_a dpi(a|s) * Q_j(s,a);  Q_j = Qs[j] means j steps remaining after action"""
    if si != s: return 0.0
    _,Qs = Qstack(max(j,1)+1)
    Qj = Qs[j] if j < len(Qs) else None
    if j == 0:
        Qj = r + gamma*P.dot(np.zeros(nS))   # Q_0 = r
    dp = np.array([pi[s,a]*((1.0 if a==ai else 0.0)-pi[s,ai]) for a in range(nA)])
    return dp @ Qj[s]

def dV_recursive(m, s0, si, ai):
    """the recursion we PROVED: dV_{m+1}(s) = localTerm_m(s) + g*sum_s' step*dV_m(s')"""
    d = np.zeros(nS)
    for j in range(m):
        newd = np.array([localTerm(j, s, si, ai) + gamma*(stepM[s] @ d) for s in range(nS)])
        d = newd
    return d[s0]

def dV_closed(m, s0, si, ai):
    """sum_{k<m} g^k sum_s visit(k) localTerm_{m-1-k}(s)"""
    tot=0.0
    for k in range(m):
        v=np.zeros(nS); v[s0]=1.0
        for _ in range(k): v = v @ stepM
        j = m-1-k
        for s in range(nS):
            tot += (gamma**k)*v[s]*localTerm(j, s, si, ai)
    return tot

print("m  s0 si ai   recursive      closed-form     diff")
worst=0
for m in range(1,6):
    for s0 in range(nS):
        for si in range(nS):
            for ai in range(nA):
                a=dV_recursive(m,s0,si,ai); b=dV_closed(m,s0,si,ai)
                worst=max(worst,abs(a-b))
    print(f"{m}  ...all s0/si/ai ok, running worst={worst:.2e}")
print(f"\nworst |recursive - closed| = {worst:.3e}")
print("VERDICT:", "INDEXING CORRECT (m-1-k)" if worst<1e-9 else "OFF-BY-ONE SOMEWHERE")
