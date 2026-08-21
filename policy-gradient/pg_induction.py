"""Verify the INDUCTIVE STEP of the finite-horizon PG theorem numerically.

Claim:  dV_{m+1}(s0) = [k=0 term]  +  gamma * sum_{s'} step(s0,s') * dV_m(s')
and that unfolding this recursion yields exactly the visitation-weighted formula.
Checking the step separately from the closed form tells us WHICH part is wrong
if something breaks later in Lean.
"""
import numpy as np
np.random.seed(1)
nS, nA, gamma = 3, 2, 0.9
P = np.random.rand(nS, nA, nS); P /= P.sum(axis=2, keepdims=True)
r = np.random.randn(nS, nA)

def policy(th):
    e = np.exp(th - th.max(axis=1, keepdims=True)); return e/e.sum(axis=1, keepdims=True)

def Vstack(th, m):
    pi = policy(th); Vs=[np.zeros(nS)]; Qs=[]
    for _ in range(m):
        Q = r + gamma*P.dot(Vs[-1]); Qs.append(Q); Vs.append((pi*Q).sum(axis=1))
    return Vs, Qs

def dV_fd(th, m, si, ai, eps=1e-6):
    tp=th.copy(); tp[si,ai]+=eps; tm=th.copy(); tm[si,ai]-=eps
    return (Vstack(tp,m)[0][m] - Vstack(tm,m)[0][m])/(2*eps)

def dpi(th, s, si, ai):
    pi=policy(th); out=np.zeros(nA)
    if si==s:
        for a in range(nA): out[a]=pi[s,a]*((1.0 if a==ai else 0.0)-pi[s,ai])
    return out

th = np.random.randn(nS,nA)*0.5
pi = policy(th)
step = np.einsum('sa,sat->st', pi, P)

print("=== inductive step: dV_{m+1}(s0) =?= k0term + gamma * sum_s' step * dV_m(s') ===")
worst=0
for m in range(0,5):
    Vs,Qs = Vstack(th, m+1)
    for si in range(nS):
        for ai in range(nA):
            lhs = dV_fd(th, m+1, si, ai)
            dVm = dV_fd(th, m, si, ai)          # vector over s0
            for s0 in range(nS):
                k0 = dpi(th,s0,si,ai) @ Qs[m][s0]     # Q with m steps remaining
                rec = gamma * (step[s0] @ dVm)
                err = abs(lhs[s0] - (k0+rec)); worst=max(worst,err)
    print(f"  m={m} -> m+1={m+1}: ok so far, worst={worst:.2e}")
print(f"\ninductive step worst error: {worst:.3e}")
print("VERDICT:", "STEP HOLDS" if worst<1e-6 else "STEP FAILS")
