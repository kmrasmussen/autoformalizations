"""Design check for the infinite-horizon extension.

(a) Does V_m converge geometrically to V_inf, at rate gamma^m?
    If |V_m - V_inf| <= C*gamma^m, then V_inf = lim V_m is well-defined and
    the finite-horizon work becomes the approximating sequence.
(b) Does the infinite-horizon PG formula hold, with d^pi(s) = sum_t gamma^t Pr(s_t=s)
    UNNORMALIZED (matching our `visit`)?
"""
import sys
import numpy as np
rng = np.random.default_rng(23)
nS,nA,gamma = 3,2,0.9
P = rng.random((nS,nA,nS)); P/=P.sum(axis=2,keepdims=True)
r = rng.normal(size=(nS,nA))
def policy(th):
    e=np.exp(th-th.max(axis=1,keepdims=True)); return e/e.sum(axis=1,keepdims=True)
th = rng.normal(size=(nS,nA))*0.5
pi = policy(th)

# V_inf by linear solve: V = (I - g*P_pi)^{-1} r_pi
Ppi = np.einsum('sa,sat->st', pi, P)
rpi = (pi*r).sum(axis=1)
Vinf = np.linalg.solve(np.eye(nS) - gamma*Ppi, rpi)

# V_m by our backward recursion
def Vm(m):
    V=np.zeros(nS)
    for _ in range(m): V=(pi*(r+gamma*P.dot(V))).sum(axis=1)
    return V

print("=== (a) geometric convergence of V_m -> V_inf ===")
print(f"{'m':>3} {'max|V_m - V_inf|':>20} {'ratio':>8}  (expect ~gamma=0.9)")
prev=None
for m in [5,10,20,40,80,160]:
    err = np.abs(Vm(m)-Vinf).max()
    ratio = (err/prev)**(1/(m-prev_m)) if prev else float('nan')
    print(f"{m:>3} {err:>20.12e} {ratio:>8.4f}" if prev else f"{m:>3} {err:>20.12e} {'--':>8}")
    prev, prev_m = err, m

# (b) infinite-horizon PG with UNNORMALIZED occupancy
def dpi_unnorm(s0, T=4000):
    d=np.zeros(nS); v=np.zeros(nS); v[s0]=1.0
    for t in range(T):
        d += (gamma**t)*v; v = v@Ppi
    return d

def Qinf(): return r + gamma*P.dot(Vinf)

def pg_inf(s0, si, ai):
    d = dpi_unnorm(s0); Q = Qinf(); tot=0.0
    for s in range(nS):
        dp = np.array([pi[s,a]*((1.0 if a==ai else 0.0)-pi[s,ai]) for a in range(nA)]) if si==s else np.zeros(nA)
        tot += d[s]*float(dp@Q[s])
    return tot

def fd(s0, si, ai, eps=1e-6):
    def J(t):
        p=policy(t); Pp=np.einsum('sa,sat->st',p,P); rp=(p*r).sum(axis=1)
        return np.linalg.solve(np.eye(nS)-gamma*Pp, rp)[s0]
    tp=th.copy(); tp[si,ai]+=eps; tm=th.copy(); tm[si,ai]-=eps
    return (J(tp)-J(tm))/(2*eps)

print("\n=== (b) infinite-horizon PG, UNNORMALIZED occupancy (no 1/(1-g)) ===")
worst=0.0
for s0 in range(nS):
    for si in range(nS):
        for ai in range(nA):
            a,b = fd(s0,si,ai), pg_inf(s0,si,ai)
            worst=max(worst,abs(a-b))
print(f"worst |finite-diff - PG formula| = {worst:.3e}")
if worst < 1e-6:
    print("PASS: infinite-horizon PG holds with UNNORMALIZED d^pi (matches our `visit`)")
else:
    print("FAIL"); sys.exit(1)
