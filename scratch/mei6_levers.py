import numpy as np
# KEY IDEA: make the objective CONSTANT in theta, so gradient = 0 everywhere,
# theta is constant, hstep holds, but gap > 0 forever.
# Vinf part: if r(s,a) is the SAME for all a, then sum_a pi(a) r(a) = r, constant.
# But entropy term tau*H(pi(s0)) still varies with theta. Hmm.
#
# Instead: TWO states? Or: note VsoftStar sup is over ALL policies including those
# NOT softmax-representable. With |A|=1 ... entropy is 0 always, everything constant!
print("=== |A| = 1 ===")
# Single action: pi(a)=1 forced. H = 0. Vinf = r. VinfSoft = r for EVERY policy.
# VsoftStar = r. gap = 0. Not a refutation (gap=0 <= 0). 
print("gap = 0, RHS = 0*(1-K)^t = 0. holds. not a refutation")

print()
print("=== The real lever: gradient is ZERO but gap > 0 ===")
# Take r(s,a) identical across a, say r=0 for all a. gamma=0.
# Vinf(pi) = 0 for all pi.  VinfSoft(pi) = tau*H(pi(s0)).
# VsoftStar = tau * max H = tau*log|A|  (uniform policy), attained.
# f(theta) = tau*H(softmax(theta)), maximized at uniform => theta const gives grad 0
# only at uniform. So pick theta0 NOT uniform -> grad nonzero. Doesn't freeze.
#
# BUT: softmax is shift invariant. Gradient of f lives in the subspace orthogonal to 1.
# theta_{t+1} = theta_t + eta*grad. Converges to uniform. gap->0. no good.
#
print("=== Lever that WORKS: |A|>=2, sup over ALL policies exceeds softmax range ===")
# Is VsoftStar attainable by a softmax policy? p* = softmax(r/tau) yes -> gap->0.
# So asymptotically the bound is fine; the issue is the RATE for small t.
# Refutation must be: gap_1 > gap_0 * (1-K) for K near 1. Confirmed numerically already.
tau=1.0
r=np.array([1.0,-1.0])
def softmax(z):
    z=z-z.max(); e=np.exp(z); return e/e.sum()
def H(p):
    p=np.clip(p,1e-300,1); return -(p*np.log(p)).sum()
def f(th): p=softmax(th); return p@r+tau*H(p)
pstar=softmax(r/tau); VS=pstar@r+tau*H(pstar)
def grad(th,h=1e-7):
    g=np.zeros(2)
    for i in range(2):
        e=np.zeros(2); e[i]=h; g[i]=(f(th+e)-f(th-e))/(2*h)
    return g
# t=1 with K = 0.9 => need gap1 <= 0.1*gap0
for theta0 in [np.array([0.0,10.0]), np.array([0.0,5.0]), np.array([0.0,20.0])]:
  for eta in [0.01,0.1,1.0]:
    th1=theta0+eta*grad(theta0)
    g0=VS-f(theta0); g1=VS-f(th1)
    K=0.9
    rhs=g0*(1-K)**1
    print(f"theta0={theta0} eta={eta}: gap0={g0:.6f} gap1={g1:.6f} RHS(K=0.9)={rhs:.6f} VIOLATED={g1>rhs}")
