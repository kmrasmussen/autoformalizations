import numpy as np

# Single state, two actions, gamma=0. Vinf(pi) = sum_a pi(a) r(a).
# VinfSoft(pi) = sum_a pi(a) r(a) + tau * H(pi)
# Parameter theta in R^{S x A} = R^2, policy = softmax(theta).
# VsoftStar = sup over ALL policies (not just softmax-representable) of VinfSoft.

r = np.array([1.0, -1.0])   # |r| <= 1  OK
tau = 1.0

def softmax(z):
    z = z - z.max()
    e = np.exp(z)
    return e / e.sum()

def H(p):
    p = np.clip(p, 1e-300, 1)
    return -(p*np.log(p)).sum()

def Vsoft_of_dist(p):
    return p @ r + tau*H(p)

# VsoftStar: maximize over the simplex. Closed form: p* propto exp(r/tau)
pstar = softmax(r/tau)
VsoftStar = Vsoft_of_dist(pstar)
print("pstar", pstar, "VsoftStar", VsoftStar)

# grid check that it's really the sup
best = max(Vsoft_of_dist(np.array([x,1-x])) for x in np.linspace(1e-9,1-1e-9,2000001))
print("grid sup", best, "diff", VsoftStar-best)

# Objective as a function of theta
def f(theta):
    return Vsoft_of_dist(softmax(theta))

def grad(theta, h=1e-6):
    g = np.zeros(2)
    for i in range(2):
        e = np.zeros(2); e[i]=h
        g[i] = (f(theta+e)-f(theta-e))/(2*h)
    return g

# Start FAR from optimum: theta0 makes pi put mass on the BAD action
theta0 = np.array([0.0, 10.0])
print("f(theta0)", f(theta0), "gap0", VsoftStar - f(theta0))

for eta in [0.1, 1.0, 10.0]:
    th = theta0.copy()
    th1 = th + eta*grad(th)
    gap1 = VsoftStar - f(th1)
    gap0 = VsoftStar - f(theta0)
    print(f"eta={eta}: gap0={gap0:.6f} gap1={gap1:.6f} ratio={gap1/gap0:.6f}")
    # Claim with K -> 1: gap1 <= gap0*(1-K)^1. As K->1, RHS -> 0.
    # So claim forces gap1 <= 0 i.e. theta1 already optimal. Is gap1 > 0?
    print("   gap1 > 0 ?", gap1 > 0)

print("\n=== CLEANEST REFUTATION: uniform theta (a stationary point) ===")
# theta = 0 constant: softmax(0)=uniform. Is gradient zero there?
# f(theta) = softmax(theta) @ r + tau H(softmax(theta)).
# grad wrt theta is NOT zero at 0 in general. Try theta = tuned so grad=0.
# Actually: softmax is shift-invariant, so f(theta + c*1) = f(theta).
# => gradient is always orthogonal to 1... but not zero.
# Stationary point: theta = r/tau + c*1 gives p = pstar, the max => grad = 0.
thstar = r/tau
print("grad at r/tau:", grad(thstar), "f =", f(thstar), "VsoftStar =", VsoftStar)
print("gap at stationary optimum:", VsoftStar - f(thstar))
