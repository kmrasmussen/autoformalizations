import numpy as np
# COUNTEREXAMPLE: constant logits (independent of theta).
# S=Unit, A=Bool, gamma=0, r(s,true)=1, r(s,false)=0, tau=1.
# logits theta s a = 0  for all a  => softmax = uniform = (1/2,1/2)
# So F.toPolicy theta = uniform for EVERY theta.
# => w |-> VinfSoft M (F.toPolicy w) tau mu  is CONSTANT
# => gradient = 0  => hstep gives theta(t+1) = theta(t) + eta*0 = theta(t). Constant!
tau=1.0
# VinfSoft(uniform) = Vinf(uniform) + tau*H(uniform)
#   Vinf(uniform) = sum_a pi(a) r(a) = 0.5*1 + 0.5*0 = 0.5
#   H(uniform) = log 2
Vinf_unif = 0.5
H_unif = np.log(2)
VinfSoft_unif = Vinf_unif + tau*H_unif
print("VinfSoft(uniform) =", VinfSoft_unif)

# VsoftStar = sup over ALL policies pi of [ pi(true)*1 + tau*H(pi) ]
# = max over p in [0,1] of p + tau*(-p log p - (1-p)log(1-p))
from scipy.optimize import minimize_scalar
def negobj(p):
    if p<=0 or p>=1: return -(p*1.0)
    return -(p + tau*(-(p*np.log(p)+(1-p)*np.log(1-p))))
ps=np.linspace(1e-12,1-1e-12,10000001)
vals = ps + tau*(-(ps*np.log(ps)+(1-ps)*np.log(1-ps)))
i=vals.argmax()
print("argmax p =",ps[i],"VsoftStar =",vals[i])
VS=vals[i]
# closed form: p* = e^{1/tau}/(e^{1/tau}+1)
pstar=np.exp(1/tau)/(np.exp(1/tau)+1)
VSc = pstar + tau*(-(pstar*np.log(pstar)+(1-pstar)*np.log(1-pstar)))
print("closed form p*=",pstar,"VsoftStar=",VSc)
# Simpler closed form: max_p [p*r1+(1-p)*r0 + tau H] = tau*log(e^{r1/tau}+e^{r0/tau})
lse = tau*np.log(np.exp(1/tau)+np.exp(0/tau))
print("log-sum-exp form:", lse)

gap = VSc - VinfSoft_unif
print("GAP (constant for all t) =", gap, " > 0 ?", gap>0)

# The claim: gap <= gap*(1-K)^t.  With K=1/2, t=1: gap <= gap/2 => gap<=0. CONTRADICTION.
print("K=1/2,t=1: RHS =", gap*0.5, " claim gap<=RHS is", gap<=gap*0.5)
