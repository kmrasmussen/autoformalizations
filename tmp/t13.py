import math
# r=(1,0), gamma=0, single state. theta0=(0,0). Analytic: p=p1, A1=1-p=q, A2=-p
# dtheta1 = eta*p*q, dtheta2 = -eta*p*q  => d(theta1-theta2)=2*eta*p*q
# grad norm = eta? ||grad|| = sqrt((p q)^2+(p q)^2)= p q sqrt2. Sum p q -> ?
# let u=theta1-theta2, p=sigmoid(u), pq = p(1-p)= sigma'(u); du=2 eta pq
# So sum_t pq = sum_t du/(2 eta) = (u_T-u_0)/(2 eta). u grows like? du=2 eta sigma'(u)~2 eta e^{-u} for large u
# => e^u du = 2 eta dt => e^u = 2 eta t => u = ln(2 eta t). So sum pq = ln(2 eta T)/(2 eta) -> LOG DIVERGENCE. confirmed analytically.
eta=0.2
for T in [1e4,1e5,1e6,4e6]:
    u=math.log(2*eta*T)
    print(T, "predicted sum||grad|| =", round(math.sqrt(2)*u/(2*eta),3))
