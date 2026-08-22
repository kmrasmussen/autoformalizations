AKM C.1 structure:
 theta_s^{t+1} = theta_s^t + eta * grad_s V(mu)
 grad_s V(mu)[a] = dinfDist(s) * pi(a|s) * A(s,a)          [repo, unnormalized d]
                 = dinfDist(s) * grad_s F_s [a]             [by dg_adv_single]
 So the step IS a gradient step on F_s with effective step  eta * dinfDist(s).
 F_s is beta-smooth with beta = C*B, B = sup|A| <= 1/(1-g).
 Need: eta * dinfDist(s) <= 1/beta.
 dinfDist(s) <= 1/(1-g)   [repo unnormalized]
 => need eta/(1-g) <= (1-g)/C  => eta <= (1-g)^2/C.
 Goal gives eta <= (1-g)^2/5.  So C=5 suffices exactly; C=6 does NOT.
