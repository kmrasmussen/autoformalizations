NEW ROUTE with C9 in hand.

Assume goal fails at (s,ap): pibar(ap|s)=0, A+ = A^pibar(s,ap) > 0.
So hplus holds.

Partition actions by sign of A^pibar(s,.):
  I+ : A > 0  -> theta bounded BELOW  (not_theta_atBot_of_adv_pos)
  I- : A < 0  -> theta -> -inf        (C9: theta_tendsto_atBot_of_adv_neg)
  I0 : A = 0  -> ???

Conservation: sum_a theta_t(s,a) = const = c.
max_a theta_t -> +inf (C7).
So sum over I+ is bounded below; sum over I- -> -inf.
For the total to stay CONSTANT while max -> +inf:
   sum_{I0} theta_t  =  c - sum_{I+} theta_t - sum_{I-} theta_t
   sum_{I-} theta_t -> -inf, so -sum_{I-} -> +inf.
   Hence  sum_{I0} theta_t + sum_{I+} theta_t  ->  ... need care.

KEY: the max must be achieved in I0 or I+ (since I- -> -inf).
  I+ actions: is theta bounded ABOVE?  pi_t(a|s) -> 0 for a in I+ (C4/R2 applies
  to EVERY a in I+ since A^pibar>0 => pibar(a|s)=0 by tendsto_pi_zero_of_adv_pos).
  So all I+ actions have pi -> 0.  All I- actions have pi -> 0 too?
    a in I-: theta -> -inf and some coord bounded below => pi -> 0. YES
    (pi_tendsto_zero_of_theta_atBot).
  So sum_{a in I0} pi_t(a|s) -> 1.   <== AKM Lemma C.4's conclusion, generalized.
  Hence I0 is NONEMPTY and max is attained in I0 eventually => 
     max_{a in I0} theta_t -> +inf.

NOW the contradiction (AKM's final chain), restricted to I0:
  0 = sum_a pi_t A_t 
    = sum_{I0} pi_t A_t + sum_{I+} pi_t A_t + sum_{I-} pi_t A_t
  For a in I+: A_t >= A+/2 > 0 eventually, pi_t > 0 => term > 0. In particular
     the ap term is >= pi_t(ap|s) * A+/2.
  For a in I-: A_t <= -Delta/2 < 0, and |A_t| <= 2/(1-g), so
     sum_{I-} pi_t A_t >= -(2/(1-g)) sum_{I-} pi_t.
  So:  sum_{I0} pi_t A_t <= -pi_t(ap|s)*A+/2 + (2/(1-g)) sum_{I-} pi_t.
  AKM's bound (a)/(b)/(c) show the RHS is < 0, because
     sum_{I-} pi_t / pi_t(ap|s) -> 0    (ratio: theta_{I-} -> -inf, theta_ap bounded below)
  THIS IS THE CRUX and it IS provable from what we have:
     for a in I-, pi_t(a|s)/pi_t(ap|s) = exp(theta_a - theta_ap) -> 0
     since theta_a -> -inf (C9) and theta_ap >= c (R1).
  => eventually sum_{I0} pi_t A_t < 0, i.e. sum_{I0} dV/dtheta(s,a) < 0,
  => sum_{I0} theta_t(s,a) is eventually strictly DECREASING.
  But max_{I0} theta_t -> +inf and each I0 theta is ... need bounded below.
     Hmm: need sum_{I0} theta_t -> +inf.  AKM get this via B_0 subset.
