FINAL CONTRADICTION (AKM Thm 5.1 proof, adapted):

Assume: pibar(a+|s)=0 and A^pibar(s,a+) > 0.   [negation of goal]
Known (proved in Resid.lean):
 (1) advInf_eq_zero_on_support: pibar(a|s)>0  =>  A^pibar(s,a)=0.
 (2) sum_pi_advInf_self at pibar: sum_a pibar(a|s) A^pibar(s,a) = 0.   [auto from (1)]
 (3) theta_t(s,a+) bounded below (theta_eventually_monotone).
 (4) max_a theta_t(s,a) -> +inf (tendsto_max_theta_atTop).
 (5) sum_a theta_t(s,a) constant (sum_theta_const).
 (6) [C8, delegated] min_a theta_t(s,a) -> -inf.
 (7) [C9, delegated] a in I_-  =>  theta_t(s,a) -> -inf.

AKM final step needs the B^s_0 partition:
  B_0 = { a in I_0 : pi_t(a+|s) < pi_t(a|s) for all t >= T0 }
  Then sum_{a in B_0} pi_t(a|s) -> 1, and sum_{a in B_0} theta_t(s,a) -> +inf.
  But bound (a),(b),(c) show sum_{a in B_0} pi_t A_t < 0 eventually,
  i.e. sum_{a in B_0} dV/dtheta(s,a) < 0, so sum_{a in B_0} theta_t(s,a)
  is eventually DECREASING -> contradiction with -> +inf.

KEY REMAINING PIECES beyond (6),(7):
 (8) Lemma C.10 (stable): pi_t(a|s) <= pi_t(a+|s) is preserved forward in t.
 (9) Lemma C.11 (thetab-diverge): B_0 nonempty, sum_{B_0} pi -> 1, max_{B_0} theta -> +inf.
 (10) Lemma C.12 (sum-bs-theta): sum_{B_0} theta_t -> +inf.
 (11) the three bounds (a),(b),(c) and the final inequality chain.
