WHERE THE PROOF STANDS (my route)

Assume goal FAILS at (s,ap): pibar(ap|s)=0 and A+ := A^pibar(s,ap) > 0.
PROVED so far (all axiom-clean):
  R1 theta_t(s,ap) bounded below                    [not_theta_atBot_of_adv_pos]
  R2 pi_t(ap|s) -> 0                                [tendsto_pi_coord + hzero]
  R3 max_a theta_t(s,a) -> +inf                     [tendsto_max_theta_atTop]
  R4 min_a theta_t(s,a) -> -inf                     [tendsto_min_theta_atBot]
  R5 exists fixed b, unbounded below                [exists_action_unbounded_below]
  R6 A^pibar(s,b) <= 0                              [adv_nonpos_of_unbounded_below]

REMAINING: derive False.
  Case A^pibar(s,b) < 0 : this is exactly AKM Lemma C.9's SETTING (delegated).
     But note: C.9 concludes theta_b -> -inf, which we ALREADY have (R5-ish).
     C.9 does NOT by itself give False.  The contradiction in AKM comes LATER,
     from Lemma C.11/C.12 + the final inequality chain (bounds (a),(b),(c)).
  Case A^pibar(s,b) = 0 : b is in I_0 but has theta -> -inf; AKM put such b in
     Bbar_0 and use Lemma C.10 (stable) + C.11 to show sum_{B_0} pi -> 1.

CONCLUSION: the residual is AKM's FINAL contradiction (their proof of Thm 5.1
after Lemma C.12), which needs:
   (i)  the B_0 / Bbar_0 partition of I_0                       [Lemma C.11]
   (ii) sum_{a in B_0} theta_t(s,a) -> +inf                     [Lemma C.12]
   (iii) the 3 bounds (a),(b),(c) giving sum_{B_0} pi_t A_t < 0 [final chain]
   (iv) contradiction: sum_{B_0} theta decreasing vs -> +inf
