# autoformalizations

Machine-checked formalizations of results that had only informal proofs.

## Projects

### [`policy-gradient/`](policy-gradient/) — the policy gradient theorem

The foundational theorem of policy-gradient reinforcement learning, proved in
Lean 4 + Mathlib for finite-horizon finite MDPs. No `sorry`; `#print axioms`
gives only the three standard Lean axioms.

Apparently the first formalization of this theorem in any proof assistant —
existing RL formalization (CertRL in Coq, Schäffeler–Abdulaziz in Isabelle,
Zhang in Lean) is all value-based: value/policy iteration, Q-learning, TD.

It also closes two gaps in the textbook proof: the "after several steps of
unrolling" hand-wave in Sutton et al. (NIPS 1999), and a use of
Chapman–Kolmogorov that no informal treatment states.
