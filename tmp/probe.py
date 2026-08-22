import numpy as np
from scan import softmax, grad, run

rng = np.random.default_rng(0)
cases = {}
for trial in range(300):
    S = int(rng.integers(1, 4)); A = int(rng.integers(2, 4))
    g = float(rng.choice([0.0, 0.3, 0.5, 0.9]))
    r = rng.integers(-1, 2, size=(S, A)).astype(float)
    P = rng.integers(0, 2, size=(S, A, S)).astype(float) + 1e-9
    P = P / P.sum(-1, keepdims=True)
    mu = np.ones(S) / S
    th0 = rng.normal(size=(S, A))
    cases[trial] = (S, A, g, r, P, mu, th0)

for trial in [63, 122, 276, 252, 97]:
    S, A, g, r, P, mu, th0 = cases[trial]
    eta = (1 - g) ** 2 / 5
    th = th0.copy()
    snaps = {}
    marks = [10**k for k in range(2, 8)]
    T = max(marks)
    for t in range(1, T + 1):
        G, V, pi = grad(P, r, g, mu, th)
        th = th + eta * G
        if t in marks:
            snaps[t] = pi.copy()
    print('=== trial', trial, 'S', S, 'A', A, 'gamma', g)
    print('r=\n', r)
    ks = sorted(snaps)
    for i in range(1, len(ks)):
        d = np.abs(snaps[ks[i]] - snaps[ks[i-1]]).max()
        print(f'  |pi({ks[i]}) - pi({ks[i-1]})|_inf = {d:.3e}')
    print('  final pi=\n', snaps[ks[-1]])
