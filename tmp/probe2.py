import numpy as np
from scan import softmax, grad

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
    marks = [10**k for k in range(2, 7)]
    T = max(marks)
    snaps = {}
    tv_total = 0.0          # total variation of the policy path
    prev = softmax(th)
    for t in range(1, T + 1):
        G, V, pi = grad(P, r, g, mu, th)
        th = th + eta * G
        cur = softmax(th)
        tv_total += np.abs(cur - prev).sum()
        prev = cur
        if t in marks:
            snaps[t] = (cur.copy(), tv_total)
    print('=== trial', trial, 'S', S, 'A', A, 'gamma', g)
    print('r =\n', r)
    ks = sorted(snaps)
    for i in range(1, len(ks)):
        d = np.abs(snaps[ks[i]][0] - snaps[ks[i-1]][0]).max()
        print(f'  t={ks[i]:>8}  |dpi| since prev mark = {d:.3e}   cumulative TV = {snaps[ks[i]][1]:.4f}')
    print('  final pi =\n', np.round(snaps[ks[-1]][0], 6))
