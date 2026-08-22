import numpy as np, itertools
from scan import softmax, grad

# Deliberate tie-seeded search: integer rewards, small MDPs, many inits.
# Diagnostic = does cumulative total variation of the policy path saturate?
rng = np.random.default_rng(12345)
worst = []
N = 0
for trial in range(2000):
    S = int(rng.integers(1, 4)); A = int(rng.integers(2, 4))
    g = float(rng.choice([0.0, 0.5, 0.9, 0.99]))
    r = rng.integers(-1, 2, size=(S, A)).astype(float)
    # deterministic transitions -> maximises chance of Q* ties
    P = np.zeros((S, A, S))
    for s in range(S):
        for a in range(A):
            P[s, a, int(rng.integers(0, S))] = 1.0
    mu = np.ones(S) / S
    eta = (1 - g) ** 2 / 5
    th = rng.normal(size=(S, A)) * float(rng.choice([0.1, 1.0, 3.0]))
    T = 200000
    tv_early = 0.0; tv_late = 0.0
    prev = softmax(th)
    for t in range(1, T + 1):
        G, V, pi = grad(P, r, g, mu, th)
        th = th + eta * G
        cur = softmax(th)
        d = np.abs(cur - prev).sum()
        if t <= T // 2: tv_early += d
        else: tv_late += d
        prev = cur
    N += 1
    worst.append((tv_late, tv_early, trial, S, A, g))

worst.sort(reverse=True)
print('ran', N)
print('largest SECOND-HALF total variation (would be ~0 if all converge):')
for w in worst[:15]:
    print(f'  tv_late={w[0]:.5f}  tv_early={w[1]:.4f}  trial={w[2]} S={w[3]} A={w[4]} g={w[5]}')
