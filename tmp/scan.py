import numpy as np

def softmax(z):
    z = z - z.max(-1, keepdims=True)
    e = np.exp(z)
    return e / e.sum(-1, keepdims=True)

def grad(P, r, g, mu, th):
    S, A, _ = P.shape
    pi = softmax(th)
    Ppi = np.einsum('sa,sat->st', pi, P)
    rpi = (pi * r).sum(1)
    V = np.linalg.solve(np.eye(S) - g * Ppi, rpi)
    Q = r + g * (P @ V)
    Adv = Q - V[:, None]
    d = (1 - g) * np.linalg.solve((np.eye(S) - g * Ppi).T, mu)
    G = (d[:, None] * pi * Adv) / (1 - g)
    return G, V, pi

def run(P, r, g, mu, th0, eta, T, rec_from):
    th = th0.copy()
    traj = []
    for t in range(T):
        G, V, pi = grad(P, r, g, mu, th)
        th = th + eta * G
        if t >= rec_from:
            traj.append(pi.copy())
    return np.array(traj), th

if __name__ == '__main__':
    rng = np.random.default_rng(0)
    worst = []
    for trial in range(300):
        S = int(rng.integers(1, 4)); A = int(rng.integers(2, 4))
        g = float(rng.choice([0.0, 0.3, 0.5, 0.9]))
        r = rng.integers(-1, 2, size=(S, A)).astype(float)   # integer grid -> ties
        P = rng.integers(0, 2, size=(S, A, S)).astype(float) + 1e-9
        P = P / P.sum(-1, keepdims=True)
        mu = np.ones(S) / S
        eta = (1 - g) ** 2 / 5
        th0 = rng.normal(size=(S, A))
        T = 20000
        traj, th = run(P, r, g, mu, th0, eta, T, T // 2)
        osc = float(np.abs(traj - traj[-1]).max())
        worst.append((osc, trial, S, A, g))

    worst.sort(reverse=True)
    for w in worst[:12]:
        print(w)
