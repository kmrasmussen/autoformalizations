import numpy as np

def sample_mdp(rng, S=None, A=None, gamma=None, mode='rand'):
    if S is None: S = rng.integers(2,6)
    if A is None: A = rng.integers(2,5)
    if gamma is None: gamma = rng.uniform(0.0,0.99)
    if mode=='grid':
        grid = np.array([-1,-0.5,0,0.5,1.0])
        r = grid[rng.integers(0,len(grid),size=(S,A))]
    elif mode=='coarse':
        grid = np.array([-1,0,1.0])
        r = grid[rng.integers(0,len(grid),size=(S,A))]
    elif mode=='bin':
        r = rng.integers(0,2,size=(S,A)).astype(float)
    else:
        r = rng.uniform(-1,1,size=(S,A))
    # transitions
    if mode in ('grid','coarse','bin') and rng.random()<0.5:
        # sparse/deterministic-ish transitions to create ties
        P = np.zeros((S,A,S))
        for s in range(S):
            for a in range(A):
                k = rng.integers(1,min(S,3)+1)
                idx = rng.choice(S,size=k,replace=False)
                P[s,a,idx] = 1.0/k
    else:
        alpha = rng.choice([0.1,0.3,1.0,3.0])
        P = rng.dirichlet(np.ones(S)*alpha, size=(S,A))
    return S,A,gamma,r,P

def value_iter(S,A,gamma,r,P,iters=3000,tol=1e-13):
    V = np.zeros(S)
    for _ in range(iters):
        Q = r + gamma*P@V
        Vn = Q.max(axis=1)
        if np.max(np.abs(Vn-V))<tol: V=Vn; break
        V = Vn
    Q = r + gamma*P@V
    return V,Q

def policy_eval(S,A,gamma,r,P,pi):
    Ppi = np.einsum('sa,sat->st',pi,P)
    rpi = (pi*r).sum(axis=1)
    V = np.linalg.solve(np.eye(S)-gamma*Ppi, rpi)
    Q = r + gamma*P@V
    return V,Q,Ppi

def occupancy(S,gamma,Ppi,mu):
    return np.linalg.solve((np.eye(S)-gamma*Ppi).T, mu)

def make_instance(rng, mode='rand', temp=None, opt_mode='uniform_argmax', astar_mode='min'):
    S,A,gamma,r,P = sample_mdp(rng, mode=mode)
    # softmax policy
    if temp is None: temp = rng.choice([0.2,1.0,3.0,10.0])
    logits = rng.normal(0,temp,size=(S,A))
    e = np.exp(logits - logits.max(axis=1,keepdims=True))
    pi = e/e.sum(axis=1,keepdims=True)
    Vstar,Qstar = value_iter(S,A,gamma,r,P)
    tolq = 1e-9
    argmax_set = Qstar >= Qstar.max(axis=1,keepdims=True) - tolq
    if opt_mode=='uniform_argmax':
        pistar = argmax_set/argmax_set.sum(axis=1,keepdims=True)
    elif opt_mode=='rand_argmax':
        w = rng.random((S,A))*argmax_set
        # ensure nonzero
        w = w + 1e-12*argmax_set
        pistar = w/w.sum(axis=1,keepdims=True)
    else: # single
        pistar = np.zeros((S,A))
        for s in range(S):
            idx = np.flatnonzero(argmax_set[s]); pistar[s, rng.choice(idx)]=1.0
    mu = rng.dirichlet(np.ones(S)*rng.choice([0.3,1.0,3.0]))
    mu = np.maximum(mu,1e-6); mu/=mu.sum()
    Vpi,Qpi,Ppi = policy_eval(S,A,gamma,r,P,pi)
    Adv = Qpi - Vpi[:,None]
    Ppistar = np.einsum('sa,sat->st',pistar,P)
    dpi = occupancy(S,gamma,Ppi,mu)
    dstar = occupancy(S,gamma,Ppistar,mu)
    mism = np.max(dstar/mu)
    supp = pistar > 1e-12
    # astar choice
    piastar = np.where(supp, pi, np.nan)
    if astar_mode=='max':   # adversarial: maximize c  -> pick max pi in support
        cvec = np.nanmax(piastar,axis=1)
    elif astar_mode=='min':
        cvec = np.nanmin(piastar,axis=1)
    else:
        # random supported
        cvec = np.empty(S)
        for s in range(S):
            idx=np.flatnonzero(supp[s]); cvec[s]=pi[s,rng.choice(idx)]
    c = cvec.min()
    m = (pi*Adv).max(axis=1)
    m = np.maximum(m,0.0)
    return dict(S=S,A=A,gamma=gamma,r=r,P=P,pi=pi,pistar=pistar,mu=mu,Vstar=Vstar,Qstar=Qstar,
                Vpi=Vpi,Qpi=Qpi,Adv=Adv,dpi=dpi,dstar=dstar,mism=mism,c=c,cvec=cvec,m=m,supp=supp,
                gap=float(mu@Vstar - mu@Vpi))
