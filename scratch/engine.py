import numpy as np
def softmax_rows(TH):
    Z=TH-TH.max(axis=1,keepdims=True); E=np.exp(Z); return E/E.sum(axis=1,keepdims=True)
def V_of(TH,P,r,gamma):
    pi=softmax_rows(TH); Ppi=np.einsum('sa,sax->sx',pi,P); rpi=np.einsum('sa,sa->s',pi,r)
    return np.linalg.solve(np.eye(len(rpi))-gamma*Ppi,rpi),pi,Ppi
def J_of(TH,P,r,gamma,mu): return V_of(TH,P,r,gamma)[0][mu]
def grad_of(TH,P,r,gamma,mu):
    S,A=TH.shape; V,pi,Ppi=V_of(TH,P,r,gamma)
    Q=r+gamma*np.einsum('sax,x->sa',P,V); Adv=Q-V[:,None]
    e=np.zeros(S); e[mu]=1.0
    d=(1-gamma)*np.linalg.solve((np.eye(S)-gamma*Ppi).T,e)
    return (1.0/(1-gamma))*d[:,None]*pi*Adv, d, V, Q, pi
def fd(TH,P,r,gamma,mu,h=1e-6):
    G=np.zeros_like(TH)
    for i in range(TH.shape[0]):
        for j in range(TH.shape[1]):
            Tp=TH.copy();Tp[i,j]+=h;Tm=TH.copy();Tm[i,j]-=h
            G[i,j]=(J_of(Tp,P,r,gamma,mu)-J_of(Tm,P,r,gamma,mu))/(2*h)
    return G
def optimal_policy(P,r,gamma):
    S,A,_=P.shape; V=np.zeros(S)
    for _ in range(200000):
        Q=r+gamma*np.einsum('sax,x->sa',P,V); Vn=Q.max(axis=1)
        if np.abs(Vn-V).max()<1e-14: V=Vn; break
        V=Vn
    Q=r+gamma*np.einsum('sax,x->sa',P,V)
    return Q.argmax(axis=1),Q,V
