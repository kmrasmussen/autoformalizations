import numpy as np
# Tight witness from fin.py, state 1 dominates everything:
mu=np.array([0.00224301,0.99775699]); dst=np.array([0.00243637,1.09783889])
dpi=np.array([0.09719398,1.00308128]); m=np.array([2.93426921e-06,2.12302260e-02])
Xp=np.array([4.14045114e-06,9.80210586e-01]); c=0.02165884181349391; mism=1.1003068966099268
print("c*dst[1]*X+[1] =",c*dst[1]*Xp[1])
print("mism*dpi[1]*m[1] =",mism*dpi[1]*m[1])
print("ratio per-state at 1:", c*dst[1]*Xp[1]/(mism*dpi[1]*m[1]))
# So the tightness is PER-STATE at the dominant state. c*X+ vs m*(mism*dpi/dst):
print("c*X+[1] =",c*Xp[1], " m[1]*mism*dpi[1]/dst[1] =", m[1]*mism*dpi[1]/dst[1])
