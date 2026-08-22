import numpy as np
tau=1.0
def obj(p): return p*1.0 + tau*(-(p*np.log(p)+(1-p)*np.log(1-p)))
print("uniform (p=1/2):", obj(0.5))
for p in [0.6,0.7,0.75,0.73]:
    print(f"p={p}: {obj(p)}  beats uniform? {obj(p)>obj(0.5)}")
# Witness p=3/4: value = 3/4 + (-(3/4 log 3/4 + 1/4 log 1/4))
p=0.75
v=obj(p); u=obj(0.5)
print("witness 3/4 value",v,"uniform",u,"margin",v-u)
# Exact symbolic: obj(3/4) = 3/4 + (3/4)log(4/3) + (1/4)log(4)
#                obj(1/2) = 1/2 + log 2
import math
exact_v = 0.75 + 0.75*math.log(4/3) + 0.25*math.log(4)
exact_u = 0.5 + math.log(2)
print("exact witness",exact_v,"exact uniform",exact_u,"margin",exact_v-exact_u)
# margin = 1/4 + (3/4)log(4/3) + (1/4)log4 - log2
#        = 1/4 + (3/4)(log4-log3) + (1/4)log4 - log2
#        = 1/4 + log4 - (3/4)log3 - log2 = 1/4 + 2log2 - (3/4)log3 - log2
#        = 1/4 + log2 - (3/4)log3
m = 0.25 + math.log(2) - 0.75*math.log(3)
print("simplified margin:", m, "positive?", m>0)
