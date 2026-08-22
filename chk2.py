# Is  invMuSup(mu) * mismatchCoeff  <=  1/(1-g)^3  provable?
# mismatchCoeff >= 1 always; invMuSup = 1/min mu >= |S|.
# Take |S| large or mu lopsided with gamma small: 1/(1-g)^3 -> 1.
# g=0: dinfDist = mu, so mismatchCoeff = 1; invMuSup = 1/min mu.
# Need 1/min mu <= 1.  False whenever min mu < 1, i.e. |S| >= 2.
print("At gamma=0, |S|=2, mu=(1/2,1/2): invMuSup*m = 2*1 = 2 > 1/(1-0)^3 = 1  -> FALSE")
