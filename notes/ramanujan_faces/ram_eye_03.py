# SCRIPT: RAM-EYE-03
# Read each step of Ramanujan's gamma fraction as one face of a stack (the mixer's feed operator):
# step matrix [[0,b_n],[1,2x]], b_n=(2n-1)^2. Its two eigenvalues are x +- sqrt(x^2+m^2), m=2n-1.
# Face rapidity r_n = ln|lam+/lam-|, face Gamma_n = tanh(r_n/2).  Claim under test:
#   (1) Gamma_n = x/sqrt(x^2+m^2) exactly;  (2) K error at depth N = C * exp(-sum_{n<=N} r_n), C constant in N.
from mpmath import mp, mpf, sqrt, log, tanh, exp, gamma, fabs, matrix
mp.dps = 60
for x in (mpf(1)/2, mpf(1), mpf(3), mpf(10)):
    tgt = 4*gamma((x+3)/4)**2/gamma((x+1)/4)**2 - x
    P = matrix([[1,0],[0,1]]); R = mpf(0); worst = mpf(0)
    print('== x =', mp.nstr(x,4))
    for n in range(1, 6401):
        m = 2*n-1; s = sqrt(x*x+m*m)
        r = log((s+x)/(s-x)); R += r
        worst = max(worst, fabs(tanh(r/2) - x/s))
        P = P*matrix([[0, m*m],[1, 2*x]]); P = P/sqrt(sum(P[i,j]**2 for i in range(2) for j in range(2)))
        if n in (100, 400, 1600, 6400):
            err = fabs(P[0,1]/P[1,1] - tgt)
            print('   N=%5d  sum r = %s   K err = %s   K err * exp(sum r) = %s' % (n, mp.nstr(R,10), mp.nstr(err,6), mp.nstr(err*exp(R),10)))
    print('   max |tanh(r_n/2) - x/sqrt(x^2+m^2)| over 6400 faces:', mp.nstr(worst,3))
    print('   faces with Gamma^2 >= 1/2 (at or above the wall): m <= x, i.e. m in', [2*n-1 for n in range(1,40) if (2*n-1) <= x])
print('wall check: x=1, first face: Gamma^2 =', mp.nstr(mpf(1)/(1+1),5), '  z = (sqrt2+1)/(sqrt2-1) =', mp.nstr((sqrt(2)+1)/(sqrt(2)-1),15), '  3+2sqrt2 =', mp.nstr(3+2*sqrt(2),15))
