# SCRIPT: RAM-EYE-02
# Gamma-quotient fraction x + 1^2/(2x + 3^2/(2x + ...)) as x -> 0: does the direction still settle?
import importlib.util, sys
from mpmath import mp, mpf, gamma, log, fabs, degrees, atan
spec = importlib.util.spec_from_file_location('e1', 'ram_eye_01.py')
src = open('ram_eye_01.py').read().split('print(\'######## CONTROLS')[0]
exec(src)
mp.dps = 60
for x in (mpf('0.2'), mpf('0.05'), mpf(0)):
    Ns = (200, 201, 400, 401, 800, 801, 1600, 1601)
    res = run(lambda n, x=x: 2*x, lambda n: mpf((2*n-1)**2), set(Ns))
    tgt = 4*gamma((x+3)/4)**2/gamma((x+1)/4)**2 - x
    print('== x =', mp.nstr(x,3), ' closed-form K =', mp.nstr(tgt,12), ' arctan K =', mp.nstr(degrees(atan(tgt)),8))
    for N in Ns:
        Phi, K, v, u, det = res[N]
        print('   N=%5d  K_N=%s  u1=(%s,%s)  rank-one resid=%s  Phi=%s' % (N, K if isinstance(K,str) else mp.nstr(K,8), mp.nstr(u[0],6), mp.nstr(u[1],6), mp.nstr(det,3), mp.nstr(Phi,8)))
    if x > 0:
        e1 = fabs(res[800][1]-tgt); e2 = fabs(res[1600][1]-tgt)
        print('   measured K-error exponent between N=800 and 1600:', mp.nstr(log(e1/e2)/log(2), 5), ' (x =', mp.nstr(x,3), ')')
