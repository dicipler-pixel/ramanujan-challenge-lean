# SCRIPT: RAM-EYE-04
# Discriminating version of the face test.  RAM-EYE-03 only used the gamma fraction, where the product of the
# face ratios is itself ~ N^x, so it could not tell the face reading from the plain power law.
# Here the SAME rule (error after N terms  x  z_1...z_N, with z_n = |lam+/lam-| of the n-th step matrix)
# is applied to fractions that converge by DIFFERENT laws: geometric, factorial, stretched-exponential, power.
# Kill line written before the run: if log10(error x product z) moves by more than a slowly varying
# (logarithmic-in-N) amount while the error itself moves by many orders, the face rule fails for that fraction.
from mpmath import mp, mpf, sqrt, pi, e, erfc, zeta, gamma, log10, fabs
def run(name, a, b, K, Ns, dps):
    mp.dps = dps
    K = K()
    pm, p, qm, q = mpf(1), mpf(0), mpf(0), mpf(1)      # tail K = b1/(a1 + b2/(a2+...)) = p_N/q_N
    logZ = mpf(0); rows = []
    for n in range(1, max(Ns)+1):
        an, bn = mpf(a(n)), mpf(b(n))
        pm, p = p, an*p + bn*pm
        qm, q = q, an*q + bn*qm
        s = sqrt(an*an + 4*bn)
        logZ += log10(fabs((an + s)/(an - s))) if an >= 0 else log10(fabs((an - s)/(an + s)))
        if n in Ns:
            err = fabs(p/q - K)
            rows.append((n, log10(err), logZ, log10(err) + logZ))
    print('==', name)
    for n, le, lz, s_ in rows:
        print('   N=%6d   log10 error = %10s   log10 prod z = %10s   sum = %s' % (n, mp.nstr(le,7), mp.nstr(lz,7), mp.nstr(s_,7)))
    print('   error moved %s orders; (error x prod z) moved %s orders' % (mp.nstr(rows[-1][1]-rows[0][1],5), mp.nstr(rows[-1][3]-rows[0][3],5)))
    last = rows[-1]; prev = rows[-2]
    print('   mean log10 z per face over the last span = %s' % mp.nstr((last[2]-prev[2])/(last[0]-prev[0]),6))

run('Challenge pi fraction Q1 (geometric)', lambda n: -220*n**3-484*n**2-301*n-42, lambda n: 4*n*n*(2*n+1)**2*(5*n-4)*(5*n+6),
    lambda: 6*(22-7*pi)/(3-pi), (10,20,40,80,160), 500)
run('e fraction 1/(1+2/(2+3/(3+...))) (factorial)', lambda n: n, lambda n: n, lambda: 1/(e-1), (10,20,40,80,160), 700)
run('pi fraction 1^2/(3+2^2/(5+...)) (geometric)', lambda n: 2*n+1, lambda n: n*n, lambda: (4-pi)/pi, (10,20,40,80,160), 400)
run('sqrt(pi e/2) fraction 1/(1+1/(1+2/(1+...))) (stretched exponential)', lambda n: 1, lambda n: 1 if n==1 else n-1,
    lambda: sqrt(pi*e/2)*erfc(1/sqrt(mpf(2))), (100,400,1600,6400,25600), 200)
run('zeta(3) fraction (power law N^-6)', lambda n: 4*n if n%2==1 else 1, lambda n: 1 if n==1 else (n//2)**3,
    lambda: zeta(3)-1, (100,400,1600,6400,25600), 80)
run('gamma fraction x=1, Brouncker (power law N^-1)', lambda n: 2, lambda n: (2*n-1)**2,
    lambda: 4*gamma(mpf(1))**2/gamma(mpf(1)/2)**2 - 1, (100,400,1600,6400,25600), 60)
run('gamma fraction x=10 (power law N^-10)', lambda n: 20, lambda n: (2*n-1)**2,
    lambda: 4*gamma(mpf(13)/4)**2/gamma(mpf(11)/4)**2 - 10, (100,400,1600,6400,25600), 120)
