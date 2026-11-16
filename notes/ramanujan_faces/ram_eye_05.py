# SCRIPT: RAM-EYE-05
# The zeta(3) fraction failed the single-term face rule in RAM-EYE-04.  Its terms come in pairs
# (denominators 4,1,12,1,20,1,...), so try the other setup: one face = one PAIR of terms.
# z_k = |lam+/lam-| of the two-step matrix M_{2k-1} M_{2k}.  Same kill line as RAM-EYE-04.
from mpmath import mp, mpf, sqrt, zeta, log10, fabs, matrix
mp.dps = 80
a = lambda n: mpf(4*n) if n%2==1 else mpf(1)
b = lambda n: mpf(1) if n==1 else mpf((n//2)**3)
K = zeta(3)-1
pm, p, qm, q = mpf(1), mpf(0), mpf(0), mpf(1); logZ = mpf(0); rows = []
for k in range(1, 12801):
    for n in (2*k-1, 2*k):
        pm, p = p, a(n)*p + b(n)*pm
        qm, q = q, a(n)*q + b(n)*qm
    A = matrix([[0,b(2*k-1)],[1,a(2*k-1)]])*matrix([[0,b(2*k)],[1,a(2*k)]])
    tr = A[0,0]+A[1,1]; det = A[0,0]*A[1,1]-A[0,1]*A[1,0]
    s = sqrt(tr*tr-4*det)
    logZ += log10(fabs((tr+s)/(tr-s))) if tr >= 0 else log10(fabs((tr-s)/(tr+s)))
    if k in (50,200,800,3200,12800):
        err = fabs(p/q-K); rows.append((k, log10(err), logZ, log10(err)+logZ))
for k, le, lz, s_ in rows:
    print('   pairs=%6d (terms=%6d)  log10 error = %9s   log10 prod z = %9s   sum = %s' % (k, 2*k, mp.nstr(le,7), mp.nstr(lz,7), mp.nstr(s_,7)))
print('   error moved %s orders; (error x prod z) moved %s orders' % (mp.nstr(rows[-1][1]-rows[0][1],5), mp.nstr(rows[-1][3]-rows[0][3],5)))
