# SCRIPT: RAM-EYE-01
# Projector eye (Phi = 1/2 ||[P,P^T]||_F^2 on the Frobenius-normalised cumulative product)
# run on (a) three controls with stored answers, (b) Ramanujan's own continued fractions.
from mpmath import mp, mpf, matrix, sqrt, pi, e, gamma, erfc, exp, asin, atan, degrees, zeta, log10, fabs
mp.dps = 80

def run(a, b, Ns):
    # tail K = b1/(a1 + b2/(a2 + ...)); P_N = prod_{k=1..N} [[0,b_k],[1,a_k]] = [[p_{N-1},p_N],[q_{N-1},q_N]]
    P = matrix([[1,0],[0,1]]); out = {}
    for k in range(1, max(Ns)+1):
        M = matrix([[0, b(k)],[1, a(k)]])
        P = P*M
        f = sqrt(sum(P[i,j]**2 for i in range(2) for j in range(2)))
        P = P/f
        if k in Ns:
            C = P*P.T - P.T*P
            Phi = sum(C[i,j]**2 for i in range(2) for j in range(2))/2
            K = (P[0,1]/P[1,1]) if P[1,1] != 0 else 'infinite (denominator is exactly 0)'
            # right direction v1 = dominant row, left direction u1 = dominant column
            r = [P[0,0],P[0,1]] if P[0,0]**2+P[0,1]**2 > P[1,0]**2+P[1,1]**2 else [P[1,0],P[1,1]]
            c = [P[0,1],P[1,1]] if P[0,1]**2+P[1,1]**2 > P[0,0]**2+P[1,0]**2 else [P[0,0],P[1,0]]
            nr = sqrt(r[0]**2+r[1]**2); nc = sqrt(c[0]**2+c[1]**2)
            det = fabs(P[0,0]*P[1,1]-P[0,1]*P[1,0])   # ~ sigma2/sigma1 after normalisation
            out[k] = (Phi, K, [x/nr for x in r], [x/nc for x in c], det)
    return out

def report(name, a, b, target_K, Ns=(25,50,100,200,400,800,1600)):
    res = run(a, b, set(Ns))
    print('==', name)
    print('   closed-form K =', mp.nstr(target_K, 20), '  arctan|K| =', mp.nstr(degrees(atan(fabs(target_K))), 10), 'deg')
    for N in Ns:
        Phi, K, v, u, det = res[N]
        print('   N=%5d  K err=%s  Phi=%s  theta=%s deg  rank-one resid=%s  v1=(%s,%s) u1=(%s,%s)' % (
            N, mp.nstr(fabs(K-target_K),3), mp.nstr(Phi,12), mp.nstr(degrees(asin(sqrt(Phi))),10), mp.nstr(det,3),
            mp.nstr(v[0],8), mp.nstr(v[1],8), mp.nstr(u[0],8), mp.nstr(u[1],8)))

print('######## CONTROLS (stored answers: Q1 20.5600554 deg, e 30.198408 deg, pi 15.282434 deg)')
report('CONTROL Q1 (challenge pi fraction)', lambda n: -220*n**3-484*n**2-301*n-42,
       lambda n: 4*n*n*(2*n+1)**2*(5*n-4)*(5*n+6), 6*(22-7*pi)/(3-pi), Ns=(25,50,100,200))
report('CONTROL e-fraction 1/(e-1) = 1/(1+2/(2+3/(3+...)))', lambda n: mpf(n), lambda n: mpf(n), 1/(e-1), Ns=(25,50,100,200,800))
report('CONTROL pi-fraction 4/pi-1 = 1^2/(3+2^2/(5+...))', lambda n: mpf(2*n+1), lambda n: mpf(n*n), (4-pi)/pi, Ns=(25,50,100,200,800))

print()
print('######## RAMANUJAN ENTRIES (each closed form is checked by the K err column before anything is read off)')
# R1: Notebook Ch.12 gamma quotient (Brouncker at x=1): 4 G((x+3)/4)^2 / G((x+1)/4)^2 = x + 1^2/(2x + 3^2/(2x + 5^2/(2x+...)))
for x in (mpf(1), mpf(3), mpf(1)/2, mpf(10)):
    report('R1 gamma quotient, x=%s' % mp.nstr(x,4), lambda n, x=x: 2*x, lambda n: mpf((2*n-1)**2),
           4*gamma((x+3)/4)**2/gamma((x+1)/4)**2 - x)
# R1n: two-parameter form: G((x+n+1)/4)G((x-n+1)/4)/(G((x+n+3)/4)G((x-n+3)/4)) = 4/(x + (1-n^2)/(2x + (9-n^2)/(2x+...)))
x, nn = mpf(3), mpf(1)/2
lhs = gamma((x+nn+1)/4)*gamma((x-nn+1)/4)/(gamma((x+nn+3)/4)*gamma((x-nn+3)/4))
report('R1n two-parameter gamma quotient, x=3, n=1/2', lambda k: 2*x, lambda k: (2*k-1)**2 - nn**2, 4/lhs - x)
# R2: letter to Hardy: 1/(1+1/(1+2/(1+3/(1+...)))) = sqrt(pi e/2) erfc(1/sqrt2)
report('R2 sqrt(pi e/2) fraction: 1/(1+1/(1+2/(1+...)))', lambda n: mpf(1), lambda n: mpf(1) if n==1 else mpf(n-1),
       sqrt(pi*e/2)*erfc(1/sqrt(mpf(2))))
# R3: Rogers-Ramanujan at q=e^{-2pi}: 1/(1+q/(1+q^2/(1+...))) = (sqrt((5+sqrt5)/2) - (sqrt5+1)/2) e^{2pi/5}
q = exp(-2*pi)
report('R3 Rogers-Ramanujan, q=e^-2pi', lambda n: mpf(1), lambda n: mpf(1) if n==1 else q**(n-1),
       (sqrt((5+sqrt(mpf(5)))/2) - (sqrt(mpf(5))+1)/2)*exp(2*pi/5), Ns=(5,10,20,40))
# R4: zeta(3) = 1 + 1/(4 + 1^3/(1 + 1^3/(12 + 2^3/(1 + 2^3/(20 + ...)))))
report('R4 zeta(3) fraction', lambda n: mpf(4*n) if n%2==1 else mpf(1), lambda n: mpf(1) if n==1 else mpf((n//2)**3),
       zeta(3)-1)
