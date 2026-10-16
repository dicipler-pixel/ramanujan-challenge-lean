# SCRIPT: RAMA-LEAN-PRECHECK-02 -- phase-2 identities checked symbolically before Lean (python3 scripts/precheck2.py)
import sympy as sp
from math import comb
from fractions import Fraction
n=sp.symbols('n')
# ---- 2.2
P=lambda x: 8*x**3+51*x**2+105*x+68
a0=-P(n); a3=(n+1)*(n+2)**4*(n+3)*(8*n**3+75*n**2+231*n+232)
rho=sp.simplify(-a3/a0); target=(n+1)*(n+2)**4*(n+3)*P(n+1)/P(n)
assert sp.simplify(rho-target)==0; print('2.2 ratio -a3/a0 = (n+1)(n+2)^4(n+3)P(n+1)/P(n) OK')
for N in range(0,8):
    prod=sp.prod([((k+1)*(k+2)**4*(k+3)*sp.Rational(P(k+1),P(k))) for k in range(N)]) if N>0 else 1
    closed=sp.factorial(N)*sp.factorial(N+1)**4*sp.factorial(N+2)/2*sp.Rational(P(N),68)
    assert prod==closed, N
# induction step: closed(n+1)/closed(n) = (n+1)(n+2)^4(n+3)P(n+1)/P(n)
print('2.2 Casoratian closed form n!((n+1)!)^4((n+2)!/2)P(n)/68 OK to N=7')
# ---- 2.6 operator factorisation (Ore: Sn f(n)=f(n+1)); L_c coefficients for u_{n+2},u_{n+1},u_n
A=lambda m: -2*(m+3)**3*(2*m+5)*(3*m+5); B=lambda m: (m+2)**2*(15*m**3+85*m**2+155*m+93); C=lambda m: -(m+1)**3*(m+2)*(3*m+8)
Lc=[sp.expand(A(n+2)), sp.expand(B(n+2)), sp.expand(C(n+2))]   # [Sn^2, Sn, 1]
r1=n**2+sp.Rational(15,2)*n+14; r0=-(sp.Rational(1,4)*n**2+sp.Rational(3,2)*n+sp.Rational(9,4))   # R2 = r1 Sn + r0
m1=-12*n**3-164*n**2-740*n-1100; m0=12*n**3+140*n**2+536*n+672                                   # M2 = m1 Sn + m0
prod=[sp.expand(m1*r1.subs(n,n+1)), sp.expand(m1*r0.subs(n,n+1)+m0*r1), sp.expand(m0*r0)]
ratios=[sp.simplify(Lc[i]/prod[i]) for i in range(3)]
print('2.6 L_c / (M2*R2) coefficientwise:',ratios)
# also check against the challenge's own u_n
u={1:sp.Rational(-93,4480),2:sp.Rational(-117,14000)}
for k in range(3,12): u[k]=-(B(k)*u[k-1]+C(k)*u[k-2])/A(k)
# R2 applied to w2: w2(n+1) r1(n) + r0(n) w2(n) = 0 -> ratio; check that u is NOT itself annihilated by R2 but L_c(u)=0
res=[sp.simplify(A(k+2)*u[k+2]+B(k+2)*u[k+1]+C(k+2)*u[k]) for k in range(1,9)]; assert all(r==0 for r in res)
print('2.6 L_c annihilates the challenge u_n (shift convention confirmed) OK')
# h ratio identity
assert sp.simplify((n+4)**2/(4*(n+5)*(n+sp.Rational(9,2))) - (n**2/4+2*n+4)/(n**2+sp.Rational(19,2)*n+sp.Rational(45,2)))==0; print('2.6 h-ratio identity OK')
# ---- 2.4: does the creative-telescoping order-2 recurrence hold for the literal bounded T(m)?
def H(k): return sum(Fraction(1,j) for j in range(1,k+1))
def T(m): return sum(Fraction(comb(m,k))**2*H(k)**2 for k in range(m+1))
bad=[m for m in range(0,12) if (m+2)**3*T(m+2)-2*(2*m+3)*(2*m*m+6*m+5)*T(m+1)+4*(m+1)*(2*m+1)*(2*m+3)*T(m)!=0]
print('2.4 order-2 CT recurrence fails at m =',bad[:6], '(boundary terms, as the history said)' if bad else 'holds m<=11')
