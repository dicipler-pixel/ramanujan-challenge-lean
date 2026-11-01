# SCRIPT: RAMA-LEAN-PRECHECK-01 -- every identity in RamanujanChallenge/Exact.lean, checked symbolically first (python3 scripts/precheck.py)
import sympy as sp
n=sp.symbols('n')
# 2.1 Pochhammer product, my indexing: prod_{k<n} b(k+1) = 25^n ((2n+1)!)^2 (1/5)_n (11/5)_n
b=lambda k: 4*k**2*(2*k+1)**2*(5*k-4)*(5*k+6)
for N in range(0,9):
    lhs=sp.prod([b(k+1) for k in range(N)]) if N>0 else 1
    rhs=25**N*sp.factorial(2*N+1)**2*sp.rf(sp.Rational(1,5),N)*sp.rf(sp.Rational(11,5),N)
    assert lhs==rhs, N
# induction step identity: b(n+1) = 25*(2n+3)^2*(2n+2)^2*(1/5+n)*(11/5+n)
assert sp.expand(b(n+1)-25*(2*n+3)**2*(2*n+2)**2*(sp.Rational(1,5)+n)*(sp.Rational(11,5)+n))==0
print('2.1 Pochhammer OK')
# 2.1 Casoratian step: W(n+1) = -b(n+2) W(n) with A(n+2)=a(n+2)A(n+1)+b(n+2)A(n)
a_,b_,A0,A1,B0,B1=sp.symbols('a b A0 A1 B0 B1')
A2=a_*A1+b_*A0; B2=a_*B1+b_*B0
assert sp.expand(A2*B1-A1*B2-(-b_)*(A1*B0-A0*B1))==0; print('2.1 Casoratian step OK')
# 2.2 telescoping: P(n+1) = 8n^3+75n^2+231n+232
P=lambda x: 8*x**3+51*x**2+105*x+68
assert sp.expand(P(n+1)-(8*n**3+75*n**2+231*n+232))==0; print('2.2 telescoping OK')
# 2.2 companion det
a0,a1,a2,a3=sp.symbols('a0 a1 a2 a3')
M=sp.Matrix([[0,1,0],[0,0,1],[-a3/a0,-a2/a0,-a1/a0]]); assert sp.simplify(M.det()+a3/a0)==0; print('2.2 det OK')
# 2.3 reciprocal pair
s2=sp.sqrt(2); assert sp.simplify((s2+1)*(s2-1)-1)==0; assert sp.expand((s2+1)**2-2*s2*(s2+1)+1)==0; print('2.3 roots OK')
# 2.5 matrices from the write-up
L=sp.Matrix([[0,0,0],[0,0,0],[-128,0,0]]); B=sp.Matrix([[0,0,0],[192,0,0],[-2808,192,0]]); C=sp.Matrix([[-272,0,0],[3944,-272,0],[-27184,3752,-16]])
Z=sp.zeros(3)
assert L*L==Z and L*B==Z and B*L==Z and B**3==Z and B*B==-288*L and L*C==-272*L and C*L==-16*L
print('2.5 algebra OK; B*B =',list(B*B), ' -288L =',list(-288*L))
# also check L,B,C against M(n) leading coefficients from the official m_ij
m={}
m[0,0]=(-2*n-5)*(n+3)**2*(136*n**4+1424*n**3+5548*n**2+9551*n+6141)
m[0,1]=384*n**6+6384*n**5+44168*n**4+162698*n**3+336377*n**2+369933*n+169011
m[0,2]=-480*n**4-4980*n**3-19210*n**2-32690*n-20730
m[1,0]=(n+2)**2*(n+3)**2*(4*n+10)*(48*n**3+386*n**2+1017*n+879)
m[1,1]=(n+2)**2*(-272*n**5-3848*n**4-21732*n**3-61184*n**2-85761*n-47808)
m[1,2]=(n+2)**2*(320*n**3+2540*n**2+6610*n+5640)
m[2,0]=(-4*n-10)*(n+2)**2*(n+3)**2*(32*n**4+302*n**3+1037*n**2+1530*n+813)
m[2,1]=(n+2)**2*(192*n**6+2984*n**5+19116*n**4+64452*n**3+120256*n**2+117279*n+46476)
m[2,2]=(n+2)**2*(-16*n**5-408*n**4-2912*n**3-8884*n**2-12254*n-6240)
def coef(d): return sp.Matrix(3,3,lambda i,j: sp.Poly(sp.expand(m[i,j]),n).coeff_monomial(n**d))
print('n^9:',list(coef(9)),' n^8:',list(coef(8)),' n^7:',list(coef(7)))
assert coef(9)==L and coef(8)==B and coef(7)==C; print('2.5 L,B,C match the official M(n) OK')
# 2.6 partial fractions and the constant
r=(sp.Rational(3,14)*n+1)/(n**3+14*n**2+65*n+100)
assert sp.simplify(r-(sp.Rational(1,7)/(n+4)-sp.Rational(1,7)/(n+5)+sp.Rational(1,14)/(n+5)**2))==0
assert sp.factor(n**3+14*n**2+65*n+100)==(n+4)*(n+5)**2
c=sp.Rational(1,35)-sp.Rational(1,14)*sum(sp.Rational(1,k*k) for k in range(1,6)); assert c==-sp.Rational(547,7200)
print('2.6 partial fractions OK, constant -547/7200 OK; numeric sum check:',sp.N(sp.Sum(r,(n,1,sp.oo)).doit()-(sp.pi**2/84-sp.Rational(547,7200)),30))
