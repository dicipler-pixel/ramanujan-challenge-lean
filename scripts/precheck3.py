#!/usr/bin/env python3
# SCRIPT: RAMANUJAN-CHALLENGE-LEAN-PRECHECK-03
"""Symbolic pre-check of every identity used in RamanujanChallenge/Problem21.lean.

Each identity is checked exactly (SymPy, rational arithmetic) before it was written in Lean;
the Lean kernel then re-checks it. The last block is a numerical cross-check (mpmath, 40
digits) that the integral-defined F_n is the official 2F1(n+1/2, n+1/2; 3n+1/2; 1/2) and that
the continued fraction approaches 6/(3 - pi); it is evidence, not part of the proof.
"""
from sympy import (symbols, Rational, sqrt, pi, atan, gamma, diff, simplify, cancel, expand,
                   Poly, combsimp, expand_func)
import mpmath as mp

u, n, x = symbols('u n x')
m = symbols('m', integer=True, nonnegative=True)
ok = True


def check(name, expr):
    global ok
    good = simplify(expr) == 0
    ok &= good
    print(f"{'OK ' if good else 'FAIL'} {name}")


A = -3*(6*n+7)*(6*n+11)*(220*n**3+484*n**2+301*n+42)/(8*(n+1)**2*(2*n+3)**2*(5*n+1))
B = 9*(5*n+6)*(6*n+1)*(6*n+5)*(6*n+7)*(6*n+11)/(16*(n+1)**2*(2*n+3)**2*(5*n+1))
a = -220*n**3-484*n**2-301*n-42
b = 4*n**2*(2*n+1)**2*(5*n-4)*(5*n+6)
r = 8*(n+1)**2*(2*n+3)**2*(5*n+1)/(3*(6*n+7)*(6*n+11))

# Substitution t = 2u^2/(1+u^2) in Euler's integral (Eq. 28): integrand and dt.
up = symbols('up', positive=True)
t = 2*up**2/(1+up**2)
lhs = t**(n-Rational(1, 2))*(1-t)**(2*n-1)*(1-t/2)**(-n-Rational(1, 2))*diff(t, up)
rhs = 2**(n+Rational(3, 2))*up**(2*n)*(1-up**2)**(2*n-1)/(1+up**2)**(2*n)
for N in range(1, 6):
    check(f"substitution t=2u^2/(1+u^2) in Eq. 28, n={N} (symbolic in u > 0)",
          lhs.subs(n, N)-rhs.subs(n, N))

# Integrands: w21 m = omega1 * G^m equals u^(2m+2)(1-u^2)^(2m+1)/(1+u^2)^(2m+2).
G = u**2*(1-u**2)**2/(1+u**2)**2
w1 = u**2*(1-u**2)/(1+u**2)**2
for M in range(0, 4):
    check(f"w21 {M} closed form", w1*G**M - u**(2*M+2)*(1-u**2)**(2*M+1)/(1+u**2)**(2*M+2))

# The certificate (hasDerivAt_Phi21): d/du[N(n,u) G^(n-1)] = (P0 + P1 G + P2 G^2) w1 G^(n-1).
q = ((10*n**2+12*n+2)*u**8 + (30*n**2+41*n+6)*u**6 - (60*n**2+82*n+18)*u**4
     - (30*n**2+51*n+14)*u**2 + (10*n**2+12*n))
N = -(u**3*(1-u**2)**2*q/(1+u**2)**5)
P0 = -2*n*(2*n+1)*(5*n+6)
P1 = 220*n**3+484*n**2+301*n+42
P2 = 2*(n+1)*(2*n+3)*(5*n+1)
check("certificate, general n (times G)", diff(N, u)*G + (n-1)*N*diff(G, u) - G*w1*(P0+P1*G+P2*G**2))
check("certificate, n = 1", (diff(N, u) - w1*(P0+P1*G+P2*G**2)).subs(n, 1))
check("certificate vanishes at u=0", N.subs(u, 0))
check("certificate vanishes at u=1", N.subs(u, 1))

# Anchors (K21_zero, K21_one): antiderivatives and values.
H1 = 2*atan(u) - u - u/(1+u**2)
H2 = (33*u**5+50*u**3+21*u)/(3*(1+u**2)**3) - u**3/3 + 7*u - 14*atan(u)
check("H1' = w21 0", diff(H1, u) - w1)
check("H2' = w21 1", diff(H2, u) - w1*G)
check("K21 0 = (pi-3)/2", H1.subs(u, 1) - H1.subs(u, 0) - (pi-3)/2)
check("K21 1 = 11 - 7pi/2", H2.subs(u, 1) - H2.subs(u, 0) - (11 - 7*pi/2))

# The Gamma prefactor (kap21_succ, kap21_zero, kap21_one); n = m + 1.
kap = lambda k: gamma(3*(k+1)+Rational(1, 2))/(gamma(k+1+Rational(1, 2))*gamma(2*(k+1)))*2**(k+2)*sqrt(2)
rho = 3*(6*m+7)*(6*m+11)/(4*(m+1)*(2*m+3))
check("kap21_succ", combsimp(expand_func(kap(m+1)/kap(m))) - rho)
check("kap21_zero", kap(0) - 15*sqrt(2))
check("kap21_one", kap(1) - 1155*sqrt(2)/4)
check("rho <= 20  <=>  poly >= 0 (coefficients)",
      0 if all(c >= 0 for c in Poly(expand(80*(m+1)*(2*m+3)-3*(6*m+7)*(6*m+11)), m).all_coeffs())
      else 1)

# Lemma 3 from the K recurrence and the kappa ratio (F21_rec), n = m + 1.
K0, K1 = symbols('K0 K1')
K2 = (2*n*(2*n+1)*(5*n+6)*K0 - P1*K1)/P2
rhon = 3*(6*n+1)*(6*n+5)/(4*n*(2*n+1))
k0 = symbols('k0')
F0, F1, F2 = k0*K0, k0*rhon*K1, k0*rhon*rhon.subs(n, n+1)*K2
check("F_{n+2} = A F_{n+1} + B F_n", F2 - A*F1 - B*F0)

# Equation (22) and the base of the s-recursion.
check("r_n A(n) = a_n", r*A - a)
check("r_n r_{n-1} B(n) = b_n", r*r.subs(n, n-1)*B - b)
check("r_0 * 77/24 = 1", r.subs(n, 0)*Rational(77, 24) - 1)

# Dominance: -A(x) - 100 has a numerator with nonnegative coefficients.
num = expand(3*(6*x+7)*(6*x+11)*(220*x**3+484*x**2+301*x+42) - 800*(x+1)**2*(2*x+3)**2*(5*x+1))
check("-A(x) >= 100 for x >= 0 (coefficients)",
      0 if all(c >= 0 for c in Poly(num, x).all_coeffs()) else 1)
check("Q_2 = a_1 = -1047", a.subs(n, 1) + 1047)
check("-Q_2 >= 100 sigma_2", 0 if 1047 >= 100*r.subs(n, 1) else 1)

# Theorem 2: a_0 - X_0 / X_{-1} = 6/(3 - pi).
Fa = 15*sqrt(2)/2*(pi-3)
Fb = 1155*sqrt(2)/8*(22-7*pi)
check("a_0 - 24 F_2/(77 F_1) = 6/(3-pi)", -42 - Fb/(Rational(77, 24)*Fa) - 6/(3-pi))

# Numerical cross-check (evidence only).
mp.mp.dps = 40
for k in range(1, 6):
    F = mp.hyp2f1(k+0.5, k+0.5, 3*k+0.5, 0.5)
    I = mp.quad(lambda s: s**(2*k)*(1-s**2)**(2*k-1)/(1+s**2)**(2*k), [0, 1])
    c = mp.gamma(3*k+mp.mpf(1)/2)/(mp.gamma(k+mp.mpf(1)/2)*mp.gamma(2*k))*2**(k+1)*mp.sqrt(2)
    print(f"     F_{k}: 2F1 = {mp.nstr(F, 20)}, |2F1 - kappa*K| = {mp.nstr(abs(F-c*I), 3)}")
P, Q = [mp.mpf(1), mp.mpf(-42)], [mp.mpf(0), mp.mpf(1)]
for k in range(1, 30):
    ak = -220*k**3-484*k**2-301*k-42
    bk = 4*k**2*(2*k+1)**2*(5*k-4)*(5*k+6)
    P.append(ak*P[-1]+bk*P[-2]); Q.append(ak*Q[-1]+bk*Q[-2])
print(f"     P_30/Q_30 - 6/(3-pi) = {mp.nstr(P[-1]/Q[-1] - 6/(3-mp.pi), 3)}")
print("ALL OK" if ok else "SOME CHECK FAILED")
raise SystemExit(0 if ok else 1)
