# SCRIPT: RAM-CHECK-03  small x, large N, double precision (errors are O(0.01..1))
import math
from mpmath import mp, mpf, gamma
mp.dps=30
for xs in ('0.2','0.05'):
    x=float(xs); X=mpf(xs); K=float(4*gamma((X+3)/4)**2/gamma((X+1)/4)**2-X)
    pm,p,qm,q=1.0,0.0,0.0,1.0; prev=None; N=1; marks=[1600*4**k for k in range(0,7)]
    for n in range(1,marks[-1]+1):
        b=float((2*n-1))**2
        pm,p=p,2*x*p+b*pm; qm,q=q,2*x*q+b*qm
        if n%8==0:
            sc=abs(q); pm/=sc;p/=sc;qm/=sc;q/=sc
        if n in marks:
            err=abs(p/q-K)
            print('x=%s N=%8d err=%.6g err*N^x=%.5f'%(xs,n,err,err*n**x), ' local exp=%.4f'%(math.log(prev/err)/math.log(4)) if prev else '')
            prev=err
