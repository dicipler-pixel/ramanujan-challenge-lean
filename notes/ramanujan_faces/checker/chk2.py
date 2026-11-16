# SCRIPT: RAM-CHECK-02
from mpmath import *
from fractions import Fraction
import math
mp.dps = 110
# b: eigenvalues numerically via mp.eig
for x in (mpf(1)/2,mpf(1),mpf(3),mpf(10)):
    w=0
    for m in (1,3,5,99,12799):
        s=sqrt(x*x+m*m); E,_=eig(matrix([[0,m*m],[1,2*x]])); ev=sorted([re(v) for v in E])
        z=(s+x)/(s-x); w=max(w,abs(ev[0]-(x-s)),abs(ev[1]-(x+s)),abs(tanh(log(z)/2)-x/s),abs(z-abs(ev[1]/ev[0])))
    print('x',nstr(x,3),'max dev eig/z/tanh:',nstr(w,3))
r2=sqrt(mpf(2)); print('d:',nstr((r2+1)/(r2-1)-(3+2*r2),3),nstr((1+r2)**2-(3+2*r2),3),nstr((1+r2)**4-(17+12*r2),3))
print('rapidities: ln(3+2r2)=',nstr(log(3+2*r2),8),' ln(17+12r2)=',nstr(log(17+12*r2),8),' ln((17+12r2)/(17-12r2))=',nstr(log((17+12*r2)/(17-12*r2)),8))
pm,p,qm,q=Fraction(1),Fraction(0),Fraction(0),Fraction(1)
for n in range(1,7):
    b=(2*n-1)**2; pm,p=p,b*pm; qm,q=q,b*qm
    print('x=0 N',n,'P=[[%s,%s],[%s,%s]]'%(pm,p,qm,q))
# e: section 5 table, product formed directly (not via logs)
G=lambda x:4*gamma((x+3)/4)**2/gamma((x+1)/4)**2
marks=[100,400,1600,6400,25600,102400]
for x in (mpf(1)/2,mpf(1),mpf(3),mpf(10)):
    K=G(x)-x; pm,p,qm,q=mpf(1),mpf(0),mpf(0),mpf(1); Z=mpf(1); vals=[]
    for n in range(1,marks[-1]+1):
        m=2*n-1; b=m*m; s=sqrt(x*x+b)
        pm,p=p,2*x*p+b*pm; qm,q=q,2*x*q+b*qm; Z*=(s+x)/(s-x)
        if n%64==0:
            sc=abs(q); pm/=sc;p/=sc;qm/=sc;q/=sc
        if n in marks:
            err=abs(p/q-K); vals.append(err*Z)
            print('x=%s N=%6d err=%s err*Z=%s err*N^x=%s'%(nstr(x,3),n,nstr(err,5),nstr(err*Z,10),nstr(err*mpf(n)**x,10)))
    d=[vals[i+1]-vals[i] for i in range(len(vals)-1)]
    print('   diffs:',[nstr(v,4) for v in d],' ratios:',[nstr(d[i]/d[i+1],4) for i in range(len(d)-1)])
# sum check
for N in (100,6400):
    print('sum 2/(2n-1) - ln N at N=%d:'%N, sum(2.0/(2*n-1) for n in range(1,N+1))-math.log(N), ' 2ln2+gamma=',2*math.log(2)+0.5772156649)
