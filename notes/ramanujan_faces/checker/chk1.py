# SCRIPT: RAM-CHECK-01 (independent checker; scalar three-term recurrence)
from mpmath import *
from fractions import Fraction
mp.dps = 90
def conv(a,b,Ns):
    # p_n = a_n p_{n-1} + b_n p_{n-2}; returns dict N -> (p_{N-1},p_N,q_{N-1},q_N) rescaled
    pm,p,qm,q = mpf(1),mpf(0),mpf(0),mpf(1); out={}
    for n in range(1,max(Ns)+1):
        an,bn=a(n),b(n)
        pm,p = p, an*p+bn*pm
        qm,q = q, an*q+bn*qm
        if n%50==0 or n in Ns:
            s=max(abs(p),abs(q),abs(pm),abs(qm)); pm/=s;p/=s;qm/=s;q/=s
        if n in Ns: out[n]=(pm,p,qm,q)
    return out
def eye(t):
    pm,p,qm,q=t
    f=sqrt(pm*pm+p*p+qm*qm+q*q); A,B,C,D=pm/f,p/f,qm/f,q/f   # P=[[A,B],[C,D]]
    # PP^T - P^TP = [[B^2-C^2, (A-D)(C-B)... compute directly
    e11=(A*A+B*B)-(A*A+C*C); e12=(A*C+B*D)-(A*B+C*D); e22=(C*C+D*D)-(B*B+D*D)
    Phi=(e11**2+2*e12**2+e22**2)/2
    return Phi, degrees(asin(sqrt(Phi))), abs(A*D-B*C)
def table(name,a,b,K,Ns):
    r=conv(a,b,set(Ns)); print('==',name,' K=',nstr(K,20),' atan|K|=',nstr(degrees(atan(abs(K))),10))
    prev=None
    for N in Ns:
        t=r[N]; err=abs(t[1]/t[3]-K) if t[3]!=0 else None; Phi,th,det=eye(t)
        s='  N=%6d err=%s theta=%s resid=%s'%(N,nstr(err,5),nstr(th,10),nstr(det,4))
        if prev:
            s+='  | err-exp=%s resid-exp=%s  (atanK-theta)*N=%s'%(nstr(log(prev[1]/err)/log(mpf(N)/prev[0]),5) if err and prev[1] else '-', nstr(log(prev[2]/det)/log(mpf(N)/prev[0]),5) if det and prev[2] else '-', nstr((degrees(atan(abs(K)))-th)*N,6))
        print(s); prev=(N,err,det)
Ns=(100,200,400,800,1600,3200)
G=lambda x:4*gamma((x+3)/4)**2/gamma((x+1)/4)**2
for x in (mpf(1)/2,mpf(1),mpf(3),mpf(10)):
    table('gamma x=%s'%nstr(x,3),lambda n,x=x:2*x,lambda n:mpf((2*n-1)**2),G(x)-x,Ns)
x,nn=mpf(3),mpf(1)/2
lhs=gamma((x+nn+1)/4)*gamma((x-nn+1)/4)/(gamma((x+nn+3)/4)*gamma((x-nn+3)/4))
table('two-param',lambda k:2*x,lambda k:(2*k-1)**2-nn**2,4/lhs-x,Ns)
table('sqrt(pi e/2)',lambda n:mpf(1),lambda n:mpf(max(n-1,1)),sqrt(pi*e/2)*erfc(1/sqrt(mpf(2))),Ns+(12800,51200))
q=exp(-2*pi)
KR=(sqrt((5+sqrt(mpf(5)))/2)-(sqrt(mpf(5))+1)/2)*exp(2*pi/5)
table('RR',lambda n:mpf(1),lambda n:mpf(1) if n==1 else q**(n-1),KR,(3,5,10,20))
print('  45-atan(K) =',nstr(45-degrees(atan(KR)),12))
table('zeta3',lambda n:mpf(4*n) if n%2 else mpf(1),lambda n:mpf(1) if n==1 else mpf((n//2)**3),zeta(3)-1,Ns)
table('Q1',lambda n:mpf(-220*n**3-484*n**2-301*n-42),lambda n:mpf(4*n*n*(2*n+1)**2*(5*n-4)*(5*n+6)),6*(22-7*pi)/(3-pi),(25,50,100,200))
table('e',lambda n:mpf(n),lambda n:mpf(n),1/(e-1),(100,200,400,800))
table('pi',lambda n:mpf(2*n+1),lambda n:mpf(n*n),(4-pi)/pi,(100,200,400,800))
# b,d algebra
for x in (mpf(1)/2,mpf(1),mpf(3),mpf(10)):
    w=0
    for m in (1,3,5,99,12799):
        s=sqrt(x*x+m*m); ev=sorted([re(v) for v in polyroots([1,-2*x,-m*m])])
        z=(s+x)/(s-x); w=max(w,abs(ev[0]-(x-s)),abs(ev[1]-(x+s)),abs(tanh(log(z)/2)-x/s),abs(z-abs(ev[1]/ev[0])))
    print('x',nstr(x,3),'max dev eig/z/tanh:',nstr(w,3))
r2=sqrt(mpf(2)); print('d:',nstr((r2+1)/(r2-1)-(3+2*r2),3),nstr((1+r2)**2-(3+2*r2),3),nstr((1+r2)**4-(17+12*r2),3))
# x=0 exact
pm,p,qm,q=Fraction(1),Fraction(0),Fraction(0),Fraction(1)
for n in range(1,8):
    b=(2*n-1)**2; pm,p=p,b*pm; qm,q=q,b*qm
    print('x=0 N',n,'P=[[%s,%s],[%s,%s]]'%(pm,p,qm,q))
