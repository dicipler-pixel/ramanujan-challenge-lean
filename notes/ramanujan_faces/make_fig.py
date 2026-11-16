# SCRIPT: RAM-EYE-FIG-01
import math, matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt
plt.rcParams.update({'font.family':'DejaVu Sans','font.size':11})
bg='#0b0c10'; fg='#e8e6df'; grid='#2a2d36'
cols={0.5:'#7fe3c4',1:'#f2b84b',3:'#ef8354',10:'#8ecae6'}
fig,ax=plt.subplots(1,2,figsize=(14.5,6.4),facecolor=bg)
for a in ax:
    a.set_facecolor(bg); a.tick_params(colors=fg); a.grid(color=grid,lw=0.6)
    for s in a.spines.values(): s.set_color(grid)
# left: Gamma_n^2 per face
ns=list(range(1,201))
for x,c in cols.items():
    g2=[x*x/(x*x+(2*n-1)**2) for n in ns]
    ax[0].plot(ns,g2,color=c,lw=2,marker='o',ms=3,label='x = %g'%x)
ax[0].axhline(0.5,color=fg,lw=1.2,ls='--')
ax[0].text(60,0.53,'the wall  Γ² = ½   (z = 3 + 2√2)',color=fg,fontsize=10)
ax[0].scatter([1],[0.5],s=160,facecolors='none',edgecolors='#f2b84b',lw=2,zorder=5)
ax[0].annotate("Brouncker's first face\n(x = 1, n = 1) is on the wall",xy=(1,0.5),xytext=(22,0.27),color='#f2b84b',fontsize=10,
               arrowprops=dict(arrowstyle='->',color='#f2b84b'))
ax[0].set_xscale('log'); ax[0].set_xlabel('face number n (depth in the fraction)',color=fg); ax[0].set_ylabel('Γₙ²  =  x² / (x² + (2n−1)²)',color=fg)
ax[0].set_title('Each term is one face. Faces grow transparent with depth.',color=fg,fontsize=12)
leg=ax[0].legend(facecolor=bg,edgecolor=grid,labelcolor=fg,loc='upper right')
# right: discriminating test (numbers from RAM-EYE-04 and RAM-EYE-05 outputs)
rows=[('Challenge π fraction (geometric)',313.48,3.4723),('e fraction (factorial)',280.38,0.0024746),
      ('π fraction (geometric)',114.83,0.84009),('√(πe/2) fraction (stretched exp.)',130.26,0.040742),
      ('ζ(3) fraction, faces in pairs (power)',14.423,0.99676),('Gamma fraction x = 10 (power)',24.038,0.043105),
      ('Gamma fraction x = 1, Brouncker (power)',2.4026,0.0056735)]
ys=list(range(len(rows)))[::-1]
ax[1].barh([y+0.19 for y in ys],[r[1] for r in rows],height=0.36,color='#8ecae6',label='orders of magnitude the error fell')
ax[1].barh([y-0.19 for y in ys],[r[2] for r in rows],height=0.36,color='#f2b84b',label='orders the product (error × all z) moved')
for y,r in zip(ys,rows):
    ax[1].text(r[1]*1.15,y+0.19,'%.3g'%r[1],color=fg,va='center',fontsize=9)
    ax[1].text(r[2]*1.15,y-0.19,'%.2g'%r[2],color=fg,va='center',fontsize=9)
ax[1].set_xscale('log'); ax[1].set_xlim(1e-3,3e3); ax[1].set_yticks(ys); ax[1].set_yticklabels([r[0] for r in rows],color=fg,fontsize=9.5)
ax[1].set_xlabel('orders of magnitude (log scale)',color=fg)
ax[1].set_title('One rule, four convergence laws',color=fg,fontsize=12)
ax[1].legend(facecolor=bg,edgecolor=grid,labelcolor=fg,loc='upper center',bbox_to_anchor=(0.35,-0.14),ncol=1,fontsize=9.5)
fig.suptitle("Continued fractions read as stacks of faces  ·  left: Ramanujan's gamma fraction  x + 1²/(2x + 3²/(2x + ⋯))",color=fg,fontsize=14,y=0.99)
fig.tight_layout(rect=[0,0,1,0.95])
fig.savefig('pkg/fig_faces.png',dpi=130,facecolor=bg)
