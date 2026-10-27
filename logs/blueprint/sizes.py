# Blueprint sizing, revision 3.8 (skip-c restored, Sel = 1 with the free kind, J_z = 4, kappa_c 5 squeezes) (Lr end / E end absorbs) (S-E2 F-1…F-4) (J_z = 5, WOTS links through the shift argument) (stage-review changes 2: per-kind lincheck claims batched by beta, E2 in the Ligerito weight, 57 steps/product) (stage-review changes 1: per-kind block matrices, stmt as hash message blocks) (fix pass 4: hashStmt 3 blocks, Sel in the weight, J_z MBP runs). One item sequence and one piSize for L32 and P30:
# every phase is sized for the larger kind; a kind's unused items are dummy queries (zero payloads).
import math
RATES=[2,4,8,16,32]; ROWS=[64,16,16,16,16]
def ladder(m):
    mp=m-7; k=2**(mp-6); lv=[]
    for i in range(5):
        rho=RATES[i]; n=k*rho; e=(n-k)//2; g=e/n
        t=math.ceil(120.25/-math.log2(1-g)); bits=int(math.log2(n)); per=256//bits
        sq=math.ceil(t/per); cap=math.ceil(math.log2(t)); sib=bits-cap
        lv.append(dict(i=i,rho=rho,rows=ROWS[i],k=k,n=n,e=e,t=t,err=t*math.log2(1-g),bits=bits,per=per,sq=sq,cap=cap,sib=sib))
        k//=8
    return lv,k
L32,kf32=ladder(32); P30,kf30=ladder(30)
M=32                                   # the item sequence is sized for m = 32
# ---- the item sequence (A.4): (phase, absorbs, squeezes, payload bytes of each absorb)
UNI=2048                               # a univariate round's message (127 F values, padded)
RND=48                                 # a sumcheck round's 3 coefficients (F); K rounds 96
seq=[]
def add(ph,a,q,ab=0): seq.append((ph,a,q,ab))
add("seed",1,0,112); add("stmt",1,0,128); add("cap0",1,0,512*32)   # stmt = the padded statement-hash message blocks (rev. 3.3)
add("Z1",0,math.ceil((M-13)/2)); add("Z2",1,1,UNI); add("Z3",M-6,M-6,RND); add("Zend",1,0,32)
add("L1",0,1); add("L2",14,14,RND); add("L3",1,1,8*16)   # 14 multilinear rounds (P1-D4); L3: the 8 node per-kind claims incl. free (rev. 3.8.2) v_kind absorbed, beta squeezed (rev. 3.4)
add("S1",0,math.ceil((M-14+10+1)/2)); add("S2",M-14+10,M-14+10,RND)   # tau (m-14), theta (10 slot coords), kappa_s; block rounds + 10 collapse rounds
add("Lr1",0,math.ceil(15/2)); add("Lr2",15,15,RND); add("Lrend",1,0,48); add("Lr3",0,1); add("Lr4",15,15,RND)   # Lr end absorb (rev. 3.7)
add("RS0",1,0,4*128*16)   # J_z = 4 (rev. 3.8: Sh is one claim); 4 claims x 128 partials
add("RS1",0,math.ceil((7+1)/2))  # r'' (7) and kappa in one phase (rev. 3.8.2: was commented out)
add("E1",0,math.ceil(21/2)); add("E2",21,21,RND); add("Eend",1,0,48); add("E3",0,1); add("Ep",0,1)   # E end absorb (rev. 3.7)  # E2's lincheck is batched into the Ligerito weight (rev. 3.4, P2 §6); kappa_E, kappa'
CAPB=[512*32,256*32,256*32,256*32,128*32]
FINAL_K=2**7                                              # the level-4 fold: 2^7 K elements (m=32), 2^5 padded (m=30)
for i,l in enumerate(L32):
    ell=6 if i==0 else 4
    add(f"P1.{i}",ell,ell,96)
    add(f"C.{i}",1,0,CAPB[i+1] if i<4 else FINAL_K*32)
    add(f"P2.{i}",0,l['sq'])
    add(f"Q.{i}",0,0)
    add(f"P3.{i}",0,5)                   # kappa_c: 9 F coordinates = 5 squeezes (rev. 3.8)
add("Pf",7,7,96)                                          # log k_4 = 7 final rounds (K)
fs_items=sum(a+q for _,a,q,_ in seq)
cols=sum(l['t'] for l in L32); sibs=sum(l['t']*l['sib'] for l in L32)
items=fs_items+cols+sibs
# hashed stream: 0x54 | items ; FS items 16(k+3) with payload 32+ab (absorb), 32 (squeeze), 112 (seed)
tb=1
for ph,a,q,ab in seq:
    if ph=="seed": tb+=8+7+112+32
    else: tb+=a*(8+8+32+ab+32)+q*(8+8+32+32)
colb=sum(l['t']*l['rows']*16 for l in L32)
tb+=cols*(8+8+32)+colb+sibs*(8+8+64+32)
comp=math.ceil(tb/64)
piop=sum(a*ab for ph,a,q,ab in seq if ph not in("seed","stmt","cap0") and not ph.startswith("C."))
caps=sum(CAPB); final=FINAL_K*32
pi=48+128+piop+caps+final+colb+sibs*32
print("== unified item sequence (sized for m=32; P30 proofs carry dummy items)")
print(f"   FS items={fs_items} columns={cols} siblings={sibs} -> items={items}; qV=10240 margin {10240/items:.2f}x")
print(f"   hashed stream bytes={tb} compressions/slot={comp}")
print(f"   piSize = 48+128 + PIOP {piop} + caps {caps} + final {final} + columns {colb} + siblings {sibs*32} = {pi} B = {pi/1024:.0f} KiB ({pi/2**20*100:.0f}% of proofCap, margin {2**20/pi:.2f}x)")
for name,lv in (("L32",L32),("P30",P30)):
    print(f"   {name} ladder:", " ".join(f"L{l['i']}:k=2^{int(math.log2(l['k']))},n=2^{l['bits']},e={l['e']},t={l['t']},err=2^{l['err']:.2f},sib={l['sib']},sq={l['sq']}" for l in lv))
# ---- node circuit (one slot program `gen Mux`, imports with one address per element)
imports = cols*0  # recomputed below
col_elems=sum(l['t']*l['rows'] for l in L32); sib_elems=sibs*6; fs_elems=fs_items*3
I_slot=col_elems+sib_elems+fs_elems
folds=sum(l['t']*(2*l['rows']-2+1) for l in L32)
enc_final=2*FINAL_K*L32[4]['t']
merkle=4*sibs                         # 2 rows per half, gated: u = b(r-l); s(cur-l-u)=0
uni_lagr=400
eq_tensor=15000; mbp=4*(M-7)*128; sumchecks=2000; linrep=2*2**14*2+2**14+2**14+8   # + the free kind's lincheck term (rev. 3.8)   # mbp: J_z = 4 runs; + per-kind row-weight adjust and the 8 stmt equalities (rev. 3.3)
evalM_rep=2*I_slot+(2*comp+2**14)     # the 'N' child's evalM over its two slots: one row per entry + eq tables
evalL_rep=2**13
gated=2*fs_items+2*cols+600+2600+266+8   # + mirror-cell mux rows (3.5); + selector-digit rows and the 8 gated stmt equalities (3.6)
per_slot=I_slot+folds+enc_final+merkle+uni_lagr+eq_tensor+mbp+sumchecks+linrep+evalM_rep+evalL_rep+gated+4
M_rows=2*per_slot; M_blocks=math.ceil(M_rows*128/2**14)
H=2*comp+6+2*498+8+2*10              # + the aligned mirror sub-region WM (rev. 3.5)                # hashStmt: 3 blocks per slot (R4-M1)
L_bits=2*(4772*8+sibs*128+133*4*2+2**12); L_blocks=math.ceil(L_bits/2**14)
total=H+M_blocks+L_blocks+1
print("== node")
print(f"   per slot: imports {I_slot} (col {col_elems}, sib {sib_elems}, fs {fs_elems}); folds {folds}; encFinal {enc_final}; merkle {merkle}; uni {uni_lagr}; eq/tensor {eq_tensor}; mbp {mbp}; sumchecks {sumchecks}; lincheck-replay {linrep}; evalM-replay {evalM_rep}; evalL-replay {evalL_rep}; gated asserts {gated}")
print(f"   M rows/node = {M_rows} = 2^{math.log2(M_rows):.2f}; N_M=2^21 margin {2**21/M_rows:.2f}x; M blocks {M_blocks}")
print(f"   H blocks {H}; L blocks {L_blocks}; total {total} of 65536 ({total/65536*100:.0f}%, margin {65536/total:.2f}x); H gap [{H}, 49152) = {49152-H} blocks holds L+P ({L_blocks+1})")
# ---- verifier products
V_node = I_slot*2 + 2*comp + 2**14 + folds + enc_final + uni_lagr + eq_tensor + mbp + sumchecks + evalL_rep + 2**15 + 2**14 + 2000   # + per-kind row-weight adjust, per-kind target MLE
V_leaf = sum(l['t']*l['rows']*2 for l in L32) + enc_final + uni_lagr + eq_tensor + mbp + sumchecks
print(f"== V products: node ~{V_node} (evalM irregular {2*I_slot}); leaf ~{V_leaf}")
# ---- extractor (m=30 node)
k0=P30[0]['k']; n0=P30[0]['n']
prod=(3+64)*k0**2 + 64*k0**2//2 + n0*k0*2 + n0*64*2
steps=prod*57+2**30                       # 57 steps per F product (S-H1, kernel)
print(f"== extractor m=30: products 2^{math.log2(prod):.2f}, steps (57/product) 2^{math.log2(steps):.2f}; fuel 2^47.5 margin {2**47.5/steps:.2f}x; budget 2^48 margin {2**48/steps:.2f}x")
w=9+2*((1+pi//8)+(1+items*5+tb//8)+597)
print(f"== outCap: node of two children ~{w} words = 2^{math.log2(w):.1f} of 2^24")
