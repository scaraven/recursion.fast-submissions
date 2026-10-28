# Blueprint sizing, revision 3.11 (A.11 replay templates: the node row model is the compiled skeleton + templates) (v_RS = rsT: Phi rows; rsWeight replaces mbp) (skip-c restored, Sel = 1 with the free kind, J_z = 4, kappa_c 5 squeezes) (Lr end / E end absorbs) (S-E2 F-1…F-4) (J_z = 5, WOTS links through the shift argument) (stage-review changes 2: per-kind lincheck claims batched by beta, E2 in the Ligerito weight, 57 steps/product) (stage-review changes 1: per-kind block matrices, stmt as hash message blocks) (fix pass 4: hashStmt 3 blocks, Sel in the weight, J_z MBP runs). One item sequence and one piSize for L32 and P30:
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
eq_tensor=15000; mbp=4*128*(M-7)+4*128*136+4032; sumchecks=2000; linrep=2*2**14*2+2**14+2**14+8   # rsWeight + Phi on 512 slice values + Z Lagrange weights (rev. 3.9); lincheck replay incl. free kind
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

# ---- A.11 replay-template row model (rev. 3.11), per slot; K products = 3 F rows
T32=L32
skeleton=68795                                       # compiled arithmetic skeleton (S-E2 F-6, measured)
eqTableK=sum(6*(2**(6 if l['i']==0 else 4)-1) for l in T32)
dotKF=sum(l['t']*2*l['rows'] for l in T32)
tensorW=sum(l['t']*3*int(math.log2(l['k'])) for l in T32)
walks=2*2**14+2*2**14+2**14                          # rowW, colW tables; A and B product rows; rowW' mask
lagrangeS=1400; targetS=10000; slotW=3*2800; linkW=8*2500; small=500; eqZ=128
phiRS=4*128*134
rsWeight=4*(23*127+128*22*3)+128
evalM_rep=2**16*3+2**14*3+2*I_slot+20000*3+10000    # eq tables over blocks/slots in K, irregular entries (K x F = 2 rows), template closed forms in K, evalL
per_slot_A11=skeleton+eqTableK+dotKF+tensorW+walks+lagrangeS+targetS+slotW+linkW+small+eqZ+phiRS+rsWeight+evalM_rep
M_rows_A11=2*per_slot_A11
print(f"== A.11 row model: skeleton {skeleton}; eqTableK {eqTableK}; dotKF {dotKF}; tensorW {tensorW}; walks {walks}; lagrangeS {lagrangeS}; targetS {targetS}; slotW {slotW}; linkW {linkW}; eqZ/shift/eqPt {small+eqZ}; phiRS {phiRS}; rsWeight {rsWeight}; evalM/evalL replay {evalM_rep}")
print(f"   per slot {per_slot_A11}; per node {M_rows_A11} = 2^{math.log2(M_rows_A11):.2f}; N_M margin {2**21/M_rows_A11:.2f}x; M blocks {math.ceil(M_rows_A11*128/2**14)}; node blocks {H+math.ceil(M_rows_A11*128/2**14)+L_blocks+1} of 65536 ({65536/(H+math.ceil(M_rows_A11*128/2**14)+L_blocks+1):.2f}x)")
# fallback: E2 lincheck restored -> evalM replay in F
evalM_F=2**16+2**14+2*I_slot+20000+10000
alt=2*(per_slot_A11-evalM_rep+evalM_F)
print(f"   fallback (E2 lincheck restored, evalM replay in F): per node {alt} = 2^{math.log2(alt):.2f} ({2**21/alt:.2f}x)")
V_evalM = 2**16*3 + 2**14*3 + 2*(2*I_slot) + 2*20000*3
print(f"== V: evalM over templates ~{V_evalM} F-products (tables shared by the slots); measured V (S-F2, VM, N30) 183 ms + ~{V_evalM*60e-9*1000:.0f} ms = ~{183+V_evalM*60e-9*1000:.0f} ms VM against 264 ms VM-equivalent cap")
# ---- stage-review changes 17 (revision 3.12): F-7 redesign. E lincheck restored (one evalM at an F point, no evalMK),
# column items padded to 64-B multiples (regular column imports), full templating, run-structured trace imports, fused walks.
us=0.12   # VM planning cost of one F product in a flat table loop (us); the measured sparse boxed entry is ~1 us
pad_col=cols*48; tb17=tb+pad_col+23*(8+8+32+RND+32)+23*(8+8+32+32)+128*16   # columns padded; E lincheck 23 rounds (absorb+squeeze); RS0 fifth claim
comp17=math.ceil(tb17/64); pi17=pi+pad_col+23*RND+128*16; items17=items+46
# evalM at an F point, fully templated, per node (imports per slot, the rest shared between the slots)
tables=2**11+2**10+2**12+2**11+2*2**14
walk=2*(2**14+60000*0.3)          # fused walkAB: products per row + XOR accumulation (an XOR ~0.3 of a product)
loc=36000*2
reg=1500*30
runs=(sibs*3.5+sibs/8+451*2+512+2000)*2
pref=3000
per_slot_imports=reg+runs
evalM_F17=tables+walk+loc+pref+2*per_slot_imports   # two slots' import terms, shared LOC/walks/tables
evalM_sym=tables+walk+loc+pref+per_slot_imports     # slot-symmetric layout
walk_now=2*15000/us                                  # the walks as implemented: 15 ms each
print(f"== stage-review changes 17: F-7 redesign")
print(f"   format: columns padded +{pad_col} B; E lincheck +{23*RND} B; RS0 +{128*16} B: piSize {pi17} B ({2**20/pi17:.2f}x); items {items17} (qV {10240/items17:.2f}x); compressions/slot {comp17} (+{comp17-comp})")
print(f"   evalM (F point, one call) F-products: tables {tables:.0f}, walks {walk:.0f} (fused, optimised; as implemented {walk_now:.0f}), LOC {loc}, regular imports {reg}, run/irregular imports {runs:.0f}/slot, prefix {pref}")
print(f"   evalM total: two slots {evalM_F17:.0f} F ~ {evalM_F17*us/1000:.0f} ms VM (walks as implemented: {(evalM_F17-walk+walk_now)*us/1000:.0f} ms); slot-symmetric layout {evalM_sym:.0f} F ~ {evalM_sym*us/1000:.0f} ms")
base=166.3; finPf=8; evalL=3
for lab,x,e in (("plan, walks as implemented",(evalM_F17-walk+walk_now)*us/1000,0),("plan + fused walks",evalM_F17*us/1000,0),("plan + fused walks + S-F2 hot spots (-40 ms)",evalM_F17*us/1000,40),("+ symmetric layout",evalM_sym*us/1000,40)):
    v=base+finPf+evalL+x-e; print(f"   V N30 ({lab}): {v:.0f} ms VM = {v/1.28:.0f} ms runner; cap 205.9 ms runner: {205.9/(v/1.28):.2f}x")
# node rows per slot: S-E3's measured skeleton+templates (246,627 rows in slot 0's dump) + the templates still missing (A.11) + the evalM replay as rows + claim 5
replay_rows=tables+2*2**14+60000+loc+pref+2*per_slot_imports   # the child's evalM replay in F: XORs are linear (no rows) but the walk product rows are
missing=37335+45604+11400+2500*8+1000+500+2800     # tensorW, rsWeight (+claim 5), linkW, kindFoldWeight, kindInd, rowW/shiftTarget (A.11 figures)
rows17=246627+missing+128*134+replay_rows
H17=2*comp17+6+2*498+8+2*10
blocks17=H17+math.ceil(2*rows17*128/2**14)+L_blocks+1
print(f"   node rows: per slot {rows17:.0f} (dump 246,627 + missing templates {missing} + Phi claim 5 {128*134} + evalM replay {replay_rows:.0f}); per node {2*rows17:.0f} = 2^{math.log2(2*rows17):.2f} ({2**21/(2*rows17):.2f}x); blocks {blocks17} of 65536 ({65536/blocks17:.2f}x)")
# ---- stage-review changes 20 (revision 3.13): E before RS (S-G1j defect 1); Lr4 merged into the E4 lincheck (defect 2: one
# 23-round lincheck over the cells for the L and M rows, J_z = 4 again); node targetS/linkW (no size effect).
seq13=[]
def add13(ph,a,q,ab=0): seq13.append((ph,a,q,ab))
for ph,a,q,ab in seq:
    if ph in ("Lr4","RS0","RS1","Ep"): continue
    add13(ph,a,q,ab)
    if ph=="E3":
        add13("E4",23,23,RND); add13("E4end",1,0,16)
        add13("RS0",1,0,4*128*16); add13("RS1",0,math.ceil((7+1)/2)); add13("Ep",0,1)
pos=0; posmap={}
for ph,a,q,ab in seq13:
    posmap[ph]=(pos,pos+a+q-1); pos+=a+q
fs13=pos
print("== stage-review changes 20 (revision 3.13): phase order and FS positions")
print("   "+"; ".join(f"{ph} {p[0]}" + (f"-{p[1]}" if p[1]>p[0] else "") for ph,p in posmap.items() if ph in ("Lr1","Lr2","Lrend","Lr3","E1","E2","Eend","E3","E4","E4end","RS0","RS1","Ep","P1.0")))
items13=fs13+cols+sibs
tb13=1
for ph,a,q,ab in seq13:
    if ph=="seed": tb13+=8+7+112+32
    else: tb13+=a*(8+8+32+ab+32)+q*(8+8+32+32)
tb13+=cols*(8+8+32)+colb+pad_col+sibs*(8+8+64+32)
comp13=math.ceil(tb13/64)
piop13=sum(a*ab for ph,a,q,ab in seq13 if ph not in("seed","stmt","cap0") and not ph.startswith("C."))
pi13=48+128+piop13+caps+final+colb+pad_col+sibs*32
H13=2*comp13+6+2*498+8+2*10
rows13=rows17-11400-128*134        # rsWeight and Phi back to 4 claims
blocks13=H13+math.ceil(2*rows13*128/2**14)+L_blocks+1
print(f"   FS items {fs13} (was 451 + 46); items {items13} (qV {10240/items13:.2f}x); hashed bytes {tb13}, compressions/slot {comp13}")
print(f"   piSize {pi13} B = {pi13/1024:.0f} KiB ({2**20/pi13:.2f}x): PIOP {piop13}, columns {colb+pad_col}, siblings {sibs*32}, caps {caps}, final {final}")
print(f"   node rows per slot {rows13:.0f}, per node {2*rows13:.0f} = 2^{math.log2(2*rows13):.2f} ({2**21/(2*rows13):.2f}x); blocks {blocks13} of 65536 ({65536/blocks13:.2f}x)")
v13=base+finPf-4+3+evalM_F17*us/1000
print(f"   V N30: {v13:.0f} ms VM = {v13/1.28:.0f} ms runner ({205.9/(v13/1.28):.2f}x) with fused walks; {v13-40:.0f} ms VM = {(v13-40)/1.28:.0f} ms runner ({205.9/((v13-40)/1.28):.2f}x) with the S-F2 hot spots; stream link ~2.94 s of 3.1 s (one 2^23 lincheck pass, +0.14 s over 2.80 s)")
# ---- stage-review changes 21 (revision 3.14): INT-2 ratified (E4end 32 B), S-CN (8 families, WM map, linkWAll), S-E5's row model
pi14=pi13+16; tb14=tb13+16; comp14=math.ceil(tb14/64)
rows_e5_313=968943-32768-11400                 # S-E5's mRowModel at 3.12, less Phi's and rsWeight's fifth claim
rows14=rows_e5_313-20000+15000+16000           # A.11's linkW (8 x 2,500) -> tplLinkWAll 15 k; + tplTargetSNode 16 k
chainN=comp14; stmtBase=2*chainN; wotsBase=stmtBase+6; wmBase=wotsBase+2*498; wmEnd=wmBase+2*146; hEnd=wmEnd+8; lBase=47616; lEnd=lBase+124
Mblocks14=math.ceil(2*rows14*128/2**14)
print("== stage-review changes 21 (revision 3.14)")
print(f"   piSize {pi14} (E4end 32 B; {2**20/pi14:.2f}x); hashed bytes {tb14} = 64 x {comp14} (no padding); last block t_lo {tb14}")
print(f"   layout: chains end {stmtBase}; wotsBase {wotsBase}; wmBase {wmBase}; WM 2 x 146 blocks end {wmEnd} (< lBase {lBase}); hEnd {hEnd}; L ends {lEnd} of 49,152 ({49152/lEnd:.2f}x)")
print(f"   node rows per slot {rows14} (S-E5 3.12 model {968943} - 44,168 claim 5 - 20,000 + 31,000); per node {2*rows14} = 2^{math.log2(2*rows14):.2f} ({2**21/(2*rows14):.2f}x); M blocks {Mblocks14} of 16,384 ({16384/Mblocks14:.2f}x); used blocks {lEnd+Mblocks14}")
v14=204.9+4.5+2.0+1.9
print(f"   V N30: measured 204.9 ms VM (S-E5, with evalM) + evalLT 4.5 + targetSNode 2.0 + linkWAll 1.9 = {v14:.1f} ms VM ({264/v14:.2f}x of 264 VM-equivalent) = {v14/1.28:.0f} ms runner ({205.9/(v14/1.28):.2f}x); stream link (P2 §12 estimate) ~3.0 s of 3.1 s (1.03x)")
# ---- changes 21 item (D): the replay fixed point, option (a) (constant-coefficient linear replay). R's rows per slot:
R_tables=2**11+2**10+2**12+2**11+2*2**14      # eq trees over tau/sigma prefixes and the walks' 14-bit tables (closed form O(log^2))
R_walks=2*(2**14+2**14)                        # per walk: u-rows (linear, nnz(A0) constant entries) + v-rows (products)
R_loc=2*15000                                  # per key: u-rows (linear, the template's entries as constants) + v-rows
R_reg=1500*22                                  # regular imports: bit-by-bit product chains reading the challenge cells (Addr constants in the forms)
R_irr=2*(sibs*3.5+sibs/8+451*2+512+2000)*1 + 2*(sibs+2000)   # run/irregular imports of the child's two slots: products + the Inc u-rows
R_pref=3000; R_misc=5000
R=R_tables+R_walks+R_loc+R_reg+R_irr+R_pref+R_misc
rows_e6=1017848                                 # S-E6 mRowModel per slot (replay at 422,912; targetS 10 k; linkW 20 k)
rows14D=rows_e6-422912+R-10000+16000-20000+15000
rows14D_lever=rows14D-62000
print("== changes 21 (D): replay fixed point, option (a)")
print(f"   R per slot {R:.0f} rows: eq trees {R_tables}, walks {R_walks}, template u/v rows {R_loc}, regular imports {R_reg}, run/irregular imports {R_irr:.0f}, prefix/misc {R_pref+R_misc} (was 422,912)")
print(f"   mRowModel per slot {rows14D:.0f} (S-E6 1,017,848 - 422,912 + R + targetSNode/linkWAll resize); per node {2*rows14D:.0f} = 2^{math.log2(2*rows14D):.2f} ({2**21/(2*rows14D):.2f}x); with the phiRS padding lever {rows14D_lever:.0f}/slot ({2**21/(2*rows14D_lever):.2f}x); M blocks {math.ceil(2*rows14D*128/2**14)} of 16,384")
# V budget: S-E6 measured 229.3 ms (M without rsWeight, walkAB, shiftTarget, 745 tensorW, linkW, R)
base6=229.3; add_link=1.9; add_tpl=3.0; add_walks_fast=16; add_walks_now=30; add_R=5
for lab,w,lever in (("fused walks (8 ms each), no other lever",add_walks_fast,0),("walks as implemented (15 ms each)",add_walks_now,0),("fused walks + S-F2 hot spots (-40 ms)",add_walks_fast,40)):
    v=base6+add_link+add_tpl+w+add_R-lever
    print(f"   V N30 ({lab}): {v:.0f} ms VM ({264/v:.2f}x of 264) = {v/1.28:.0f} ms runner ({205.9/(v/1.28):.2f}x)")
# ---- stage-review changes 22 (revision 3.15): S-E9's measured sizes; the walk ruling (XOR-DAG rows in the G-template layout,
# D-hat closed form: R replays no walk); the levers. Inputs: S-E9 §1 (rstat-0, rcount.py), §6.
meas=436092; rsW=45604; walkDAG=90851; shT=1300; tW=47680; tgtN=16000; lkA=15000
# rcount.py's R1s classes (per slot): tables 48,400; keys 29,623; per-child-slot 193,472 (beta 61,530 + alpha 18,507 + sparse 55,065 + shared 20,112 + own 11,116 + inst 27,142); walks 106,496; closed forms 8,300; out 1,000
R_T=48400; R_K=29623; R_beta=61530; R_alpha=18507; R_sparse=55065; R_shared=20112; R_own=11116; R_inst=27142; R_Psi=8300; R_out=1000
R_walk_DAG=106496+25315               # S-E9: R replays the walk as the XOR DAG (412,606 - 387,291 over the u/v-row walk)
R_walk_Dhat=13000                     # ruling: the DAG rows' MLE is the G-template closed form (80 instances + 480 word wires): no walk in R
R0=R_T+R_K+R_beta+R_alpha+R_sparse+R_shared+R_own+R_inst+R_Psi+R_out
R_E9=R0+R_walk_DAG; R_rule=R0+R_walk_Dhat
lever_phi=62464; lever_sparse=110000; lever_inst=20000
def node(rows): return 2*rows
rows_E9=meas+rsW+walkDAG+shT+tW+tgtN+lkA+R_E9
rows_A=meas+rsW+walkDAG+shT+tW+tgtN+lkA+R_rule
rows_B=rows_A-lever_phi
rows_C=rows_B-lever_sparse-lever_inst
print("== stage-review changes 22 (revision 3.15): rows per slot / per node")
for lab,r in (("S-E9 as sized (DAG walk replayed in R)",rows_E9),("ruling: D-hat closed form in R",rows_A),("+ phiRS key split (-62,464, measured)",rows_B),("+ sparse-skeleton templating (-110 k) + instance AP layout (-20 k)",rows_C)):
    print(f"   {lab}: {r:.0f} per slot, {node(r):.0f} per node = 2^{math.log2(node(r)):.3f} ({2**21/node(r):.3f}x); M blocks {math.ceil(node(r)*128/2**14)} of 16,384; used blocks {47740+math.ceil(node(r)*128/2**14)} of 65,536 ({65536/(47740+math.ceil(node(r)*128/2**14)):.3f}x)")
print(f"   R per slot: S-E9 {R_E9} -> ruling {R_rule} -> with the skeleton/instance levers {R_rule-lever_sparse-lever_inst}")
# T_V (VM): S-E8 169.4 ms (maskRows foreign); S-E9 207.2 with maskRows bound (+39 ms, evaluator defect); fix: shift class
v_base=169.4; v_mask=1.0; v_tpl=4.0; v_Dhat=1.5; v_R=7.0
v15=v_base+v_mask+v_tpl+v_Dhat+v_R
print(f"   V N30: 169.4 (S-E8) + maskRows shift class {v_mask} + remaining templates {v_tpl} + D-hat {v_Dhat} + R closed forms/Inc {v_R} = {v15:.0f} ms VM ({264/v15:.2f}x of 264) = {v15/1.28:.0f} ms runner ({205.9/(v15/1.28):.2f}x); S-E9's projection with two replayed walks was 231-240 ms")
print(f"   stream link: P2 estimate ~3.0 s of 3.1 s (1.03x) before the ruling; nnz(M) falls by ~{(rows_E9-rows_B)/rows_E9*100:.0f}% (rows) -> P2 re-measures; target >= 1.05x = 2.95 s")
# ---- stage-review changes 23 (revision 3.16): R-V-M1 (a) the Phi-aware kind factor in rsWeight's claim 2; R-V-M2 the free term as a
# closed form; H-V's measured VM -> 7763 ratio 1.19 (not the checker's 1.28); cap 206.0 ms measured.
RATIO=1.19; CAP=206.0
kf_products=128*22*24           # 128 Frobenius stages x ~22 kind pattern-intervals x ~24 products (per-bit factors + dyadic range sums)
kf_rows=kf_products+7*127       # + beta's Frobenius chains (7 kinds x 127 squarings)
free_term=64+8+8                # (1+alpha) v_free <rowW, eq(r_k)>: 64-term sum + eqPt on 8 coordinates
rows16=rows_B+kf_rows+free_term+3000     # changes-22 baseline (phiRS split) + kind factor + free term + R's closed-form share
rows16_lever=rows16-lever_sparse-lever_inst
v16=v15+kf_products*0.09/1000+0.05
print("== stage-review changes 23 (revision 3.16)")
print(f"   R-V-M1 (a): kind factor ~{kf_products} products (~{kf_products*0.09/1000:.1f} ms VM), rows +{kf_rows} per slot; items, piSize, error rows unchanged. (b) would cost items +36, pi +864 B, error 3*18/2^128 and a second 2^30-bit fold pass in the prover (~0.2-0.3 s on a 3.0 s link).")
print(f"   rows per slot {rows16:.0f}, per node {2*rows16:.0f} = 2^{math.log2(2*rows16):.3f} ({2**21/(2*rows16):.3f}x); with the sparse-skeleton + instance-AP levers {rows16_lever:.0f} per slot ({2**21/(2*rows16_lever):.3f}x); M blocks {math.ceil(2*rows16*128/2**14)} of 16,384; used {47740+math.ceil(2*rows16*128/2**14)} ({65536/(47740+math.ceil(2*rows16*128/2**14)):.3f}x)")
print(f"   T_V: {v16:.0f} ms VM -> {v16/RATIO:.0f} ms on the 7763 (ratio {RATIO}); cap {CAP} ms: {CAP/(v16/RATIO):.2f}x. Measured H-V: V N30 best 169.9-175.6 ms on the 7763 (maskRows slowdown included), cap 206.0: 1.17-1.21x; 183 ms VM (changes 22) = {183/RATIO:.0f} ms runner ({CAP/(183/RATIO):.2f}x)")
print(f"   piSize 797904 (1.31x); items 8891 (1.15x); stream link: P2 estimate ~3.0 s of 3.1 s (re-measure)")
# ---- stage-review changes 24 (revision 3.17): S-N1's O2/O2b complete budget; INT-5's measured V; the T_V frontier.
parts24={"measured aligned layout (S-E9: skeleton + bound templates)":436092,"rsWeight (4 claims)":45604,"rsWeight claim-2 kind factor":68473,
 "walkAB (XOR DAG, G-template)":90851,"shiftTarget (bnd 22)":1300,"745 tensorW":47680,"tplTargetSNode":16000,"tplLinkWAll":15000,
 "evalL replay (closed-form L regions; risk +30 k if chunked)":10000,"free term":80,"WOTS mux: selectors 266, a_{i,s} 1,596, e_i 532, path l/r 128, digit->h_out 266":2788,
 "R (293,795 + 3,000 kind-factor share)":296795,"phiRS key split":-62464,"sparse-skeleton templating":-110000,"instance AP layout":-20000}
rows24=sum(parts24.values())
print("== stage-review changes 24 (revision 3.17): O2/O2b complete row budget per slot")
for k,v in parts24.items(): print(f"   {v:>9} {k}")
print(f"   total {rows24} per slot; {2*rows24} per node = 2^{math.log2(2*rows24):.3f} ({2**21/(2*rows24):.3f}x); with the evalL-replay risk {2**21/(2*(rows24+30000)):.3f}x; M blocks {math.ceil(2*rows24*128/2**14)} of 16,384; used {47740+math.ceil(2*rows24*128/2**14)} ({65536/(47740+math.ceil(2*rows24*128/2**14)):.3f}x)")
# T_V frontier (VM ms; ratio 1.19; cap 206.0)
base=192.9      # S-E11 HEAD (maskRows fixed, S-E11 evaluator), before the kind factor
kf_now=33.0; kf_ST1_full=8.0; kf_ST1_part=20.0; e11=12.0; tobind=7+1.5+4+1+0.3
for lab,kf,ev in (("INT-5 as measured (226-233), + to-bind",kf_now,0),("S-T1 kind factor to ~20 ms, no S-E11 levers",kf_ST1_part,0),("S-T1 to ~20 ms + S-E11 levers",kf_ST1_part,e11),("S-T1 to ~8 ms (F-side, shared endpoints) + S-E11 levers",kf_ST1_full,e11)):
    v=base+kf+tobind-ev; print(f"   T_V ({lab}): {v:.0f} ms VM = {v/RATIO:.0f} ms on the 7763 -> {CAP/(v/RATIO):.2f}x")
print(f"   >= 1.10x needs V <= {CAP/1.10*RATIO:.0f} ms VM ({CAP/1.10:.0f} ms runner); the floor with the current evaluator is ~{base+kf_ST1_full+tobind-e11:.0f} ms VM")
