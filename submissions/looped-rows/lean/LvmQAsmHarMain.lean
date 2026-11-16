-- New for lvm (HAR-TOP): the node-level `harith` (BLUEPRINT §12.6): Q_arith's rows and assertions (gate on)
-- give `decideCore = true` and `accOutOf = accIn x` on the child's stream, composed from the phase families'
-- replay lemmas (`busG_replays`, `tabG_replays`, `qacc_replays`, `p47_at`, the claim equations, `openPh_run`)
-- through `core_of_phases`. Generic in the configuration `C` and the placement record `D`.
import LvmQAsmHarP47
import LvmQAsmHarShape
import LvmQAsmHarIn
import LvmQShapeH
import LvmQAsmArith2WhirP
import LvmQAsmHarTails

/-!
# `harith_core`

**`harith_core C D G …`**: wherever `qarith' C D = phases47 C >>= qarithT C D` holds and asserts at `p2`
(the node flag on, `PUB` lane 0 = 1), and the stream cells bind `Σ'` (`Streamed M Σ' T`), the child's
`decideCore` accepts and its folded accumulator is the current proof's `acc_in` (`accC M (pbB C)`, its
`PUB` cells), for `M3.real C.p (tabs C G D)` with any cache `G` (the circuit reads only the tables'
shapes, `tabs_shape`).

Hypotheses: the static facts of `(C, D)` in `HarStatic` (positions, lane bounds, glue `SLok` checks,
WHIR layouts; decidable on the final record), the memory facts (`Streamed`, the gate, `PUB`'s `vk`
lanes, `SBits`/`NBits`, the position cells `PosOk`), `1 ≤ n'`, the end of `Σ'`, and the claims'
well-formedness `ClaimsWF` on the claim list Q_arith builds (`qarithCs`).
-/

set_option autoImplicit false

namespace Lvm.Har

open Lvm Lvm.Loop Lvm.Loop.Build Lvm.Q1 Lvm.QAsm DM

/-- **Q_arith on the record `D`** (`qarith C = qarith' C (dataOf C)`). -/
def qarith' (C : QCfg) (D : QData) : BM Unit := phases47 C >>= qarithT C D

theorem qarith_eq' (C : QCfg) : qarith C = qarith' C (dataOf C) := rfl

/-! ## Helpers -/

/-! ## Phase 2 (bus) -/

/-! ## Phase 3 (tables) -/

theorem evLoads_length : ∀ (ws : List Nat) (a : Nat) (p : Ptr), (evLoads a ws p).1.length = ws.length
  | [], _, _ => rfl
  | w :: ws, a, p => by
    simp only [evLoads, bind_apply, pure_apply, List.length_cons]
    rw [evLoads_length ws]

/-- **The table gadget's output**: per table its point cells (the rounds' challenge cells, reversed,
the first `τ`) and its evaluation cells. -/
theorem tabG_fst (S : List TShape) (R P : Nat) (z o g : Cell) (bc : BusC) (ptr : Ptr) :
    ∃ (qe : Nat) (evs : List (List Cell)), evs.length = S.length ∧
      (tabG S R P z o g bc ptr).1 =
        (S.zip evs).map fun x => (((List.range R).map (chC qe)).reverse.take x.1.τ, x.2) := by
  simp only [tabG, bind_apply, pure_apply]
  exact ⟨_, _, by rw [evLoads_length]; simp, rfl⟩

/-- The longest point's length (`tablePointC`) is the largest length. -/
theorem tablePointC_len : ∀ (l : List (List Cell × List Cell)) (r : List Cell),
    (l.foldl (fun r e => if r.length < e.1.length then e.1 else r) r).length =
      (l.map (·.1.length)).foldl max r.length
  | [], _ => rfl
  | e :: l, r => by
    simp only [List.foldl_cons, List.map_cons]
    rw [tablePointC_len l]
    congr 1
    split_ifs with h <;> omega

theorem foldl_max_le : ∀ (l : List Nat) (a R : Nat), a ≤ R → (∀ x ∈ l, x ≤ R) → l.foldl max a ≤ R
  | [], _, _, ha, _ => ha
  | x :: l, a, R, ha, hl => by
    simp only [List.foldl_cons]
    exact foldl_max_le l _ R (max_le ha (hl x (List.mem_cons_self ..)))
      fun y hy => hl y (List.mem_cons_of_mem _ hy)

/-- What `Q_acc` needs of the table gadget's output: `PUB`'s point cells are `E` cells, `10` of them; the
longest point has `tableRounds` cells. -/
theorem tab_facts (S : List TShape) (R P : Nat) (z o g : Cell) (bc : BusC) (ptr : Ptr) (pt : Nat)
    (hpt : pt < S.length) (hτ : (S.map (·.τ)).getD pt 0 = 10) (h10 : 10 ≤ R)
    (hmax : ∃ s ∈ S, R ≤ s.τ) :
    (∀ x ∈ ((tabG S R P z o g bc ptr).1.getD pt default).1, x.ty = .E) ∧
    ((tabG S R P z o g bc ptr).1.getD pt default).1.length = 10 ∧
    (Lvm.QAcc.tablePointC (tabG S R P z o g bc ptr).1).length = R := by
  obtain ⟨qe, evs, hl, he⟩ := tabG_fst S R P z o g bc ptr
  rw [he]
  have hz : (S.zip evs).length = S.length := by simp [hl]
  have hg : ((S.zip evs).map fun x => (((List.range R).map (chC qe)).reverse.take x.1.τ, x.2)).getD pt
      default = (((List.range R).map (chC qe)).reverse.take S[pt].τ, evs.getD pt default) := by
    rw [List.getD_eq_getElem _ _ (by simp [hz, hpt]), List.getElem_map, List.getElem_zip,
      List.getD_eq_getElem _ _ (by omega)]
  have hτ' : S[pt].τ = 10 := by
    rw [← hτ, List.getD_eq_getElem _ _ (by simpa using hpt), List.getElem_map]
  refine ⟨?_, ?_, ?_⟩
  · rw [hg]
    intro x hx
    obtain ⟨i, -, rfl⟩ := List.mem_map.mp (List.mem_reverse.mp (List.mem_of_mem_take hx))
    rfl
  · rw [hg, hτ']
    simp only [List.length_take, List.length_reverse, List.length_map, List.length_range]
    omega
  · unfold Lvm.QAcc.tablePointC
    rw [tablePointC_len]
    have e : ((S.zip evs).map fun x => (((List.range R).map (chC qe)).reverse.take x.1.τ, x.2)).map
        (·.1.length) = S.map fun s => min s.τ R := by
      rw [List.map_map]
      have h1 : (S.zip evs).map Prod.fst = S := List.map_fst_zip (by omega)
      conv_rhs => rw [← h1]
      rw [List.map_map]
      refine List.map_congr_left fun x _ => ?_
      simp
    rw [e]
    apply le_antisymm
    · exact foldl_max_le _ _ _ (Nat.zero_le _) fun x hx => by
        obtain ⟨s, -, rfl⟩ := List.mem_map.mp hx; exact Nat.min_le_right _ _
    · obtain ⟨s, hs, hR⟩ := hmax
      have := (le_foldl_max (S.map fun s => min s.τ R) ([] : List Cell).length).2 (min s.τ R)
        (List.mem_map.mpr ⟨s, hs, rfl⟩)
      omega

/-! ## `fixCols`' cells depend only on the shapes -/

theorem fixColsR_idx (ts : List M3.Tab) (pubTab : Nat) :
    (M3.fixColsR ts pubTab).map (fun c => (c.tab, c.col)) = fixIdx (ts.map M3.Tab.shape) pubTab := by
  unfold M3.fixColsR fixIdx
  rw [List.map_flatMap, List.zipIdx_map, List.flatMap_map]
  refine List.flatMap_congr fun x _ => ?_
  rcases x with ⟨t, j⟩
  rw [List.map_filterMap]
  simp only [M3.Tab.shape, Prod.map, id_eq]
  rw [List.zipIdx_map, List.filterMap_map]
  refine List.filterMap_congr fun ci _ => ?_
  rcases ci with ⟨col, i⟩
  cases col with
  | com rec off => rfl
  | fix f ev =>
    simp only [colKind, Function.comp_apply, Prod.map, id_eq]
    split_ifs <;> rfl

/-- `fixCellsR` on the shapes' indices. -/
theorem fixCellsR_idx (ts : List M3.Tab) (pubTab : Nat) (evc : List (List Cell × List Cell)) (zc : Cell) :
    Lvm.QAcc.fixCellsR ts pubTab evc zc =
      (fixIdx (ts.map M3.Tab.shape) pubTab).map fun ji => (evc.getD ji.1 default).2.getD ji.2 zc := by
  rw [← fixColsR_idx, List.map_map]
  rfl

theorem fixCellsR_shape (ts ts' : List M3.Tab) (pubTab : Nat) (evc : List (List Cell × List Cell)) (zc : Cell)
    (h : ts.map M3.Tab.shape = ts'.map M3.Tab.shape) :
    Lvm.QAcc.fixCellsR ts pubTab evc zc = Lvm.QAcc.fixCellsR ts' pubTab evc zc := by
  rw [fixCellsR_idx, fixCellsR_idx, h]

/-- A public array's shape does not depend on its values. -/
theorem pubArr_shape (τ base stride : Nat) (val fin : Bool × Nat) (vals vals' : List FK) :
    (M3.pubArr τ base stride val fin vals).tab.shape = (M3.pubArr τ base stride val fin vals').tab.shape :=
  inArr_shape _ _ rfl rfl rfl rfl rfl rfl rfl

/-- `arrsS` has `arrs`' shapes. -/
theorem arrsS_shape (C : QCfg) (D : QData) (P : Pub) :
    (arrsS C D).map (·.tab.shape) = (arrs C D P).map (·.tab.shape) := by
  unfold arrsS arrs
  simp only [List.map_append, List.map_cons, List.map_nil]
  rw [pubArr_shape _ _ _ _ _ [] (hdrOfPub P), pubArr_shape _ _ _ _ _ [] (Lvm.QLink.qltData C.p (lay C))]

/-- **The table shapes the circuit is built from are those of `tabs C G D pub`** (any cache, any `PUB`). -/
theorem shapesOf_eq (C : QCfg) (D : QData) (G : M3.PG) (pub : Pub) :
    shapesOf C D = (M3.sumcheckTabs (tabs C G D pub)).map M3.Tab.shape := by
  rw [shapesOf, sumcheckTabs_shape, sumcheckTabs_shape, tabsS, tabs,
    lvmTabsC_shape G0 G (plOf D) D.groups (arrsS C D) (arrs C D pub) (aux C D) (arrsS_shape C D pub)]

/-! ## The static facts -/

/-- The lane of phase 3b's start (`accInOf`'s `L`). -/
def accL (C : QCfg) (D : QData) : Nat := tabEnd (shapesOf C D) C.p.tableRounds (tabPos C.p) / 8

/-- The lane of phase 3b's zero-scalar position (`AccIn.z0`); phase 4 starts at `8 · accZ0 + 24`. -/
def accZ0 (C : QCfg) (D : QData) : Nat := accL C D + 9 * C.p.accLog + 3 * (accVars + 1) + 9

/-- **The static facts of `(C, D)`** that `harith_core` uses (decidable on the final record; `T` the
stream's lanes, `P4 … P8` the starts of phases 4–8). -/
structure HarStatic (C : QCfg) (D : QData) (T P4 P5 P6 P7 P8 : Nat) : Prop where
  /-- Phases 4–7 (`p47_at`): positions, sizes, lane bounds, the links' glue checks. -/
  pos47 : P47Pos C.p P4 P5 P6 P7 P8
  hn : 5 ≤ C.p.logN
  hk : 4 ≤ C.p.ksLog
  hlay : layOk (C.p.logN - 5) = true
  hlayk : layOk (C.p.ksLog - 4) = true
  hq : 5 ≤ aLane C.p 2
  hqw : 5 ≤ aLane C.p 3
  hqk : 5 ≤ aLane C.p 6
  hTw : Lvm.Q1.wireEnd (C.p.logN - 5) (aLane C.p 3) + 2 ≤ T
  hTgk : gkrEnd (C.p.ksLog - 4) (aLane C.p 6) + 48 ≤ T
  hTr : aLane C.p 0 + 9 * C.p.logN + 2 < T
  hTv : aLane C.p 1 + 3 * 25 + 2 < T
  hTrk : aLane C.p 4 + 9 * C.p.ksLog + 2 < T
  hTvk : aLane C.p 5 + 3 * 25 + 2 < T
  hD : C.p.logN ≤ 2 ^ clog2 C.p.logN
  hDk : C.p.ksLog ≤ 2 ^ clog2 C.p.ksLog
  hTlk : ksQV C.p.ksLog (aLane C.p 7) + 3 * 4 + 3 ≤ T
  hTlk' : aLane C.p 7 + 9 * (C.p.ksLog + laneBits) + 15 * C.p.ksLog + 12 ≤ T
  hB : 1 ≤ spongeBlocks C.p
  hB2 : spongeBlocks C.p ≤ 2 ^ C.p.ksLog
  /-- `KS`'s WOTS group fits above the split (lvm2 CR-K, KS14). -/
  hK : ksSplit C.p + 431 ≤ 2 ^ C.p.ksLog
  /-- Block E of the `KS` link (`ksBlockE`: KS14's or v1's). -/
  okE : ∀ sh : LoopOut, SLok (ksBlockE C.p (aLane C.p 7) sh (kc (pbB C))) = true
  /-- Phase 2 (`busG_replays`). -/
  hld : C.p.leafdecReads = 1
  hbP : busPos C.p % 8 = 0
  hbT : busEnd C.p (busPos C.p) + 40 ≤ 8 * T
  /-- Phase 3 (`tabG_replays`): position, lanes, `PUB`'s table, the tallest table. -/
  htP : tabPos C.p % 8 = 0
  htT : tabEnd (shapesOf C D) C.p.tableRounds (tabPos C.p) + 40 ≤ 8 * T
  hpubT : C.p.pubTab < (shapesOf C D).length
  hpubτ : ((shapesOf C D).map (·.τ)).getD C.p.pubTab 0 = 10
  h10 : 10 ≤ C.p.tableRounds
  hRmax : ∃ s ∈ shapesOf C D, C.p.tableRounds ≤ s.τ
  /-- Phase 3b (`qacc_replays`). -/
  hRacc : C.p.tableRounds ≤ accVars
  hdk1 : 1 ≤ C.p.accLog
  hnf : (fixIdx (shapesOf C D) C.p.pubTab).length ≤ 2 ^ C.p.accLog
  hzL : accZ0 C D + 5 + 2 < T
  hH : 11 + pubLanes ≤ T
  hP4 : 8 * accZ0 C D + 24 = P4
  /-- The claims (the header lanes `pub_h`, `pub_s`). -/
  hT29 : 29 ≤ T
  hlog64 : C.p.logN ≤ 64
  /-- Phases 8–9 (`openPh_run`): the layouts, the start. -/
  hlr : LayOk (cfgRec C.p (posBase C) (pwBase C)) T = true
  hlm : LayOk (cfgMain C.p (posBase C) (pwBase C)) T = true
  hP8 : P8 = 8 * openU C.p
  /-- The PoW class's rows cover the openings (`C_rec`'s levels, then `C_main`'s). -/
  hop : C.p.recLevels.length ≤ (Lvm.QLink.opens C.p).length ∧
    C.p.recLevels.length + C.p.mainLevels.length ≤ (Lvm.QLink.opens C.p).length

/-! ## Phases 2, 3, 3b -/

theorem tabEnd_eight {S : List TShape} {R P : Nat} (hP : P % 8 = 0) : 8 * (tabEnd S R P / 8) = tabEnd S R P :=
  Nat.mul_div_cancel' (Nat.dvd_of_mod_eq_zero (by simp only [tabEnd]; omega))

/-- **Phases 2, 3 and 3b as `PhaseAt` facts** from the bus, table and `Q_acc` gadgets' rows and
assertions (gate on): the values are the output cells' values, phase 3b's is the current proof's
`acc_in` (`accC M (pbB C)`); the bus flag holds. -/
theorem p23_at (C : QCfg) (D : QData) (G : M3.PG) (vk cL : Vector UInt8 32) {c : Ctx} {M : Mem}
    {sig : ByteArray} {T P4 P5 P6 P7 P8 : Nat} (hst : HarStatic C D T P4 P5 P6 P7 P8)
    (hS : Streamed M sig T) (hg : M.k (pbB C) = 1)
    (hvk : ∀ i < 4, M.k (pbB C + 1 + i) = (digestLanes vk).getD i 0)
    {z one : Cell} (hzE : z.ty = .E) (hoE : one.ty = .E) (hz : z.val M = 0) (ho : one.val M = 1)
    {q2 q3 q4 : Ptr} {bus : BusC} {tab : List (List Cell × List Cell)}
    (hB : Lvm.QSig.Ok c M (busG C.p z one (kc (pbB C)) (busPos C.p)) q2)
    (hbus : (busG C.p z one (kc (pbB C)) (busPos C.p) q2).1 = bus)
    (hT : Lvm.QSig.Ok c M (tabG (shapesOf C D) C.p.tableRounds (tabPos C.p) z one (kc (pbB C)) bus) q3)
    (htab : (tabG (shapesOf C D) C.p.tableRounds (tabPos C.p) z one (kc (pbB C)) bus q3).1 = tab)
    (hA : Lvm.QSig.Ok c M (Lvm.QAcc.qacc (accInOf C (shapesOf C D) tab z)) q4) :
    PhaseAt (busPh C.p) sig (busPos C.p) (tabPos C.p) (busV M bus) ∧
    ((M3.real C.p (tabs C G D)).busFinal ⟨vs M bus.al, bus.be.val M, bus.cnt.val M, vs M bus.pt,
      vs M bus.vals, [0], pubOf vk cL sig⟩).ok = true ∧
    PhaseAt (tabPh C.p (M3.real C.p (tabs C G D)) (pubOf vk cL sig)
      ((M3.real C.p (tabs C G D)).busFinal ⟨vs M bus.al, bus.be.val M, bus.cnt.val M, vs M bus.pt,
        vs M bus.vals, [0], pubOf vk cL sig⟩) (vs M bus.pt))
      sig (tabPos C.p) (8 * accL C D) (Lvm.QAcc.evV M tab) ∧
    PhaseAt (accFold C.p (M3.real C.p (tabs C G D)) (pubOf vk cL sig) (Lvm.QAcc.evV M tab)) sig
      (8 * accL C D) P4 (Lvm.QAcc.accC M (pbB C)) := by
  have hgv : (kc (pbB C)).val M = 1 := gate_val C hg
  -- phase 2
  have rb := busG_replays (c := c) hS hz ho hgv C.p hst.hld hst.hbP hst.hbT q2
  have hb : PhaseAt (busPh C.p) sig (busPos C.p) (tabPos C.p) (busV M bus) :=
    phaseAt_of rb hB fun a ha => (busR_eq (hbus ▸ ha)).1
  obtain ⟨-, -, hR⟩ := rb hB ⟨busPos C.p, 0, true⟩ rfl rfl
  rw [hbus] at hR
  have h3 := (busR_eq hR).2
  have hok : ((M3.real C.p (tabs C G D)).busFinal ⟨vs M bus.al, bus.be.val M, bus.cnt.val M, vs M bus.pt,
      vs M bus.vals, [0], pubOf vk cL sig⟩).ok = ((vs M bus.vals).length == 3 && [(0 : FE)] == [0]) := rfl
  rw [hok, h3]
  refine ⟨hb, by decide, ?_⟩
  -- phase 3
  obtain ⟨hal, d, hpt⟩ := busG_fst C.p z one (kc (pbB C)) (busPos C.p) q2
  rw [hbus] at hal hpt
  obtain ⟨hE, h10, hRl⟩ := tab_facts (shapesOf C D) C.p.tableRounds (tabPos C.p) z one (kc (pbB C)) bus q3
    C.p.pubTab hst.hpubT hst.hpubτ hst.h10 hst.hRmax
  rw [htab] at hE h10 hRl
  have hS0 := shapesOf_eq C D G (pubOf vk cL sig)
  have hL : 8 * accL C D = tabEnd ((M3.sumcheckTabs (tabs C G D (pubOf vk cL sig))).map M3.Tab.shape)
      C.p.tableRounds (tabPos C.p) := by
    rw [accL, tabEnd_eight hst.htP, hS0]
  rw [hS0] at hT htab
  have rt := tabG_replays (c := c) hS hz ho hgv hzE hoE C.p (M3.real C.p (tabs C G D)) (pubOf vk cL sig)
    (tabs C G D (pubOf vk cL sig)) rfl bus (countRoot := bus.cnt.val M) (leafdec := [0]) rfl rfl rfl rfl
    (by rw [hal]; simp [vs, busBits])
    (by rw [hal]; intro x hx; obtain ⟨i, -, rfl⟩ := List.mem_map.mp hx; rfl)
    (by rw [hpt]; intro x hx; obtain ⟨i, -, rfl⟩ := List.mem_map.mp hx; rfl)
    _ rfl hst.htP (by rw [← hS0]; exact hst.htT) q3
  refine ⟨hL ▸ phaseAt_of rt hT fun a ha => by rw [htab] at ha; exact ha, ?_⟩
  -- phase 3b
  have hpp : ∀ i, ((accInOf C (shapesOf C D) tab z).pp i).ty = .E := by
    intro i
    show ((tab.getD C.p.pubTab default).1.getD i (ec 0)).ty = .E
    rw [List.getD_eq_getElem?_getD]
    cases hx : (tab.getD C.p.pubTab default).1[i]? with
    | none => rfl
    | some x => exact hE x (List.mem_of_getElem? hx)
  have hfs : (M3.real C.p (tabs C G D)).fixSent (pubOf vk cL sig) (Lvm.QAcc.evV M tab) =
      (accInOf C (shapesOf C D) tab z).fx.map (Cell.val M) := by
    show M3.fixSentR (M3.sumcheckTabs (tabs C G D (pubOf vk cL sig))) C.p.pubTab (Lvm.QAcc.evV M tab) =
      ((fixIdx (shapesOf C D) C.p.pubTab).map fun ji => (tab.getD ji.1 default).2.getD ji.2 z).map (Cell.val M)
    rw [Lvm.QAcc.fixSentR_evV _ _ _ hz, fixCellsR_idx, ← hS0]
  have ra := Lvm.QAcc.qacc_replays (c := c) (A := accInOf C (shapesOf C D) tab z) (p := q4) C.p
    (M3.real C.p (tabs C G D)) vk cL (Lvm.QAcc.evV M tab) hS (by show accZ0 C D + 5 + 2 < T; exact hst.hzL) hst.hH
    hg hpp (by show pubLanes ≤ 2 ^ 10; decide) (Nat.div_le_self _ _)
    (by show (List.map _ _).length ≤ _; rw [List.length_map]; exact hst.hnf)
    (by show (Lvm.QAcc.tablePointC tab).length + C.p.accLog = accVars
        rw [hRl, Params.accLog]; have := hst.hRacc; omega)
    rfl hst.hdk1 hvk h10 hfs (Lvm.QAcc.pubCheckR_evV _ _ _ hz) (Lvm.QAcc.tablePoint_evV tab)
  have e4 : 8 * (accInOf C (shapesOf C D) tab z).z0 + 24 = P4 := hst.hP4
  exact e4 ▸ phaseAt_of ra hA fun a ha => ha

/-! ## The claims of phases 8–9 -/

/-- **The claim list Q_arith builds is `F`'s** (`claimsOf`, phase 8's list) on the values of the phases'
cells: the table claims (phase 3's cells), the tape's claims (`tapeClaimsC_val`), `KS`'s Keccak claims
(the ring switch as `F` computes it after the GKR, `ringGkr_rel`), the link's claims (`F`'s link view at
`P7`), `KS`'s output claims. -/
theorem claims_at (C : QCfg) (D : QData) (G : M3.PG) (vk cL : Vector UInt8 32) {c : Ctx} {M : Mem}
    {sig : ByteArray} {T P4 P5 P6 P7 P8 : Nat} (hst : HarStatic C D T P4 P5 P6 P7 P8)
    (hS : Streamed M sig T) {p2 : Ptr} (h47 : Lvm.QSig.Ok c M (phases47 C) p2)
    {o : P47Out} (ho47 : (phases47 C p2).1 = o) {tp : TapeRes} {wo : WireOut}
    (htw : TW C M o (pubOf vk cL sig) tp wo)
    {ze oe : Nat} (hz : M.e ze = 0) (ho : M.e oe = 1) (bus : BusOut) (hbus : bus.claims = [])
    (tab : List (List Cell × List Cell)) {q8 q9 : Ptr}
    (h8 : SegsHold c M q8 (ringGkr (C.p.ksLog - 4) (aLane C.p 6) ze q8).2)
    (h9 : SegsHold c M q9 (ksLinkG C.p (aLane C.p 7) ze oe q9).2) :
    (claimsC (tabClaims (shapesOf C D) tab (ec ze)) (tapeClaimsC C.p ze oe o)
      (kClaimsC ⟨C.p.ksLog + slotLog, (layout0 C.p).ks⟩ o.kko (ringGkr (C.p.ksLog - 4) (aLane C.p 6) ze q8).1)
      (ksOutC C.p o.rk o.vk ze oe) (ksLinkG C.p (aLane C.p 7) ze oe q9).1).map (CClaim.val M) =
    claimsOf C.p (M3.real C.p (tabs C G D)) (pubOf vk cL sig) bus (Lvm.QAcc.evV M tab) tp wo
      (vs M o.rk) (vs M o.vk) (o.kko.vals M)
      (ringAt (feAt sig) (8 * gkrEnd (C.p.ksLog - 4) (aLane C.p 6) - 40) (o.kko.vals M).slicePoint
        (o.kko.vals M).slices)
      ((M3.real C.p (tabs C G D)).ksLink (ksLinkView C.p (M3.real C.p (tabs C G D)) (feAt sig) P7 (vs M o.rk)
        (pubOf vk cL sig))).2 := by
  have hO : (phases47 C p2).1 = o := ho47
  simp only [phases47, bind_apply, pure_apply] at hO
  have ekko := congrArg P47Out.kko hO
  have ev : o.v.length = 25 := by rw [← hO]; simp only [List.length_map, List.length_range]
  have evk : o.vk.length = 25 := by rw [← hO]; simp only [List.length_map, List.length_range]
  dsimp only at ekko
  clear hO
  obtain ⟨hh, -⟩ := h47
  simp only [phases47] at hh
  rw [hold_bind] at hh; obtain ⟨-, hh⟩ := hh
  rw [hold_bind] at hh; obtain ⟨-, hh⟩ := hh
  rw [hold_bind] at hh; obtain ⟨-, hh⟩ := hh
  rw [hold_bind] at hh; obtain ⟨-, hh⟩ := hh
  rw [hold_bind] at hh; obtain ⟨-, hh⟩ := hh
  rw [hold_bind] at hh; obtain ⟨-, hh⟩ := hh
  rw [hold_bind] at hh; obtain ⟨-, hh⟩ := hh
  rw [hold_bind] at hh; obtain ⟨-, hh⟩ := hh
  rw [hold_bind] at hh; obtain ⟨-, hh⟩ := hh
  rw [hold_bind] at hh; obtain ⟨hhGk, -⟩ := hh
  have sK := gkrGadget_slices hst.hlayk hst.hqk hS (by have := hst.hTgk; omega) hhGk
  rw [ekko] at sK
  have rK := ringGkr_rel _ hst.hqk sK hS hst.hTgk hz h8
  have hz' : (ec ze).val M = 0 := hz
  rw [real_eq]
  refine claimsC_val M C.p _ _ bus _ _ _ _ _ _ _ _ hbus ?_ ?_ ?_ ?_ ?_
  · rw [shapesOf_eq C D G (pubOf vk cL sig), tabClaims_val hz']
    rfl
  · exact tapeClaimsC_val C hz ho htw ev (pub_h hS hst.hT29 vk cL)
  · have := kClaimsC_val (M := M) ⟨C.p.ksLog + slotLog, (layout0 C.p).ks⟩ _ _ _ rK
    exact this
  · exact ksOutC_val C.p _ _ hz ho evk
  · exact ksLinkG_val' C.p _ _ hst.hk hst.pos47.l7 hS hst.hTlk' hz ho h9

/-! ## Roll 7 (CR-Q): the claims with their tails -/

/-- **The static check of the claims in both shapes** (decided on the record): every claim off the tape has tail
`0` by its form, every `C_main` claim has the static form `ZWF`. -/
def zChk (z : Cell) (tabC tapeC ksC ksOut clK : List CClaim) : Bool :=
  (tabC ++ ksC ++ ksOut ++ clK).all noDR && (onCom (claimsC tabC tapeC ksC ksOut clK) .main).all (Lvm.QShape.ZWF z)

theorem tails_eq {M : Mem} (tabC tapeC ksC outC clK : List CClaim) (tabs kecc outs : List (Com × BlockClaim))
    (tapeL : List BlockClaim) (TT : List FE)
    (hnd : ∀ x ∈ tabC ++ ksC ++ outC ++ clK, noDR x = true) (htape : tapeC.map (Lvm.QShape.tailC M) = TT)
    (hTT : TT.length = tapeL.length) (h1 : tabC.length = tabs.length) (h2 : ksC.length = kecc.length)
    (h3 : tapeC.length = tapeL.length)
    (hlen : tabC.length + tapeC.length + ksC.length + outC.length + clK.length =
      tabs.length + tapeL.length + kecc.length + outs.length) :
    (claimsT M (claimsC tabC tapeC ksC outC clK)).map (·.2.2) =
      (Lvm.Shape.zeroTails tabs ++ (((tapeL.zip TT).map fun e => (Com.main, e.1, e.2)) ++ Lvm.Shape.zeroTails kecc) ++
        Lvm.Shape.zeroTails outs).map (·.2.2) := by
  have z1 : tabC.map (Lvm.QShape.tailC M) = List.replicate tabC.length 0 :=
    map_tailC_zero _ (List.all_eq_true.mpr fun x hx => hnd x (by simp [hx]))
  have z2 : ksC.map (Lvm.QShape.tailC M) = List.replicate ksC.length 0 :=
    map_tailC_zero _ (List.all_eq_true.mpr fun x hx => hnd x (by simp [hx]))
  have z3 : (outC ++ clK).map (Lvm.QShape.tailC M) = List.replicate (outC ++ clK).length 0 :=
    map_tailC_zero _ (List.all_eq_true.mpr fun x hx => hnd x (by simp at hx ⊢; tauto))
  have e1 : (claimsT M (claimsC tabC tapeC ksC outC clK)).map (·.2.2) =
      tabC.map (Lvm.QShape.tailC M) ++ (tapeC.map (Lvm.QShape.tailC M) ++ ksC.map (Lvm.QShape.tailC M)) ++
        (outC ++ clK).map (Lvm.QShape.tailC M) := by
    simp only [claimsT, claimsC, List.map_map, List.map_append, List.append_assoc]; rfl
  have e2 : ((tapeL.zip TT).map fun e => (Com.main, e.1, e.2)).map (·.2.2) = TT := by
    rw [List.map_map]
    exact List.map_snd_zip (by omega)
  rw [e1, z1, z2, z3, htape, List.map_append, List.map_append, List.map_append, zeroTails_tails, zeroTails_tails,
    zeroTails_tails, e2, h1, h2]
  simp only [List.length_append]
  congr 2
  omega

/-! ## Phases 8–9 -/

-- (R11-IS, M′: `open_at` is removed: the dead bus path's phases 8–9 against M′'s `openG`; no consumer.)

/-! ## The composition -/

/-- The padding rows are an extra conjunct: `m` holds. -/
theorem ok_withPad {α : Type} {c : Ctx} {M : Mem} {zK zE : Cell} {m : BM α} {p : Ptr}
    (h : Lvm.QSig.Ok c M (withPad zK zE m) p) : Lvm.QSig.Ok c M m p :=
  ⟨((segsHold_append c M p _ _).mp h.1).1, ((segsAssert_append M p _ _).mp h.2).1⟩

/-- **Q_arith's claim list**: `qarithT` up to phase 8 (the claims as cells, as `qarithT` builds them;
`ClaimsWF` is a static check on it; the padding comes after them). -/
def qarithCs (C : QCfg) (D : QData) (o : P47Out) : BM (List CClaim) := do
  let g := kc (pbB C)
  let p := C.p
  let S := shapesOf C D
  let z ← const .E 0 (kc 0)
  let one ← const .E 1 (kc 0)
  let _zK ← const .K 0 (kc 0)
  let ksB : Placement := ⟨p.ksLog + slotLog, (layout0 p).ks⟩
  let bus ← busG p z one g (busPos p)
  let tab ← tabG S p.tableRounds (tabPos p) z one g bus
  Lvm.QAcc.qacc (accInOf C S tab z)
  let rgK ← ringGkr (p.ksLog - 4) (aLane p 6) z.n
  let clK ← ksLinkG p (aLane p 7) z.n one.n
  pure (claimsC (tabClaims S tab z) (tapeClaimsC p z.n one.n o) (kClaimsC ksB o.kko rgK)
    (ksOutC p o.rk o.vk z.n one.n) clK)

/-- **The static check of Q_arith's claims in both shapes** (`zChk` on `qarithCs`' lists; decided on the record). -/
def qarithZ (C : QCfg) (D : QData) (o : P47Out) : BM Bool := do
  let g := kc (pbB C)
  let p := C.p
  let S := shapesOf C D
  let z ← const .E 0 (kc 0)
  let one ← const .E 1 (kc 0)
  let _zK ← const .K 0 (kc 0)
  let ksB : Placement := ⟨p.ksLog + slotLog, (layout0 p).ks⟩
  let bus ← busG p z one g (busPos p)
  let tab ← tabG S p.tableRounds (tabPos p) z one g bus
  Lvm.QAcc.qacc (accInOf C S tab z)
  let rgK ← ringGkr (p.ksLog - 4) (aLane p 6) z.n
  let clK ← ksLinkG p (aLane p 7) z.n one.n
  pure (zChk z (tabClaims S tab z) (tapeClaimsC p z.n one.n o) (kClaimsC ksB o.kko rgK)
    (ksOutC p o.rk o.vk z.n one.n) clK)

-- (R11-IS, M′: `harith_core` is removed: the dead bus path's composition, whose `F` still skips a `C_rec` cap;
-- no consumer. The typed node path is `LvmQTypedHarS`.)

end Lvm.Har
