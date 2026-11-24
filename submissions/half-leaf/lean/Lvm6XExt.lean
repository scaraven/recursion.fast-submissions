-- lvm6 X5 (BLUEPRINT v3 §3 step 3, §5 T8; X2 §1b; CAND-decision §3): the extraction map `ExtSpec6` (the witness of the
-- pinned member of the opening's candidates), the output stage `outIR6_sem`, the stack-to-witness bridge and
-- `ext_eq6` from the named facts `SFront6`; X4's `foldsQX` is W1's `foldsQ`.
import Lvm6XTop
import Lvm6XDesc
import Lvm6WhirRound
import Lvm6StmtPhase

/-!
# `ExtSpec6` and `ext_eq6`

* **`ExtSpec6 I c x h`** `= witOf6 (hdrView P17 x) q (child6 q) (sigLeaf6 q)`, `q = pick6 I h` the member of
  `I.cands h` (any, by choice: on a pinned history there is at most one, `pinned_sub`). The children are read off the
  stack's slot 33 (`STREAM`, CD §0): `child6 q = leftOf6 lensD leafLsD (stW q) (33·2^18) (33·2^18 + 2^17)`,
  `sigLeaf6 q = sigOf (stW q) (33·2^18 + 2^17 + 597)` (`P17`).
* **`outIR6_sem`**: by header word `b` the program appends the leaf witness or the node witness (proved).
* **`out_witOf6`**: when the heap holds the stack `q` from `colB6` (`HeapHolds`), that witness is
  `witOf6 x q (child6 q) (sigLeaf6 q)` (X2's `xs6_blocksOf`, `leftOf6_congr`, `sigOf_congr`).
* **`SFront6`**: the facts this WP does not prove, as fields: `len` (V1: an accepted proof has `piLenOf P17`
  bytes), `hdrTape` (V1/F1, pure: tape words 6–15 are the parsed header's `b, n, h, c'`), `childFits` (pure: the
  left child fits the output format), `goodL` (W1's doom chain: on an available log every level's challenges are
  outside `excSet`, X4's `GoodL`, as the predicate `G`), `descends` (deterministic: under `G`, the state before the
  output holds `pick6 I h`; X2's readers/chain, X4's `descD_correct`/`roundIR_sem`, W1's deployed `hdom`, lane reads,
  level transitions and the loaders).
* **`ext_eq6`** (`K.ext = ExtSpec6 I`): `ExtEq6 (EX6 descX) K`.
* **`foldsQ_eq_foldsQX`**: X4 §4 item 5 (W1's `foldsQ` on `Rnd`s is X4's `foldsQX` on their `(α, β)`).
-/

namespace Lvm6.X

open RecursionFast Lvm Lvm.X Lvm.FS Lvm.T
open LeanVM.Protocol.Compile (Ev)
open LeanVM.Parameters (K)

/-! ## X4 §4 item 5 -/

theorem foldsQ_eq_foldsQX {F : Type} [Field F] {n m : ℕ} (dom : Fin n ↪ F) :
    ∀ (j : ℕ) (rs : List (Lvm6.Whir.Rnd F)) (Q : Lvm6.Whir.Wd F n (m + j)),
      Lvm6.Whir.foldsQ dom j rs Q = foldsQX dom j (rs.map fun r => (r.α, r.β)) Q
  | 0, _, _ => rfl
  | j + 1, [], Q => by
    rw [Lvm6.Whir.foldsQ, foldsQX]
    exact foldsQ_eq_foldsQX dom j [] _
  | j + 1, r :: rs, Q => by
    rw [Lvm6.Whir.foldsQ, foldsQX]
    exact foldsQ_eq_foldsQX dom j rs _

/-! ## The output stage -/

theorem readAt_sem (I : Array Word) (s : St) (hM : Inv s.M) (d pos : ℕ) (hd : 4 ≤ d) (hdr : d < regs)
    (hdA : d ≠ rA) (hpos : pos < 2 ^ 64) :
    rd (semXIR I (readAt d pos) s).M d = I.getD pos 0 ∧
    (∀ y, regs ≤ y → rd (semXIR I (readAt d pos) s).M y = rd s.M y) ∧
    (semXIR I (readAt d pos) s).o = s.o := by
  have hs := hM.1
  simp only [regs] at hs hdr
  refine ⟨?_, fun y hy => ?_, rfl⟩
  · simp only [readAt, semXIR, runPrims, List.foldl, Prim.run]
    simp (disch := first | decide | omega | (simp only [size_set, rA]; omega) | (simp only [rA]; omega))
      [rd_set_self, rd_set_ne, rA]
    rw [Nat.mod_eq_of_lt (show pos < 18446744073709551616 by omega)]
  · simp only [regs] at hy
    simp only [readAt, semXIR, runPrims, List.foldl, Prim.run]
    rw [rd_set_ne (by omega), rd_set_ne (by simp only [rA]; omega)]

/-- The output stage with node program `P`. -/
def outIRG (P : XIR) : XIR := .seq (readAt rB6 6) (.ite rB6 P (leafOutIR nD colB6 stride6))

theorem outIR6_eq : outIR6 = outIRG nodeOutIR := rfl

/-- **The output stage**: by header word `b`, the leaf witness or the node witness of the heap's columns. -/
theorem outIRG_sem {P : XIR} {wn : Mem → Wit} (I : Array Word)
    (hP : ∀ s : St, Inv s.M → (semXIR I P s).o.toList = s.o.toList ++ witWords (wn s.M))
    (hwn : ∀ M M' : Mem, (∀ x, regs ≤ x → rd M' x = rd M x) → wn M' = wn M)
    (s : St) (hM : Inv s.M) {b : ℕ} (hb : I.getD 6 0 = toWord b)
    (hb64 : b < 2 ^ 64) :
    (semXIR I (outIRG P) s).o.toList = s.o.toList ++ witWords (if b = 0 then
      .leaf (xs6 nD fun m r => rd s.M (colB6 + m * stride6 + r)) else wn s.M) := by
  obtain ⟨r1, f1, o1⟩ := readAt_sem I s hM rB6 6 (by decide) (by decide) (by decide) (by norm_num)
  have i1 := inv_sem I (P := readAt rB6 6) (by simp +decide [readAt, WF, Prim.dst, rA, rB6]) hM
  simp only [outIRG, semXIR_seq, semXIR_ite]
  generalize semXIR I (readAt rB6 6) s = s1 at r1 f1 o1 i1
  have hq : (fun m r => rd s1.M (colB6 + m * stride6 + r)) = (fun m r => rd s.M (colB6 + m * stride6 + r)) :=
    funext fun m => funext fun r => f1 (colB6 + m * stride6 + r) (by simp only [regs, colB6]; omega)
  by_cases hb0 : b = 0
  · subst hb0
    rw [if_pos (by rw [r1, hb]; rfl), if_pos rfl, (leafOutIR_sem I s1 i1 (by simp only [regs, colB6]; omega)
      (by simp only [colB6, nD, stride6]; norm_num)).1, o1, hq]
  · have hne : rd s1.M rB6 ≠ 0 := by
      rw [r1, hb]
      intro h0
      have := congrArg BitVec.toNat h0
      rw [toNat_toWord hb64] at this
      exact hb0 this
    rw [if_neg hne, if_neg hb0, hP s1 i1, o1, hwn s.M s1.M f1]

theorem nodeWit6_frame (c' L : Digest) (M M' : Mem) (hf : ∀ x, regs ≤ x → rd M' x = rd M x) :
    nodeWit6 lensD leafLsD c' L nD (fun m r => rd M' (colB6 + m * stride6 + r)) (rd M') tB6 sB6 sLB6 =
      nodeWit6 lensD leafLsD c' L nD (fun m r => rd M (colB6 + m * stride6 + r)) (rd M) tB6 sB6 sLB6 := by
  have hq : (fun m r => rd M' (colB6 + m * stride6 + r)) = (fun m r => rd M (colB6 + m * stride6 + r)) :=
    funext fun m => funext fun r => hf (colB6 + m * stride6 + r) (by simp only [regs, colB6]; omega)
  have hl : leftOf6 lensD leafLsD (rd M') tB6 sB6 = leftOf6 lensD leafLsD (rd M) tB6 sB6 :=
    leftOf6_congr (fun u _ => hf (tB6 + u) (by simp only [regs, tB6]; omega))
      (fun j _ => hf (sB6 + j) (by simp only [regs, sB6]; omega))
  have hσ : sigOf (rd M') sLB6 = sigOf (rd M) sLB6 :=
    sigOf_congr fun j _ => hf (sLB6 + j) (by simp only [regs, sLB6]; omega)
  simp only [nodeWit6, hq, hl, hσ]

/-- **The output stage**: by header word `b`, the leaf witness or the node witness of the heap's columns. -/
theorem outIR6_sem (I : Array Word) (s : St) (hM : Inv s.M) {b : ℕ} (hb : I.getD 6 0 = toWord b)
    (hb64 : b < 2 ^ 64) (c' h : Digest) (n : ℕ)
    (hc : (List.range 4).map (fun j => I.getD (12 + j) 0) = packBytes c'.toList)
    (hh : ∀ i < 4, I.getD (8 + i) 0 = (packBytes h.toList).getD i 0) (hn : I.getD 7 0 = toWord n)
    (hn64 : n < 2 ^ 64) :
    (semXIR I outIR6 s).o.toList = s.o.toList ++ witWords (if b = 0 then
      .leaf (xs6 nD fun m r => rd s.M (colB6 + m * stride6 + r)) else nodeWit6 lensD leafLsD c' (leafStmt h n) nD
        (fun m r => rd s.M (colB6 + m * stride6 + r)) (rd s.M) tB6 sB6 sLB6) := by
  rw [outIR6_eq]
  exact outIRG_sem (wn := fun M => nodeWit6 lensD leafLsD c' (leafStmt h n) nD
    (fun m r => rd M (colB6 + m * stride6 + r)) (rd M) tB6 sB6 sLB6) I
    (fun s hM => (nodeOutIR_sem I s hM c' h n hc hh hn hn64).1) (nodeWit6_frame c' (leafStmt h n)) s hM hb hb64

/-! ## The extraction map -/

/-- The stack as a word table: slot `s`'s word at row `r` is word `r + 2^18 s` (`P17`). -/
def stW (q : Stack) (w : ℕ) : Word := (K.lane (q w)).toBitVec

/-- **The left child** of a stack: the trace and `σ'` in its `STREAM` slot (33). -/
def child6 (q : Stack) : Signed := leftOf6 lensD leafLsD (stW q) (33 * stride6) (33 * stride6 + 2 ^ 17)

/-- **The leaf signature** of a stack: `σ_leaf` in its `STREAM` slot. -/
def sigLeaf6 (q : Stack) : Sig := sigOf (stW q) (33 * stride6 + 2 ^ 17 + 597)

open Classical in
/-- **A member of the candidates** (the pinned one on a pinned history), the zero stack if there is none. -/
noncomputable def pick6 (I : OpeningIface) (h : List Ev) : Stack :=
  if hq : ∃ q, q ∈ I.cands h then hq.choose else fun _ => 0

theorem pick6_mem {I : OpeningIface} {h : List Ev} (hq : ∃ q, q ∈ I.cands h) : pick6 I h ∈ I.cands h := by
  rw [pick6, dif_pos hq]; exact hq.choose_spec

/-- **The extraction map `ExtSpec6`** (X2 §1b): the witness of the pinned member of `I.cands h`. -/
noncomputable def ExtSpec6 (I : OpeningIface) : Digest → List UInt8 → List Ev → Wit :=
  fun _ x h => witOf6 (hdrView P17 x) (pick6 I h) (child6 (pick6 I h)) (sigLeaf6 (pick6 I h))

/-- The heap holds the stack `q` (slots 0–33) from `colB6`. -/
def HeapHolds (M : Mem) (q : Stack) : Prop := ∀ w < 34 * stride6, rd M (colB6 + w) = stW q w

theorem xs6_congr {n : ℕ} {q q' : Cols} (h : ∀ m < 4, ∀ i < n, q m (n + i) = q' m (n + i)) : xs6 n q = xs6 n q' := by
  simp only [xs6, blkW]
  exact List.map_congr_left fun i hi => by
    have := List.mem_range.mp hi
    rw [h 0 (by omega) i this, h 1 (by omega) i this, h 2 (by omega) i this, h 3 (by omega) i this]

/-- **The output's witness is the stack's**: on a heap holding `q`, the leaf or node witness of `outIR6_sem` is
`witOf6 x q (child6 q) (sigLeaf6 q)`. -/
theorem out_witOf6 {M : Mem} {q : Stack} (hH : HeapHolds M q) (x : Hdr) :
    (if x.b.toNat = 0 then .leaf (xs6 nD fun m r => rd M (colB6 + m * stride6 + r)) else nodeWit6 lensD leafLsD
      x.c' (leafStmt x.h x.n.toNat) nD (fun m r => rd M (colB6 + m * stride6 + r)) (rd M) tB6 sB6 sLB6) =
      witOf6 x q (child6 q) (sigLeaf6 q) := by
  have hx : xs6 nD (fun m r => rd M (colB6 + m * stride6 + r)) = blocksOf q := by
    rw [← xs6_blocksOf q, show nD = 2 ^ 17 from rfl]
    refine xs6_congr fun m hm i hi => ?_
    rw [Nat.add_assoc, hH _ (by simp only [stride6]; omega), stW]
    congr 3
    simp only [stride6]; ring
  have hb : (x.b.toNat = 0) ↔ x.b = 0 := by
    constructor
    · intro h; exact UInt64.toNat_inj.mp (by simpa using h)
    · intro h; simp [h]
  by_cases h0 : x.b = 0
  · rw [if_pos (hb.mpr h0), witOf6, if_pos h0, hx]
  · rw [if_neg (fun h => h0 (hb.mp h)), witOf6, if_neg h0, nodeWit6, rightOf, hx]
    have hl : leftOf6 lensD leafLsD (rd M) tB6 sB6 = child6 q :=
      leftOf6_congr (fun u hu => by
        rw [lanesD] at hu
        rw [show tB6 + u = colB6 + (33 * stride6 + u) by simp only [tB6, colB6, stride6]; ring,
          hH _ (by simp only [stride6]; omega)])
        (fun j hj => by
          rw [show sB6 + j = colB6 + (33 * stride6 + 2 ^ 17 + j) by simp only [sB6, colB6, stride6]; ring,
            hH _ (by simp only [stride6]; omega)])
    have hσ : sigOf (rd M) sLB6 = sigLeaf6 q :=
      sigOf_congr fun j hj => by
        rw [show sLB6 + j = colB6 + (33 * stride6 + 2 ^ 17 + 597 + j) by simp only [sLB6, colB6, stride6]; ring,
          hH _ (by simp only [stride6]; omega)]
    rw [hl, hσ]

/-! ## `ext_eq6` -/

/-- The state before the output: parse, replay, descent. -/
def preOut6 (descX : XIR) (inp : List Word) : St :=
  semXIR inp.toArray descX (semXIR inp.toArray frontIR6
    (semXIR inp.toArray (parseIR pz6) (initSt (mem6 + mpwX * inp.length))))

/-- The header's words on the tape (FORMAT6 §2 offsets 8, 16, 24, 56: tape words 6, 7, 8–11, 12–15). -/
def HdrTape (I : Array Word) (x : Hdr) : Prop :=
  I.getD 6 0 = toWord x.b.toNat ∧ I.getD 7 0 = toWord x.n.toNat ∧
    (∀ i < 4, I.getD (8 + i) 0 = (packBytes x.h.toList).getD i 0) ∧
    (List.range 4).map (fun j => I.getD (12 + j) 0) = packBytes x.c'.toList

/-- **The extractor's open facts** (named; see the module docstring for the owner of each). `G x h` is the
goodness of every level's challenges in the accepting history `h` (X4's `GoodL` at W1's deployed levels). -/
structure SFront6 {prog : Shape → Digest → List UInt8 → LeanVM.Protocol.Compile.VerifierProgram Bool} {vk : Digest}
    {R : Digest → Wit → Prop} (K : KCert (schemeOf prog P17 vk) R) (I : OpeningIface) (descX : XIR)
    (G : List UInt8 → List Ev → Prop) : Prop where
  /-- V1: an accepted proof has the schedule's length. -/
  len : ∀ c π L, Avail K c π L → π.size = pz6
  /-- V1/F1 (pure bytes): the replayed header's fields are on the tape. -/
  hdrTape : ∀ c π L x h, (schemeOf prog P17 vk).Ex (fun _ x h => (x, h)) c π L = some (x, h) →
    HdrTape (extractorInput c π L).toArray (hdrView P17 x)
  /-- Pure: the left child of a stack fits the output format. -/
  childFits : ∀ q, (child6 q).Fits
  /-- W1's doom chain (X4's `GoodL`): on an available log the replayed history's challenges are good. -/
  goodL : ∀ c π L, Avail K c π L → ∀ x h, (schemeOf prog P17 vk).Ex (fun _ x h => (x, h)) c π L = some (x, h) →
    G x h
  /-- The descent (X2's readers and chain, X4's `descD_correct`/`roundIR_sem`, W1's deployed `hdom`, lane reads,
  level transitions, the loaders): under `G`, the state before the output holds the pinned member. -/
  descends : ∀ c π L x h, (schemeOf prog P17 vk).Ex (fun _ x h => (x, h)) c π L = some (x, h) →
    π.size = pz6 → G x h → Inv (preOut6 descX (extractorInput c π L)).M ∧
      (preOut6 descX (extractorInput c π L)).o = #[] ∧
      HeapHolds (preOut6 descX (extractorInput c π L)).M (pick6 I h)

/-- `Ex` is its history's image. -/
theorem Ex_map {S : Scheme} {W' : Type} (ext : Digest → S.Stmt → List Ev → W') (c : Digest) (π : Proof)
    (L : Log) : S.Ex ext c π L = (S.Ex (fun _ x h => (x, h)) c π L).map (fun p => ext c p.1 p.2) := by
  unfold Scheme.Ex
  rcases S.hdr π with _ | ⟨x, body⟩
  · rfl
  · simp only
    split_ifs
    · simp [Option.map_bind, apply_ite]
    · rfl

theorem fits_witOf6 (hF : ∀ q, (child6 q).Fits) (x : Hdr) (q : Stack) :
    (witOf6 x q (child6 q) (sigLeaf6 q)).Fits := by
  have hlen : (blocksOf q).length = 2 ^ 17 := length_blocksOfAt 17 q
  unfold witOf6
  split_ifs
  · show (blocksOf q).length < 2 ^ 64
    rw [hlen]; norm_num
  · refine ⟨hF q, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · show (WitnessSending.encode (.leaf (blocksOf q))).size < 2 ^ 64
      rw [WitnessSending.size_encode_leaf, hlen]; norm_num
    · show ([] : Trace).length < 2 ^ 64
      norm_num
    · intro e he; exact absurd he List.not_mem_nil
    · show (sigLeaf6 q).idx < 2 ^ 64
      simp only [sigLeaf6, sigOf]; exact BitVec.isLt _
    · show (sigLeaf6 q).ots.length = wotsLen
      simp only [sigLeaf6, sigOf, List.length_map, List.length_range]
    · show (sigLeaf6 q).path.length = sigHeight
      simp only [sigLeaf6, sigOf, List.length_map, List.length_range]

/-- **T8 `ext_eq6`**: with the extraction map `ExtSpec6 I`, on every available log the program's specification is
the ideal extractor, given the named facts `SFront6`. -/
theorem ext_eq6 {prog : Shape → Digest → List UInt8 → LeanVM.Protocol.Compile.VerifierProgram Bool} {vk : Digest}
    {R : Digest → Wit → Prop} (K : KCert (schemeOf prog P17 vk) R) (I : OpeningIface) {descX : XIR}
    {G : List UInt8 → List Ev → Prop} (hK : K.ext = ExtSpec6 I) (hF : SFront6 K I descX G) :
    ExtEq6 (EX6 descX) K := by
  intro c π L hA
  have hA' := hA
  obtain ⟨hS, -, hμ, hacc⟩ := hA'
  obtain ⟨w, hw, -⟩ := Scheme.final_law K L c π hμ hacc
  rw [Eideal, hw]
  rw [Ex_map] at hw
  obtain ⟨⟨x, h⟩, hp, rfl⟩ := Option.map_eq_some_iff.mp hw
  have hlen := hF.len c π L hA
  obtain ⟨hI, hO, hH⟩ := hF.descends c π L x h hp hlen (hF.goodL c π L hA x h hp)
  obtain ⟨t6, t7, t8, t12⟩ := hF.hdrTape c π L x h hp
  rw [EX6, if_pos hS, Eden, den, extIR6, hK]
  set inp := extractorInput c π L
  -- the parse takes the `S` branch at `|π| = pz6`
  have hreg : regs ≤ mem6 := by simp only [regs, mem6]; norm_num
  have h0 : Inv (initSt (mem6 + mpwX * inp.length)).M := inv_initSt (Nat.le_add_right_of_le hreg)
  have hk5 := Lvm6.W.parse_isK pz6 inp.toArray _ h0
  have hz5 := parse_regs pz6 inp.toArray _ h0
  have hb0 : π.data[0]? = some sByte := by
    have hpos : 0 < π.data.size := by
      have : π.size = π.data.size := rfl
      rw [← this, hlen]; simp only [pz6]; norm_num
    have hg : π.data.getD 0 0 = sByte := by simpa [isS] using hS
    rw [Array.getElem?_eq_getElem hpos]
    rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hpos] at hg
    simpa using hg
  have hK5 : inp.toArray.getD 5 0 &&& 0xFF = kindS := by
    apply BitVec.eq_of_toNat_eq
    rw [Lvm6.W.lowByte, getD_toArray, Lvm6.W.tape_byte0 c π L hb0]
    rfl
  have hZ : inp.toArray.getD 4 0 = BitVec.ofNat 64 pz6 := by
    rw [getD_toArray, tape_getD4, hlen]; rfl
  rw [if_pos hK5] at hk5
  rw [if_pos hZ] at hz5
  rw [extIRWith, semXIR_seq, semXIR_ite, if_neg (by rw [hk5]; decide), semXIR_ite,
    if_neg (by rw [hz5]; decide), dec6, semXIR_seq, semXIR_seq]
  rw [show semXIR inp.toArray descX (semXIR inp.toArray frontIR6 (semXIR inp.toArray (parseIR pz6)
    (initSt (mem6 + mpwX * inp.length)))) = preOut6 descX inp from rfl]
  rw [outIR6_sem inp.toArray _ hI t6 (UInt64.toNat_lt _) (hdrView P17 x).c' (hdrView P17 x).h
    (hdrView P17 x).n.toNat t12 t8 t7 (UInt64.toNat_lt _), hO, Array.toList_empty, List.nil_append,
    out_witOf6 hH]
  exact decodeWit_witWords _ (fits_witOf6 hF.childFits _ _)

end Lvm6.X
