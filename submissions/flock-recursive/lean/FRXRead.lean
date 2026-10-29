-- New for `flock-recursive` (BLUEPRINT §6.5 `read_spec`; stage S-H2, track L-ext).
import FRXReadDefs
import FRXField
import FRFieldBaseCorrect

/-!
# The ladder read's semantics (`read_spec`)

On a domain tape of a SNARK proof, after the log index (`idxIR`, sorted by `idxIR_sorted`),
`readIR sib np` leaves in cell `colBase + 128 p + w` (`p < np`, `w < 128`) word `w` of the column
that `FRMerkle.colL (frEnc 0)` reads under π's cap entry `p / 2^sib` at height `sib`, and `0`
where `colL` reads no column (`colWord`).

* `look_spec`: the lookup on a sorted index (from `lookIR_sem`, `lookup_pure`, `bsRun_spec`),
  with its frames.
* `nodeStepP`, `colL_succ`: one step of `colL` as a function of the current digest.
* `nodeBody_sem`: one machine step is `nodeStepP`; `nodeLoop`: `sib` steps.
* `colIR_sem`, `copyLoop`: the leaf and the copy; `posBody_sem`: one position.
* **`read_spec`**; **`read_spec_F`**: the store read as `F` elements (`rdF`, two words each)
  is S-G's reading `readF col (16 r)` of the column (`wordOf`'s), `0` where none is read.

**Parameters (S-H4 pass 5).** The read's semantics take the index base `bX` and the tape word `pL` of
`|L|` (`Dom4 pL`, `readIR4_sem`, `posLoop4`); 3.x's `readIR_sem`, `posLoop` are the instances at
`memX`, `posL` (`Dom.d4`).
-/

namespace FR.X

open RecursionFast FR.Merkle

attribute [local irreducible] entryK storeM

/-! ## The domain and the tape -/

/-- The tape as the machine reads it. -/
abbrev tp (c : Digest) (π : Proof) (L : Log) : Array Word := (extractorInput c π L).toArray

/-- A domain tape of a SNARK proof. -/
structure Dom (c : Digest) (π : Proof) (L : Log) : Prop where
  hs : π.size = piSize
  hq : ∀ e ∈ L, e.1.size < 2 ^ 64
  ht : (extractorInput c π L).length ≤ 2 ^ 64

/-- A domain tape of a SNARK proof whose `|L|` sits at tape word `pL`
(`5 + ⌈|π|/8⌉ = pL`); 3.x's `Dom` is the instance at `posL` (`Dom.d4`). -/
structure Dom4 (pL : ℕ) (c : Digest) (π : Proof) (L : Log) : Prop where
  hs : 5 + (π.size + 7) / 8 = pL
  hq : ∀ e ∈ L, e.1.size < 2 ^ 64
  ht : (extractorInput c π L).length ≤ 2 ^ 64

theorem Dom.d4 {c : Digest} {π : Proof} {L : Log} (hD : Dom c π L) : Dom4 posL c π L :=
  ⟨hs_posL hD.hs, hD.hq, hD.ht⟩
/-- The column word `w` of a reading: `0` where no column is read. -/
def colWord (o : Option ByteArray) (w : ℕ) : Word :=
  match o with
  | some col => (packBytes col.data.toList).getD w 0
  | none => 0

section Indep

variable {c : Digest} {π : Proof} {L : Log} {i : ℕ}

theorem len_entries (L : Log) : 5 * L.length ≤ entryOff L L.length := by
  have := length_logEntries L
  rwa [entries_length, ← entryOff_length] at this

/-! ## Words -/

theorem shr_toWord {a k : ℕ} (ha : a < 2 ^ 64) (hk : k < 64) :
    XOp.shr.eval (toWord a) (toWord k) = toWord (a / 2 ^ k) := by
  apply BitVec.eq_of_toNat_eq
  simp only [XOp.eval]
  rw [BitVec.toNat_ushiftRight, toNat_toWord ha, toNat_toWord (by omega : k < 2 ^ 64),
    Nat.mod_eq_of_lt hk, toNat_toWord (lt_of_le_of_lt (Nat.div_le_self _ _) ha),
    Nat.shiftRight_eq_div_pow]

theorem shl_toWord {a k : ℕ} (hk : k < 64) (hb : a * 2 ^ k < 2 ^ 64) :
    XOp.shl.eval (toWord a) (toWord k) = toWord (a * 2 ^ k) := by
  apply BitVec.eq_of_toNat_eq
  simp only [XOp.eval]
  have ha : a < 2 ^ 64 := lt_of_le_of_lt (Nat.le_mul_of_pos_right _ (by positivity)) hb
  rw [BitVec.toNat_shiftLeft, toNat_toWord ha, toNat_toWord (by omega : k < 2 ^ 64),
    Nat.mod_eq_of_lt hk, toNat_toWord hb, Nat.shiftLeft_eq, Nat.mod_eq_of_lt hb]

theorem and_one_toWord {a : ℕ} (ha : a < 2 ^ 64) :
    XOp.and.eval (toWord a) 1 = toWord (a % 2) := by
  apply BitVec.eq_of_toNat_eq
  simp only [XOp.eval]
  rw [BitVec.toNat_and, toNat_toWord ha, show (1 : Word).toNat = 2 ^ 1 - 1 from rfl,
    Nat.and_two_pow_sub_one_eq_mod, toNat_toWord (by omega)]

theorem bit_eq (p h : ℕ) : p / 2 ^ h % 2 = if p.testBit h then 1 else 0 := by
  rw [Nat.testBit_eq_decide_div_mod_eq]
  by_cases e : p / 2 ^ h % 2 = 1
  · simp [e]
  · simp [e]; omega

/-! ## Heap frames of store-free code with counted loops -/

/-- No store, no tape-length loop, register destinations; `loopK` counters registers. -/
def LoK : XIR → Prop
  | .blk ps => ∀ p ∈ ps, p.dst < regs
  | .load d _ => d < regs
  | .input d _ => d < regs
  | .out _ => True
  | .seq p q => LoK p ∧ LoK q
  | .ite _ p q => LoK p ∧ LoK q
  | .loopK c _ _ b => c < regs ∧ LoK b
  | _ => False

theorem iterL_hframe {f : St → St} {c : ℕ} (hc : c < regs)
    (hf : ∀ s, ∀ x, regs ≤ x → rd (f s).M x = rd s.M x) :
    ∀ k s, ∀ x, regs ≤ x → rd (iterL f c k s).M x = rd s.M x
  | 0, _, _, _ => rfl
  | k + 1, s, x, hx => (iterL_hframe hc hf k _ x hx).trans
      ((rd_decS (by omega) _).trans (hf s x hx))

/-- **Heap frame** for `LoK` code. -/
theorem hframeK (I : Array Word) : ∀ (P : XIR) (s : St), LoK P → ∀ x, regs ≤ x →
    rd (semXIR I P s).M x = rd s.M x
  | .blk _, _, h, _, hx => rd_runPrims_of_not_writes (fun p hp he => by have := h p hp; omega) _
  | .load _ _, _, h, _, hx => rd_set_ne (by simp only [LoK] at h; omega)
  | .input _ _, _, h, _, hx => rd_set_ne (by simp only [LoK] at h; omega)
  | .out _, _, _, _, _ => rfl
  | .seq p q, s, h, x, hx => (hframeK I q _ h.2 x hx).trans (hframeK I p s h.1 x hx)
  | .ite _ p q, s, h, x, hx => by
    simp only [semXIR]; split
    · exact hframeK I q s h.2 x hx
    · exact hframeK I p s h.1 x hx
  | .loopK c n K b, s, h, x, hx => by
    simp only [semXIR]
    rw [iterL_hframe h.1 (fun s' x' hx' => hframeK I b s' h.2 x' hx') _ _ x hx]
    exact entryK_frame _ (by have := h.1; omega) (by simp only [cTmp, regs] at *; omega)
  | .store .., _, h, _, _ => h.elim
  | .loopT .., _, h, _, _ => h.elim

/-- The count of a `loopK` whose count register holds `K`. -/
theorem entryK_count {c n : ℕ} {K : Word} {M : Mem} (hM : Inv M) (hc : 4 < c) (hcr : c < regs)
    (hn : n ≠ c) (hN : rd M n = K) : rd (entryK c n K M) c = K := by
  have hs := hM.1
  unfold entryK
  dsimp only
  have h1 : rd (M.setIfInBounds c K) n = K := by rw [rd_set_ne (Ne.symm hn), hN]
  have h2 : rd (M.setIfInBounds c K) c = K := rd_set_self (by simp only [regs] at *; omega)
  rw [h1, h2, rd_set_self (by simp only [size_set, cTmp, regs] at *; omega)]
  have : XOp.ltu.eval K K = 0 := by simp [XOp.eval]
  rw [this, if_pos rfl, rd_set_ne (by simp only [cTmp]; omega), h2]

theorem inv_entryK {c n : ℕ} {K : Word} {M : Mem} (hM : Inv M) (hc : 4 < c) :
    Inv (entryK c n K M) :=
  inv_of_frame hM (size_entryK ..) fun i hi =>
    entryK_frame _ (by omega) (by simp only [cTmp]; omega)

theorem inv_decS {c : ℕ} {s : St} (hM : Inv s.M) (hc : 4 ≤ c) : Inv (decS c s).M :=
  inv_of_frame hM (size_decS ..) fun i hi => rd_decS (by omega) _

theorem rd_decS_self {c : ℕ} {s : St} (hM : Inv s.M) (hcr : c < regs) {m : ℕ}
    (h : rd s.M c = toWord (m + 1)) (hm : m + 1 < 2 ^ 64) : rd (decS c s).M c = toWord m := by
  have hs := hM.1
  have h1 : rd s.M cOne = 1 := hM.2 0 (by decide)
  simp only [decS]
  rw [rd_set_self (by simp only [regs] at *; omega), h, h1, show (1 : Word) = toWord 1 from rfl,
    sub_toWord hm (by omega)]
  rfl

/-! ## The lookup on a sorted index -/

/-! ## Straight-line blocks -/

/-- A digest's four packed words as a list. -/
theorem packBytes_digest_eq4 (d : Digest) : packBytes d.toList =
    [(packBytes d.toList).getD 0 0, (packBytes d.toList).getD 1 0, (packBytes d.toList).getD 2 0,
      (packBytes d.toList).getD 3 0] := by
  have h := packBytes_digest_length d
  match e : packBytes d.toList, h with
  | [a0, a1, a2, a3], _ => rfl

theorem wf_ld4IR : WF ld4IR := by simp +decide only [ld4IR, WF, Prim.dst, rQ0, rQ1, rQ2, rQ3, rTA,
  and_true]

theorem lo_ld4IR : Lo ld4IR := by simp +decide only [ld4IR, Lo, Prim.dst, regs, rQ0, rQ1, rQ2, rQ3,
  rTA, and_true]

/-- **Four tape words** into `rQ0 … rQ3`. -/
theorem ld4_sem (I : Array Word) (s : St) (hM : Inv s.M) {a : ℕ} (ha : a + 3 < 2 ^ 64)
    (hA : rd s.M rTA = toWord a) :
    [rd (semXIR I ld4IR s).M rQ0, rd (semXIR I ld4IR s).M rQ1, rd (semXIR I ld4IR s).M rQ2,
      rd (semXIR I ld4IR s).M rQ3] =
      [I.getD a 0, I.getD (a + 1) 0, I.getD (a + 2) 0, I.getD (a + 3) 0] := by
  have hs := hM.1
  have h1 : rd s.M cOne = 1 := hM.2 0 (by decide)
  simp only [regs] at hs
  simp only [ld4IR, semXIR, runPrims, List.foldl, Prim.run]
  simp (disch := first | decide | (simp only [size_set, rQ0, rQ1, rQ2, rQ3, rTA]; omega)) only
    [rd_set_self, rd_set_ne]
  rw [hA, h1, add_one_toWord, add_one_toWord, add_one_toWord, toNat_toWord (by omega),
    toNat_toWord (by omega), toNat_toWord (by omega), toNat_toWord (by omega)]

/-- **The cap entry's words**: after `capPs sib ; ld4IR`, `rQ0 … rQ3` hold `capPi π (p / 2^sib)`. -/
theorem capLd_sem {c : Digest} {π : Proof} {L : Log} (s : St) (hM : Inv s.M)
    {cw ncap : ℕ} {cap : ℕ → Digest} (hcw : cw + 4 * ncap < 2 ^ 62)
    (hcap : ∀ e < ncap, ∀ m < 4, (tp c π L).getD (cw + 4 * e + m) 0 = (packBytes (cap e).toList).getD m 0)
    {sib p : ℕ} (hsib : sib < 64) (hp : p < 2 ^ 62) (he : p / 2 ^ sib < ncap)
    (hP : rd s.M rPp = toWord p) :
    [rd (semXIR (tp c π L) (.seq (.blk (capPs cw sib)) ld4IR) s).M rQ0,
      rd (semXIR (tp c π L) (.seq (.blk (capPs cw sib)) ld4IR) s).M rQ1,
      rd (semXIR (tp c π L) (.seq (.blk (capPs cw sib)) ld4IR) s).M rQ2,
      rd (semXIR (tp c π L) (.seq (.blk (capPs cw sib)) ld4IR) s).M rQ3] =
      packBytes (cap (p / 2 ^ sib)).toList := by
  have hs := hM.1
  simp only [regs] at hs
  have hw : WF (.blk (capPs cw sib)) := by simp +decide only [capPs, WF, Prim.dst, rK2, rB, rTA,
    List.mem_cons, List.mem_nil_iff, forall_eq_or_imp, forall_eq, or_false, and_true]
  have hA : rd (semXIR (tp c π L) (.blk (capPs cw sib)) s).M rTA =
      toWord (cw + 4 * (p / 2 ^ sib)) := by
    simp only [capPs, semXIR, runPrims, List.foldl, Prim.run]
    simp (disch := first | decide | (simp only [size_set, rK2, rB, rTA]; omega)) only
      [rd_set_self, rd_set_ne]
    have hq : p / 2 ^ sib < 2 ^ 64 := by omega
    rw [hP, shr_toWord (by omega) hsib, show (2 : Word) = toWord 2 from rfl,
      shl_toWord (by omega) (by omega), add_toWord]
    congr 1; omega
  rw [semXIR_seq, ld4_sem _ _ (inv_sem _ hw hM) (by omega) hA, packBytes_digest_eq4,
    ← hcap _ he 0 (by decide), ← hcap _ he 1 (by decide), ← hcap _ he 2 (by decide),
    ← hcap _ he 3 (by decide)]
  simp only [Nat.add_zero]

/-- The node test `nodeChkPs`. -/
theorem nodeChk_sem (I : Array Word) (i : ℕ) (s : St) (hM : Inv s.M) :
    rd (semXIR I (.blk (nodeChkPs i)) s).M rB =
      bW (decide (rd s.M rQn = toWord 72) && decide (rd s.M rV2 = tagNWl i)) := by
  have hs := hM.1
  simp only [regs] at hs
  simp only [nodeChkPs, semXIR, runPrims, List.foldl, Prim.run]
  simp (disch := first | decide | (simp only [size_set, rK2, rB, rMk]; omega)) only
    [rd_set_self, rd_set_ne]
  rw [eq_bW, eq_bW, bW_and]; rfl

theorem ltu_bW (a b : Word) : XOp.ltu.eval a b = bW (decide (a < b)) := by
  by_cases h : a < b <;> simp [XOp.eval, bW, h]

/-- The column test `colChkPs`. -/
theorem colChk_sem (I : Array Word) (i : ℕ) (s : St) (hM : Inv s.M) :
    rd (semXIR I (.blk (colChkPs i)) s).M rB =
      bW (decide ((7 : Word) < rd s.M rQn) && decide (rd s.M rV2 = tagCWl i)) := by
  have hs := hM.1
  simp only [regs] at hs
  simp only [colChkPs, semXIR, runPrims, List.foldl, Prim.run]
  simp (disch := first | decide | (simp only [size_set, rK2, rB, rMk]; omega)) only
    [rd_set_self, rd_set_ne]
  rw [eq_bW, ltu_bW, bW_and]

/-- **The child's offset**: `rTA := X + 2 + 4 · bit_h(p)` at height `h + 1`. -/
theorem child_sem (I : Array Word) (s : St) (hM : Inv s.M) {x p h : ℕ} (hp : p < 2 ^ 64) (hh : h + 1 < 64) (hX : rd s.M rXq = toWord x) (hP : rd s.M rPp = toWord p)
    (hH : rd s.M rHc = toWord (h + 1)) :
    rd (semXIR I (.blk childPs) s).M rTA = toWord (x + 2 + 4 * (if p.testBit h then 1 else 0)) := by
  have hs := hM.1
  have h1 : rd s.M cOne = 1 := hM.2 0 (by decide)
  simp only [regs] at hs
  simp only [childPs, semXIR, runPrims, List.foldl, Prim.run]
  simp (disch := first | decide | (simp only [size_set, rK2, rB, rTA]; omega)) only
    [rd_set_self, rd_set_ne]
  have hb : p / 2 ^ h < 2 ^ 64 := lt_of_le_of_lt (Nat.div_le_self _ _) hp
  have hbit : p / 2 ^ h % 2 ≤ 1 := by omega
  rw [hH, h1, hP, hX, show (1 : Word) = toWord 1 from rfl, sub_toWord (by omega) (by omega),
    Nat.add_sub_cancel, shr_toWord hp (by omega), show (toWord 1 : Word) = 1 from rfl,
    and_one_toWord hb, show (2 : Word) = toWord 2 from rfl, shl_toWord (by omega) (by omega),
    add_toWord, add_toWord, bit_eq]
  congr 1
  split <;> simp

/-! ## One step down the tree -/

/-- **One step of `colL`** at height `h + 1`: the first preimage of `d`, parsed as a node query of
level 0, gives the child picked by bit `h` of `p`. -/
def nodeStepP (i : ℕ) (L : Log) (p h : ℕ) (d : Digest) : Option Digest :=
  (pre L d).bind fun e => (parseNode i e.1).map fun ab => if p.testBit h then ab.2 else ab.1

theorem colL_succ (i : ℕ) (L : Log) (d : Digest) (h p : ℕ) :
    colL (frEnc i) L d (h + 1) p = (nodeStepP i L p h d).bind fun d' => colL (frEnc i) L d' h p := by
  have e0 : (frEnc i).parseNode = parseNode i := rfl
  simp only [colL, nodeStepP, Option.bind_assoc, e0]
  congr 1; funext e
  cases parseNode i e.1 <;> rfl

theorem wf_nodeChk {i : ℕ} : WF (.blk (nodeChkPs i)) := by simp +decide only [nodeChkPs, WF,
  Prim.dst, rK2, rB, rMk, List.mem_cons, List.mem_nil_iff, forall_eq_or_imp, forall_eq, or_false,
  and_true]
theorem wf_colChk {i : ℕ} : WF (.blk (colChkPs i)) := by simp +decide only [colChkPs, WF, Prim.dst,
  rK2, rB, rMk, List.mem_cons, List.mem_nil_iff, forall_eq_or_imp, forall_eq, or_false, and_true]
theorem wf_child : WF (.blk childPs) := by simp +decide only [childPs, WF, Prim.dst, rK2, rB, rTA]

/-- **The walk's state at height `h`**: either every entry so far was found and `rQ0 … rQ3` hold a
digest `d` whose reading at height `h` is the reading under `d₀` at height `sib`, or an entry
was missing and the reading under `d₀` is `none`. -/
def WalkSt (i : ℕ) (L : Log) (d0 : Digest) (sib p h : ℕ) (M : Mem) : Prop :=
  (rd M rOk = 1 ∧ ∃ d : Digest, [rd M rQ0, rd M rQ1, rd M rQ2, rd M rQ3] = packBytes d.toList ∧
    colL (frEnc i) L d0 sib p = colL (frEnc i) L d h p) ∨
  (rd M rOk = 0 ∧ colL (frEnc i) L d0 sib p = none)

/-! ## The leaf and the copy -/

/-- What the copy stores as word `w`: tape word `x + 2 + w` if `8 (w + 1) < ql`, else `0`. -/
def cpW (I : Array Word) (x : Word) (ql w : ℕ) : Word :=
  if 8 * (w + 1) < ql then I.getD (x + toWord (2 + w)).toNat 0 else 0

theorem cpW_zero (I : Array Word) (x : Word) (w : ℕ) : cpW I x 0 w = 0 := by simp [cpW]

theorem colL_zero (L : Log) (d : Digest) (p : ℕ) :
    colL (frEnc i) L d 0 p = (pre L d).bind fun e => parseCol i e.1 := rfl

theorem mask_ltu (v a b : Word) :
    XOp.and.eval v (XOp.sub.eval 0 (XOp.ltu.eval a b)) = if a < b then v else 0 := by
  by_cases h : a < b
  · have h1 : (0 : Word) - 1 = BitVec.allOnes 64 := by decide
    show v &&& (0 - (if a < b then 1 else 0)) = _
    rw [if_pos h, if_pos h, h1, BitVec.and_allOnes]
  · show v &&& (0 - (if a < b then 1 else 0)) = _
    rw [if_neg h, if_neg h, BitVec.sub_self, BitVec.and_zero]
    rfl

theorem wf_copyBody : WF copyBody := by
  simp +decide only [copyBody, WF, Prim.dst, rV2, rMk, rK2, rWA, rTA, r8, cTmp, and_true]

/-- **One copy step**: cell `a + j` gets `cpW I x ql j`; the pointers advance. -/
theorem copyBody_sem (I : Array Word) (s : St) (hM : Inv s.M) {x : Word} {ql a j : ℕ}
    (hql : ql < 2 ^ 64) (ha : regs ≤ a + j) (ha2 : a + j + 1 < 2 ^ 64) (hj : 8 * (j + 2) < 2 ^ 64)
    (has : a + j < s.M.size) (hA : rd s.M rWA = toWord (a + j))
    (hT : rd s.M rTA = x + toWord (2 + j)) (h8 : rd s.M r8 = toWord (8 * (j + 1)))
    (hQ : rd s.M rQe = toWord ql) :
    rd (semXIR I copyBody s).M (a + j) = cpW I x ql j ∧
    (∀ y, regs ≤ y → y ≠ a + j → rd (semXIR I copyBody s).M y = rd s.M y) ∧
    rd (semXIR I copyBody s).M rWA = toWord (a + (j + 1)) ∧
    rd (semXIR I copyBody s).M rTA = x + toWord (2 + (j + 1)) ∧
    rd (semXIR I copyBody s).M r8 = toWord (8 * (j + 1 + 1)) ∧
    rd (semXIR I copyBody s).M rQe = toWord ql ∧
    rd (semXIR I copyBody s).M rPp = rd s.M rPp := by
  have hs := hM.1
  have h1 : rd s.M cOne = 1 := hM.2 0 (by decide)
  simp only [regs] at hs ha
  -- the masked word
  have wf1 : WF (.seq (.input rV2 rTA) (.blk [.op .ltu rMk r8 rQe, .const rK2 0,
      .op .sub rMk rK2 rMk, .op .and rV2 rV2 rMk])) := by simp +decide only [WF, Prim.dst, rV2, rMk,
        rK2, and_true]
  have v1 : rd (semXIR I (.seq (.input rV2 rTA) (.blk [.op .ltu rMk r8 rQe, .const rK2 0,
      .op .sub rMk rK2 rMk, .op .and rV2 rV2 rMk])) s).M rV2 = cpW I x ql j := by
    simp only [semXIR, runPrims, List.foldl, Prim.run]
    simp (disch := first | decide | (simp only [size_set, rV2, rMk, rK2]; omega)) only
      [rd_set_self, rd_set_ne]
    rw [hT, h8, hQ, mask_ltu, cpW]
    by_cases hc : 8 * (j + 1) < ql
    · rw [if_pos ((toWord_lt_toWord (by omega) hql).2 hc), if_pos hc]
    · rw [if_neg (fun h => hc ((toWord_lt_toWord (by omega) hql).1 h)), if_neg hc]
  have fr1 : ∀ r, r = rWA ∨ r = rTA ∨ r = r8 ∨ r = rQe ∨ r = rPp ∨ r = cOne →
      rd (semXIR I (.seq (.input rV2 rTA) (.blk [.op .ltu rMk r8 rQe, .const rK2 0,
        .op .sub rMk rK2 rMk, .op .and rV2 rV2 rMk])) s).M r = rd s.M r := fun r hr =>
    frame I _ s wf1 hM r (by rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> decide)
      (by rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;>
        simp +decide only [Writes, Prim.dst, rV2, rMk, rK2, rWA, rTA, r8, rQe, rPp, cOne, or_false])
  have hh1 : ∀ y, regs ≤ y → rd (semXIR I (.seq (.input rV2 rTA) (.blk [.op .ltu rMk r8 rQe,
      .const rK2 0, .op .sub rMk rK2 rMk, .op .and rV2 rV2 rMk])) s).M y = rd s.M y :=
    hframe I _ s (by simp +decide only [Lo, Prim.dst, regs, rV2, rMk, rK2, and_true])
  have hM1 := inv_sem I wf1 hM
  have hsz1 := size_sem I (.seq (.input rV2 rTA) (.blk [.op .ltu rMk r8 rQe, .const rK2 0,
      .op .sub rMk rK2 rMk, .op .and rV2 rV2 rMk])) s
  have e : semXIR I copyBody s = semXIR I (.seq (.store rWA rV2) (.blk [.op .add rWA rWA cOne,
      .op .add rTA rTA cOne, .const rK2 8, .op .add r8 r8 rK2])) (semXIR I (.seq (.input rV2 rTA)
      (.blk [.op .ltu rMk r8 rQe, .const rK2 0, .op .sub rMk rK2 rMk, .op .and rV2 rV2 rMk]))
      s) := rfl
  rw [e]
  generalize semXIR I (.seq (.input rV2 rTA) (.blk [.op .ltu rMk r8 rQe, .const rK2 0,
    .op .sub rMk rK2 rMk, .op .and rV2 rV2 rMk])) s = s1 at v1 fr1 hh1 hM1 hsz1
  have hs1 := hM1.1
  simp only [regs] at hs1
  -- the store
  have hA1 : rd s1.M rWA = toWord (a + j) := (fr1 _ (.inl rfl)).trans hA
  have hsz : a + j < s1.M.size := by omega
  have st : ∀ i, i ≠ cTmp → rd (storeM s1.M rWA rV2) i =
      if i = a + j then rd s1.M rV2 else rd s1.M i := fun i hi =>
    rd_storeM hM1 hA1 (by simp only [regs]; omega) (by omega) hsz (by decide) (by decide) hi
  rw [semXIR_seq]
  have e2 : semXIR I (.store rWA rV2) s1 = ⟨storeM s1.M rWA rV2, s1.o⟩ := rfl
  rw [e2]
  have hc1 : rd s1.M cOne = 1 := (fr1 _ (.inr (.inr (.inr (.inr (.inr rfl)))))).trans h1
  have hM2 : Inv (storeM s1.M rWA rV2) := inv_sem I (P := .store rWA rV2) (by simp +decide only [WF,
    rWA, cTmp])
    hM1
  have hs2 := hM2.1
  simp only [regs, size_storeM] at hs2
  have reg : ∀ r, r < 256 → r ≠ cTmp → rd (storeM s1.M rWA rV2) r = rd s1.M r := fun r hr hrt => by
    rw [st r hrt, if_neg (by omega)]
  simp only [semXIR, runPrims, List.foldl, Prim.run]
  refine ⟨?_, fun y hy hne => ?_, ?_⟩
  · rw [rd_set_ne (by simp only [r8]; omega), rd_set_ne (by simp only [rK2]; omega),
      rd_set_ne (by simp only [rTA]; omega), rd_set_ne (by simp only [rWA]; omega),
      st _ (by simp only [cTmp]; omega), if_pos rfl, v1]
  · simp only [regs] at hy
    rw [rd_set_ne (by simp only [r8]; omega), rd_set_ne (by simp only [rK2]; omega),
      rd_set_ne (by simp only [rTA]; omega), rd_set_ne (by simp only [rWA]; omega),
      st _ (by simp only [cTmp]; omega), if_neg hne, hh1 y (by simp only [regs]; omega)]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;>
  simp (disch := first | decide | (simp only [size_set, size_storeM, rWA, rTA, rK2, r8]; omega))
    only [rd_set_self, rd_set_ne]
  · rw [reg _ (by decide) (by decide), reg _ (by decide) (by decide), hA1, hc1, add_one_toWord,
      Nat.add_assoc]
  · rw [reg _ (by decide) (by decide), reg _ (by decide) (by decide), fr1 _ (.inr (.inl rfl)), hT,
      hc1]
    show x + toWord (2 + j) + 1 = _
    rw [BitVec.add_assoc, toWord_add_one, Nat.add_assoc]
  · rw [reg _ (by decide) (by decide), fr1 _ (.inr (.inr (.inl rfl))), h8,
      show (8 : Word) = toWord 8 from rfl, add_toWord]
    congr 1
  · rw [reg _ (by decide) (by decide), fr1 _ (.inr (.inr (.inr (.inl rfl)))), hQ]
  · rw [reg _ (by decide) (by decide), fr1 _ (.inr (.inr (.inr (.inr (.inl rfl)))))]

/-- **The copy loop**: `m` steps from word `j` store `cpW I x ql i` at `a + i`, `j ≤ i < j + m`. -/
theorem copyLoop (I : Array Word) {x : Word} {ql a nw : ℕ} (hql : ql < 2 ^ 64) (ha : regs ≤ a)
    (ha2 : a + nw + 2 < 2 ^ 64) (hnw : nw < 2 ^ 60) :
    ∀ (m j : ℕ) (s : St), j + m ≤ nw → Inv s.M → a + nw ≤ s.M.size →
      rd s.M rWA = toWord (a + j) → rd s.M rTA = x + toWord (2 + j) →
      rd s.M r8 = toWord (8 * (j + 1)) → rd s.M rQe = toWord ql →
      (∀ i, j ≤ i → i < j + m →
        rd (iterL (semXIR I copyBody) rCw m s).M (a + i) = cpW I x ql i) ∧
      (∀ y, regs ≤ y → (y < a + j ∨ a + j + m ≤ y) →
        rd (iterL (semXIR I copyBody) rCw m s).M y = rd s.M y) ∧
      Inv (iterL (semXIR I copyBody) rCw m s).M ∧
      rd (iterL (semXIR I copyBody) rCw m s).M rWA = toWord (a + (j + m)) ∧
      rd (iterL (semXIR I copyBody) rCw m s).M rPp = rd s.M rPp
  | 0, j, s, _, hM, _, hA, _, _, _ =>
    ⟨fun i h1 h2 => by omega, fun _ _ _ => rfl, hM, by show rd s.M rWA = _; rw [hA, Nat.add_zero], rfl⟩
  | m + 1, j, s, hjm, hM, hsz, hA, hT, h8, hQ => by
    obtain ⟨c1, c2, c3, c4, c5, c6, c7⟩ := copyBody_sem I s hM hql (by simp only [regs] at *; omega)
      (by omega) (by omega) (by omega) hA hT h8 hQ
    have hM1 := inv_sem I wf_copyBody hM
    have hM' : Inv (decS rCw (semXIR I copyBody s)).M := inv_decS hM1 (by decide)
    have dk : ∀ r, r ≠ rCw → rd (decS rCw (semXIR I copyBody s)).M r =
        rd (semXIR I copyBody s).M r := fun r hr => rd_decS (Ne.symm hr) _
    have hsz' : a + nw ≤ (decS rCw (semXIR I copyBody s)).M.size := by
      rw [size_decS, size_sem]; exact hsz
    have hy : ∀ y, regs ≤ y → y ≠ rCw := fun y hy => by simp only [rCw, regs] at *; omega
    obtain ⟨d1, d2, d3, d4, d5⟩ := copyLoop I hql ha ha2 hnw m (j + 1) _ (by omega) hM' hsz'
      (by rw [dk _ (by decide), c3])
      (by rw [dk _ (by decide), c4]) (by rw [dk _ (by decide), c5]) (by rw [dk _ (by decide), c6])
    simp only [iterL]
    refine ⟨fun i h1 h2 => ?_, fun y hy1 hy2 => ?_, d3,
      by rw [d4, show j + 1 + m = j + (m + 1) by omega], ?_⟩
    · by_cases hij : i = j
      · subst hij
        rw [d2 _ (by simp only [regs] at *; omega) (.inl (by omega)), dk _ (hy _ (by
          simp only [regs] at *; omega)), c1]
      · exact d1 i (by omega) (by omega)
    · rw [d2 _ hy1 (by omega), dk _ (hy _ hy1), c2 _ hy1 (by omega)]
    · rw [d5, dk _ (by decide), c7]

theorem wf_copyIR {nw : ℕ} : WF (copyIR nw) := by
  simp +decide only [copyIR, copyBody, WF, Writes, Prim.dst, rV2, rMk, rK2, rWA, rTA, r8, rNw, rCw,
    cTmp, regs, List.mem_cons, List.mem_nil_iff, forall_eq_or_imp, forall_eq, or_false, and_true]

/-- **The copy**: from `rXq = x`, `rQe = ql`, `rWA = a`, cells `a … a + nw − 1` get
`cpW I x ql ·`; every other heap cell is kept; `rWA` ends at `a + nw`. -/
theorem copyIR_sem (I : Array Word) (s : St) (hM : Inv s.M) {x : Word} {ql a nw : ℕ}
    (hql : ql < 2 ^ 64) (ha : regs ≤ a) (ha2 : a + nw + 2 < 2 ^ 64) (hnw : nw < 2 ^ 60)
    (hsz : a + nw ≤ s.M.size)
    (hX : rd s.M rXq = x) (hQ : rd s.M rQe = toWord ql) (hA : rd s.M rWA = toWord a) :
    (∀ i < nw, rd (semXIR I (copyIR nw) s).M (a + i) = cpW I x ql i) ∧
    (∀ y, regs ≤ y → (y < a ∨ a + nw ≤ y) → rd (semXIR I (copyIR nw) s).M y = rd s.M y) ∧
    Inv (semXIR I (copyIR nw) s).M ∧ rd (semXIR I (copyIR nw) s).M rWA = toWord (a + nw) ∧
    rd (semXIR I (copyIR nw) s).M rPp = rd s.M rPp := by
  have hs := hM.1
  simp only [regs] at hs
  have wf0 : WF (.blk [.const rK2 2, .op .add rTA rXq rK2, .const r8 8, .const rNw (toWord nw)]) := by
    simp +decide only [WF, Prim.dst, rK2, rTA, r8, rNw, List.mem_cons, List.mem_nil_iff,
      forall_eq_or_imp, forall_eq, or_false, and_true]
  have hM0 := inv_sem I wf0 hM
  have hH0 := hframe I (.blk [.const rK2 2, .op .add rTA rXq rK2, .const r8 8, .const rNw (toWord nw)]) s
    (by simp +decide only [Lo, Prim.dst, regs, rK2, rTA, r8, rNw, List.mem_cons, List.mem_nil_iff,
      forall_eq_or_imp, forall_eq, or_false, and_true])
  have hsz0 := size_sem I (.blk [.const rK2 2, .op .add rTA rXq rK2, .const r8 8,
    .const rNw (toWord nw)]) s
  have r0 : rd (semXIR I (.blk [.const rK2 2, .op .add rTA rXq rK2, .const r8 8, .const rNw (toWord nw)])
        s).M rTA = x + toWord (2 + 0) ∧
      rd (semXIR I (.blk [.const rK2 2, .op .add rTA rXq rK2, .const r8 8, .const rNw (toWord nw)])
        s).M r8 = toWord (8 * (0 + 1)) ∧
      rd (semXIR I (.blk [.const rK2 2, .op .add rTA rXq rK2, .const r8 8, .const rNw (toWord nw)])
        s).M rNw = toWord nw ∧
      rd (semXIR I (.blk [.const rK2 2, .op .add rTA rXq rK2, .const r8 8, .const rNw (toWord nw)])
        s).M rQe = toWord ql ∧
      rd (semXIR I (.blk [.const rK2 2, .op .add rTA rXq rK2, .const r8 8, .const rNw (toWord nw)])
        s).M rWA = toWord (a + 0) ∧
      rd (semXIR I (.blk [.const rK2 2, .op .add rTA rXq rK2, .const r8 8, .const rNw (toWord nw)])
        s).M rPp = rd s.M rPp := by
    simp only [semXIR, runPrims, List.foldl, Prim.run]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp (disch := first | decide | (simp only [size_set, rK2, rTA, r8, rNw]; omega)) only
      [rd_set_self, rd_set_ne]
    · rw [hX]; rfl
    · rfl
    · exact hQ
    · exact hA
  rw [copyIR, semXIR_seq]
  generalize semXIR I (.blk [.const rK2 2, .op .add rTA rXq rK2, .const r8 8, .const rNw (toWord nw)])
    s = s0 at hM0 hH0 hsz0 r0
  obtain ⟨t0, e0, n0, q0, a0, p0⟩ := r0
  have hE : ∀ i, i ≠ rCw → i ≠ cTmp → rd (entryK rCw rNw (toWord nw) s0.M) i = rd s0.M i :=
    fun i h1 h2 => entryK_frame _ (Ne.symm h1) (Ne.symm h2)
  have hcnt : rd (entryK rCw rNw (toWord nw) s0.M) rCw = toWord nw :=
    entryK_count hM0 (by decide) (by decide) (by decide) n0
  have hME := inv_entryK (c := rCw) (n := rNw) (K := toWord nw) hM0 (by decide)
  have e : semXIR I (.loopK rCw rNw (toWord nw) copyBody) s0 =
      iterL (semXIR I copyBody) rCw nw ⟨entryK rCw rNw (toWord nw) s0.M, s0.o⟩ := by
    simp only [semXIR, hcnt, toNat_toWord (show nw < 2 ^ 64 by omega)]
  rw [e]
  have hy : ∀ y, regs ≤ y → y ≠ rCw ∧ y ≠ cTmp := fun y hy => by
    simp only [rCw, cTmp, regs] at *; omega
  obtain ⟨d1, d2, d3, d4, d5⟩ := copyLoop I hql ha ha2 hnw nw 0 ⟨entryK rCw rNw (toWord nw) s0.M, s0.o⟩
    (by omega) hME (by simp only [size_entryK]; omega) (by rw [hE _ (by decide) (by decide), a0])
    (by rw [hE _ (by decide) (by decide), t0]) (by rw [hE _ (by decide) (by decide), e0])
    (by rw [hE _ (by decide) (by decide), q0])
  refine ⟨fun i hi => d1 i (by omega) (by omega), fun y hy1 hy2 => ?_, d3, by rw [d4, Nat.zero_add], ?_⟩
  · rw [d2 y hy1 (by omega)]
    show rd (entryK rCw rNw (toWord nw) s0.M) y = rd s.M y
    rw [hE y (hy y hy1).1 (hy y hy1).2, hH0 y hy1]
  · rw [d5]
    show rd (entryK rCw rNw (toWord nw) s0.M) rPp = rd s.M rPp
    rw [hE _ (by decide) (by decide), p0]

/-! ## One position -/

/-! ## `read_spec` -/

end Indep

/-! ## The read at a parametric index base `bX` and log position `pL`

S-H4 pass 5: one copy of each proof. 3.x's read (`readIR`, index at `memX`, `|L|` at `posL`) is the
instance `readIR4 memX posL` (`posLoop`, `readIR_sem` below). -/

section Read4

variable {c : Digest} {π : Proof} {L : Log} {i : ℕ} {bX pL : ℕ}

theorem Dom4.small (hD : Dom4 pL c π L) : L.length < 2 ^ 62 := by
  have := tape_entries_end4 c π L hD.hs
  have := len_entries L; have := hD.ht
  omega

theorem Dom4.posE_lt (hD : Dom4 pL c π L) {k : ℕ} (hk : k < L.length) :
    posE4 pL L k + 1 + (L[k].1.size + 7) / 8 + 4 ≤ 2 ^ 64 := by
  have hend := tape_entries_end4 c π L hD.hs
  have := entryOff_lt L (Nat.lt_succ_self k) (by omega : k + 1 ≤ L.length)
  rw [entryOff_succ L hk] at this
  have hk1 : entryOff L (k + 1) ≤ entryOff L L.length := by
    rcases Nat.lt_or_ge (k + 1) L.length with h | h
    · exact (entryOff_lt L h le_rfl).le
    · rw [show k + 1 = L.length by omega]
  rw [entryOff_succ L hk] at hk1
  have hqw : qWords L[k] = 5 + (L[k].1.size + 7) / 8 := rfl
  have := hD.ht
  simp only [posE4]; omega

theorem tp_posL4 (hD : Dom4 pL c π L) : (tp c π L).getD pL 0 = toWord L.length := by
  rw [tp, getD_toArray, tape_getD_posL4 c π L hD.hs]

/-- The entry's length word on the tape. -/
theorem tp_len (hD : Dom4 pL c π L) {k : ℕ} (hk : k < L.length) :
    (tp c π L).getD (posE4 pL L k) 0 = toWord L[k].1.size := by
  rw [tp, getD_toArray]; exact tape_entry4 c π L hD.hs hk

/-- The entry's query words on the tape. -/
theorem tp_q (hD : Dom4 pL c π L) {k : ℕ} (hk : k < L.length) {j : ℕ}
    (hj : j < (L[k].1.size + 7) / 8) :
    (tp c π L).getD (posE4 pL L k + 1 + j) 0 = (packBytes L[k].1.data.toList).getD j 0 := by
  rw [tp, getD_toArray]; exact tape_query4 c π L hD.hs hk hj

/-- **The machine's node test is `parseNode i`**. -/
theorem nodeFlag (hD : Dom4 pL c π L) {k : ℕ} (hk : k < L.length) :
    (decide ((tp c π L).getD (posE4 pL L k) 0 = toWord 72) &&
      decide ((tp c π L).getD (posE4 pL L k + 1) 0 = tagNWl i)) =
      decide (L[k].1.data.toList.take 8 = tagNode i ∧ L[k].1.size = 72) := by
  have hq := hD.hq _ (List.getElem_mem hk)
  rw [tp_len hD hk]
  by_cases h72 : L[k].1.size = 72
  · have h1 := tp_q hD hk (j := 0) (by omega)
    rw [Nat.add_zero] at h1
    rw [h1, ← Bool.decide_and]
    exact decide_eq_decide.mpr (nodeChk_iff _ i hq)
  · have hne : toWord L[k].1.size ≠ toWord 72 := fun e => h72 (by
      have := congrArg BitVec.toNat e; rwa [toNat_toWord hq, toNat_toWord (by norm_num)] at this)
    simp [hne, h72]

/-- **The machine's column test is `parseCol i`**. -/
theorem colFlag (hD : Dom4 pL c π L) {k : ℕ} (hk : k < L.length) :
    (decide ((7 : Word) < (tp c π L).getD (posE4 pL L k) 0) &&
      decide ((tp c π L).getD (posE4 pL L k + 1) 0 = tagCWl i)) =
      decide (L[k].1.data.toList.take 8 = tagCol i) := by
  have hq := hD.hq _ (List.getElem_mem hk)
  rw [tp_len hD hk]
  by_cases h7 : (7 : Word) < toWord L[k].1.size
  · have h8 : 7 < L[k].1.size := (toWord_lt_toWord (by norm_num) hq).1 h7
    have h1 := tp_q hD hk (j := 0) (by omega)
    rw [Nat.add_zero] at h1
    rw [h1, ← Bool.decide_and]
    exact decide_eq_decide.mpr (colChk_iff _ i hq)
  · have : ¬ L[k].1.data.toList.take 8 = tagCol i := fun e =>
      h7 ((colChk_iff _ i hq).2 e).1
    rw [show decide ((7 : Word) < toWord L[k].1.size) = false from decide_eq_false h7,
      Bool.false_and, decide_eq_false this]

/-- **The child's words**: after a successful node test, the tape words at
`X + 2 + 4 · bit` are the child digest's. -/
theorem child_words (hD : Dom4 pL c π L) {k : ℕ} (hk : k < L.length) (h72 : L[k].1.size = 72)
    (bt : Bool) :
    [(tp c π L).getD (posE4 pL L k + 2 + 4 * (if bt then 1 else 0)) 0,
      (tp c π L).getD (posE4 pL L k + 2 + 4 * (if bt then 1 else 0) + 1) 0,
      (tp c π L).getD (posE4 pL L k + 2 + 4 * (if bt then 1 else 0) + 2) 0,
      (tp c π L).getD (posE4 pL L k + 2 + 4 * (if bt then 1 else 0) + 3) 0] =
      packBytes (if bt then bytesAt L[k].1 40 32 else bytesAt L[k].1 8 32).toList := by
  have e : (if bt then bytesAt L[k].1 40 32 else bytesAt L[k].1 8 32) =
      bytesAt L[k].1 (8 * (1 + 4 * (if bt then 1 else 0))) 32 := by cases bt <;> rfl
  have hb : (if bt then 1 else 0) ≤ 1 := by split <;> omega
  rw [e, packBytes_digest_eq4]
  have w : ∀ m < 4, (tp c π L).getD (posE4 pL L k + 2 + 4 * (if bt then 1 else 0) + m) 0 =
      (packBytes (bytesAt L[k].1 (8 * (1 + 4 * (if bt then 1 else 0))) 32).toList).getD m 0 :=
    fun m hm => by
      rw [packBytes_bytesAt _ (by omega) hm, ← tp_q hD hk (by omega)]
      congr 1; omega
  rw [← w 0 (by decide), ← w 1 (by decide), ← w 2 (by decide), ← w 3 (by decide)]
  simp only [Nat.add_zero]

/-- **The copy of a parsed column is its words**. -/
theorem cpW_entry (hD : Dom4 pL c π L) {k : ℕ} (hk : k < L.length) (w : ℕ) :
    cpW (tp c π L) (toWord (posE4 pL L k))
      (if L[k].1.data.toList.take 8 = tagCol i then L[k].1.size else 0) w =
      colWord (parseCol i L[k].1) w := by
  have hxl := hD.posE_lt hk
  by_cases hC : L[k].1.data.toList.take 8 = tagCol i
  · simp only [hC, ite_true, parseCol, colWord]
    rw [packBytes_col, packBytes_getD, size_toList, cpW]
    by_cases hw : 8 * (w + 1) < L[k].1.size
    · rw [if_pos hw, if_pos (by omega), toWord_add, toNat_toWord (by omega),
        show posE4 pL L k + (2 + w) = posE4 pL L k + 1 + (1 + w) by omega, tp_q hD hk (by omega),
        packBytes_getD, size_toList, if_pos (by omega)]
    · rw [if_neg hw, if_neg (by omega)]
  · simp only [hC, ite_false, cpW_zero, parseCol, colWord]

theorem loK_lookIR4 : LoK (lookIR4 bX pL) := by
  simp +decide [lookIR4, bsBody4, ansLtIR, cmpTWord, eqTWord, foundIR4, aposIR, ceil8Ps, readAt,
    LoK, Prim.dst, regs, rQ0, rQ1, rQ2, rQ3, rLo, rLn, rHf, rMd, rCB, rNB, rFd, rA, rN, rQL, rT2,
    rKc, rAd, rX, rPa, rKa, rG, rH, rF, and_true, List.cons_append, List.nil_append]

theorem wf_getIR : WF (getIR bX) := by simp +decide [getIR, WF, Prim.dst, rK2, rAd2, rXq, rQn, rTA,
  rV2, and_true]

theorem lo_getIR : Lo (getIR bX) := by simp +decide [getIR, Lo, Prim.dst, regs, rK2, rAd2, rXq, rQn,
  rTA, rV2, and_true]

theorem wf_nodeBody : WF (nodeBody bX pL i) := by
  have := (wf_lookIR4 bX pL)
  simp +decide only [nodeBody, getIR, nodeChkPs, childPs, ld4IR, WF, Prim.dst, rK2, rAd2, rXq, rQn,
    rTA, rV2, rB, rMk, rOk, rQ0, rQ1, rQ2, rQ3, this, List.mem_cons, List.mem_nil_iff,
    forall_eq_or_imp, forall_eq, or_false, and_true]

theorem loK_nodeBody : LoK (nodeBody bX pL i) := by
  have := loK_lookIR4 (bX := bX) (pL := pL)
  simp +decide only [nodeBody, getIR, nodeChkPs, childPs, ld4IR, LoK, Prim.dst, regs, rK2, rAd2,
    rXq, rQn, rTA, rV2, rB, rMk, rOk, rQ0, rQ1, rQ2, rQ3, this, List.mem_cons, List.mem_nil_iff,
    forall_eq_or_imp, forall_eq, or_false, and_true]

/-- The registers the walk keeps across a node step. -/
theorem nodeBody_nw {r : ℕ} (hr : r = rPp ∨ r = rWA ∨ r = rHc) : ¬ Writes (nodeBody bX pL i) r := by
  have hl : ¬ Writes (lookIR4 bX pL) r := lookIR4_nw bX pL (by rcases hr with rfl | rfl | rfl <;> decide)
  simp only [nodeBody, Writes, not_or]
  refine ⟨⟨hl, ?_⟩, ?_⟩ <;>
  rcases hr with rfl | rfl | rfl <;>
  simp +decide only [getIR, nodeChkPs, childPs, ld4IR, Writes, Prim.dst, rK2, rAd2, rXq, rQn, rTA,
    rV2, rB, rMk, rOk, rQ0, rQ1, rQ2, rQ3, rPp, rWA, rHc, List.mem_cons, List.mem_nil_iff,
    exists_eq_or_imp, exists_eq_left, or_false, and_true]

theorem wf_colIR : WF (colIR bX pL i) := by
  have := (wf_lookIR4 bX pL)
  simp +decide only [colIR, getIR, colChkPs, WF, Prim.dst, rK2, rAd2, rXq, rQn, rTA, rV2, rB, rMk,
    rQe, this, List.mem_cons, List.mem_nil_iff, forall_eq_or_imp, forall_eq, or_false, and_true]

theorem loK_colIR : LoK (colIR bX pL i) := by
  have := loK_lookIR4 (bX := bX) (pL := pL)
  simp +decide only [colIR, getIR, colChkPs, LoK, Prim.dst, regs, rK2, rAd2, rXq, rQn, rTA, rV2, rB,
    rMk, rQe, this, List.mem_cons, List.mem_nil_iff, forall_eq_or_imp, forall_eq, or_false,
    and_true]

theorem colIR_nw {r : ℕ} (hr : r = rPp ∨ r = rWA) : ¬ Writes (colIR bX pL i) r := by
  have hl : ¬ Writes (lookIR4 bX pL) r := lookIR4_nw bX pL (by rcases hr with rfl | rfl <;> decide)
  simp only [colIR, Writes, not_or]
  refine ⟨?_, ⟨hl, ?_⟩, ?_⟩ <;>
  rcases hr with rfl | rfl <;>
  simp +decide only [getIR, colChkPs, Writes, Prim.dst, rK2, rAd2, rXq, rQn, rTA, rV2, rB, rMk, rQe,
    rPp, rWA, List.mem_cons, List.mem_nil_iff, exists_eq_or_imp, exists_eq_left, or_false, and_true]

theorem wf_posBody (i cw nw sib : ℕ) : WF (posBody4 bX pL i cw nw sib) :=
  (wf_readIR4 bX pL i cw 0 nw sib 0).2.2.2.2

variable (hbX : regs ≤ bX) (hbX2 : bX ≤ 2 ^ 60) (hpL : pL ≤ 2 ^ 60)
include hbX hbX2 hpL

/-- **The lookup** on a sorted index `Xi` held in `X[0..|L|)`: the first preimage's slot when
the target is answered, `rFd = 0` otherwise; the heap and this phase's registers are kept. -/
theorem look_spec (hD : Dom4 pL c π L) {Xi : ℕ → Word} (hX : Sorted4 pL (tp c π L) L Xi) (s : St)
    (hM : Inv s.M) (hXs : ∀ a < L.length, rd s.M (bX + a) = Xi a) (t : Digest)
    (hT : [rd s.M rQ0, rd s.M rQ1, rd s.M rQ2, rd s.M rQ3] = packBytes t.toList) :
    (∀ k, FR.Snd.ansIdx L t = some k → ∃ b < L.length,
      rd (semXIR (tp c π L) (lookIR4 bX pL) s).M rLo = toWord b ∧
      rd (semXIR (tp c π L) (lookIR4 bX pL) s).M rFd = 1 ∧ Xi b = toWord (posE4 pL L k)) ∧
    (FR.Snd.ansIdx L t = none → rd (semXIR (tp c π L) (lookIR4 bX pL) s).M rFd = 0) ∧
    (∀ x, regs ≤ x → rd (semXIR (tp c π L) (lookIR4 bX pL) s).M x = rd s.M x) ∧
    Inv (semXIR (tp c π L) (lookIR4 bX pL) s).M ∧
    (∀ r, 117 ≤ r → r < regs → rd (semXIR (tp c π L) (lookIR4 bX pL) s).M r = rd s.M r) := by
  set I := tp c π L with hI
  obtain ⟨l1, l2, l3⟩ := lookIR4_sem hbX hbX2 hpL I s hM (n := L.length) (X := Xi) (tp_posL4 hD) hD.small hT hXs
  obtain ⟨hmono, hpure⟩ := lookup_pure4 c π L hD.hs hD.hq hD.ht hX t
  obtain ⟨b1, b2, b3⟩ := bsRun_spec (p := ltT I Xi (packBytes t.toList)) (n := L.length)
    (by have := hD.small; omega) hmono
  obtain ⟨hsome, hnone⟩ := hpure _ b1 b2 b3
  refine ⟨fun k hk => ?_, fun hk => ?_, l3, inv_sem I (wf_lookIR4 bX pL) hM,
    fun r hr hr2 => frame I _ s (wf_lookIR4 bX pL) hM r hr2 (lookIR4_nw bX pL hr)⟩
  · obtain ⟨hb, e⟩ := hsome k hk
    obtain ⟨hkl, hkc⟩ := FR.Snd.ansIdx_lt hk
    refine ⟨_, hb, l1, ?_, e⟩
    rw [l2, hXs _ hb, e, ansW_entry4 c π L hD.hs hD.hq hD.ht hkl, hkc]
    simp [hb, bW]
  · rw [l2]
    by_cases hb : (bsRun (ltT I Xi (packBytes t.toList)) 64 (0, L.length)).1 < L.length
    · rw [hXs _ hb]
      have := hnone hk _ hb
      simp [hb, bW]
      exact this
    · simp [hb, bW]

/-- **After a lookup**: the entry's position, its query length and its first query word. -/
theorem getIR_sem (I : Array Word) (s : St) (hM : Inv s.M) {b x : ℕ} (hb : b < 2 ^ 62)
    (hx : x + 1 < 2 ^ 64) (hL : rd s.M rLo = toWord b) (hX : rd s.M (bX + b) = toWord x) :
    rd (semXIR I (getIR bX) s).M rXq = toWord x ∧ rd (semXIR I (getIR bX) s).M rQn = I.getD x 0 ∧
      rd (semXIR I (getIR bX) s).M rV2 = I.getD (x + 1) 0 := by
  have hs := hM.1
  have h1 : rd s.M cOne = 1 := hM.2 0 (by decide)
  simp only [regs] at hs
  simp only [getIR, semXIR, runPrims, List.foldl, Prim.run]
  refine ⟨?_, ?_, ?_⟩ <;>
  simp (disch := first | decide | (simp only [size_set, rK2, rAd2, rXq, rQn, rTA, rV2]; omega))
    only [rd_set_self, rd_set_ne]
  all_goals
    rw [hL, add_toWord, toNat_toWord (by omega), rd_set_ne (by simp only [rAd2, regs] at hbX ⊢; omega),
      rd_set_ne (by simp only [rK2, regs] at hbX ⊢; omega), show b + bX = bX + b by omega, hX]
  · rw [toNat_toWord (by omega)]
  · rw [h1, add_one_toWord, toNat_toWord (by omega)]

/-- **One machine step down the tree is `nodeStepP`**: from `rOk = 1` with the digest `d` in
`rQ0 … rQ3` at height `h + 1`, the step leaves `rOk = 1` and the child's digest, or `rOk = 0`
when `colL` reads nothing. -/
theorem nodeBody_sem (hD : Dom4 pL c π L) {Xi : ℕ → Word} (hX : Sorted4 pL (tp c π L) L Xi) (s : St)
    (hM : Inv s.M) (hXs : ∀ a < L.length, rd s.M (bX + a) = Xi a) {p h : ℕ} (hp : p < 2 ^ 62)
    (hh : h + 1 < 64) (hP : rd s.M rPp = toWord p) (hH : rd s.M rHc = toWord (h + 1))
    (hOk : rd s.M rOk = 1) {d : Digest}
    (hT : [rd s.M rQ0, rd s.M rQ1, rd s.M rQ2, rd s.M rQ3] = packBytes d.toList) :
    (∀ d', nodeStepP i L p h d = some d' → rd (semXIR (tp c π L) (nodeBody bX pL i) s).M rOk = 1 ∧
      [rd (semXIR (tp c π L) (nodeBody bX pL i) s).M rQ0, rd (semXIR (tp c π L) (nodeBody bX pL i) s).M rQ1,
        rd (semXIR (tp c π L) (nodeBody bX pL i) s).M rQ2, rd (semXIR (tp c π L) (nodeBody bX pL i) s).M rQ3] =
        packBytes d'.toList) ∧
    (nodeStepP i L p h d = none → rd (semXIR (tp c π L) (nodeBody bX pL i) s).M rOk = 0) := by
  set I := tp c π L with hI
  have hs := hM.1
  simp only [regs] at hs
  rw [nodeBody, semXIR_ite, hOk, if_neg (by decide), semXIR_seq]
  obtain ⟨lk1, lk2, lk3, lk4, lk5⟩ := look_spec hbX hbX2 hpL hD hX s hM hXs d hT
  have hP1 := (lk5 rPp (by decide) (by decide)).trans hP
  have hH1 := (lk5 rHc (by decide) (by decide)).trans hH
  have hO1 := (lk5 rOk (by decide) (by decide)).trans hOk
  generalize semXIR I (lookIR4 bX pL) s = s1 at lk1 lk2 lk3 lk4 hP1 hH1 hO1
  have hs1 := lk4.1
  simp only [regs] at hs1
  rw [semXIR_ite]
  cases hk : FR.Snd.ansIdx L d with
  | none =>
    have hn : nodeStepP i L p h d = none := by simp [nodeStepP, pre_none hk]
    rw [lk2 hk, if_pos rfl]
    refine ⟨fun d' h' => (by rw [hn] at h'; cases h'), fun _ => ?_⟩
    simp only [semXIR, runPrims, List.foldl, Prim.run]
    exact rd_set_self (by simp only [rOk]; omega)
  | some k =>
    obtain ⟨b, hb, hlo, hfd, hxb⟩ := lk1 k hk
    obtain ⟨hkL, hpre⟩ := pre_some hk
    rw [hfd, if_neg (by decide)]
    have hxl := hD.posE_lt hkL
    have hsm := hD.small
    obtain ⟨g1, g2, g3⟩ := getIR_sem hbX hbX2 hpL I s1 lk4 (b := b) (x := posE4 pL L k) (by omega) (by omega) hlo
      (by rw [lk3 _ (by simp only [regs] at hbX ⊢; omega), hXs b hb, hxb])
    have fG : ∀ r, r = rOk ∨ r = rPp ∨ r = rHc → rd (semXIR I (getIR bX) s1).M r = rd s1.M r :=
      fun r hr => frame I _ s1 (wf_getIR (bX := bX)) lk4 r (by rcases hr with rfl | rfl | rfl <;> decide)
        (by rcases hr with rfl | rfl | rfl <;>
          simp +decide [getIR, Writes, Prim.dst, rK2, rAd2, rXq, rQn, rTA, rV2, rOk, rPp, rHc,
            or_false])
    have hM2 := inv_sem I (wf_getIR (bX := bX)) lk4
    rw [semXIR_seq]
    generalize semXIR I (getIR bX) s1 = s2 at g1 g2 g3 fG hM2
    have hB := nodeChk_sem I i s2 hM2
    rw [g2, g3, nodeFlag hD hkL] at hB
    have fC : ∀ r, r = rOk ∨ r = rPp ∨ r = rHc ∨ r = rXq →
        rd (semXIR I (.blk (nodeChkPs i)) s2).M r = rd s2.M r :=
      fun r hr => frame I _ s2 (wf_nodeChk (i := i)) hM2 r
        (by rcases hr with rfl | rfl | rfl | rfl <;> decide)
        (by rcases hr with rfl | rfl | rfl | rfl <;>
          simp +decide only [nodeChkPs, Writes, Prim.dst, rK2, rB, rMk, rOk, rPp, rHc, rXq,
            List.mem_cons, List.mem_nil_iff, exists_eq_or_imp, exists_eq_left, or_false])
    have hM3 := inv_sem I (wf_nodeChk (i := i)) hM2
    rw [semXIR_seq]
    generalize semXIR I (.blk (nodeChkPs i)) s2 = s3 at hB fC hM3
    have hs3 := hM3.1
    simp only [regs] at hs3
    rw [semXIR_ite, hB]
    by_cases hC : L[k].1.data.toList.take 8 = tagNode i ∧ L[k].1.size = 72
    · rw [decide_eq_true hC, if_neg bW_ne_zero]
      have hsome : nodeStepP i L p h d =
          some (if p.testBit h then bytesAt L[k].1 40 32 else bytesAt L[k].1 8 32) := by
        simp only [nodeStepP, hpre, Option.bind_some, parseNode_eq_some _ hC, Option.map_some]
      refine ⟨fun d' h' => ?_, fun h' => by rw [hsome] at h'; cases h'⟩
      rw [hsome] at h'
      cases h'
      rw [semXIR_seq]
      have hA := child_sem I s3 hM3 (x := posE4 pL L k) (p := p) (h := h) (by omega) hh
        (by rw [fC _ (.inr (.inr (.inr rfl))), g1])
        (by rw [fC _ (.inr (.inl rfl)), fG _ (.inr (.inl rfl)), hP1])
        (by rw [fC _ (.inr (.inr (.inl rfl))), fG _ (.inr (.inr rfl)), hH1])
      have hM4 := inv_sem I wf_child hM3
      have hO4 : rd (semXIR I (.blk childPs) s3).M rOk = 1 := by
        rw [frame I _ s3 wf_child hM3 rOk (by decide) (by
          simp +decide only [childPs, Writes, Prim.dst, rK2, rB, rTA, rOk]), fC _ (.inl rfl),
          fG _ (.inl rfl), hO1]
      generalize semXIR I (.blk childPs) s3 = s4 at hA hM4 hO4
      have hbt : (if p.testBit h then 1 else 0) ≤ 1 := by split <;> omega
      refine ⟨by
        rw [frame I _ s4 wf_ld4IR hM4 rOk (by decide) (by
          simp +decide only [ld4IR, Writes, Prim.dst, rQ0, rQ1, rQ2, rQ3, rTA, rOk, or_false])]
        exact hO4, ?_⟩
      rw [ld4_sem I s4 hM4 (by omega) hA]
      exact child_words hD hkL hC.2 _
    · rw [decide_eq_false hC, if_pos bW_false]
      have hnone : nodeStepP i L p h d = none := by
        simp only [nodeStepP, hpre, Option.bind_some, parseNode_eq_none _ hC, Option.map_none]
      refine ⟨fun d' h' => (by rw [hnone] at h'; cases h'), fun _ => ?_⟩
      simp only [semXIR, runPrims, List.foldl, Prim.run]
      exact rd_set_self (by simp only [rOk]; omega)

/-- **One node step keeps the walk's state**, one level down. -/
theorem nodeWalk (hD : Dom4 pL c π L) {Xi : ℕ → Word} (hX : Sorted4 pL (tp c π L) L Xi) (s : St)
    (hM : Inv s.M) (hXs : ∀ a < L.length, rd s.M (bX + a) = Xi a) {d0 : Digest} {sib p h : ℕ}
    (hp : p < 2 ^ 62) (hh : h + 1 < 64) (hP : rd s.M rPp = toWord p)
    (hH : rd s.M rHc = toWord (h + 1)) (hW : WalkSt i L d0 sib p (h + 1) s.M) :
    WalkSt i L d0 sib p h (semXIR (tp c π L) (nodeBody bX pL i) s).M := by
  rcases hW with ⟨hOk, d, hT, hc⟩ | ⟨hOk, hc⟩
  · obtain ⟨n1, n2⟩ := nodeBody_sem hbX hbX2 hpL hD hX s hM hXs hp hh hP hH hOk hT
    rw [colL_succ] at hc
    cases hn : nodeStepP i L p h d with
    | none =>
      rw [hn] at hc
      exact .inr ⟨n2 hn, hc⟩
    | some d' =>
      rw [hn] at hc
      obtain ⟨o1, o2⟩ := n1 d' hn
      exact .inl ⟨o1, d', o2, hc⟩
  · have e : semXIR (tp c π L) (nodeBody bX pL i) s = s := by
      rw [nodeBody, semXIR_ite, hOk, if_pos rfl]; rfl
    rw [e]; exact .inr ⟨hOk, hc⟩

/-- **The height loop**: `m` node steps from height `m` reach height `0`; the heap, `rPp` and
`rWA` are kept. -/
theorem nodeLoop (hD : Dom4 pL c π L) {Xi : ℕ → Word} (hX : Sorted4 pL (tp c π L) L Xi) {d0 : Digest}
    {sib p : ℕ} (hp : p < 2 ^ 62) :
    ∀ (m : ℕ) (s : St), m < 64 → Inv s.M → (∀ a < L.length, rd s.M (bX + a) = Xi a) →
      rd s.M rPp = toWord p → rd s.M rHc = toWord m → WalkSt i L d0 sib p m s.M →
      WalkSt i L d0 sib p 0 (iterL (semXIR (tp c π L) (nodeBody bX pL i)) rHc m s).M ∧
      Inv (iterL (semXIR (tp c π L) (nodeBody bX pL i)) rHc m s).M ∧
      (∀ x, regs ≤ x → rd (iterL (semXIR (tp c π L) (nodeBody bX pL i)) rHc m s).M x = rd s.M x) ∧
      rd (iterL (semXIR (tp c π L) (nodeBody bX pL i)) rHc m s).M rPp = rd s.M rPp ∧
      rd (iterL (semXIR (tp c π L) (nodeBody bX pL i)) rHc m s).M rWA = rd s.M rWA
  | 0, s, _, hM, _, _, _, hW => ⟨hW, hM, fun _ _ => rfl, rfl, rfl⟩
  | m + 1, s, hm, hM, hXs, hP, hH, hW => by
    set I := tp c π L
    have h1 := nodeWalk hbX hbX2 hpL hD hX s hM hXs (h := m) hp (by omega) hP hH hW
    have hM1 := inv_sem I (wf_nodeBody (bX := bX) (pL := pL) (i := i)) hM
    have hH1 := hframeK I (nodeBody bX pL i) s loK_nodeBody
    have fr : ∀ r, (r = rPp ∨ r = rWA ∨ r = rHc) → rd (semXIR I (nodeBody bX pL i) s).M r = rd s.M r :=
      fun r hr => frame I _ s (wf_nodeBody (bX := bX) (pL := pL) (i := i)) hM r
        (by rcases hr with rfl | rfl | rfl <;> decide) (nodeBody_nw hr)
    have hM' : Inv (decS rHc (semXIR I (nodeBody bX pL i) s)).M := inv_decS hM1 (by decide)
    have hHc : rd (decS rHc (semXIR I (nodeBody bX pL i) s)).M rHc = toWord m :=
      rd_decS_self hM1 (by decide) (by rw [fr _ (.inr (.inr rfl)), hH]) (by omega)
    have dk : ∀ r, r ≠ rHc → rd (decS rHc (semXIR I (nodeBody bX pL i) s)).M r =
        rd (semXIR I (nodeBody bX pL i) s).M r := fun r hr => rd_decS (Ne.symm hr) _
    have hW' : WalkSt i L d0 sib p m (decS rHc (semXIR I (nodeBody bX pL i) s)).M := by
      unfold WalkSt at h1 ⊢
      rw [dk rOk (by decide), dk rQ0 (by decide), dk rQ1 (by decide), dk rQ2 (by decide),
        dk rQ3 (by decide)]
      exact h1
    have hHp : ∀ x, regs ≤ x → rd (decS rHc (semXIR I (nodeBody bX pL i) s)).M x = rd s.M x :=
      fun x hx => (dk x (by simp only [rHc, regs] at *; omega)).trans (hH1 x hx)
    obtain ⟨a1, a2, a3, a4, a5⟩ := nodeLoop hD hX hp m _ (by omega) hM'
      (fun a ha => by rw [hHp _ (by simp only [regs] at hbX ⊢; omega), hXs a ha])
      (by rw [dk _ (by decide), fr _ (.inl rfl), hP]) hHc hW'
    simp only [iterL]
    refine ⟨a1, a2, fun x hx => (a3 x hx).trans (hHp x hx), ?_, ?_⟩
    · rw [a4, dk _ (by decide), fr _ (.inl rfl)]
    · rw [a5, dk _ (by decide), fr _ (.inr (.inl rfl))]

/-- **The leaf**: after `colIR`, `rXq` and `rQe` are such that the copy stores the words of the
reading `colL` makes under `d₀` (`colWord`, zeros for `none`). -/
theorem colIR_sem (hD : Dom4 pL c π L) {Xi : ℕ → Word} (hX : Sorted4 pL (tp c π L) L Xi) (s : St)
    (hM : Inv s.M) (hXs : ∀ a < L.length, rd s.M (bX + a) = Xi a) {d0 : Digest} {sib p : ℕ}
    (hW : WalkSt i L d0 sib p 0 s.M) :
    ∃ ql < 2 ^ 64, rd (semXIR (tp c π L) (colIR bX pL i) s).M rQe = toWord ql ∧
      ∀ w, cpW (tp c π L) (rd (semXIR (tp c π L) (colIR bX pL i) s).M rXq) ql w =
        colWord (colL (frEnc i) L d0 sib p) w := by
  set I := tp c π L with hI
  have hs := hM.1
  simp only [regs] at hs
  rw [colIR, semXIR_seq]
  have hM0 := inv_sem I (P := .blk [.const rQe 0]) (by simp +decide only [WF, Prim.dst, rQe]) hM
  have hQ0 : rd (semXIR I (.blk [.const rQe 0]) s).M rQe = toWord 0 := by
    simp only [semXIR, runPrims, List.foldl, Prim.run]
    exact rd_set_self (by simp only [rQe]; omega)
  have fr0 : ∀ r, r ≠ rQe → rd (semXIR I (.blk [.const rQe 0]) s).M r = rd s.M r := fun r hr => by
    simp only [semXIR, runPrims, List.foldl, Prim.run]; exact rd_set_ne (Ne.symm hr)
  have hXs0 : ∀ a < L.length, rd (semXIR I (.blk [.const rQe 0]) s).M (bX + a) = Xi a :=
    fun a ha => by rw [fr0 _ (by simp only [rQe, regs] at hbX ⊢; omega), hXs a ha]
  have hW0 : WalkSt i L d0 sib p 0 (semXIR I (.blk [.const rQe 0]) s).M := by
    unfold WalkSt at hW ⊢
    rw [fr0 rOk (by decide), fr0 rQ0 (by decide), fr0 rQ1 (by decide), fr0 rQ2 (by decide),
      fr0 rQ3 (by decide)]
    exact hW
  generalize semXIR I (.blk [.const rQe 0]) s = s0 at hM0 hQ0 hXs0 hW0
  have hs0 := hM0.1
  simp only [regs] at hs0
  rw [semXIR_ite]
  rcases hW0 with ⟨hOk, d, hT, hc⟩ | ⟨hOk, hc⟩
  · rw [hOk, if_neg (by decide), semXIR_seq, hc, colL_zero]
    obtain ⟨lk1, lk2, lk3, lk4, lk5⟩ := look_spec hbX hbX2 hpL hD hX s0 hM0 hXs0 d hT
    have hQ1 := (lk5 rQe (by decide) (by decide)).trans hQ0
    generalize semXIR I (lookIR4 bX pL) s0 = s1 at lk1 lk2 lk3 lk4 hQ1
    have hs1 := lk4.1
    simp only [regs] at hs1
    rw [semXIR_ite]
    cases hk : FR.Snd.ansIdx L d with
    | none =>
      rw [lk2 hk, if_pos rfl, pre_none hk]
      refine ⟨0, by norm_num, hQ1, fun w => ?_⟩
      rw [cpW_zero]; rfl
    | some k =>
      obtain ⟨b, hb, hlo, hfd, hxb⟩ := lk1 k hk
      obtain ⟨hkL, hpre⟩ := pre_some hk
      rw [hfd, if_neg (by decide), hpre, Option.bind_some]
      have hxl := hD.posE_lt hkL
      have hsm := hD.small
      have hq := hD.hq _ (List.getElem_mem hkL)
      obtain ⟨g1, g2, g3⟩ := getIR_sem hbX hbX2 hpL I s1 lk4 (b := b) (x := posE4 pL L k) (by omega) (by omega) hlo
        (by rw [lk3 _ (by simp only [regs] at hbX ⊢; omega), hXs0 b hb, hxb])
      have hQ2 : rd (semXIR I (getIR bX) s1).M rQe = toWord 0 := by
        rw [frame I _ s1 (wf_getIR (bX := bX)) lk4 rQe (by decide) (by
          simp +decide [getIR, Writes, Prim.dst, rK2, rAd2, rXq, rQn, rTA, rV2, rQe, or_false]), hQ1]
      have hM2 := inv_sem I (wf_getIR (bX := bX)) lk4
      rw [semXIR_seq]
      generalize semXIR I (getIR bX) s1 = s2 at g1 g2 g3 hQ2 hM2
      have hB := colChk_sem I i s2 hM2
      rw [g2, g3, colFlag hD hkL] at hB
      have fC : ∀ r, r = rQe ∨ r = rXq ∨ r = rQn →
          rd (semXIR I (.blk (colChkPs i)) s2).M r = rd s2.M r :=
        fun r hr => frame I _ s2 (wf_colChk (i := i)) hM2 r (by rcases hr with rfl | rfl | rfl <;> decide)
          (by rcases hr with rfl | rfl | rfl <;>
            simp +decide only [colChkPs, Writes, Prim.dst, rK2, rB, rMk, rQe, rXq, rQn,
              List.mem_cons, List.mem_nil_iff, exists_eq_or_imp, exists_eq_left, or_false])
      have hM3 := inv_sem I (wf_colChk (i := i)) hM2
      rw [semXIR_seq]
      generalize semXIR I (.blk (colChkPs i)) s2 = s3 at hB fC hM3
      have hs3 := hM3.1
      simp only [regs] at hs3
      rw [semXIR_ite, hB]
      by_cases hC : L[k].1.data.toList.take 8 = tagCol i
      · rw [decide_eq_true hC, if_neg bW_ne_zero]
        refine ⟨L[k].1.size, hq, ?_, fun w => ?_⟩
        · simp only [semXIR, runPrims, List.foldl, Prim.run]
          rw [rd_set_self (by simp only [rQe]; omega), fC _ (.inr (.inr rfl)), g2, tp_len hD hkL,
            or_self_eval]
        · have e : rd (semXIR I (.blk [.op .or rQe rQn rQn]) s3).M rXq = toWord (posE4 pL L k) := by
            simp only [semXIR, runPrims, List.foldl, Prim.run]
            rw [rd_set_ne (by decide), fC _ (.inr (.inl rfl)), g1]
          rw [e, ← cpW_entry hD hkL w, if_pos hC]
      · rw [decide_eq_false hC, if_pos bW_false]
        refine ⟨0, by norm_num, by
          show rd (runPrims [] s3.M) rQe = _
          rw [runPrims_nil, fC _ (.inl rfl), hQ2], fun w => ?_⟩
        rw [cpW_zero]
        show (0 : Word) = colWord (parseCol i L[k].1) w
        simp only [parseCol, if_neg hC, colWord]
  · rw [hOk, if_pos rfl, hc]
    refine ⟨0, by norm_num, by
      show rd (runPrims [] s0.M) rQe = _
      rw [runPrims_nil, hQ0], fun w => ?_⟩
    rw [cpW_zero]; rfl

/-- **One position**: the column words of position `p` at `a … a + 127`; `rPp := p + 1`,
`rWA := a + 128`; every other heap cell kept. -/
theorem posBody_sem (hD : Dom4 pL c π L) {Xi : ℕ → Word} (hX : Sorted4 pL (tp c π L) L Xi) (s : St)
    (hM : Inv s.M) (hXs : ∀ a < L.length, rd s.M (bX + a) = Xi a) {cw nw ncap : ℕ}
    {cap : ℕ → Digest} (hcw : cw + 4 * ncap < 2 ^ 62)
    (hcap : ∀ e < ncap, ∀ m < 4,
      (tp c π L).getD (cw + 4 * e + m) 0 = (packBytes (cap e).toList).getD m 0)
    (hnw : nw < 2 ^ 60) {sib p a : ℕ}
    (hsib : sib < 64) (hp : p < 2 ^ 62) (he : p / 2 ^ sib < ncap) (hP : rd s.M rPp = toWord p)
    (hA : rd s.M rWA = toWord a) (ha : regs ≤ a) (ha2 : a + nw + 2 < 2 ^ 64)
    (hsz : a + nw ≤ s.M.size) :
    (∀ w < nw, rd (semXIR (tp c π L) (posBody4 bX pL i cw nw sib) s).M (a + w) =
      colWord (colL (frEnc i) L (cap (p / 2 ^ sib)) sib p) w) ∧
    (∀ y, regs ≤ y → (y < a ∨ a + nw ≤ y) →
      rd (semXIR (tp c π L) (posBody4 bX pL i cw nw sib) s).M y = rd s.M y) ∧
    Inv (semXIR (tp c π L) (posBody4 bX pL i cw nw sib) s).M ∧
    rd (semXIR (tp c π L) (posBody4 bX pL i cw nw sib) s).M rWA = toWord (a + nw) ∧
    rd (semXIR (tp c π L) (posBody4 bX pL i cw nw sib) s).M rPp = toWord (p + 1) := by
  set I := tp c π L with hI
  set d0 := cap (p / 2 ^ sib)
  have hs := hM.1
  simp only [regs] at hs
  -- the cap entry
  have wf1 : WF (.seq (.blk (capPs cw sib)) ld4IR) := ⟨by simp +decide only [capPs, WF, Prim.dst,
    rK2, rB, rTA, List.mem_cons, List.mem_nil_iff, forall_eq_or_imp, forall_eq, or_false, and_true],
    wf_ld4IR⟩
  have lo1 : Lo (.seq (.blk (capPs cw sib)) ld4IR) := ⟨by simp +decide only [capPs, Lo, Prim.dst,
    regs, rK2, rB, rTA, List.mem_cons, List.mem_nil_iff, forall_eq_or_imp, forall_eq, or_false,
    and_true], lo_ld4IR⟩
  have q1 := capLd_sem s hM hcw hcap hsib hp he hP
  have hH1 := hframe I _ s lo1
  have f1 : ∀ r, r = rPp ∨ r = rWA → rd (semXIR I (.seq (.blk (capPs cw sib)) ld4IR) s).M r =
      rd s.M r := fun r hr => frame I _ s wf1 hM r (by rcases hr with rfl | rfl <;> decide)
    (by rcases hr with rfl | rfl <;>
      simp +decide only [capPs, ld4IR, Writes, Prim.dst, rK2, rB, rTA, rQ0, rQ1, rQ2, rQ3, rPp, rWA,
        List.mem_cons, List.mem_nil_iff, exists_eq_or_imp, exists_eq_left, or_false])
  have hM1 := inv_sem I wf1 hM
  have hsz1 := size_sem I (.seq (.blk (capPs cw sib)) ld4IR) s
  rw [posBody4, semXIR_seq]
  generalize semXIR I (.seq (.blk (capPs cw sib)) ld4IR) s = s1 at q1 hH1 f1 hM1 hsz1
  -- `rOk := 1`, the height count
  have wf2 : WF (.blk [.const rOk 1, .const rNH (toWord sib)]) := by simp +decide only [WF,
    Prim.dst, rOk, rNH, List.mem_cons, List.mem_nil_iff, forall_eq_or_imp, forall_eq, or_false,
    and_true]
  have hs1 := hM1.1
  simp only [regs] at hs1
  have r2 : ∀ r, r ≠ rOk → r ≠ rNH →
      rd (semXIR I (.blk [.const rOk 1, .const rNH (toWord sib)]) s1).M r = rd s1.M r :=
    fun r h1 h2 => by
      simp only [semXIR, runPrims, List.foldl, Prim.run]
      rw [rd_set_ne (Ne.symm h2), rd_set_ne (Ne.symm h1)]
  have o2 : rd (semXIR I (.blk [.const rOk 1, .const rNH (toWord sib)]) s1).M rOk = 1 ∧
      rd (semXIR I (.blk [.const rOk 1, .const rNH (toWord sib)]) s1).M rNH = toWord sib := by
    simp only [semXIR, runPrims, List.foldl, Prim.run]
    refine ⟨?_, ?_⟩ <;>
    simp (disch := first | decide | (simp only [size_set, rOk, rNH]; omega)) only
      [rd_set_self, rd_set_ne]
  have hM2 := inv_sem I wf2 hM1
  have hsz2 := size_sem I (.blk [.const rOk 1, .const rNH (toWord sib)]) s1
  rw [semXIR_seq]
  generalize semXIR I (.blk [.const rOk 1, .const rNH (toWord sib)]) s1 = s2 at r2 o2 hM2 hsz2
  have hW2 : WalkSt i L d0 sib p sib s2.M := by
    refine .inl ⟨o2.1, d0, ?_, rfl⟩
    rw [r2 rQ0 (by decide) (by decide), r2 rQ1 (by decide) (by decide),
      r2 rQ2 (by decide) (by decide), r2 rQ3 (by decide) (by decide)]
    exact q1
  have hH2 : ∀ y, regs ≤ y → rd s2.M y = rd s.M y := fun y hy => by
    rw [r2 y (by simp only [rOk, regs] at *; omega) (by simp only [rNH, regs] at *; omega),
      hH1 y hy]
  -- the height loop
  have hE : ∀ i, i ≠ rHc → i ≠ cTmp → rd (entryK rHc rNH (toWord sib) s2.M) i = rd s2.M i :=
    fun i h1 h2 => entryK_frame _ (Ne.symm h1) (Ne.symm h2)
  have hcnt : rd (entryK rHc rNH (toWord sib) s2.M) rHc = toWord sib :=
    entryK_count hM2 (by decide) (by decide) (by decide) o2.2
  have hME := inv_entryK (c := rHc) (n := rNH) (K := toWord sib) hM2 (by decide)
  have e : semXIR I (.loopK rHc rNH (toWord sib) (nodeBody bX pL i)) s2 =
      iterL (semXIR I (nodeBody bX pL i)) rHc sib ⟨entryK rHc rNH (toWord sib) s2.M, s2.o⟩ := by
    simp only [semXIR, hcnt, toNat_toWord (show sib < 2 ^ 64 by omega)]
  have hyE : ∀ y, regs ≤ y → y ≠ rHc ∧ y ≠ cTmp := fun y hy => by
    simp only [rHc, cTmp, regs] at *; omega
  have hWE : WalkSt i L d0 sib p sib (entryK rHc rNH (toWord sib) s2.M) := by
    unfold WalkSt at hW2 ⊢
    rw [hE rOk (by decide) (by decide), hE rQ0 (by decide) (by decide),
      hE rQ1 (by decide) (by decide), hE rQ2 (by decide) (by decide),
      hE rQ3 (by decide) (by decide)]
    exact hW2
  have hxr : ∀ a', regs ≤ bX + a' := fun a' => by simp only [regs] at hbX ⊢; omega
  have hXE : ∀ a' < L.length, rd (entryK rHc rNH (toWord sib) s2.M) (bX + a') = Xi a' :=
    fun a' ha' => by
      rw [hE _ (hyE _ (hxr a')).1 (hyE _ (hxr a')).2, hH2 _ (hxr a'), hXs a' ha']
  have hPE : rd (entryK rHc rNH (toWord sib) s2.M) rPp = toWord p := by
    rw [hE _ (by decide) (by decide), r2 _ (by decide) (by decide), f1 _ (.inl rfl), hP]
  obtain ⟨n1, n2, n3, n4, n5⟩ := nodeLoop hbX hbX2 hpL hD hX hp sib ⟨entryK rHc rNH (toWord sib) s2.M, s2.o⟩
    hsib hME hXE hPE hcnt hWE
  have hH3 : ∀ y, regs ≤ y →
      rd (iterL (semXIR I (nodeBody bX pL i)) rHc sib ⟨entryK rHc rNH (toWord sib) s2.M, s2.o⟩).M y =
        rd s.M y := fun y hy => by
    rw [n3 y hy]
    show rd (entryK rHc rNH (toWord sib) s2.M) y = _
    rw [hE y (hyE y hy).1 (hyE y hy).2, hH2 y hy]
  have hP3 : rd (iterL (semXIR I (nodeBody bX pL i)) rHc sib
      ⟨entryK rHc rNH (toWord sib) s2.M, s2.o⟩).M rPp = toWord p := by
    rw [n4]
    show rd (entryK rHc rNH (toWord sib) s2.M) rPp = _
    rw [hE _ (by decide) (by decide), r2 _ (by decide) (by decide), f1 _ (.inl rfl), hP]
  have hA3 : rd (iterL (semXIR I (nodeBody bX pL i)) rHc sib
      ⟨entryK rHc rNH (toWord sib) s2.M, s2.o⟩).M rWA = toWord a := by
    rw [n5]
    show rd (entryK rHc rNH (toWord sib) s2.M) rWA = _
    rw [hE _ (by decide) (by decide), r2 _ (by decide) (by decide), f1 _ (.inr rfl), hA]
  have hsz3 : (iterL (semXIR I (nodeBody bX pL i)) rHc sib
      ⟨entryK rHc rNH (toWord sib) s2.M, s2.o⟩).M.size = s.M.size := by
    rw [size_iterL (fun s' => size_sem I (nodeBody bX pL i) s')]
    show (entryK rHc rNH (toWord sib) s2.M).size = _
    rw [size_entryK, hsz2, hsz1]
  rw [semXIR_seq, e]
  generalize iterL (semXIR I (nodeBody bX pL i)) rHc sib ⟨entryK rHc rNH (toWord sib) s2.M, s2.o⟩ = s3
    at n1 n2 hH3 hP3 hA3 hsz3
  -- the leaf
  obtain ⟨ql, hql, c1, c2⟩ := colIR_sem hbX hbX2 hpL hD hX s3 n2 (fun a' ha' => by
    rw [hH3 _ (by simp only [regs] at hbX ⊢; omega), hXs a' ha']) n1
  have hH4 := hframeK I (colIR bX pL i) s3 loK_colIR
  have hP4 : rd (semXIR I (colIR bX pL i) s3).M rPp = toWord p := by
    rw [frame I _ s3 (wf_colIR (bX := bX) (pL := pL) (i := i)) n2 rPp (by decide) (colIR_nw (.inl rfl)), hP3]
  have hA4 : rd (semXIR I (colIR bX pL i) s3).M rWA = toWord a := by
    rw [frame I _ s3 (wf_colIR (bX := bX) (pL := pL) (i := i)) n2 rWA (by decide) (colIR_nw (.inr rfl)), hA3]
  have hM4 := inv_sem I (wf_colIR (bX := bX) (pL := pL) (i := i)) n2
  have hsz4 := size_sem I (colIR bX pL i) s3
  rw [semXIR_seq]
  generalize semXIR I (colIR bX pL i) s3 = s4 at c1 c2 hH4 hP4 hA4 hM4 hsz4
  -- the copy
  obtain ⟨k1, k2, k3, k4, k5⟩ := copyIR_sem I s4 hM4 hql ha ha2 hnw (by omega) rfl c1 hA4
  rw [semXIR_seq]
  generalize semXIR I (copyIR nw) s4 = s5 at k1 k2 k3 k4 k5
  have hs5 := k3.1
  simp only [regs] at hs5
  have hc5 : rd s5.M cOne = 1 := k3.2 0 (by decide)
  have wf6 : WF (.blk [.op .add rPp rPp cOne]) := by simp +decide only [WF, Prim.dst, rPp]
  have r6 : ∀ r, r ≠ rPp → rd (semXIR I (.blk [.op .add rPp rPp cOne]) s5).M r = rd s5.M r :=
    fun r hr => by
      simp only [semXIR, runPrims, List.foldl, Prim.run]; exact rd_set_ne (Ne.symm hr)
  refine ⟨fun w hw => ?_, fun y hy1 hy2 => ?_, inv_sem I wf6 k3, ?_, ?_⟩
  · rw [r6 _ (by simp only [rPp, regs] at *; omega), k1 w hw, c2]
  · rw [r6 _ (by simp only [rPp, regs] at *; omega), k2 y hy1 hy2, hH4 y hy1, hH3 y hy1]
  · rw [r6 _ (by decide), k4]
  · simp only [semXIR, runPrims, List.foldl, Prim.run]
    rw [rd_set_self (by simp only [rPp]; omega), k5, hP4, hc5, add_one_toWord]

/-- **The position loop**: `m` positions from `j` fill their columns' cells. -/
theorem posLoop4 (hD : Dom4 pL c π L) {Xi : ℕ → Word} (hX : Sorted4 pL (tp c π L) L Xi) {cw nw ncap sb : ℕ}
    {cap : ℕ → Digest} (hcw : cw + 4 * ncap < 2 ^ 62)
    (hcap : ∀ e < ncap, ∀ m < 4,
      (tp c π L).getD (cw + 4 * e + m) 0 = (packBytes (cap e).toList).getD m 0)
    (hnw : nw < 2 ^ 60) {sib np : ℕ}
    (hsib : sib < 64) (hnp : np ≤ 2 ^ 20) (hst : sb + nw * np ≤ bX) (hsb : regs ≤ sb)
    (hcapn : np ≤ ncap * 2 ^ sib) :
    ∀ (m j : ℕ) (s : St), j + m ≤ np → Inv s.M → bX ≤ s.M.size →
      (∀ a < L.length, rd s.M (bX + a) = Xi a) → rd s.M rPp = toWord j →
      rd s.M rWA = toWord (sb + nw * j) →
      (∀ q, j ≤ q → q < j + m → ∀ w < nw,
        rd (iterL (semXIR (tp c π L) (posBody4 bX pL i cw nw sib)) rCp m s).M (sb + nw * q + w) =
          colWord (colL (frEnc i) L (cap (q / 2 ^ sib)) sib q) w) ∧
      (∀ y, regs ≤ y → (y < sb + nw * j ∨ sb + nw * (j + m) ≤ y) →
        rd (iterL (semXIR (tp c π L) (posBody4 bX pL i cw nw sib)) rCp m s).M y = rd s.M y) ∧
      Inv (iterL (semXIR (tp c π L) (posBody4 bX pL i cw nw sib)) rCp m s).M
  | 0, j, s, _, hM, _, _, _, _ => ⟨fun q h1 h2 => by omega, fun _ _ _ => rfl, hM⟩
  | m + 1, j, s, hjm, hM, hsz, hXs, hP, hA => by
    set I := tp c π L
    have hdiv : j / 2 ^ sib < ncap := by
      rw [Nat.div_lt_iff_lt_mul (by positivity)]; omega
    have e1 : nw * (j + 1) = nw * j + nw := Nat.mul_succ nw j
    have e2 : nw * (j + 1) ≤ nw * np := Nat.mul_le_mul_left nw (by omega)
    have e3 : nw * (j + 1 + m) = nw * (j + (m + 1)) := by rw [show j + 1 + m = j + (m + 1) by omega]
    have e4 : nw * (j + 1) ≤ nw * (j + (m + 1)) := Nat.mul_le_mul_left nw (by omega)
    obtain ⟨b1, b2, b3, b4, b5⟩ := posBody_sem hbX hbX2 hpL hD hX s hM hXs hcw hcap hnw (sib := sib) (p := j)
      (a := sb + nw * j) hsib (by omega) hdiv hP hA (by omega) (by omega) (by omega)
    have hM' : Inv (decS rCp (semXIR I (posBody4 bX pL i cw nw sib) s)).M := inv_decS b3 (by decide)
    have dk : ∀ r, r ≠ rCp → rd (decS rCp (semXIR I (posBody4 bX pL i cw nw sib) s)).M r =
        rd (semXIR I (posBody4 bX pL i cw nw sib) s).M r := fun r hr => rd_decS (Ne.symm hr) _
    have hy : ∀ y, regs ≤ y → y ≠ rCp := fun y hy => by simp only [rCp, regs] at *; omega
    have hsz' : bX ≤ (decS rCp (semXIR I (posBody4 bX pL i cw nw sib) s)).M.size := by
      rw [size_decS, size_sem]; exact hsz
    obtain ⟨d1, d2, d3⟩ := posLoop4 hD hX hcw hcap hnw hsib hnp hst hsb hcapn m (j + 1) _ (by omega)
      hM' hsz'
      (fun a ha => by
        rw [dk _ (hy _ (by simp only [regs] at hbX ⊢; omega)), b2 _ (by simp only [regs] at hbX ⊢; omega)
          (.inr (by omega)), hXs a ha])
      (by rw [dk _ (by decide), b5])
      (by rw [dk _ (by decide), b4, e1, Nat.add_assoc])
    rw [e3] at d2
    simp only [iterL]
    refine ⟨fun q h1 h2 w hw => ?_, fun y hy1 hy2 => ?_, d3⟩
    · by_cases hq : q = j
      · subst hq
        rw [d2 _ (by omega) (.inl (by omega)), dk _ (hy _ (by omega)), b1 w hw]
      · exact d1 q (by omega) (by omega) w hw
    · rw [d2 _ hy1 (by omega), dk _ (hy _ hy1), b2 _ hy1 (by omega)]

/-- **The ladder read's semantics**: on a sorted index, `readIR sib np` stores at
`colBase + 128 q + w` word `w` of the column `colL (frEnc i)` reads under cap entry `q / 2^sib`
at height `sib`, for every position `q < np`; it keeps the index. -/
theorem readIR4_sem (hD : Dom4 pL c π L) {Xi : ℕ → Word} (hX : Sorted4 pL (tp c π L) L Xi) (s : St)
    (hM : Inv s.M) (hXs : ∀ a < L.length, rd s.M (bX + a) = Xi a) {cw nw ncap sb : ℕ}
    {cap : ℕ → Digest} (hcw : cw + 4 * ncap < 2 ^ 62)
    (hcap : ∀ e < ncap, ∀ m < 4,
      (tp c π L).getD (cw + 4 * e + m) 0 = (packBytes (cap e).toList).getD m 0)
    (hnw : nw < 2 ^ 60) {sib np : ℕ}
    (hsib : sib < 64) (hnp : np ≤ 2 ^ 20) (hst : sb + nw * np ≤ bX) (hsb : regs ≤ sb)
    (hcapn : np ≤ ncap * 2 ^ sib) (hsz : bX ≤ s.M.size) :
    (∀ q < np, ∀ w < nw, rd (semXIR (tp c π L) (readIR4 bX pL i cw sb nw sib np) s).M (sb + nw * q + w) =
      colWord (colL (frEnc i) L (cap (q / 2 ^ sib)) sib q) w) ∧
    (∀ a < L.length, rd (semXIR (tp c π L) (readIR4 bX pL i cw sb nw sib np) s).M (bX + a) = Xi a) ∧
    Inv (semXIR (tp c π L) (readIR4 bX pL i cw sb nw sib np) s).M := by
  set I := tp c π L
  have hs := hM.1
  simp only [regs] at hs
  have wf0 : WF (.blk [.const rPp 0, .const rWA (toWord sb), .const rNp (toWord np)]) := by
    simp +decide only [WF, Prim.dst, rPp, rWA, rNp, List.mem_cons, List.mem_nil_iff,
      forall_eq_or_imp, forall_eq, or_false, and_true]
  have r0 : rd (semXIR I (.blk [.const rPp 0, .const rWA (toWord sb),
        .const rNp (toWord np)]) s).M rPp = toWord 0 ∧
      rd (semXIR I (.blk [.const rPp 0, .const rWA (toWord sb),
        .const rNp (toWord np)]) s).M rWA = toWord (sb + nw * 0) ∧
      rd (semXIR I (.blk [.const rPp 0, .const rWA (toWord sb),
        .const rNp (toWord np)]) s).M rNp = toWord np := by
    simp only [semXIR, runPrims, List.foldl, Prim.run]
    refine ⟨?_, ?_, ?_⟩ <;>
    simp (disch := first | decide | (simp only [size_set, rPp, rWA, rNp]; omega)) only
      [rd_set_self, rd_set_ne]
    · rfl
    · rw [Nat.mul_zero, Nat.add_zero]
  have hH0 := hframe I (.blk [.const rPp 0, .const rWA (toWord sb), .const rNp (toWord np)]) s
    (by simp +decide only [Lo, Prim.dst, regs, rPp, rWA, rNp, List.mem_cons, List.mem_nil_iff,
      forall_eq_or_imp, forall_eq, or_false, and_true])
  have hM0 := inv_sem I wf0 hM
  have hsz0 := size_sem I (.blk [.const rPp 0, .const rWA (toWord sb),
    .const rNp (toWord np)]) s
  rw [readIR4, semXIR_seq]
  generalize semXIR I (.blk [.const rPp 0, .const rWA (toWord sb),
    .const rNp (toWord np)]) s = s0 at r0 hH0 hM0 hsz0
  obtain ⟨p0, a0, n0⟩ := r0
  have hE : ∀ i, i ≠ rCp → i ≠ cTmp → rd (entryK rCp rNp (toWord np) s0.M) i = rd s0.M i :=
    fun i h1 h2 => entryK_frame _ (Ne.symm h1) (Ne.symm h2)
  have hcnt : rd (entryK rCp rNp (toWord np) s0.M) rCp = toWord np :=
    entryK_count hM0 (by decide) (by decide) (by decide) n0
  have hME := inv_entryK (c := rCp) (n := rNp) (K := toWord np) hM0 (by decide)
  have e : semXIR I (.loopK rCp rNp (toWord np) (posBody4 bX pL i cw nw sib)) s0 =
      iterL (semXIR I (posBody4 bX pL i cw nw sib)) rCp np ⟨entryK rCp rNp (toWord np) s0.M, s0.o⟩ := by
    simp only [semXIR, hcnt, toNat_toWord (show np < 2 ^ 64 by omega)]
  rw [e]
  have hy : ∀ y, regs ≤ y → y ≠ rCp ∧ y ≠ cTmp := fun y hy => by
    simp only [rCp, cTmp, regs] at *; omega
  have hHE : ∀ y, regs ≤ y → rd (entryK rCp rNp (toWord np) s0.M) y = rd s.M y := fun y hy' => by
    rw [hE y (hy y hy').1 (hy y hy').2, hH0 y hy']
  have e0 : nw * (0 + np) = nw * np := by rw [Nat.zero_add]
  obtain ⟨d1, d2, d3⟩ := posLoop4 hbX hbX2 hpL hD hX hcw hcap hnw hsib hnp hst hsb hcapn np 0
    ⟨entryK rCp rNp (toWord np) s0.M, s0.o⟩
    (by omega) hME (by simp only [size_entryK]; omega)
    (fun a ha => by
      show rd (entryK rCp rNp (toWord np) s0.M) (bX + a) = _
      rw [hHE _ (by simp only [regs] at hbX ⊢; omega), hXs a ha])
    (by show rd (entryK rCp rNp (toWord np) s0.M) rPp = _; rw [hE _ (by decide) (by decide), p0])
    (by show rd (entryK rCp rNp (toWord np) s0.M) rWA = _; rw [hE _ (by decide) (by decide), a0])
  refine ⟨fun q hq w hw => d1 q (by omega) (by omega) w hw, fun a ha => ?_, d3⟩
  rw [d2 _ (by simp only [regs] at hbX ⊢; omega) (.inr (by rw [e0]; omega))]
  show rd (entryK rCp rNp (toWord np) s0.M) (bX + a) = _
  rw [hHE _ (by simp only [regs] at hbX ⊢; omega), hXs a ha]

/-- **The ladder read's frame** (`posLoop`'s): `readIR4` keeps every heap cell outside
`[sb, sb + nw·np)`. `readIR4_sem` states the store and the index. -/
theorem readIR4_frame (hD : Dom4 pL c π L) {Xi : ℕ → Word} (hX : Sorted4 pL (tp c π L) L Xi) (s : St)
    (hM : Inv s.M) (hXs : ∀ a < L.length, rd s.M (bX + a) = Xi a) {cw nw ncap sb : ℕ}
    {cap : ℕ → Digest} (hcw : cw + 4 * ncap < 2 ^ 62)
    (hcap : ∀ e < ncap, ∀ m < 4,
      (tp c π L).getD (cw + 4 * e + m) 0 = (packBytes (cap e).toList).getD m 0)
    (hnw : nw < 2 ^ 60) {sib np : ℕ}
    (hsib : sib < 64) (hnp : np ≤ 2 ^ 20) (hst : sb + nw * np ≤ bX) (hsb : regs ≤ sb)
    (hcapn : np ≤ ncap * 2 ^ sib) (hsz : bX ≤ s.M.size) :
    ∀ y, regs ≤ y → (y < sb ∨ sb + nw * np ≤ y) →
      rd (semXIR (tp c π L) (readIR4 bX pL i cw sb nw sib np) s).M y = rd s.M y := by
  set I := tp c π L
  have hs := hM.1
  simp only [regs] at hs
  have wf0 : WF (.blk [.const rPp 0, .const rWA (toWord sb), .const rNp (toWord np)]) := by
    simp +decide only [WF, Prim.dst, rPp, rWA, rNp, List.mem_cons, List.mem_nil_iff,
      forall_eq_or_imp, forall_eq, or_false, and_true]
  have r0 : rd (semXIR I (.blk [.const rPp 0, .const rWA (toWord sb),
        .const rNp (toWord np)]) s).M rPp = toWord 0 ∧
      rd (semXIR I (.blk [.const rPp 0, .const rWA (toWord sb),
        .const rNp (toWord np)]) s).M rWA = toWord (sb + nw * 0) ∧
      rd (semXIR I (.blk [.const rPp 0, .const rWA (toWord sb),
        .const rNp (toWord np)]) s).M rNp = toWord np := by
    simp only [semXIR, runPrims, List.foldl, Prim.run]
    refine ⟨?_, ?_, ?_⟩ <;>
    simp (disch := first | decide | (simp only [size_set, rPp, rWA, rNp]; omega)) only
      [rd_set_self, rd_set_ne]
    · rfl
    · rw [Nat.mul_zero, Nat.add_zero]
  have hH0 := hframe I (.blk [.const rPp 0, .const rWA (toWord sb), .const rNp (toWord np)]) s
    (by simp +decide only [Lo, Prim.dst, regs, rPp, rWA, rNp, List.mem_cons, List.mem_nil_iff,
      forall_eq_or_imp, forall_eq, or_false, and_true])
  have hM0 := inv_sem I wf0 hM
  have hsz0 := size_sem I (.blk [.const rPp 0, .const rWA (toWord sb),
    .const rNp (toWord np)]) s
  rw [readIR4, semXIR_seq]
  generalize semXIR I (.blk [.const rPp 0, .const rWA (toWord sb),
    .const rNp (toWord np)]) s = s0 at r0 hH0 hM0 hsz0
  obtain ⟨p0, a0, n0⟩ := r0
  have hE : ∀ i, i ≠ rCp → i ≠ cTmp → rd (entryK rCp rNp (toWord np) s0.M) i = rd s0.M i :=
    fun i h1 h2 => entryK_frame _ (Ne.symm h1) (Ne.symm h2)
  have hcnt : rd (entryK rCp rNp (toWord np) s0.M) rCp = toWord np :=
    entryK_count hM0 (by decide) (by decide) (by decide) n0
  have hME := inv_entryK (c := rCp) (n := rNp) (K := toWord np) hM0 (by decide)
  have e : semXIR I (.loopK rCp rNp (toWord np) (posBody4 bX pL i cw nw sib)) s0 =
      iterL (semXIR I (posBody4 bX pL i cw nw sib)) rCp np ⟨entryK rCp rNp (toWord np) s0.M, s0.o⟩ := by
    simp only [semXIR, hcnt, toNat_toWord (show np < 2 ^ 64 by omega)]
  rw [e]
  have hy : ∀ y, regs ≤ y → y ≠ rCp ∧ y ≠ cTmp := fun y hy => by
    simp only [rCp, cTmp, regs] at *; omega
  have hHE : ∀ y, regs ≤ y → rd (entryK rCp rNp (toWord np) s0.M) y = rd s.M y := fun y hy' => by
    rw [hE y (hy y hy').1 (hy y hy').2, hH0 y hy']
  have e0 : nw * (0 + np) = nw * np := by rw [Nat.zero_add]
  obtain ⟨d1, d2, d3⟩ := posLoop4 hbX hbX2 hpL hD hX hcw hcap hnw hsib hnp hst hsb hcapn np 0
    ⟨entryK rCp rNp (toWord np) s0.M, s0.o⟩
    (by omega) hME (by simp only [size_entryK]; omega)
    (fun a ha => by
      show rd (entryK rCp rNp (toWord np) s0.M) (bX + a) = _
      rw [hHE _ (by simp only [regs] at hbX ⊢; omega), hXs a ha])
    (by show rd (entryK rCp rNp (toWord np) s0.M) rPp = _; rw [hE _ (by decide) (by decide), p0])
    (by show rd (entryK rCp rNp (toWord np) s0.M) rWA = _; rw [hE _ (by decide) (by decide), a0])
  intro y hy hy2
  rw [d2 y hy (by rw [Nat.mul_zero, Nat.add_zero, e0]; exact hy2)]
  show rd (entryK rCp rNp (toWord np) s0.M) y = _
  rw [hHE y hy]

end Read4

/-! ## 3.x's instances (`memX`, `posL`) -/

section Pos

variable {c : Digest} {π : Proof} {L : Log} {i : ℕ}

/-- **The position loop**: `m` positions from `j` fill their columns' cells. -/
theorem posLoop (hD : Dom c π L) {Xi : ℕ → Word} (hX : Sorted (tp c π L) L Xi) {cw nw ncap sb : ℕ}
    {cap : ℕ → Digest} (hcw : cw + 4 * ncap < 2 ^ 62)
    (hcap : ∀ e < ncap, ∀ m < 4,
      (tp c π L).getD (cw + 4 * e + m) 0 = (packBytes (cap e).toList).getD m 0)
    (hnw : nw < 2 ^ 60) {sib np : ℕ}
    (hsib : sib < 64) (hnp : np ≤ 2 ^ 20) (hst : sb + nw * np ≤ memX) (hsb : regs ≤ sb)
    (hcapn : np ≤ ncap * 2 ^ sib) :
    ∀ (m j : ℕ) (s : St), j + m ≤ np → Inv s.M → memX ≤ s.M.size →
      (∀ a < L.length, rd s.M (memX + a) = Xi a) → rd s.M rPp = toWord j →
      rd s.M rWA = toWord (sb + nw * j) →
      (∀ q, j ≤ q → q < j + m → ∀ w < nw,
        rd (iterL (semXIR (tp c π L) (posBody i cw nw sib)) rCp m s).M (sb + nw * q + w) =
          colWord (colL (frEnc i) L (cap (q / 2 ^ sib)) sib q) w) ∧
      (∀ y, regs ≤ y → (y < sb + nw * j ∨ sb + nw * (j + m) ≤ y) →
        rd (iterL (semXIR (tp c π L) (posBody i cw nw sib)) rCp m s).M y = rd s.M y) ∧
      Inv (iterL (semXIR (tp c π L) (posBody i cw nw sib)) rCp m s).M :=
  posLoop4 (bX := memX) (pL := posL) (by decide) (by decide) (by decide) hD.d4 hX hcw hcap hnw hsib hnp hst hsb hcapn

/-- **The ladder read's semantics**: on a sorted index, `readIR sib np` stores at
`colBase + 128 q + w` word `w` of the column `colL (frEnc i)` reads under cap entry `q / 2^sib`
at height `sib`, for every position `q < np`; it keeps the index. -/
theorem readIR_sem (hD : Dom c π L) {Xi : ℕ → Word} (hX : Sorted (tp c π L) L Xi) (s : St)
    (hM : Inv s.M) (hXs : ∀ a < L.length, rd s.M (memX + a) = Xi a) {cw nw ncap sb : ℕ}
    {cap : ℕ → Digest} (hcw : cw + 4 * ncap < 2 ^ 62)
    (hcap : ∀ e < ncap, ∀ m < 4,
      (tp c π L).getD (cw + 4 * e + m) 0 = (packBytes (cap e).toList).getD m 0)
    (hnw : nw < 2 ^ 60) {sib np : ℕ}
    (hsib : sib < 64) (hnp : np ≤ 2 ^ 20) (hst : sb + nw * np ≤ memX) (hsb : regs ≤ sb)
    (hcapn : np ≤ ncap * 2 ^ sib) (hsz : memX ≤ s.M.size) :
    (∀ q < np, ∀ w < nw, rd (semXIR (tp c π L) (readIR i cw sb nw sib np) s).M (sb + nw * q + w) =
      colWord (colL (frEnc i) L (cap (q / 2 ^ sib)) sib q) w) ∧
    (∀ a < L.length, rd (semXIR (tp c π L) (readIR i cw sb nw sib np) s).M (memX + a) = Xi a) ∧
    Inv (semXIR (tp c π L) (readIR i cw sb nw sib np) s).M :=
  readIR4_sem (bX := memX) (pL := posL) (by decide) (by decide) (by decide) hD.d4 hX s hM hXs hcw hcap hnw hsib hnp hst hsb hcapn hsz

end Pos

/-- **`read_spec`** (BLUEPRINT §6.5). On a domain tape of a SNARK proof, after the log index and
the read (`idxIR ; read0`), cell `colBase + 128 q + w` holds word `w` of the column that
`FRMerkle.colL (frEnc 0)` reads under π's cap entry `q / 2^9` at height `9`, for every
position `q < 2^18` (`P30` level 0), and `0` where it reads no column (`colWord`). -/
theorem read_spec (c : Digest) (π : Proof) (L : Log) (hD : Dom c π L) (s : St) (hM : Inv s.M)
    (hsz : memX + L.length + L.length ≤ s.M.size) {q w : ℕ} (hq : q < 2 ^ 18) (hw : w < 128) :
    rd (semXIR (tp c π L) (.seq idxIR read0) s).M (colBase + 128 * q + w) =
      colWord (colL (frEnc 0) L (capPi π (q / 2 ^ 9)) 9 q) w := by
  obtain ⟨r1, r2, r3⟩ := idxIR_sorted c π L hD.hs hD.hq hD.ht s hM hsz
  have hM1 : Inv (semXIR (tp c π L) idxIR s).M := inv_sem _ wf_logIR hM
  have hsz1 := size_sem (tp c π L) idxIR s
  rw [semXIR_seq]
  generalize semXIR (tp c π L) idxIR s = s1 at r1 r2 r3 hM1 hsz1
  exact (readIR_sem hD (Xi := fun a => rd s1.M (memX + a)) ⟨r1, r2, r3⟩ s1 hM1 (fun _ _ => rfl)
    (i := 0) (cw := capW0) (nw := 128) (ncap := 512) (sb := colBase) (cap := capPi π)
    (by rw [capW0_eq]; norm_num)
    (fun e he m hm => by simp only [tp, getD_toArray]; exact tape_cap c π L hD.hs he hm)
    (by norm_num) (by norm_num) (by norm_num) (by simp only [colBase, memX]; norm_num)
    (by simp only [regs, colBase]; norm_num) (by norm_num) (by omega)).1 q hq w hw

/-! ## The store as `F` elements: S-G's reading -/

theorem ofListLE_eq_ofLE : ∀ l : List UInt8, CompPoly.Bytes.ofListLE l = ofLE l
  | [] => rfl
  | b :: l => by rw [CompPoly.Bytes.ofListLE, ofLE_cons, ofListLE_eq_ofLE l]

/-- A word's eight little-endian bytes decode to the word. -/
theorem b64_ofBytes_word (w : Word) :
    B64.ofBytes (Vector.ofFn fun i : Fin 8 => (w.toNat / 256 ^ i.1).toUInt8) = wB w := by
  have h : (B64.ofBytes (Vector.ofFn fun i : Fin 8 => (w.toNat / 256 ^ i.1).toUInt8)).val.toNat =
      w.toNat := by
    rw [B64.ofBytes_toNat, CompPoly.Bytes.ofVecLE, Vector.toList_ofFn, ofListLE_eq_ofLE, ofLE_ofFn,
      Nat.mod_eq_of_lt (by simpa using w.isLt)]
  show B64.mk (B64.ofBytes _).val = B64.mk (wB w).val
  exact congrArg B64.mk (UInt64.toNat_inj.mp h)

/-- **An `F` element read off a byte string is its two packed words** (`readF`'s decoding). -/
theorem F_ofBytes_words (l : ByteArray) (r : ℕ) :
    F.ofBytes (bytesAt l (16 * r) 16) =
      ⟨wB ((packBytes l.data.toList).getD (2 * r) 0),
        wB ((packBytes l.data.toList).getD (2 * r + 1) 0)⟩ := by
  have key : ∀ m o : ℕ, ∀ (_ : o = 16 * r + 8 * (m - 2 * r)) (_ : 2 * r ≤ m) (_ : m ≤ 2 * r + 1),
      (Vector.ofFn fun i : Fin 8 => (bytesAt l (16 * r) 16)[o - 16 * r + i.1]'(by omega)) =
      Vector.ofFn fun i : Fin 8 => (((packBytes l.data.toList).getD m 0).toNat / 256 ^ i.1).toUInt8 :=
    fun m o ho h1 h2 => by
      ext i hi
      simp only [Vector.getElem_ofFn]
      rw [getElem_bytesAt _ _ _ _ (by omega), ← wordByte_packBytes, wordByte,
        show (16 * r + (o - 16 * r + i)) / 8 = m by omega,
        show (16 * r + (o - 16 * r + i)) % 8 = i by omega]
  have k0 := key (2 * r) (16 * r) (by omega) le_rfl (by omega)
  have k1 := key (2 * r + 1) (16 * r + 8) (by omega) (by omega) le_rfl
  simp only [Nat.sub_self, Nat.zero_add, show 16 * r + 8 - 16 * r = 8 by omega] at k0 k1
  rw [F.ofBytes, k0, k1, b64_ofBytes_word, b64_ofBytes_word]

/-- `F`'s zero is two zero words. -/
theorem F_zero_words : (⟨wB 0, wB 0⟩ : F) = 0 := rfl

/-- **`read_spec_F`**: read as `F` elements, the store is S-G's reading of the committed word:
`rdF` at `colBase + 128 q + 2 r` is `readF col (16 r)` (`F.ofBytes (bytesAt col (16 r) 16)`) of
the column `colL (frEnc 0)` reads under π's cap entry `q / 2^9`, and `0` where none is read: the
form of `FR.Snd.wordOf`, with the cap entries taken from π (`capPi`). -/
theorem read_spec_F (c : Digest) (π : Proof) (L : Log) (hD : Dom c π L) (s : St) (hM : Inv s.M)
    (hsz : memX + L.length + L.length ≤ s.M.size) {q r : ℕ} (hq : q < 2 ^ 18) (hr : r < 64) :
    rdF (semXIR (tp c π L) (.seq idxIR read0) s).M (colBase + 128 * q + 2 * r) =
      ((colL (frEnc 0) L (capPi π (q / 2 ^ 9)) 9 q).map
        fun col => F.ofBytes (bytesAt col (16 * r) 16)).getD 0 := by
  rw [rdF, rdB, rdB, read_spec c π L hD s hM hsz hq (by omega),
    show colBase + 128 * q + 2 * r + 1 = colBase + 128 * q + (2 * r + 1) by omega,
    read_spec c π L hD s hM hsz hq (by omega)]
  cases colL (frEnc 0) L (capPi π (q / 2 ^ 9)) 9 q with
  | none => rfl
  | some col => rw [Option.map_some, Option.getD_some, F_ofBytes_words]; rfl



/-! ## Controls -/

namespace ReadControls

open FR.Merkle

/-- A toy log: a level-0 node query `(dg 1, dg 2)` answered `dg 3`, and a level-0 column query
answered `dg 1`. -/
def toyN : Log := [(colQ 0 ⟨#[1, 2, 3, 4, 5, 6, 7, 8, 9]⟩, dg 1), (nodeQ 0 (dg 1) (dg 2), dg 3)]

/-- **Positive control of `nodeStepP`**: bit `h` of `p` picks the child. -/
theorem nodeStepP_toy : nodeStepP 0 toyN 0 0 (dg 3) = some (dg 1) ∧
    nodeStepP 0 toyN 1 0 (dg 3) = some (dg 2) := by decide +kernel

/-- **Negative controls of `nodeStepP`**: a digest with no preimage, and a node query of another
level (the level byte is checked), give `none`. -/
theorem nodeStepP_toy_none : nodeStepP 0 toyN 0 0 (dg 4) = none ∧
    nodeStepP 0 [(nodeQ 1 (dg 1) (dg 2), dg 3)] 0 0 (dg 3) = none := by decide +kernel

/-- **Positive control of the reading the store holds**: under `dg 3` at height 1, position 0
reads the column `1, …, 9`; its first word is bytes `1 … 8`, its second byte `9`, its third `0`. -/
theorem colWord_toy :
    colWord (colL (frEnc 0) toyN (dg 3) 1 0) 0 = toWord (ofLE [1, 2, 3, 4, 5, 6, 7, 8]) ∧
    colWord (colL (frEnc 0) toyN (dg 3) 1 0) 1 = 9 ∧
    colWord (colL (frEnc 0) toyN (dg 3) 1 0) 2 = 0 := by decide +kernel

/-- **Negative control**: position 1 under `dg 3` is `dg 2`'s subtree, which has no preimage, so
the store holds zeros; a column query of level 1 is not a level-0 column. -/
theorem colWord_toy_none : colWord (colL (frEnc 0) toyN (dg 3) 1 1) 0 = 0 ∧
    colL (frEnc 0) [(colQ 1 ⟨#[1]⟩, dg 1)] (dg 1) 0 0 = none := by decide +kernel

/-- `LoK` excludes stores (the heap frame needs it). -/
theorem not_loK_store : ¬ LoK (.store rWA rV2) := id

end ReadControls

end FR.X


