-- lvm6 EXF (DP6 §2 item 1, X8b `DescProg6`'s first piece): the extractor's front tied to the history. After
-- `parseIR ; frontIR6` on the tape of an `S` proof whose replay `Ex` returns `(x, h)`, the heap holds W1's committed
-- rows of `commits h` at `wB6 i` and the history's challenges at the chain's answer cells. New.
import Lvm6XFront6P18
import Lvm6Len
import Lvm6XDescFold

/-!
# The front on an accepted proof's tape

* Codec: **`kOfBytes_decLE`**, **`wK_packBytes6`** (a packed answer word is the scheme's `K` lane),
  **`readRowG_wordOf6`** (season 1's O12 at M′, ported: the generic reading is the scheme's `wordOf`),
  **`digestsOf_capOf6`** (the scheme's cap record is `capOf6`).
* **`cap6 π i`**: level `i`'s cap as π carries it (`capOf6` at X5's `capW6 i`). **`capEnt6`**: the history's
  record of commitment `i` is `(ht6 i, zp6 i + occ6 i, p ↦ 0^{zp6 i} ++ rows6 i L (cap6 π i) p)` (IDX.md's shift).
* **`ex_run`**: `Ex` returns `(x, h)` only after an accepting replay from the seed's answer, chain position 1.
* **`front6_hist`**: for phases that follow `sched6 P18` (`PhasesFollow`) and whose opening opens `tP18 i`
  positions (`QLen`; `qlen_whirAt` for the deployed one), `ChainHist P18 π L h` and `commits h` is the five caps'
  records (`trun_front`, `front18`).
* **`frontSt6`** (parse, then the front), **`front6_sem`**: `Inv`, no output, the rows `rows6 i L (cap6 π i)` at
  `wB6 i + occ6 i · p + t` (`read6IR_sem` five times, each keeping the others' rows and the chain), the chain's
  answers at `ansB + 4p` (`chain6_sem`).
* **`front6_heap`**: the two together, on the history: the heap's row word `t` of level `i` at position `p` is word
  `zp6 i + t` of `commits h`'s `i`-th word at `p`, and `rdE2` at `ansB + 4 (j + 2)` is `e2OfE` of the history's
  `j`-th sample (the `E2` challenge W1's rounds read, `chalE2.rd = e2OfE`).
-/

set_option autoImplicit false

namespace Lvm6.X

open RecursionFast Lvm Lvm.X Lvm.FS
open LeanVM.Protocol.Compile (Ev VerifierProgram commits)
open LeanVM.Parameters (E2 e2OfE)

/-! ## Codec -/

/-- The scheme's word decoder is the reader's on the first eight bytes. -/
theorem kOfBytes_decLE (b : List UInt8) : Lvm.FS.kOfBytes b = decLE (b.take 8) := by
  have hlt : ofLE (b.take 8) < 2 ^ 64 := (RecursionFast.ofLE_lt _).trans_le (by
    rw [show (2 : ℕ) ^ 64 = 256 ^ 8 by norm_num]
    exact Nat.pow_le_pow_right (by norm_num) (by simp))
  unfold Lvm.FS.kOfBytes decLE
  congr 1
  apply BitVec.eq_of_toNat_eq
  rw [toNat_toWord hlt, ofLE_take, ← Fin.sum_univ_eq_sum_range (fun i => (b.getD i 0).toNat * 256 ^ i)]
  simp only [BitVec.toNat_ofFin, Fin.val_cast, finFunctionFinEquiv_apply]
  rfl

/-- **A packed word read as `K`** is the scheme's word of its eight bytes. -/
theorem wK_packBytes6 (l : List UInt8) {j : ℕ} (hj : j < (packBytes l).length) :
    wK ((packBytes l).getD j 0) = Lvm.FS.kOfBytes (l.drop (8 * j)) := by
  rw [List.getD_eq_getElem _ _ hj, kOfBytes_decLE]
  simp only [packBytes, List.getElem_map, List.getElem_range]
  rfl

theorem xDescend_eq6 (L : Log) : ∀ (n : ℕ) (v : Digest) (q : ℕ), xDescend L n v q = Scheme.descend L n v q
  | 0, _, _ => rfl
  | n + 1, v, q => by
    simp only [xDescend, Scheme.descend, xDescend_eq6 L n]
    rfl

/-- **The generic reading is the scheme's word** (season 1's `readRowG_eq_wordOf`, `LvmMPXExtEq`, ported). -/
theorem readRowG_wordOf6 (S : Scheme) (hK : S.decK = Lvm.FS.kOfBytes) {ht lv z occ : ℕ}
    (hO : S.occ ht (z + occ) = occ) (L : Log) (cap : List Digest) (p : ℕ) :
    readRowG ht lv z occ L cap p = S.wordOf L ⟨ht, z + occ, lv, cap⟩ p := by
  have hl : xLeafBytesG ht lv L cap p = Scheme.leafBytes L ⟨ht, z + occ, lv, cap⟩ p := by
    simp only [xLeafBytesG, Scheme.leafBytes, xDescend_eq6]
    rfl
  rw [readRowG, Scheme.wordOf, Scheme.padRow, hl, hK]
  show _ = padRowOf Lvm.FS.kOfBytes (z + occ) (S.occ ht (z + occ)) _
  rw [hO, padRowOf, Nat.min_eq_left (Nat.le_add_left _ _), Nat.add_sub_cancel]
  simp only [xRowOf, rowOf, kOfBytes_decLE, List.take_take, Nat.min_self]

/-- **The scheme's cap record** of the `2^lv` digests at π offset `off` is `capOf6`. -/
theorem digestsOf_capOf6 (π : Proof) (off lv : ℕ) :
    digestsOf ((π.data.toList.drop off).take (32 * 2 ^ lv)) (2 ^ lv) = capOf6 π off lv := by
  unfold digestsOf capOf6
  refine List.map_congr_left fun e he => ?_
  rw [List.mem_range] at he
  apply Vector.ext
  intro i hi
  simp only [dg, xWin, xDg, xQb, Vector.getElem_ofFn, List.getD_eq_getElem?_getD, List.getElem?_drop,
    List.getElem?_take]
  rw [if_pos (by omega), Nat.add_assoc]

/-! ## The history's commitments at `P18` -/

/-- Level `i`'s cap as π carries it (X5's `capW6 i`). -/
def cap6 (π : Proof) (i : ℕ) : List Digest := capOf6 π (8 * (capW6 i - 5)) (lv6 i)

/-- **The history's record of commitment `i`**: W1's padded row, the leaf's words `rows6` after `zp6 i` zeros. -/
theorem capEnt6 (prog : Shape → Digest → List UInt8 → VerifierProgram Bool) (vk : Digest) (L : Log)
    (π : Proof) {i : ℕ} (hi : i < 5) :
    capEnt (schemeOf prog P18 vk) L π (ht6 i, zp6 i + occ6 i, 8 * (capW6 i - 5)) =
      (ht6 i, zp6 i + occ6 i, fun p => List.replicate (zp6 i) 0 ++ rows6 i L (cap6 π i) p) := by
  obtain ⟨hcO, hoc, -⟩ := lev18 hi
  have hcO' : (schemeOf prog P18 vk).capOf (ht6 i) (zp6 i + occ6 i) = lv6 i := hcO
  have hoc' : (schemeOf prog P18 vk).occ (ht6 i) (zp6 i + occ6 i) = occ6 i := hoc
  have hci : (schemeOf prog P18 vk).capI (ht6 i) (zp6 i + occ6 i) (π.data.toList.drop (8 * (capW6 i - 5))) =
      ⟨ht6 i, zp6 i + occ6 i, lv6 i, cap6 π i⟩ := by
    simp only [Scheme.capI, Scheme.capBytes, hcO']
    rw [digestsOf_capOf6]
    rfl
  simp only [capEnt, hci]
  congr 2
  funext p
  rw [← readRowG_wordOf6 _ rfl hoc', rows6, readRowG, readRowG, List.replicate_zero, List.nil_append]

/-! ## The replay `Ex` returns -/

/-- **`Ex` returns `(x, h)` after an accepting replay** from the seed's answer (chain position 1) on the body
`π[hdrLen, |π|)`. -/
theorem ex_run {prog : Shape → Digest → List UInt8 → VerifierProgram Bool} {vk c : Digest} {π : Proof}
    {L : Log} {x : List UInt8} {h : List Ev}
    (hE : (schemeOf prog P18 vk).Ex (fun _ x h => (x, h)) c π L = some (x, h)) :
    ∃ a₁, fmAns (fsQ6 P18 π) zeroDL L 1 = some a₁ ∧
      (schemeOf prog P18 vk).trun L (prog P18 vk x) a₁ [] [] (π.data.toList.drop (hdrLen P18)) [] =
        some (true, h) := by
  obtain ⟨hx, -⟩ := Ex_hdr hE
  subst hx
  unfold Scheme.Ex at hE
  have hh : (schemeOf prog P18 vk).hdr π = V.hdr6 (toV P18) π := rfl
  rw [hh] at hE
  by_cases hs : V.hdrLen (toV P18) ≤ π.size
  · rw [V.hdr6, if_pos hs] at hE
    try dsimp only at hE
    split_ifs at hE
    obtain ⟨e₀, h0, hE⟩ := Option.bind_eq_some_iff.mp hE
    obtain ⟨e₁, h1, hE⟩ := Option.bind_eq_some_iff.mp hE
    obtain ⟨⟨b, h'⟩, hr, hE⟩ := Option.bind_eq_some_iff.mp hE
    split_ifs at hE with hr1
    obtain ⟨-, rfl⟩ := Prod.mk.inj (Option.some.inj hE)
    have hb : b = true := hr1
    subst hb
    refine ⟨e₁.2, ?_, hr⟩
    rw [fmAns6_one P18 vk (fun _ _ => true), fmAns6_zero]
    have h0' : L.find? (fun e => decide (e.1 = Lvm.FS.toQ V.q06)) = some e₀ := h0
    rw [h0', Option.map_some, Option.bind_some]
    have h1' : L.find? (fun e => decide (e.1 = (V.scheme6V (toV P18) vk fun _ _ => true).seedQ e₀.2
        (π.data.toList.take (hdrLen P18)))) = some e₁ := h1
    rw [h1', Option.map_some]
  · rw [V.hdr6, if_neg hs] at hE
    cases hE

/-! ## The history at `P18` -/

/-- **The deployed opening opens `tP18 i` positions** (LEN's `len6_whirAt`). -/
theorem qlen_whirAt {Φ : Phases} (hw : Φ.whir = whirAt Whir.whirP18) : ∀ cl, QLen tP18 (Φ.whir P18 cl) :=
  fun cl ↦ by
    rw [hw]
    show QLen tP18 (if openKey P18 = true then Whir.whirP18 cl else .fail)
    rw [Whir.openKey_P18]
    exact Whir.qlen_whirP18 cl

/-- **The sources of the `P18` replay's events**, from π offset `hdrLen` and chain position 1. -/
def srcs18 : List Src :=
  srcsOp (V.capOfL P18.levs) (V.occL P18.levs) tP18 [] (V.widths (sched6 P18)) (hdrLen P18) 1
    (opsOf P18.levs (sched6 P18))

/-- **The replayed history at `P18`**: its challenges are the chain's, its five commitments are W1's padded rows of
the five caps π carries, and every event is its source's (`srcs18`). -/
theorem front6_hist {Φ : Phases} (hF : PhasesFollow Φ P18) (hW : ∀ cl, QLen tP18 (Φ.whir P18 cl))
    {vk c : Digest} {π : Proof} {L : Log} {x : List UInt8} {h : List Ev}
    (hE : (schemeOf (prog6 Φ) P18 vk).Ex (fun _ x h => (x, h)) c π L = some (x, h)) :
    ChainHist P18 π L h ∧
      commits h = (List.range 5).map (fun i =>
        (ht6 i, zp6 i + occ6 i, fun p => List.replicate (zp6 i) 0 ++ rows6 i L (cap6 π i) p)) ∧
      List.Forall₂ (EvSrc (schemeOf (prog6 Φ) P18 vk) P18 π L) srcs18 h := by
  obtain ⟨a₁, hfm, hT⟩ := ex_run hE
  have hR : RS P18 π L 1 (hdrLen P18) 0 a₁ [] (π.data.toList.drop (hdrLen P18)) [] :=
    ⟨rfl, by simp, Nat.zero_le _, hfm, rfl, fun j hj => absurd hj (by simp [samples])⟩
  obtain ⟨⟨hm, hct, hcaps, -⟩⟩ := (⟨front18⟩ : Nonempty _)
  obtain ⟨hc, hcm, evs, he1, he2⟩ := trun_front (schemeOf (prog6 Φ) P18 vk) (fun _ => rfl) P18 π L tP18 (prog6 Φ P18 vk x)
    (opsOf P18.levs (sched6 P18)) (V.widths (sched6 P18)) 1 (hdrLen P18) 0 a₁ [] [] _ [] h
    (prog6_sched Φ hF vk x) (qlen_prog6 hF hW vk x) (fun k => by rw [nReads_nil, Nat.zero_add]; rfl) hR
    (by simp [msgs6]) hm hct hT
  refine ⟨hc, ?_, by rw [he1, List.nil_append]; exact he2⟩
  rw [hcm, show commits ([] : List Ev) = [] from rfl, List.nil_append]
  have hcaps' : capsOp (schemeOf (prog6 Φ) P18 vk).capOf (schemeOf (prog6 Φ) P18 vk).occ tP18
      (([] : List CapI).map shp) (V.widths (sched6 P18)) (hdrLen P18) (opsOf P18.levs (sched6 P18)) =
      (List.range 5).map (fun i => (ht6 i, zp6 i + occ6 i, 8 * (capW6 i - 5))) := hcaps
  rw [hcaps', List.map_map]
  refine List.map_congr_left fun i hi => ?_
  exact capEnt6 (prog6 Φ) vk L π (List.mem_range.1 hi)

/-! ## The machine: parse, then the front -/

/-- **The state after the parse and the front** (`preOut6 descX inp` runs `descX` from it). -/
def frontSt6 (inp : List Word) : St :=
  semXIR inp.toArray frontIR6 (semXIR inp.toArray (parseIR pz6) (initSt (mem6 + mpwX * inp.length)))

theorem preOut6_eqF (descX : XIR) (inp : List Word) : preOut6 descX inp = semXIR inp.toArray descX (frontSt6 inp) :=
  rfl

theorem hasOut_storesIR : ∀ (b : ℕ) (ws : List Word), hasOut (storesIR b ws) = false
  | _, [] => rfl
  | b, _ :: ws => by simp only [storesIR, hasOut, hasOut_storesIR (b + 1) ws, Bool.or_false]

theorem hasOut_frontIR6 : hasOut frontIR6 = false := by
  simp only [frontIR6, chain6, chainIR, hasOut, hasOut_storesIR]
  decide

theorem log_le_input (c : Digest) (π : Proof) (L : Log) : 5 * L.length ≤ (extractorInput c π L).length := by
  have := length_logEntries L
  rw [tape_eq]
  simp only [List.length_append, logWords, List.length_cons]
  omega

section Machine

variable {c : Digest} {π : Proof} {L : Log}

/-- One level's reads from a state that holds the index: the rows, the frame, the index, `Inv`. -/
theorem read6_step (hs : π.size = pz6) (hq : ∀ e ∈ L, e.1.size < 2 ^ 64)
    (ht : (extractorInput c π L).length ≤ 2 ^ 64) (s : St) (hM : Inv s.M)
    (hsz : bX6 + L.length + L.length ≤ s.M.size) {i : ℕ} (hi : i < 5) (s₂ : St) (hM₂ : Inv s₂.M)
    (hsz₂ : s₂.M.size = s.M.size)
    (hX₂ : ∀ a < L.length, rd s₂.M (bX6 + a) =
      rd (semXIR (extractorInput c π L).toArray (idxIR4 bX6 pL6) s).M (bX6 + a)) :
    (∀ p < 2 ^ ht6 i, ∀ t < occ6 i,
      rdK (semXIR (extractorInput c π L).toArray (read6IR i bX6 pL6 (capW6 i) (wB6 i)) s₂).M
        (wB6 i + occ6 i * p + t) = (rows6 i L (cap6 π i) p).getD t 0) ∧
    (∀ y, regs ≤ y → (y < wB6 i ∨ wB6 i + occ6 i * 2 ^ ht6 i ≤ y) →
      rd (semXIR (extractorInput c π L).toArray (read6IR i bX6 pL6 (capW6 i) (wB6 i)) s₂).M y = rd s₂.M y) ∧
    (∀ a < L.length, rd (semXIR (extractorInput c π L).toArray (read6IR i bX6 pL6 (capW6 i) (wB6 i)) s₂).M
      (bX6 + a) = rd (semXIR (extractorInput c π L).toArray (idxIR4 bX6 pL6) s).M (bX6 + a)) ∧
    Inv (semXIR (extractorInput c π L).toArray (read6IR i bX6 pL6 (capW6 i) (wB6 i)) s₂).M ∧
    (semXIR (extractorInput c π L).toArray (read6IR i bX6 pL6 (capW6 i) (wB6 i)) s₂).M.size = s.M.size := by
  have h5 := (lev18 hi).2.2
  have hnum : 8 * (capW6 i - 5) + 32 * 2 ^ lv6 i ≤ pz6 ∧ capW6 i + 4 * 2 ^ lv6 i < 2 ^ 62 ∧ regs ≤ wB6 i ∧
      wB6 i + occ6 i * 2 ^ ht6 i ≤ bX6 := by
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4) with rfl | rfl | rfl | rfl | rfl <;>
      simp only [capW6, lv6, ht6, occ6, wB6, bX6, pz6, regs] <;> norm_num
  obtain ⟨n1, n2, n3, n4⟩ := hnum
  have hcap : ∀ e (he : e < (cap6 π i).length), ∀ m < 4,
      (extractorInput c π L).toArray.getD (capW6 i + 4 * e + m) 0 = (packBytes (cap6 π i)[e].toList).getD m 0 := by
    intro e he m hm
    have := capOf6_tape c π L (a := capW6 i - 5) (lv := lv6 i) (by rw [hs]; exact n1) e he m hm
    rw [show capW6 i = 5 + (capW6 i - 5) by omega]
    exact this
  obtain ⟨r1, r2, r3, r4⟩ := read6IR_sem (i := i) (bX := bX6) (pL := pL6) (by simp [regs, bX6])
    (by simp [bX6]) (by simp [pL6]) c π L (by rw [hs]; rfl) hq ht s hM hsz s₂ hM₂ (by rw [hsz₂]; omega) hX₂
    (capOf6_length _ _ _) n2 hcap n3 n4
  exact ⟨r1, r2, fun a ha => (r3 a ha).trans (hX₂ a ha), r4, by rw [size_sem, hsz₂]⟩

/-- **The front's machine facts**: after the parse and the front, `Inv`, no output, the five levels' rows at
`wB6 i`, the chain's answers at `ansB + 4p`. -/
theorem front6_sem (hs : π.size = pz6) (hq : ∀ e ∈ L, e.1.size < 2 ^ 64)
    (ht : (extractorInput c π L).length ≤ 2 ^ 64) (hS : ¬ StateHit L) :
    Inv (frontSt6 (extractorInput c π L)).M ∧ (frontSt6 (extractorInput c π L)).o = #[] ∧
    (∀ i < 5, ∀ p < 2 ^ ht6 i, ∀ t < occ6 i,
      rdK (frontSt6 (extractorInput c π L)).M (wB6 i + occ6 i * p + t) = (rows6 i L (cap6 π i) p).getD t 0) ∧
    (∀ p < nCh6 P18, ∀ a, fmAns (fsQ6 P18 π) zeroDL L p = some a → ∀ m < 4,
      rd (frontSt6 (extractorInput c π L)).M (ansB + 4 * p + m) = (packBytes a.toList).getD m 0) := by
  have hreg : regs ≤ mem6 := by simp only [regs, mem6]; norm_num
  have h0 : Inv (initSt (mem6 + mpwX * (extractorInput c π L).length)).M :=
    inv_initSt (Nat.le_add_right_of_le hreg)
  have hP : WF (parseIR pz6) := (wf_extIRWith (pz := pz6) (dec := .blk []) (by simp [WF])).1
  have hO : (frontSt6 (extractorInput c π L)).o = #[] := by
    rw [frontSt6, sem_o _ _ _ hasOut_frontIR6, parse_o, initSt_o]
  suffices H : Inv (frontSt6 (extractorInput c π L)).M ∧
      (∀ i < 5, ∀ p < 2 ^ ht6 i, ∀ t < occ6 i,
        rdK (frontSt6 (extractorInput c π L)).M (wB6 i + occ6 i * p + t) = (rows6 i L (cap6 π i) p).getD t 0) ∧
      (∀ p < nCh6 P18, ∀ a, fmAns (fsQ6 P18 π) zeroDL L p = some a → ∀ m < 4,
        rd (frontSt6 (extractorInput c π L)).M (ansB + 4 * p + m) = (packBytes a.toList).getD m 0) from
    ⟨H.1, hO, H.2.1, H.2.2⟩
  have hM₀ := inv_sem (extractorInput c π L).toArray hP h0
  have hz₀ := size_sem (extractorInput c π L).toArray (parseIR pz6)
    (initSt (mem6 + mpwX * (extractorInput c π L).length))
  rw [initSt_M, size_runPrims, Array.size_replicate] at hz₀
  rw [frontSt6, frontIR6, readsIR6]
  repeat rw [semXIR_seq]
  generalize semXIR (extractorInput c π L).toArray (parseIR pz6)
    (initSt (mem6 + mpwX * (extractorInput c π L).length)) = s₀ at hM₀ hz₀ ⊢
  have hlog := log_le_input c π L
  have hsz : bX6 + L.length + L.length ≤ s₀.M.size := by
    rw [hz₀]; simp only [mem6, bX6, mpwX]; omega
  -- the index, the chain
  have hM₁ := inv_sem (extractorInput c π L).toArray (wf_idxIR4 bX6 pL6) hM₀
  have hz₁ := size_sem (extractorInput c π L).toArray (idxIR4 bX6 pL6) s₀
  obtain ⟨cA, cK⟩ := chain6_sem P18 chainOK6_P18 c π L (hs.trans pz6_eq) hq ht hS _ hM₁
    (by rw [hz₁, hz₀]; simp only [chEnd, mem6]; omega)
  have hM₂ := inv_sem (extractorInput c π L).toArray wf_chain6 hM₁
  have hz₂ : (semXIR (extractorInput c π L).toArray (chain6 P18)
      (semXIR (extractorInput c π L).toArray (idxIR4 bX6 pL6) s₀)).M.size = s₀.M.size := by
    rw [size_sem, size_sem]
  have hX₂ : ∀ a < L.length, rd (semXIR (extractorInput c π L).toArray (chain6 P18)
      (semXIR (extractorInput c π L).toArray (idxIR4 bX6 pL6) s₀)).M (bX6 + a) =
      rd (semXIR (extractorInput c π L).toArray (idxIR4 bX6 pL6) s₀).M (bX6 + a) := fun a _ =>
    cK _ (by simp only [regs, bX6]; omega) (Or.inr (by simp only [chEnd, bX6]; omega))
  generalize semXIR (extractorInput c π L).toArray (chain6 P18)
    (semXIR (extractorInput c π L).toArray (idxIR4 bX6 pL6) s₀) = s₂ at cA cK hM₂ hz₂ hX₂ ⊢
  -- the five reads
  obtain ⟨a0, f0, x0, m0, z0⟩ := read6_step hs hq ht s₀ hM₀ hsz (i := 0) (by norm_num) s₂ hM₂ hz₂ hX₂
  generalize semXIR (extractorInput c π L).toArray (read6IR 0 bX6 pL6 (capW6 0) (wB6 0)) s₂ = t0
    at a0 f0 x0 m0 z0 ⊢
  obtain ⟨a1, f1, x1, m1, z1⟩ := read6_step hs hq ht s₀ hM₀ hsz (i := 1) (by norm_num) t0 m0 z0 x0
  generalize semXIR (extractorInput c π L).toArray (read6IR 1 bX6 pL6 (capW6 1) (wB6 1)) t0 = t1
    at a1 f1 x1 m1 z1 ⊢
  obtain ⟨a2, f2, x2, m2, z2⟩ := read6_step hs hq ht s₀ hM₀ hsz (i := 2) (by norm_num) t1 m1 z1 x1
  generalize semXIR (extractorInput c π L).toArray (read6IR 2 bX6 pL6 (capW6 2) (wB6 2)) t1 = t2
    at a2 f2 x2 m2 z2 ⊢
  obtain ⟨a3, f3, x3, m3, z3⟩ := read6_step hs hq ht s₀ hM₀ hsz (i := 3) (by norm_num) t2 m2 z2 x2
  generalize semXIR (extractorInput c π L).toArray (read6IR 3 bX6 pL6 (capW6 3) (wB6 3)) t2 = t3
    at a3 f3 x3 m3 z3 ⊢
  obtain ⟨a4, f4, -, m4, -⟩ := read6_step hs hq ht s₀ hM₀ hsz (i := 4) (by norm_num) t3 m3 z3 x3
  generalize semXIR (extractorInput c π L).toArray (read6IR 4 bX6 pL6 (capW6 4) (wB6 4)) t3 = t4
    at a4 f4 m4 ⊢
  -- below `wB6 k`, the later reads keep the heap
  have k1 : ∀ y, regs ≤ y → y < wB6 1 → rd t4.M y = rd t0.M y := fun y hy hy' => by
    rw [f4 y hy (Or.inl (by simp only [wB6] at hy' ⊢; omega)), f3 y hy (Or.inl (by simp only [wB6] at hy' ⊢; omega)),
      f2 y hy (Or.inl (by simp only [wB6] at hy' ⊢; omega)), f1 y hy (Or.inl hy')]
  have k2 : ∀ y, regs ≤ y → y < wB6 2 → rd t4.M y = rd t1.M y := fun y hy hy' => by
    rw [f4 y hy (Or.inl (by simp only [wB6] at hy' ⊢; omega)), f3 y hy (Or.inl (by simp only [wB6] at hy' ⊢; omega)),
      f2 y hy (Or.inl hy')]
  have k3 : ∀ y, regs ≤ y → y < wB6 3 → rd t4.M y = rd t2.M y := fun y hy hy' => by
    rw [f4 y hy (Or.inl (by simp only [wB6] at hy' ⊢; omega)), f3 y hy (Or.inl hy')]
  have k4 : ∀ y, regs ≤ y → y < wB6 4 → rd t4.M y = rd t3.M y := fun y hy hy' => f4 y hy (Or.inl hy')
  refine ⟨m4, fun i hi p hp t htt => ?_, fun p hp a ha m hm => ?_⟩
  · have hy : ∀ k, i < k → k < 5 → wB6 i + occ6 i * p + t < wB6 k := by
      intro k hik hk
      have hpt : occ6 i * p + t < occ6 i * 2 ^ ht6 i := by
        calc occ6 i * p + t < occ6 i * p + occ6 i := by omega
          _ = occ6 i * (p + 1) := by ring
          _ ≤ occ6 i * 2 ^ ht6 i := Nat.mul_le_mul_left _ hp
      rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4) with rfl | rfl | rfl | rfl | rfl <;>
      rcases (by omega : k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4) with rfl | rfl | rfl | rfl <;>
        simp only [wB6, occ6, ht6] at hpt ⊢ <;> omega
    have hr : regs ≤ wB6 i + occ6 i * p + t := by
      rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4) with rfl | rfl | rfl | rfl | rfl <;>
        simp only [wB6, regs] <;> omega
    unfold rdK
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4) with rfl | rfl | rfl | rfl | rfl
    · rw [k1 _ hr (hy 1 (by norm_num) (by norm_num))]; exact a0 p hp t htt
    · rw [k2 _ hr (hy 2 (by norm_num) (by norm_num))]; exact a1 p hp t htt
    · rw [k3 _ hr (hy 3 (by norm_num) (by norm_num))]; exact a2 p hp t htt
    · rw [k4 _ hr (hy 4 (by norm_num) (by norm_num))]; exact a3 p hp t htt
    · exact a4 p hp t htt
  · have hn := chainOK6_P18.nCh
    norm_num at hn
    have hy : ansB + 4 * p + m < wB6 0 := by simp only [ansB, wB6]; omega
    have hr : regs ≤ ansB + 4 * p + m := by simp only [ansB, regs]; omega
    rw [k1 _ hr (by simp only [wB6] at hy ⊢; omega), f0 _ hr (Or.inl hy)]
    exact cA p hp a ha m hm

end Machine

/-! ## The front on the history -/

/-- **`front6_heap`** (DP6 §2 item 1): on the tape of an `S` proof of `pz6` bytes whose replay returns `(x, h)`
(phases following `sched6 P18`, the opening opening `tP18 i` positions), a log with no state hit and the tape's
size facts, after `parseIR ; frontIR6`:
* `Inv`, no output;
* `h` has five commitments, `i`-th of shape `(ht6 i, zp6 i + occ6 i)`, its rows `zp6 i` zeros then words that
  the heap holds: word `zp6 i + t` of the row at `p` is `rdK` at `wB6 i + occ6 i · p + t`;
* the history's `j`-th sample is inside the chain (`j + 2 < nCh6 P18`) and its `E2` lanes are `rdE2` at
  `ansB + 4 (j + 2)`. -/
theorem front6_heap {Φ : Phases} (hF : PhasesFollow Φ P18) (hW : ∀ cl, QLen tP18 (Φ.whir P18 cl))
    {vk c : Digest} {π : Proof} {L : Log} {x : List UInt8} {h : List Ev}
    (hE : (schemeOf (prog6 Φ) P18 vk).Ex (fun _ x h => (x, h)) c π L = some (x, h)) (hs : π.size = pz6)
    (hq : ∀ e ∈ L, e.1.size < 2 ^ 64) (ht : (extractorInput c π L).length ≤ 2 ^ 64) (hS : ¬ StateHit L) :
    Inv (frontSt6 (extractorInput c π L)).M ∧ (frontSt6 (extractorInput c π L)).o = #[] ∧
    (commits h).length = 5 ∧
    (∀ i < 5, ((commits h).getD i default).1 = ht6 i ∧ ((commits h).getD i default).2.1 = zp6 i + occ6 i ∧
      (∀ p, ∀ t < zp6 i, (((commits h).getD i default).2.2 p).getD t 0 = 0) ∧
      ∀ p < 2 ^ ht6 i, ∀ t < occ6 i, rdK (frontSt6 (extractorInput c π L)).M (wB6 i + occ6 i * p + t) =
        (((commits h).getD i default).2.2 p).getD (zp6 i + t) 0) ∧
    (∀ j (hj : j < (samples h).length), j + 2 < nCh6 P18 ∧
      rdE2 (frontSt6 (extractorInput c π L)).M (ansB + 4 * (j + 2)) = e2OfE (samples h)[j]) := by
  obtain ⟨hc, hcm, -⟩ := front6_hist hF hW hE
  obtain ⟨m1, m2, m3, m4⟩ := front6_sem (c := c) hs hq ht hS
  refine ⟨m1, m2, by rw [hcm]; simp, fun i hi => ?_, fun j hj => ?_⟩
  · have hg : (commits h).getD i default =
        (ht6 i, zp6 i + occ6 i, fun p => List.replicate (zp6 i) 0 ++ rows6 i L (cap6 π i) p) := by
      rw [hcm, List.getD_eq_getElem _ _ (by simpa using hi), List.getElem_map, List.getElem_range]
    rw [hg]
    refine ⟨rfl, rfl, fun p t htz => ?_, fun p hp t htt => ?_⟩
    · rw [List.getD_append _ _ _ _ (by simpa using htz), List.getD_replicate]
      simp [htz]
    · rw [m3 i hi p hp t htt, List.getD_append_right _ _ _ _ (by simp), List.length_replicate,
        Nat.add_sub_cancel_left]
  · obtain ⟨a, ha1, ha2, ha3⟩ := hc j hj
    refine ⟨ha3, ?_⟩
    have w0 := m4 (j + 2) ha3 a ha1 0 (by norm_num)
    have w1 := m4 (j + 2) ha3 a ha1 1 (by norm_num)
    have hl : (packBytes a.toList).length = 4 := by rw [packBytes_length, Vector.length_toList]
    rw [ha2, e2OfE_chalOf]
    unfold rdE2 rdK
    rw [Nat.add_zero] at w0
    rw [w0, show ansB + 4 * (j + 2) + 1 = ansB + 4 * (j + 2) + 1 from rfl, w1,
      wK_packBytes6 _ (by omega), wK_packBytes6 _ (by omega)]
    rfl

end Lvm6.X
