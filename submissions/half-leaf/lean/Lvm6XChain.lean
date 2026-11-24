-- lvm6 X2 (part 2): the Fiat–Shamir chain of FORMAT6 v2.3 replayed by season 1's scan (`chainIR`). New;
-- the table, the seed block and the instance follow season 1's `LvmXSComputes`/`LvmXSNodeSem` (`tabEntS`,
-- `sdL`, `tabW_chTabS`, `chainLS_spec`), with V1's schedule walk in place of season 1's.
import Lvm6Format
import Lvm6P17MemoS
import LvmXChainL

/-!
# The chain replay at a shape

* **`msgsAux`**: the chain's messages after the seed, one `(π offset, |buf|)` per draw, walking V1's items
  (`FORMAT6.md` §4: scalars, words, caps and nonces are absorbed; openings are not). **`msgsAux_lens`**: the
  query lengths `32 + |buf|` are V1's `fsLensAux`, so the walk is V1's.
* **`msgs6`**: the seed's message first. The seed is taken in form (a) of finding F-X3 (`a₀ ‖ HDR`, the header
  being `π[0, hdrLen)`): FORMAT6 v2.3's `a₀ ‖ c ‖ HDR` is not one slice of the tape (`c` is tape words 0–3,
  `|π|` word 4, `π` from word 5), so season 1's scan cannot match it.
* **`fsQ6`** (the target of position `p`), **`tab6`**, **`sd6`** (`H[0] := q₀`'s word), **`chain6`**.
* **`tabW6`**, **`chain6_sem`**: under the static facts `ChainOK6` (decided at `P18`, `chainOK6_P18` (in `Lvm6P18Park` since INT11)) the scan's
  answers are the first-match chain's. **`cost_chain6`**: the exact cost.
-/

set_option autoImplicit false

namespace Lvm6.X

open RecursionFast Lvm Lvm.X

/-! ## The messages -/

/-- **The chain's messages** of a schedule from π offset `o`, the buffer holding `b` bytes (it is `π[o − b, o)`):
one `(offset, length)` per draw. -/
def msgsAux (L : List V.Lev) : List V.Item → ℕ → ℕ → List (ℕ × ℕ)
  | [], _, _ => []
  | .E k :: r, o, b => msgsAux L r (o + 16 * k) (b + 16 * k)
  | .K k :: r, o, b => msgsAux L r (o + 8 * k) (b + 8 * k)
  | .cap i :: r, o, b => msgsAux L r (o + 32 * 2 ^ (L.getD i default).lv) (b + 32 * 2 ^ (L.getD i default).lv)
  | .G _ :: r, o, b => (o - b, b + 8) :: msgsAux L r (o + 8) 0
  | .D 0 :: r, o, b => msgsAux L r o b
  | .D (k + 1) :: r, o, b => (o - b, b) :: List.replicate k (o, 0) ++ msgsAux L r o 0
  | .B :: r, o, b => (o - b, b) :: msgsAux L r o 0
  | .pos i _ :: r, o, b =>
    (o - b, b + 8) :: List.replicate ((L.getD i default).draws - 1) (o + 8, 0) ++ msgsAux L r (o + 8) 0
  | .open i :: r, o, b =>
    msgsAux L r (o + (L.getD i default).t * ((L.getD i default).lb + 32 * (L.getD i default).path)) b

/-- **The walk is V1's**: the query lengths `32 + |buf|` of the messages are `fsLensAux`. -/
theorem msgsAux_lens (L : List V.Lev) :
    ∀ (s : List V.Item) (o b : ℕ), (msgsAux L s o b).map (fun m => 32 + m.2) = V.fsLensAux L s b
  | [], _, _ => rfl
  | .E k :: r, o, b => by rw [msgsAux, V.fsLensAux, msgsAux_lens L r]
  | .K k :: r, o, b => by rw [msgsAux, V.fsLensAux, msgsAux_lens L r]
  | .cap i :: r, o, b => by rw [msgsAux, V.fsLensAux, msgsAux_lens L r]
  | .G _ :: r, o, b => by
    rw [msgsAux, V.fsLensAux, List.map_cons, msgsAux_lens L r, Nat.add_assoc]
  | .D 0 :: r, o, b => by rw [msgsAux, V.fsLensAux, msgsAux_lens L r]
  | .D (k + 1) :: r, o, b => by
    rw [msgsAux, V.fsLensAux, List.map_append, List.map_cons, List.map_replicate, msgsAux_lens L r]; rfl
  | .B :: r, o, b => by rw [msgsAux, V.fsLensAux, List.map_cons, msgsAux_lens L r]
  | .pos i _ :: r, o, b => by
    rw [msgsAux, V.fsLensAux, List.map_append, List.map_cons, List.map_replicate, msgsAux_lens L r]; rfl
  | .open i :: r, o, b => by rw [msgsAux, V.fsLensAux, msgsAux_lens L r]

/-- **Openings never split a buffer**: at every `open` the buffer is empty, so each message is one slice
`π[o − b, o)` of the proof (what `msgsAux` assumes; the bridge to the scheme's `trun` uses it). -/
def contigAux : List V.Item → ℕ → Bool
  | [], _ => true
  | .E k :: r, b => contigAux r (b + 16 * k)
  | .K k :: r, b => contigAux r (b + 8 * k)
  | .cap _ :: r, b => contigAux r (b + 1)
  | .G _ :: r, _ => contigAux r 0
  | .D 0 :: r, b => contigAux r b
  | .D (_ + 1) :: r, _ => contigAux r 0
  | .B :: r, _ => contigAux r 0
  | .pos _ _ :: r, _ => contigAux r 0
  | .open _ :: r, b => b == 0 && contigAux r b

/-- **The seed's message**, form (a) of F-X3: the header `π[0, hdrLen)`. -/
def seedMsg6 (sh : Shape) : ℕ × ℕ := (0, hdrLen sh)

/-- **The chain's messages** at a shape: the seed, then the schedule's draws. -/
def msgs6 (sh : Shape) : List (ℕ × ℕ) := seedMsg6 sh :: msgsAux sh.levs (sched6 sh) (hdrLen sh) 0

/-- The message of chain position `p ≥ 1`. -/
def msg6 (sh : Shape) (p : ℕ) : ℕ × ℕ := (msgs6 sh).getD (p - 1) (0, 0)

/-- The scan's targets `0 … nCh6 − 1`: `q₀` and one per message. -/
def nCh6 (sh : Shape) : ℕ := (msgs6 sh).length + 1

/-- **The query of chain position `p`**, the previous answer being `a`. -/
def fsQ6 (sh : Shape) (π : Proof) (p : ℕ) (a : Digest) : ByteArray :=
  if p = 0 then Lvm.FS.toQ V.q06 else digestBytes a ++ π.extract (msg6 sh p).1 ((msg6 sh p).1 + (msg6 sh p).2)

/-- A message is lane-aligned, inside π and its query within `queryCap`. -/
def msgOk6 (sh : Shape) (m : ℕ × ℕ) : Bool :=
  m.1 % 8 == 0 && m.2 % 8 == 0 && m.1 + m.2 ≤ piLenOf sh && 32 + m.2 ≤ queryCap

/-- **The static facts of the chain** at a shape. -/
structure ChainOK6 (sh : Shape) : Prop where
  msgs : (msgs6 sh).all (msgOk6 sh) = true
  nCh : nCh6 sh < 2 ^ 11
  pz : piLenOf sh < 2 ^ 32

/-! ## The table and the seed block -/

/-- One table entry: `tl`, the tape word of the message, two unused words (`q₀`: `tl = 7`). -/
def tabEnt6 (sh : Shape) (p : ℕ) : List Word :=
  if p = 0 then [toWord 7, 0, 0, 0] else [toWord (32 + (msg6 sh p).2), toWord (5 + (msg6 sh p).1 / 8), 0, 0]

/-- **The table**: entries `0 … nCh6`. -/
def tab6 (sh : Shape) : List Word := (List.range (nCh6 sh + 1)).flatMap (tabEnt6 sh)

/-- `q₀`'s packed word (FORMAT6 §3: `"lvm6/1"`, 0). -/
def q06W : Word := toWord (ofLE V.q06)

/-- **The seed block**: `H[0] := q₀`'s word. -/
def sd6 : XIR := .seq (.blk [.const rAd4 (toWord hB), .const rKd q06W]) (.store rAd4 rKd)

/-- **The chain program** at a shape. -/
def chain6 (sh : Shape) : XIR := chainIR (posL (piLenOf sh)) (nCh6 sh) (tab6 sh) sd6

theorem q06W_eq : (packBytes (Lvm.FS.toQ V.q06).data.toList).getD 0 0 = q06W := by decide

theorem wf_sd6 : WF sd6 := by
  refine ⟨fun p hp => ?_, show rAd4 ≠ cTmp by decide⟩
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hp
  rcases hp with rfl | rfl <;> simp only [Prim.dst, rAd4, rKd] <;> omega

theorem nw_sd6 (r : ℕ) (h1 : r ≠ rAd4) (h2 : r ≠ rKd) (h3 : r ≠ cTmp) : ¬ Writes sd6 r := by
  rintro (⟨p, hp, he⟩ | he)
  · simp only [List.mem_cons, List.mem_nil_iff, or_false] at hp
    rcases hp with rfl | rfl
    · exact h1 he.symm
    · exact h2 he.symm
  · exact h3 he

theorem seedOK_sd6 (I : Array Word) : SeedOK sd6 I (Lvm.FS.toQ V.q06) := by
  refine ⟨wf_sd6, nw_sd6 _ (by decide) (by decide) (by decide), fun s hM hsz => ?_⟩
  rw [show sd6 = .seq (.blk [.const rAd4 (toWord hB), .const rKd q06W]) (.store rAd4 rKd) from rfl,
    semXIR_seq]
  have hs := hM.1
  simp only [regs] at hs
  have hM1 : Inv (semXIR I (.blk [.const rAd4 (toWord hB), .const rKd q06W]) s).M := inv_sem I wf_sd6.1 hM
  have a1 : rd (semXIR I (.blk [.const rAd4 (toWord hB), .const rKd q06W]) s).M rAd4 = toWord hB := by
    simp only [semXIR, runPrims, List.foldl, Prim.run]
    rw [rd_set_ne (by decide), rd_set_self (by simp only [size_set, rAd4]; omega)]
  have k1 : rd (semXIR I (.blk [.const rAd4 (toWord hB), .const rKd q06W]) s).M rKd = q06W := by
    simp only [semXIR, runPrims, List.foldl, Prim.run]
    rw [rd_set_self (by simp only [size_set, rKd]; omega)]
  have f1 : ∀ i, i ≠ rAd4 → i ≠ rKd →
      rd (semXIR I (.blk [.const rAd4 (toWord hB), .const rKd q06W]) s).M i = rd s.M i :=
    fun i h1 h2 => rd_runPrims_of_not_writes (by
      simp only [List.mem_cons, List.mem_nil_iff, or_false]
      rintro q (rfl | rfl)
      · exact Ne.symm h1
      · exact Ne.symm h2) _
  have z1 := size_sem I (.blk [.const rAd4 (toWord hB), .const rKd q06W]) s
  generalize semXIR I (.blk [.const rAd4 (toWord hB), .const rKd q06W]) s = s1 at hM1 a1 k1 f1 z1
  have hB' : hB < s1.M.size := by rw [z1]; simp only [hB_eq, chEnd] at hsz ⊢; omega
  have st : ∀ i, i ≠ cTmp → rd (storeM s1.M rAd4 rKd) i = if i = hB then rd s1.M rKd else rd s1.M i :=
    fun i hi => rd_storeM hM1 a1 (by simp only [hB_eq, regs]; omega) (by simp only [hB_eq]; omega)
      hB' (by decide) (by decide) hi
  have e8 : semXIR I (.store rAd4 rKd) s1 = ⟨storeM s1.M rAd4 rKd, s1.o⟩ := rfl
  rw [e8]
  refine ⟨?_, ?_, fun y hy hy' => ?_⟩
  · rw [st _ (by simp only [hB_eq, cTmp]; omega), if_pos rfl, k1, q06W_eq]
  · rw [st _ (by decide), if_neg (by simp only [hB_eq, rCn5]; omega), f1 _ (by decide) (by decide)]
  · simp only [regs] at hy
    rw [st _ (by simp only [cTmp]; omega), if_neg (by omega),
      f1 _ (by simp only [rAd4]; omega) (by simp only [rKd]; omega)]

/-! ## The table realises the targets -/

theorem tabEnt6_length (sh : Shape) (p : ℕ) : (tabEnt6 sh p).length = 4 := by unfold tabEnt6; split <;> rfl

theorem tab6_length (sh : Shape) : (tab6 sh).length = 4 * (nCh6 sh + 1) := by
  have h : ∀ n : ℕ, ((List.range n).flatMap (tabEnt6 sh)).length = 4 * n := fun n => by
    rw [List.length_flatMap]
    simp only [tabEnt6_length, List.map_const', List.length_range, List.sum_replicate, smul_eq_mul]
    ring
  exact h _

theorem tab6_getD (sh : Shape) {p k : ℕ} (hp : p ≤ nCh6 sh) (hk : k < 4) :
    (tab6 sh).getD (4 * p + k) 0 = (tabEnt6 sh p).getD k 0 :=
  getD_flatMap4 (tabEnt6 sh) (tabEnt6_length sh) _ p k (by omega) hk

theorem msg6_ok (sh : Shape) (hok : ChainOK6 sh) {p : ℕ} (hp0 : 0 < p) (hpN : p < nCh6 sh) :
    (msg6 sh p).1 % 8 = 0 ∧ (msg6 sh p).2 % 8 = 0 ∧ (msg6 sh p).1 + (msg6 sh p).2 ≤ piLenOf sh ∧
      32 + (msg6 sh p).2 ≤ queryCap := by
  have hl : p - 1 < (msgs6 sh).length := by simp only [nCh6] at hpN; omega
  have h := List.all_eq_true.mp hok.msgs _ (List.getElem_mem hl)
  rw [msg6, List.getD_eq_getElem _ _ hl]
  simp only [msgOk6, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
  exact ⟨h.1.1.1, h.1.1.2, h.1.2, h.2⟩

theorem msg6_cap (sh : Shape) (hok : ChainOK6 sh) (p : ℕ) : 32 + (msg6 sh p).2 ≤ queryCap := by
  rw [msg6]
  by_cases h : p - 1 < (msgs6 sh).length
  · rw [List.getD_eq_getElem _ _ h]
    have h' := List.all_eq_true.mp hok.msgs _ (List.getElem_mem h)
    simp only [msgOk6, Bool.and_eq_true, decide_eq_true_eq] at h'
    exact h'.2
  · rw [List.getD_eq_default _ _ (by omega)]; decide

theorem fsQ6_data (sh : Shape) {π : Proof} (p : ℕ) (hp0 : 0 < p) (d : Digest) :
    (fsQ6 sh π p d).data.toList =
      d.toList ++ (π.extract (msg6 sh p).1 ((msg6 sh p).1 + (msg6 sh p).2)).data.toList := by
  rw [fsQ6, if_neg (by omega), ByteArray.data_append, Array.toList_append]
  rfl

/-- Every query after `q₀` carries its state. -/
theorem stateIn_fsQ6 (sh : Shape) (hok : ChainOK6 sh) (π : Proof) {p : ℕ} (hp0 : 0 < p) (d : Digest) :
    stateIn (fsQ6 sh π p d) = some d := by
  have hc := msg6_cap sh hok p
  have hd := fsQ6_data sh (π := π) p hp0 d
  have hz : (fsQ6 sh π p d).size = 32 + (π.extract (msg6 sh p).1 ((msg6 sh p).1 + (msg6 sh p).2)).size := by
    rw [fsQ6, if_neg (by omega), ByteArray.size_append, digestBytes_size]
  generalize msg6 sh p = m at hc hd hz
  have he : (π.extract m.1 (m.1 + m.2)).size ≤ m.2 := by
    rw [ByteArray.size_extract]; omega
  generalize fsQ6 sh π p d = q at hd hz ⊢
  generalize π.extract m.1 (m.1 + m.2) = x at hd hz he
  have hl : q.data.toList.length = q.size := Array.length_toList
  rw [stateIn, if_pos ⟨by omega, by omega⟩]
  refine congrArg some (Vector.ext fun i hi => ?_)
  rw [Vector.getElem_ofFn, List.getD_eq_getElem _ _ (by omega), List.getElem_of_eq hd,
    List.getElem_append_left (by simp; omega), Vector.getElem_toList]

/-- **The table realises the chain's targets** on every proof of the shape's size. -/
theorem tabW6 (sh : Shape) (hok : ChainOK6 sh) (c : Digest) (π : Proof) (L : Log) (hs : π.size = piLenOf sh) :
    TabW (extractorInput c π L).toArray (fsQ6 sh π) (nCh6 sh) (tab6 sh) := by
  have hpz := hok.pz
  refine ⟨tab6_length sh, fun p hp0 hpN => ⟨?_, fun hpN' d => ?_⟩⟩
  · rw [tab6_getD sh hpN (by norm_num), tabEnt6, if_neg (by omega)]
    show (toWord (5 + (msg6 sh p).1 / 8)).toNat < 2 ^ 62
    have : (msg6 sh p).1 ≤ piLenOf sh := by
      by_cases hp : p < nCh6 sh
      · have := (msg6_ok sh hok hp0 hp).2.2.1; omega
      · have hp' : p - 1 = (msgs6 sh).length := by simp only [nCh6] at hp hpN; omega
        rw [msg6, List.getD_eq_default _ _ (by omega)]; exact Nat.zero_le _
    generalize msg6 sh p = m at this
    rw [toNat_toWord (by omega)]; omega
  · obtain ⟨ho, hl, hol, hq⟩ := msg6_ok sh hok hp0 hpN'
    have e0 := tab6_getD sh hpN (k := 0) (by norm_num)
    have e1 := tab6_getD sh hpN (k := 1) (by norm_num)
    rw [Nat.add_zero] at e0
    rw [e0, e1, tabEnt6, if_neg (by omega)]
    have hz : (fsQ6 sh π p d).size = 32 + (msg6 sh p).2 := by
      rw [fsQ6, if_neg (by omega), ByteArray.size_append, extract_size π (by omega), digestBytes_size]
    refine ⟨by rw [hz]; rfl, by rw [hz]; omega, fun j hj => ?_⟩
    rw [hz] at hj
    rw [fsQ6_data sh p hp0, packBytes_appendK _ _ (k := 4) (by simp)]
    show _ = if j < 4 then _ else (extractorInput c π L).toArray.getD
      ((toWord (5 + (msg6 sh p).1 / 8)).toNat + (j - 4)) 0
    split_ifs with h4
    · rfl
    · generalize msg6 sh p = m at ho hl hol hj ⊢
      obtain ⟨a, ha⟩ : ∃ a, m.1 = 8 * a := ⟨m.1 / 8, by omega⟩
      obtain ⟨n, hn⟩ : ∃ n, m.2 = 8 * n := ⟨m.2 / 8, by omega⟩
      rw [ha, hn] at hol ⊢
      rw [hn] at hj
      rw [toNat_toWord (by omega), getD_toArray,
        show 5 + 8 * a / 8 + (j - 4) = 5 + (a + (j - 4)) by omega,
        tape_getD_proof c π L (by rw [hs]; omega), ← List.getD_eq_getElem _ 0,
        extract_words π (by rw [hs]; omega) (by omega)]

/-! ## The scan at a shape -/

/-- **`chain6_sem`**: on a proof of the shape's size and a log with no state hit, the scan's answers at
`ansB + 4p` are the first-match chain's; the heap outside `[chB, chEnd)` is kept. -/
theorem chain6_sem (sh : Shape) (hok : ChainOK6 sh) (c : Digest) (π : Proof) (L : Log)
    (hs : π.size = piLenOf sh) (hq : ∀ e ∈ L, e.1.size < 2 ^ 64) (ht : (extractorInput c π L).length ≤ 2 ^ 64)
    (hS : ¬ StateHit L) (s : St) (hM : Inv s.M) (hsz : chEnd ≤ s.M.size) :
    (∀ p < nCh6 sh, ∀ a, fmAns (fsQ6 sh π) zeroDL L p = some a → ∀ m < 4,
      rd (semXIR (extractorInput c π L).toArray (chain6 sh) s).M (ansB + 4 * p + m) =
        (packBytes a.toList).getD m 0) ∧
    (∀ y, regs ≤ y → (y < chB ∨ chEnd ≤ y) →
      rd (semXIR (extractorInput c π L).toArray (chain6 sh) s).M y = rd s.M y) := by
  have hT : ∀ p d, 0 < p → stateIn (fsQ6 sh π p d) = some d := fun p d hp0 => stateIn_fsQ6 sh hok π hp0 d
  obtain ⟨-, hans, hheap⟩ := chainIR_sem (pL := posL (piLenOf sh)) c π L (hs_posL hs) hq ht (N := nCh6 sh)
    hok.nCh (tabW6 sh hok c π L hs) (seedOK_sd6 _) (st₀ := zeroDL) (by rw [fsQ6, if_pos rfl]; rfl) s hM hsz
  refine ⟨fun p hpN a ha m hm => ?_, hheap⟩
  have hsc := scanC_answers (N := nCh6 sh) (st₀ := zeroDL) hT hS hpN
  rw [ha] at hsc
  have hlen := (scanC_fm (N := nCh6 sh) (st₀ := zeroDL) (L := L) (T := fsQ6 sh π) hT hS).1
  have hpl : p < (scanC (fsQ6 sh π) (nCh6 sh) zeroDL L).1 := by
    rw [← hlen]; exact (List.getElem?_eq_some_iff.mp hsc).1
  have hg : (scanC (fsQ6 sh π) (nCh6 sh) zeroDL L).2.2.getD p default = a := by
    rw [List.getD_eq_getElem?_getD, hsc, Option.getD_some]
  rw [chain6, hans p hpl m hm, hg]

theorem cost_sd6 (t : ℕ) : cost sd6 t = 8 := rfl

/-- **The chain's exact cost.** -/
theorem cost_chain6 (sh : Shape) (t : ℕ) :
    cost (chain6 sh) t = 34 + 36 * (nCh6 sh + 1) + cost sd6 t + t / 5 * 24 + t * 168 := by
  rw [chain6, cost_chainIR, tab6_length]; ring

/-! ## `P18` -/

/-! ## `P17` (PORT17 X1; over L1's schedule memo) -/

/-- **The chain's static facts at `P17`.** -/
theorem chainOK6_P17 : ChainOK6 P17 := by
  refine ⟨?_, ?_, ?_⟩
  · unfold msgs6 msgOk6; rw [piLen_P17, sched6_P17_eq]; decide +kernel
  · unfold nCh6 msgs6; rw [sched6_P17_eq]; decide +kernel
  · rw [piLen_P17]; decide

/-- The chain has 1,055 targets at `P17`. -/
theorem nCh6_P17 : nCh6 P17 = 1055 := by
  unfold nCh6 msgs6; rw [sched6_P17_eq]; decide +kernel

theorem contig6_P17 : contigAux (sched6 P17) 0 = true := by rw [sched6_P17_eq]; decide +kernel

end Lvm6.X
