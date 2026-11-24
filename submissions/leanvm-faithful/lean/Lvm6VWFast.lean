-- New for lvm6 (WP-VW): a byte-level twin of the witness-sending branch of `Vwith`, proved equal to it.
import LvmVerifier

/-!
# The `W` branch at byte level (`VwithT`)

`Vwith`'s `W` branch decodes `π` through the Library's word-level decoder (`decodeF`: bytes to
64-bit words, then the reader monad) and re-encodes the witness (`encodeF`: words back to bytes)
to compare it with `π`. Both go through `Word = BitVec 64` and `Nat` arithmetic per byte, about
0.4 µs a byte compiled, and every level of a node re-runs them on its child's bytes: at the smoke
shape (`M = 4`, `n = 6`) the final `W` proof (29,800 bytes, three nested levels) took 52 ms pinned
on an idle core and 90–227 ms in the harness under load (VW.md).

Here the same decision reads `π` once, strictly, at byte offsets (`ByteArray.extract`, `ofLE` of 8
bytes for a number, 32 bytes for a digest, zero padding checked):

* `pNat`, `pDig`, `pStr`, `pList`, `pCnt`, `pPair`, `pMap`, `pWit`: parsers `ByteArray → offset →
  Option (value × offset)`; **`Cod p e F`**: `p` reads exactly the bytes `e x` of a value `x` with
  `F x` (`sound`), and reads every such encoding back (`compl`);
* `eWit_eq`: the parsers' encoding of a witness is `encode`'s bytes (`wordsBytes (witWords w)`);
* `fits_of_decode`: a decoded witness fits the format (`Wit.Fits`);
* **`pW_iff`**: `pW π = some w ↔ decode π = some w ∧ encode w = π`;
* **`VwithT`**, **`VwithT_eq : VwithT VS = Vwith VS`** for every `VS`.
-/

set_option autoImplicit false

namespace Lvm6.VTw

open RecursionFast Lvm.T
open RecursionFast.WitnessSending (encode decode encodeF decodeF encodeF_eq decodeF_eq decode_encode
  size_child_lt)

/-! ## Byte positions -/

/-- The bytes of `π` from offset `o`. -/
def tl (π : ByteArray) (o : Nat) : List UInt8 := π.data.toList.drop o

theorem tl_length (π : ByteArray) (o : Nat) : (tl π o).length = π.size - o := by
  simp [tl, ← ByteArray.size_data]

theorem tl_add (π : ByteArray) (o k : Nat) : tl π (o + k) = (tl π o).drop k := by
  simp only [tl, List.drop_drop]

theorem tl_size (π : ByteArray) : tl π π.size = [] := by
  simp [tl, ← ByteArray.size_data]

/-- `k` bytes of `π` at `o` (fewer at the end). -/
def rdL (π : ByteArray) (o k : Nat) : List UInt8 := (π.extract o (o + k)).data.toList

theorem rdL_eq (π : ByteArray) (o k : Nat) : rdL π o k = (tl π o).take k := by
  simp [rdL, tl]

/-! ## Codecs -/

/-- A parser at a byte offset. -/
abbrev Pr (α : Type) : Type := ByteArray → Nat → Option (α × Nat)

/-- **`p` is a strict parser of the encoding `e`** for the values with `F`: what it reads is the
encoding of a value with `F` (`sound`), and it reads every such encoding (`compl`). -/
structure Cod {α : Type} (p : Pr α) (e : α → List UInt8) (F : α → Prop) : Prop where
  sound : ∀ π o x o', p π o = some (x, o') → F x ∧ tl π o = e x ++ tl π o'
  compl : ∀ π o x rest, F x → tl π o = e x ++ rest → p π o = some (x, o + (e x).length)

/-- Two parsers in turn. -/
@[inline] def pPair {α β : Type} (p : Pr α) (q : Pr β) : Pr (α × β) := fun π o =>
  match p π o with
  | some (a, o₁) =>
    match q π o₁ with
    | some (b, o₂) => some ((a, b), o₂)
    | none => none
  | none => none

theorem cod_pair {α β : Type} {p : Pr α} {q : Pr β} {e : α → List UInt8} {e' : β → List UInt8}
    {F : α → Prop} {G : β → Prop} (hp : Cod p e F) (hq : Cod q e' G) :
    Cod (pPair p q) (fun x => e x.1 ++ e' x.2) (fun x => F x.1 ∧ G x.2) where
  sound π o x o' h := by
    unfold pPair at h
    rcases h1 : p π o with _ | ⟨a, o₁⟩ <;> rw [h1] at h <;> dsimp only at h
    · cases h
    · rcases h2 : q π o₁ with _ | ⟨b, o₂⟩ <;> rw [h2] at h <;> dsimp only at h
      · cases h
      · cases h
        obtain ⟨ha, ea⟩ := hp.sound _ _ _ _ h1
        obtain ⟨hb, eb⟩ := hq.sound _ _ _ _ h2
        exact ⟨⟨ha, hb⟩, by rw [ea, eb, List.append_assoc]⟩
  compl π o x rest hx h := by
    unfold pPair
    rw [hp.compl π o x.1 (e' x.2 ++ rest) hx.1 (by rw [h, List.append_assoc])]
    dsimp only
    have h2 : tl π (o + (e x.1).length) = e' x.2 ++ rest := by
      rw [tl_add, h, List.append_assoc, List.drop_left]
    rw [hq.compl π _ x.2 rest hx.2 h2]
    simp [Nat.add_assoc]

/-- A parser's value mapped. -/
@[inline] def pMap {α β : Type} (f : α → β) (p : Pr α) : Pr β := fun π o =>
  match p π o with
  | some (a, o₁) => some (f a, o₁)
  | none => none

theorem cod_map {α β : Type} {p : Pr α} {e : α → List UInt8} {F : α → Prop} (hp : Cod p e F)
    (f : α → β) (g : β → α) (G : β → Prop) (hgf : ∀ a, F a → g (f a) = a)
    (hfg : ∀ b, G b → f (g b) = b) (hGF : ∀ a, F a → G (f a)) (hFG : ∀ b, G b → F (g b)) :
    Cod (pMap f p) (fun b => e (g b)) G where
  sound π o x o' h := by
    unfold pMap at h
    rcases h1 : p π o with _ | ⟨a, o₁⟩ <;> rw [h1] at h <;> dsimp only at h
    · cases h
    · cases h
      obtain ⟨ha, ea⟩ := hp.sound _ _ _ _ h1
      exact ⟨hGF a ha, by rw [hgf a ha]; exact ea⟩
  compl π o x rest hx h := by
    unfold pMap
    rw [hp.compl π o (g x) rest (hFG x hx) h]
    dsimp only
    rw [hfg x hx]

/-- `n` values in turn. -/
def pList {α : Type} (p : Pr α) : Nat → Pr (List α)
  | 0 => fun _ o => some ([], o)
  | n + 1 => fun π o =>
    match p π o with
    | some (a, o₁) =>
      match pList p n π o₁ with
      | some (as, o₂) => some (a :: as, o₂)
      | none => none
    | none => none

theorem cod_pList {α : Type} {p : Pr α} {e : α → List UInt8} {F : α → Prop} (hp : Cod p e F) :
    ∀ n, Cod (pList p n) (fun xs => xs.flatMap e) (fun xs => xs.length = n ∧ ∀ x ∈ xs, F x)
  | 0 => {
      sound := fun π o x o' h => by
        simp only [pList, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        simp
      compl := fun π o x rest hx _ => by
        obtain ⟨hl, -⟩ := hx
        rw [List.length_eq_zero_iff] at hl
        subst hl
        simp [pList] }
  | n + 1 => {
      sound := fun π o x o' h => by
        simp only [pList] at h
        rcases h1 : p π o with _ | ⟨a, o₁⟩ <;> rw [h1] at h <;> dsimp only at h
        · cases h
        · rcases h2 : pList p n π o₁ with _ | ⟨as, o₂⟩ <;> rw [h2] at h <;> dsimp only at h
          · cases h
          · cases h
            obtain ⟨ha, ea⟩ := hp.sound _ _ _ _ h1
            obtain ⟨⟨hl, has⟩, eas⟩ := (cod_pList hp n).sound _ _ _ _ h2
            refine ⟨⟨by simp [hl], ?_⟩, by rw [ea, eas]; simp⟩
            intro x hx
            rcases List.mem_cons.1 hx with rfl | hx
            · exact ha
            · exact has x hx
      compl := fun π o x rest hx h => by
        obtain ⟨hl, hF⟩ := hx
        match x, hl, hF, h with
        | a :: as, hl, hF, h =>
          simp only [pList]
          simp only [List.flatMap_cons, List.append_assoc] at h
          rw [hp.compl π o a _ (hF a (List.mem_cons_self ..)) h]
          dsimp only
          have h2 : tl π (o + (e a).length) = as.flatMap e ++ rest := by
            rw [tl_add, h, List.drop_left]
          rw [(cod_pList hp n).compl π _ as rest
            ⟨by simpa using hl, fun y hy => hF y (List.mem_cons_of_mem _ hy)⟩ h2]
          simp [Nat.add_assoc] }

/-! ## Numbers, digests, byte strings -/

/-- A number's encoding: its word's 8 bytes. -/
def eN (n : Nat) : List UInt8 := wordBytes (toWord n)

theorem eN_length (n : Nat) : (eN n).length = 8 := wordBytes_length _

theorem enc64_ofLE {l : List UInt8} (h : l.length = 8) : enc64 (ofLE l) = l := by
  apply List.ext_getElem (by rw [enc64_length, h])
  intro i h1 h2
  simp only [enc64, List.getElem_ofFn]
  rw [← toUInt8_mod, ofLE_div_mod, List.getD_eq_getElem _ _ h2]
  simp

theorem ofLE_lt64 {l : List UInt8} (h : l.length = 8) : ofLE l < 2 ^ 64 := by
  have := ofLE_lt l
  rw [h] at this
  norm_num at this ⊢
  exact this

theorem eN_ofLE {l : List UInt8} (h : l.length = 8) : eN (ofLE l) = l := by
  rw [eN, wordBytes, toNat_toWord (ofLE_lt64 h), enc64_ofLE h]

/-- A number: 8 bytes, little-endian. -/
def pNat : Pr Nat := fun π o => if o + 8 ≤ π.size then some (ofLE (rdL π o 8), o + 8) else none

theorem cod_pNat : Cod pNat eN (· < 2 ^ 64) where
  sound π o x o' h := by
    unfold pNat at h
    split at h
    · next hle =>
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      have hl : ((tl π o).take 8).length = 8 := by
        rw [List.length_take, tl_length]; omega
      rw [rdL_eq]
      exact ⟨ofLE_lt64 hl, by rw [eN_ofLE hl, tl_add, List.take_append_drop]⟩
    · cases h
  compl π o x rest hx h := by
    have hlen := congrArg List.length h
    rw [List.length_append, eN_length, tl_length] at hlen
    unfold pNat
    rw [if_pos (by omega), rdL_eq, h, List.take_left' (eN_length x), eN_length, eN, ofLE_wordBytes,
      toNat_toWord hx]

/-- A digest's encoding: its 32 bytes. -/
def eD (d : Digest) : List UInt8 := d.toList

/-- A digest: 32 bytes. -/
def pDig : Pr Digest := fun π o =>
  if h : (π.extract o (o + 32)).data.size = 32 then some (⟨(π.extract o (o + 32)).data, h⟩, o + 32)
  else none

theorem cod_pDig : Cod pDig eD (fun _ => True) where
  sound π o x o' h := by
    unfold pDig at h
    split at h
    · next hs =>
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      refine ⟨trivial, ?_⟩
      have ht : (π.extract o (o + 32)).data.toList = (tl π o).take 32 := rdL_eq π o 32
      rw [eD, Vector.toList_mk, ht, tl_add, List.take_append_drop]
    · cases h
  compl π o x rest _ h := by
    have hlen := congrArg List.length h
    rw [List.length_append, eD, Vector.length_toList, tl_length] at hlen
    have ht : (π.extract o (o + 32)).data.toList = x.toList := by
      rw [show (π.extract o (o + 32)).data.toList = rdL π o 32 from rfl, rdL_eq, h, eD,
        List.take_left' (by simp)]
    have hs : (π.extract o (o + 32)).data.size = 32 := by
      rw [← Array.length_toList, ht, Vector.length_toList]
    unfold pDig
    rw [dif_pos hs]
    have hx : (⟨(π.extract o (o + 32)).data, hs⟩ : Digest) = x := by
      apply Vector.toArray_inj.1
      apply Array.toList_inj.1
      rw [ht]
      rfl
    rw [hx, eD, Vector.length_toList]

/-- The bytes a byte string of length `n` occupies: whole words. -/
def pad8 (n : Nat) : Nat := 8 * ((n + 7) / 8)

theorem le_pad8 (n : Nat) : n ≤ pad8 n := by unfold pad8; omega

/-- A byte string's bytes, zero-padded to whole words. -/
def eB (b : List UInt8) : List UInt8 := b ++ List.replicate (pad8 b.length - b.length) 0

/-- A byte string's encoding: its length, then its bytes padded. -/
def eS (b : ByteArray) : List UInt8 := eN b.size ++ eB b.data.toList

/-- `k` zero bytes at `o`. -/
def zeros (π : ByteArray) (o k : Nat) : Bool := (rdL π o k).all (· == 0)

/-- A byte string: its length, its bytes, zero padding to whole words. -/
def pStr : Pr ByteArray := fun π o =>
  match pNat π o with
  | some (n, o₁) =>
    if o₁ + pad8 n ≤ π.size && zeros π (o₁ + n) (pad8 n - n) then
      some (π.extract o₁ (o₁ + n), o₁ + pad8 n)
    else none
  | none => none

theorem tl_split (π : ByteArray) (o k : Nat) : tl π o = (tl π o).take k ++ tl π (o + k) := by
  rw [tl_add, List.take_append_drop]

theorem len_data (b : ByteArray) : b.data.toList.length = b.size := by
  simp [← ByteArray.size_data]

theorem cod_pStr : Cod pStr eS (fun b => b.size < 2 ^ 64) where
  sound π o x o' h := by
    unfold pStr at h
    rcases h1 : pNat π o with _ | ⟨n, o₁⟩ <;> rw [h1] at h <;> dsimp only at h
    · cases h
    · obtain ⟨hn, en⟩ := cod_pNat.sound _ _ _ _ h1
      split at h
      · next hc =>
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
        obtain ⟨hle, hz⟩ := hc
        have hp := le_pad8 n
        have hl1 := tl_length π o₁
        have hb : (π.extract o₁ (o₁ + n)).data.toList = (tl π o₁).take n := rdL_eq π o₁ n
        have hbl : (π.extract o₁ (o₁ + n)).data.toList.length = n := by
          rw [hb, List.length_take, tl_length]; omega
        have hsz : (π.extract o₁ (o₁ + n)).size = n := by rw [← len_data, hbl]
        have hzl : (tl π (o₁ + n)).take (pad8 n - n) = List.replicate (pad8 n - n) 0 := by
          rw [List.eq_replicate_iff]
          refine ⟨by rw [List.length_take, tl_length]; omega, fun b hb' => ?_⟩
          unfold zeros at hz
          rw [rdL_eq, List.all_eq_true] at hz
          simpa using hz b hb'
        refine ⟨by rw [hsz]; exact hn, ?_⟩
        rw [en, eS, eB, hsz, hbl, tl_split π o₁ n, ← hb, tl_split π (o₁ + n) (pad8 n - n), hzl,
          show o₁ + n + (pad8 n - n) = o₁ + pad8 n by omega]
        simp only [List.append_assoc]
      · cases h
  compl π o x rest hx h := by
    have hp := le_pad8 x.size
    rw [eS, eB, len_data, List.append_assoc] at h
    have h1 := cod_pNat.compl π o x.size _ hx h
    rw [eN_length] at h1
    have hlen0 := congrArg List.length h
    simp only [tl_length, List.length_append, List.length_replicate, len_data, eN_length] at hlen0
    have h2 : tl π (o + 8) = x.data.toList ++ (List.replicate (pad8 x.size - x.size) 0 ++ rest) := by
      rw [tl_add, h, List.drop_left' (eN_length _), List.append_assoc]
    have hlen := congrArg List.length h2
    simp only [tl_length, List.length_append, List.length_replicate, len_data] at hlen
    have h3 : tl π (o + 8 + x.size) = List.replicate (pad8 x.size - x.size) 0 ++ rest := by
      rw [tl_add, h2, List.drop_left' (len_data x)]
    have hz : zeros π (o + 8 + x.size) (pad8 x.size - x.size) = true := by
      unfold zeros
      rw [rdL_eq, h3, List.take_left' (List.length_replicate ..), List.all_eq_true]
      intro b hb
      rw [List.eq_of_mem_replicate hb]
      rfl
    have hx' : π.extract (o + 8) (o + 8 + x.size) = x := by
      apply ByteArray.ext
      apply Array.toList_inj.1
      rw [show (π.extract (o + 8) (o + 8 + x.size)).data.toList = rdL π (o + 8) x.size from rfl,
        rdL_eq, h2, List.take_left' (len_data x)]
    unfold pStr
    rw [h1]
    dsimp only
    have hc : (decide (o + 8 + pad8 x.size ≤ π.size) &&
        zeros π (o + 8 + x.size) (pad8 x.size - x.size)) = true := by
      simp only [Bool.and_eq_true, decide_eq_true_eq]
      exact ⟨by omega, hz⟩
    rw [if_pos hc, hx']
    simp only [eS, eB, List.length_append, eN_length, len_data, List.length_replicate,
      Option.some.injEq, Prod.mk.injEq, true_and]
    omega

/-- A count, then that many values. -/
@[inline] def pCnt {α : Type} (p : Pr α) : Pr (List α) := fun π o =>
  match pNat π o with
  | some (n, o₁) => pList p n π o₁
  | none => none

theorem cod_pCnt {α : Type} {p : Pr α} {e : α → List UInt8} {F : α → Prop} (hp : Cod p e F) :
    Cod (pCnt p) (fun xs => eN xs.length ++ xs.flatMap e)
      (fun xs => xs.length < 2 ^ 64 ∧ ∀ x ∈ xs, F x) where
  sound π o x o' h := by
    unfold pCnt at h
    rcases h1 : pNat π o with _ | ⟨n, o₁⟩ <;> rw [h1] at h <;> dsimp only at h
    · cases h
    · obtain ⟨hn, en⟩ := cod_pNat.sound _ _ _ _ h1
      obtain ⟨⟨hl, hF⟩, el⟩ := (cod_pList hp n).sound _ _ _ _ h
      exact ⟨⟨by rw [hl]; exact hn, hF⟩, by rw [en, el, hl, List.append_assoc]⟩
  compl π o x rest hx h := by
    rw [List.append_assoc] at h
    have h1 := cod_pNat.compl π o x.length _ hx.1 h
    have h2 : tl π (o + (eN x.length).length) = x.flatMap e ++ rest := by
      rw [tl_add, h, List.drop_left]
    unfold pCnt
    rw [h1]
    dsimp only
    rw [(cod_pList hp x.length).compl π _ x rest ⟨rfl, hx.2⟩ h2]
    simp [Nat.add_assoc]

/-! ## Entries, traces, signatures, signed proofs, witnesses -/

/-- A trace entry's encoding. -/
def eE (x : ByteArray × Digest) : List UInt8 := eS x.1 ++ eD x.2

/-- A trace's encoding. -/
def eT (tr : Trace) : List UInt8 := eN tr.length ++ tr.flatMap eE

/-- A signature's encoding. -/
def eSig (σ : Sig) : List UInt8 := eN σ.idx ++ (σ.ots.flatMap eD ++ σ.path.flatMap eD)

/-- A signed proof's encoding. -/
def eSg (p : Signed) : List UInt8 := eS p.π ++ (eT p.tr ++ eSig p.σ)

/-- A witness's encoding. -/
def eWit : Wit → List UInt8
  | .leaf xs => eN 0 ++ (eN xs.length ++ xs.flatMap eD)
  | .node c₁ c₂ p₁ p₂ => eN 1 ++ (eD c₁ ++ (eD c₂ ++ (eSg p₁ ++ eSg p₂)))

/-- A trace entry. -/
def pEntry : Pr (ByteArray × Digest) := pPair pStr pDig

theorem cod_pEntry : Cod pEntry eE (fun x => x.1.size < 2 ^ 64 ∧ True) := cod_pair cod_pStr cod_pDig

/-- A trace. -/
def pTrace : Pr Trace := pCnt pEntry

theorem cod_pTrace : Cod pTrace eT (fun tr => tr.length < 2 ^ 64 ∧ ∀ x ∈ tr, x.1.size < 2 ^ 64 ∧ True) :=
  cod_pCnt cod_pEntry

/-- A signature. -/
def pSig : Pr Sig :=
  pMap (fun x : Nat × List Digest × List Digest => (⟨x.1, x.2.1, x.2.2⟩ : Sig)) (pPair pNat (pPair (pList pDig wotsLen) (pList pDig sigHeight)))

/-- What a signature fits. -/
def SigF (σ : Sig) : Prop := σ.idx < 2 ^ 64 ∧ σ.ots.length = wotsLen ∧ σ.path.length = sigHeight

theorem cod_pSig : Cod pSig eSig SigF :=
  cod_map (cod_pair cod_pNat (cod_pair (cod_pList cod_pDig wotsLen) (cod_pList cod_pDig sigHeight)))
    (fun x : Nat × List Digest × List Digest => (⟨x.1, x.2.1, x.2.2⟩ : Sig))
    (fun σ : Sig => (σ.idx, σ.ots, σ.path)) SigF (fun _ _ => rfl) (fun _ _ => rfl)
    (fun _ h => ⟨h.1, h.2.1.1, h.2.2.1⟩) (fun _ h => ⟨h.1, ⟨h.2.1, by simp⟩, ⟨h.2.2, by simp⟩⟩)

/-- A signed proof. -/
def pSigned : Pr Signed :=
  pMap (fun x : ByteArray × Trace × Sig => (⟨x.1, x.2.1, x.2.2⟩ : Signed)) (pPair pStr (pPair pTrace pSig))

theorem cod_pSigned : Cod pSigned eSg Signed.Fits :=
  cod_map (cod_pair cod_pStr (cod_pair cod_pTrace cod_pSig))
    (fun x : ByteArray × Trace × Sig => (⟨x.1, x.2.1, x.2.2⟩ : Signed))
    (fun p : Signed => (p.π, p.tr, p.σ)) Signed.Fits (fun _ _ => rfl) (fun _ _ => rfl)
    (fun _ h => ⟨h.1, h.2.1.1, fun e he => (h.2.1.2 e he).1, h.2.2.1, h.2.2.2.1, h.2.2.2.2⟩)
    (fun _ h => ⟨h.1, ⟨h.2.1, fun e he => ⟨h.2.2.1 e he, trivial⟩⟩, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2⟩)

/-- A node's fields after its tag. -/
def pNodeF : Pr (Digest × Digest × Signed × Signed) := pPair pDig (pPair pDig (pPair pSigned pSigned))

theorem cod_pNodeF : Cod pNodeF (fun x => eD x.1 ++ (eD x.2.1 ++ (eSg x.2.2.1 ++ eSg x.2.2.2)))
    (fun x => True ∧ True ∧ x.2.2.1.Fits ∧ x.2.2.2.Fits) :=
  cod_pair cod_pDig (cod_pair cod_pDig (cod_pair cod_pSigned cod_pSigned))

/-- **A witness**: tag `0`, a count and the leaf's digests; or tag `1`, two digests and two signed
proofs. -/
def pWit : Pr Wit := fun π o =>
  match pNat π o with
  | some (t, o₁) =>
    if t = 0 then
      match pCnt pDig π o₁ with
      | some (xs, o₂) => some (.leaf xs, o₂)
      | none => none
    else if t = 1 then
      match pNodeF π o₁ with
      | some (x, o₂) => some (.node x.1 x.2.1 x.2.2.1 x.2.2.2, o₂)
      | none => none
    else none
  | none => none

theorem cod_pWit : Cod pWit eWit Wit.Fits where
  sound π o x o' h := by
    unfold pWit at h
    rcases h1 : pNat π o with _ | ⟨t, o₁⟩ <;> rw [h1] at h <;> dsimp only at h
    · cases h
    · obtain ⟨-, en⟩ := cod_pNat.sound _ _ _ _ h1
      split_ifs at h with ht0 ht1
      · subst ht0
        rcases h2 : pCnt pDig π o₁ with _ | ⟨xs, o₂⟩ <;> rw [h2] at h <;> dsimp only at h
        · cases h
        · cases h
          obtain ⟨⟨hl, -⟩, el⟩ := (cod_pCnt cod_pDig).sound _ _ _ _ h2
          exact ⟨hl, by rw [en, el, eWit]; simp only [List.append_assoc]⟩
      · subst ht1
        rcases h2 : pNodeF π o₁ with _ | ⟨y, o₂⟩ <;> rw [h2] at h <;> dsimp only at h
        · cases h
        · cases h
          obtain ⟨⟨-, -, f1, f2⟩, el⟩ := cod_pNodeF.sound _ _ _ _ h2
          exact ⟨⟨f1, f2⟩, by rw [en, el, eWit]; simp only [List.append_assoc]⟩
  compl π o x rest hx h := by
    cases x with
    | leaf xs =>
      simp only [eWit, List.append_assoc] at h
      have h1 := cod_pNat.compl π o 0 _ (by norm_num) h
      rw [eN_length] at h1
      have h2 : tl π (o + 8) = (eN xs.length ++ xs.flatMap eD) ++ rest := by
        rw [tl_add, h, List.drop_left' (eN_length 0), List.append_assoc]
      have h3 := (cod_pCnt cod_pDig).compl π _ xs rest ⟨hx, fun _ _ => trivial⟩ h2
      unfold pWit
      rw [h1]
      dsimp only
      rw [if_pos rfl, h3]
      dsimp only
      simp only [eWit, List.length_append, eN_length, Option.some.injEq, Prod.mk.injEq, true_and]
      omega
    | node c₁ c₂ p₁ p₂ =>
      simp only [eWit, List.append_assoc] at h
      have h1 := cod_pNat.compl π o 1 _ (by norm_num) h
      rw [eN_length] at h1
      have h2 : tl π (o + 8) = (eD c₁ ++ (eD c₂ ++ (eSg p₁ ++ eSg p₂))) ++ rest := by
        rw [tl_add, h, List.drop_left' (eN_length 1)]
        simp only [List.append_assoc]
      have h3 := cod_pNodeF.compl π _ (c₁, c₂, p₁, p₂) rest ⟨trivial, trivial, hx.1, hx.2⟩ h2
      unfold pWit
      rw [h1]
      dsimp only
      rw [if_neg (by norm_num), if_pos rfl, h3]
      dsimp only
      simp only [eWit, List.length_append, eN_length, Option.some.injEq, Prod.mk.injEq, true_and]
      omega

/-! ## The encoding is `encode`'s -/

theorem wordsBytes_cons (w : Word) (ws : List Word) :
    wordsBytes (w :: ws) = wordBytes w ++ wordsBytes ws := List.flatMap_cons ..

theorem wordsBytes_append (a b : List Word) : wordsBytes (a ++ b) = wordsBytes a ++ wordsBytes b :=
  List.flatMap_append ..

theorem wordsBytes_flatMap {α : Type} (xs : List α) (f : α → List Word) :
    wordsBytes (xs.flatMap f) = xs.flatMap fun x => wordsBytes (f x) := List.flatMap_assoc ..

theorem wordsBytes_packBytes (b : List UInt8) : wordsBytes (packBytes b) = eB b := by
  apply List.ext_getElem
  · rw [wordsBytes_length, packBytes_length, eB, List.length_append, List.length_replicate, pad8]
    omega
  · intro i h1 h2
    rw [← List.getD_eq_getElem _ 0 h1, ← List.getD_eq_getElem _ 0 h2, ← wordByte_eq_getD,
      wordByte_packBytes, eB]
    by_cases hi : i < b.length
    · rw [List.getD_append _ _ _ _ hi]
    · rw [List.getD_append_right _ _ _ _ (by omega), List.getD_eq_default _ _ (by omega)]
      simp only [List.getD_eq_getElem?_getD, List.getElem?_replicate]
      split <;> rfl

theorem eB_digest (d : Digest) : eB d.toList = d.toList := by
  simp [eB, pad8]

theorem wordsBytes_digest (d : Digest) : wordsBytes (packBytes d.toList) = eD d := by
  rw [wordsBytes_packBytes, eB_digest, eD]

theorem wordsBytes_bytes (b : ByteArray) : wordsBytes (bytesWords b.data.toList) = eS b := by
  rw [bytesWords, wordsBytes_cons, wordsBytes_packBytes, eS, len_data]
  rfl

theorem wordsBytes_signed (p : Signed) : wordsBytes (signedWords p) = eSg p := by
  simp only [signedWords, logWords, sigWords, wordsBytes_append, wordsBytes_cons, wordsBytes_flatMap,
    wordsBytes_bytes, wordsBytes_digest, eSg, eT, eSig, eE, List.append_assoc]
  rfl

/-- **The parsers' encoding of a witness is `encode`'s bytes.** -/
theorem eWit_eq (w : Wit) : (encode w).data.toList = eWit w := by
  rw [WitnessSending.encode_data]
  cases w with
  | leaf xs =>
    simp only [witWords, wordsBytes_cons, wordsBytes_flatMap, wordsBytes_digest, eWit]
    rfl
  | node c₁ c₂ p₁ p₂ =>
    simp only [witWords, List.cons_append, wordsBytes_cons, wordsBytes_append, wordsBytes_digest,
      wordsBytes_signed, eWit, List.append_assoc]
    rfl

/-! ## A decoded witness fits -/

theorem run_bind_some {α β : Type} {x : Reader α} {f : α → Reader β} {o : List Word} {b : β}
    {o' : List Word} (h : (x >>= f).run o = some (b, o')) :
    ∃ a o₁, x.run o = some (a, o₁) ∧ (f a).run o₁ = some (b, o') := by
  rw [StateT.run_bind] at h
  rcases h1 : x.run o with _ | ⟨a, o₁⟩ <;> rw [h1] at h
  · simp at h
  · exact ⟨a, o₁, rfl, h⟩

theorem run_pure_some {α : Type} {x b : α} {o o' : List Word}
    (h : (pure x : Reader α).run o = some (b, o')) : b = x ∧ o' = o := by
  simp only [StateT.run_pure, Option.pure_def, Option.some.injEq, Prod.mk.injEq] at h
  exact ⟨h.1.symm, h.2.symm⟩

theorem readNat_lt {o o' : List Word} {n : Nat} (h : readNat.run o = some (n, o')) : n < 2 ^ 64 := by
  cases o with
  | nil => simp [readNat, StateT.run] at h
  | cons w o =>
    simp only [readNat, StateT.run, Option.some.injEq, Prod.mk.injEq] at h
    rw [← h.1]
    exact w.isLt

theorem readBytes_len {o o' : List Word} {n : Nat} {b : List UInt8}
    (h : (readBytes n).run o = some (b, o')) : b.length = n := by
  simp only [readBytes, StateT.run] at h
  split at h
  · next hl =>
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    rw [← h.1, List.length_take, show List.flatMap wordBytes (o.take ((n + 7) / 8)) =
      wordsBytes (o.take ((n + 7) / 8)) from rfl, wordsBytes_length, hl]
    omega
  · cases h

theorem readString_lt {o o' : List Word} {b : ByteArray} (h : readString.run o = some (b, o')) :
    b.size < 2 ^ 64 := by
  unfold readString at h
  obtain ⟨n, o₁, h1, h⟩ := run_bind_some h
  obtain ⟨l, o₂, h2, h⟩ := run_bind_some h
  obtain ⟨rfl, -⟩ := run_pure_some h
  rw [← len_data]
  simp only [List.toList_toArray]
  rw [readBytes_len h2]
  exact readNat_lt h1

theorem readList_prop {α : Type} {r : Reader α} {P : α → Prop}
    (hr : ∀ o a o', r.run o = some (a, o') → P a) :
    ∀ n o xs o', (readList r n).run o = some (xs, o') → xs.length = n ∧ ∀ x ∈ xs, P x
  | 0, o, xs, o', h => by
    obtain ⟨rfl, -⟩ := run_pure_some h
    simp
  | n + 1, o, xs, o', h => by
    unfold readList at h
    obtain ⟨a, o₁, h1, h⟩ := run_bind_some h
    obtain ⟨as, o₂, h2, h⟩ := run_bind_some h
    obtain ⟨rfl, -⟩ := run_pure_some h
    obtain ⟨hl, hP⟩ := readList_prop hr n _ _ _ h2
    refine ⟨by simp [hl], fun x hx => ?_⟩
    rcases List.mem_cons.1 hx with rfl | hx
    · exact hr _ _ _ h1
    · exact hP x hx

theorem readSigned_fits {o o' : List Word} {p : Signed} (h : readSigned.run o = some (p, o')) :
    p.Fits := by
  unfold readSigned at h
  obtain ⟨b, o₁, h1, h⟩ := run_bind_some h
  obtain ⟨tr, o₂, h2, h⟩ := run_bind_some h
  obtain ⟨σ, o₃, h3, h⟩ := run_bind_some h
  obtain ⟨rfl, -⟩ := run_pure_some h
  unfold readTrace at h2
  obtain ⟨m, o₄, h4, h2⟩ := run_bind_some h2
  obtain ⟨hm, hq⟩ := readList_prop (P := fun e : ByteArray × Digest => e.1.size < 2 ^ 64)
    (fun o a o' ha => by
      unfold readEntry at ha
      obtain ⟨q, o₁, h1, ha⟩ := run_bind_some ha
      obtain ⟨d, o₂, -, ha⟩ := run_bind_some ha
      obtain ⟨rfl, -⟩ := run_pure_some ha
      exact readString_lt h1) _ _ _ _ h2
  unfold readSig at h3
  obtain ⟨i, o₅, h5, h3⟩ := run_bind_some h3
  obtain ⟨ots, o₆, h6, h3⟩ := run_bind_some h3
  obtain ⟨path, o₇, h7, h3⟩ := run_bind_some h3
  obtain ⟨rfl, -⟩ := run_pure_some h3
  exact ⟨readString_lt h1, by rw [hm]; exact readNat_lt h4, hq, readNat_lt h5,
    (readList_prop (P := fun _ => True) (fun _ _ _ _ => trivial) _ _ _ _ h6).1,
    (readList_prop (P := fun _ => True) (fun _ _ _ _ => trivial) _ _ _ _ h7).1⟩

theorem readWit_fits {o o' : List Word} {w : Wit} (h : readWit.run o = some (w, o')) : w.Fits := by
  unfold readWit at h
  obtain ⟨t, o₁, h1, h⟩ := run_bind_some h
  split at h
  · obtain ⟨n, o₂, h2, h⟩ := run_bind_some h
    obtain ⟨xs, o₃, h3, h⟩ := run_bind_some h
    obtain ⟨rfl, -⟩ := run_pure_some h
    show xs.length < 2 ^ 64
    rw [(readList_prop (P := fun _ => True) (fun _ _ _ _ => trivial) _ _ _ _ h3).1]
    exact readNat_lt h2
  · obtain ⟨c₁, o₂, -, h⟩ := run_bind_some h
    obtain ⟨c₂, o₃, -, h⟩ := run_bind_some h
    obtain ⟨p₁, o₄, h4, h⟩ := run_bind_some h
    obtain ⟨p₂, o₅, h5, h⟩ := run_bind_some h
    obtain ⟨rfl, -⟩ := run_pure_some h
    exact ⟨readSigned_fits h4, readSigned_fits h5⟩
  · first
      | cases h
      | exact absurd h (by simp [failure])

/-- **A decoded witness fits the format.** -/
theorem fits_of_decode {π : Proof} {w : Wit} (h : decode π = some w) : w.Fits := by
  replace h : Prod.fst <$> readWit.run (packBytes π.data.toList) = some w := h
  rcases h1 : readWit.run (packBytes π.data.toList) with _ | ⟨w', o'⟩ <;> rw [h1] at h
  · simp at h
  · simp only [Functor.map, Option.map_some, Option.some.injEq] at h
    subst h
    exact readWit_fits h1

/-! ## The strict parse of a whole proof -/

/-- **The witness `π` encodes**, read strictly: all of `π`, nothing after. -/
def pW (π : Proof) : Option Wit :=
  match pWit π 0 with
  | some (w, o) => if o = π.size then some w else none
  | none => none

theorem tl_zero (π : ByteArray) : tl π 0 = π.data.toList := List.drop_zero

/-- **The strict parse is the decoder with the canonical-encoding check.** -/
theorem pW_iff (π : Proof) (w : Wit) : pW π = some w ↔ decode π = some w ∧ encode w = π := by
  constructor
  · intro h
    unfold pW at h
    rcases h1 : pWit π 0 with _ | ⟨w', o⟩ <;> rw [h1] at h <;> dsimp only at h
    · cases h
    · split at h
      · next ho =>
        cases h
        obtain ⟨hF, he⟩ := cod_pWit.sound _ _ _ _ h1
        rw [ho, tl_size, List.append_nil, tl_zero] at he
        have henc : encode w = π := by
          apply ByteArray.ext
          apply Array.toList_inj.1
          rw [eWit_eq]
          exact he.symm
        exact ⟨by rw [← henc]; exact decode_encode _ hF, henc⟩
      · cases h
  · rintro ⟨hd, he⟩
    have hF := fits_of_decode hd
    have ht : tl π 0 = eWit w ++ [] := by rw [List.append_nil, ← eWit_eq, he, tl_zero]
    unfold pW
    rw [cod_pWit.compl π 0 w [] hF ht]
    dsimp only
    rw [if_pos (by rw [Nat.zero_add, ← eWit_eq, he, len_data])]

/-! ## The verifier -/

/-- **The verifier, byte-level `W` branch**: `Vwith VS` with the strict parse `pW` in place of
`decodeF` and the `encodeF` comparison. -/
def VwithT (VS : SProg) (vk c : Digest) (π : Proof) : OProg Bool :=
  if isS π then VS vk c π else
    match h : pW π with
    | some (.leaf xs) =>
      .ret (decide (xs.length ≤ leafCap) && decide (c = leafStmtF (dataRootF xs) xs.length))
    | some (.node c₁ c₂ p₁ p₂) =>
      .ret (decide (c = nodeStmtF c₁ c₂) && accWith vk p₁ (fun _ => VwithT VS vk c₁ p₁.π) &&
        accWith vk p₂ (fun _ => VwithT VS vk c₂ p₂.π))
    | none => .ret false
termination_by π.size
decreasing_by
  · rw [← ((pW_iff π _).1 h).2]; exact (size_child_lt _ _ _ _).1
  · rw [← ((pW_iff π _).1 h).2]; exact (size_child_lt _ _ _ _).2

theorem VwithT_eq_at (VS : SProg) (vk : Digest) :
    ∀ n (c : Digest) (π : Proof), π.size = n → VwithT VS vk c π = Vwith VS vk c π := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro c π hn
    rw [VwithT, Vwith]
    by_cases hS : isS π
    · simp only [hS, if_true]
    · simp only [hS, Bool.false_eq_true, if_false]
      split
      · next xs h =>
        obtain ⟨hd, he⟩ := (pW_iff π _).1 h
        rw [decodeF_eq, hd]
        dsimp only
        rw [encodeF_eq, he]
        simp
      · next c₁ c₂ p₁ p₂ h =>
        obtain ⟨hd, he⟩ := (pW_iff π _).1 h
        rw [decodeF_eq, hd]
        dsimp only
        rw [dif_pos (by rw [encodeF_eq]; exact he)]
        have h1 := ih _ (hn ▸ he ▸ (size_child_lt c₁ c₂ p₁ p₂).1) c₁ p₁.π rfl
        have h2 := ih _ (hn ▸ he ▸ (size_child_lt c₁ c₂ p₁ p₂).2) c₂ p₂.π rfl
        simp only [h1, h2]
      · next h =>
        rcases hd : decodeF π with _ | w
        · rfl
        · rw [decodeF_eq] at hd
          by_cases he : encode w = π
          · rw [((pW_iff π w).2 ⟨hd, he⟩)] at h
            cases h
          · cases w with
            | leaf xs => simp [encodeF_eq, he]
            | node c₁ c₂ p₁ p₂ => simp [encodeF_eq, he]

/-- **The byte-level verifier is `Vwith`.** -/
theorem VwithT_eq (VS : SProg) : VwithT VS = Vwith VS := by
  funext vk c π
  exact VwithT_eq_at VS vk _ c π rfl

end Lvm6.VTw
