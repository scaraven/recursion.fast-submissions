-- New for lvm6 (WP N4-tail phase 2, RV4 M4 (a), (b)). The typed run's inputs at the child's header: the public-word
-- cells are `pwOf` of the header's bytes and the accumulator cells are `accFix` of it (`hdrBytes ∘ hdrView = id`
-- on header bytes, the stream's header words, zeros above), and the A23 promise from `AccOkE` of the node's header.
import Lvm6NodeChildOk
import Lvm6VGuard
import Lvm6NodeChild
import Lvm6QSigHdr
import Lvm6LeafBlock
import LvmXRead2
import Lvm6NodeDeploy

/-!
# The typed run's header inputs (WP N4-tail, RV4 M4 (a), (b))

* Bytes (generic): `seg p o n` (bytes `o … o+n−1`), `toBF64_le8` (a word read little-endian is `kOfBytes`),
  `byteOf_le8`, `le64_rdU64`, `eBytes_rdE`, `toList_rdD`, `flat_rdE`; **`hdrBytes_hdrView`**: on header bytes (the
  magic, `136 + 16v` bytes) `hdrBytes (hdrView sh p) = p`; `kOfBytes_le64`, **`accIn_hdrView`**: the accumulator
  read back from `hdrBytes x` is `x`'s (`|x.accIn.1| = v`).
* Cells (generic over a base cell `b`): **`accFix_of_cells`** (cells `b + accW + 2i`, `b + accW + 2v` hold the
  header's words ⟹ their values are `accFix (hdrView sh H)`), **`pwOf_of_cells`** (header words below
  `hdrLen/8`, zeros above ⟹ `pwOf Ti (hdrBytes (hdrView sh H))`).
* At the deployed cells: **`tyIn_hdr`** (M4 (a)): `TyIn M Ti (hdrOf6 πW)`, the typed run's `pw` and `acc` are the
  cells' (`pubCOf`, `ainC`, `yInC`), from `LinkOk6`, the magic of `ChildHdr6`, the stream cells and the zero cell;
  **`typedRun_hdr`** turns `node6E_har`'s typed run into `dec_of_runs`'s `hY` form; **`promise_of_accOk`**
  (M4 (b)): `AccOkE Ti (accFix x)` and the own cells holding `x`'s header give `PhiQE … own = ownY`.
-/

set_option autoImplicit false
namespace Lvm6.Node.Hdr
open RecursionFast LeanVM.Parameters Lvm Lvm.Loop Lvm6.Q
open Lvm.X (decLE)

/-! ## Byte lemmas

Restatements of the extractor's `ofLE_take`, `kOfBytes_decLE` and `byteOf_ofBitVec` (same proofs), so
that the node theorem's closure does not import the extractor's modules (PORT17 N1). -/

theorem ofLE_take (l : List UInt8) : ∀ n, ofLE (l.take n) = ∑ i ∈ Finset.range n, (l.getD i 0).toNat * 256 ^ i := by
  induction l with
  | nil => intro n; simp [ofLE]
  | cons a r ih =>
    intro n
    cases n with
    | zero => simp [ofLE]
    | succ n =>
      rw [List.take_succ_cons, Finset.sum_range_succ', ofLE, List.foldr_cons, ← ofLE, ih n, Finset.mul_sum]
      simp only [List.getD_cons_succ, List.getD_cons_zero, pow_zero, mul_one, pow_succ]
      rw [add_comm]
      congr 1
      exact Finset.sum_congr rfl fun i _ => by ring

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

theorem byteOf_ofBitVec (w : Word) {k : ℕ} (hk : k < 8) :
    byteOf (UInt64.ofBitVec w) k = (w.toNat / 256 ^ k).toUInt8 := by
  refine byte_ext fun r hr => ?_
  rw [byteOf_bit _ hk hr]
  simp only [Nat.toUInt8]
  rw [show (UInt8.ofNat (w.toNat / 256 ^ k)).toBitVec = BitVec.ofNat 8 (w.toNat / 256 ^ k) from rfl,
    BitVec.getLsbD_ofNat, show (256 : ℕ) ^ k = 2 ^ (8 * k) by rw [pow_mul]; norm_num,
    Nat.testBit_div_two_pow, BitVec.getLsbD, show r + 8 * k = 8 * k + r by ring]
  simp [hr]

/-- `accIn`'s first header word (FORMAT6 §2: byte 120). -/
def hdrAccW : ℕ := 15

theorem getD_drop' (l : List UInt8) (o i : ℕ) : (l.drop o).getD i 0 = l.getD (o + i) 0 := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_drop, ← List.getD_eq_getElem?_getD]

theorem le8_eq (l : List UInt8) (o : ℕ) :
    le8 l o = ∑ i ∈ Finset.range 8, ((l.drop o).getD i 0).toNat * 256 ^ i := by
  simp only [le8, getD_drop', List.range_succ, List.range_zero, List.nil_append, List.map_append,
    List.map_cons, List.map_nil, List.sum_append, List.sum_cons, List.sum_nil, Finset.sum_range_succ,
    Finset.sum_range_zero]
  norm_num

theorem le8_lt (l : List UInt8) (o : ℕ) : le8 l o < 2 ^ 64 := by
  rw [le8_eq, ← ofLE_take]
  exact lt_of_lt_of_le (ofLE_lt _) (by
    rw [show (2 : ℕ) ^ 64 = 256 ^ 8 by norm_num]
    exact Nat.pow_le_pow_right (by norm_num) (by simp))

theorem toBF64_le8 (l : List UInt8) (o : ℕ) :
    FK.toBF64 (QSig.w64 (le8 l o).toUInt64) = Lvm.FS.kOfBytes (l.drop o) := by
  rw [kOfBytes_decLE]
  unfold FK.toBF64 decLE
  congr 1
  apply BitVec.eq_of_toNat_eq
  have hlt := le8_lt l o
  rw [toNat_toWord (by rw [ofLE_take, ← le8_eq]; exact lt_of_lt_of_le hlt (by norm_num)), ofLE_take,
    ← le8_eq]
  simpa using hlt

/-! ## Bytes -/

/-- `n` bytes of `p` from `o` (zeros past the end). -/
def seg (p : List UInt8) (o n : ℕ) : List UInt8 := (List.range n).map fun k ↦ p.getD (o + k) 0

theorem lane_toBF64 (n : ℕ) : K.lane (FK.toBF64 (QSig.w64 n.toUInt64)) = n.toUInt64 := rfl

theorem byteOf_le8 (b : List UInt8) (o : ℕ) {k : ℕ} (hk : k < 8) :
    byteOf (le8 b o).toUInt64 k = b.getD (o + k) 0 := by
  have hlt := le8_lt b o
  have e : (le8 b o).toUInt64 = UInt64.ofBitVec (BitVec.ofNat 64 (le8 b o)) := rfl
  rw [e, byteOf_ofBitVec _ hk, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt]
  apply UInt8.toNat_inj.mp
  rw [show ∀ n : ℕ, (UInt8.ofNat n).toNat = n % 256 from fun _ ↦ rfl]
  rw [le8_eq]
  simp only [getD_drop', Finset.sum_range_succ, Finset.sum_range_zero]
  have h0 : (b.getD (o + 0) 0).toNat < 256 := by
    have := (b.getD (o + 0) 0).toNat_lt; simpa using this
  have h1 : (b.getD (o + 1) 0).toNat < 256 := by
    have := (b.getD (o + 1) 0).toNat_lt; simpa using this
  have h2 : (b.getD (o + 2) 0).toNat < 256 := by
    have := (b.getD (o + 2) 0).toNat_lt; simpa using this
  have h3 : (b.getD (o + 3) 0).toNat < 256 := by
    have := (b.getD (o + 3) 0).toNat_lt; simpa using this
  have h4 : (b.getD (o + 4) 0).toNat < 256 := by
    have := (b.getD (o + 4) 0).toNat_lt; simpa using this
  have h5 : (b.getD (o + 5) 0).toNat < 256 := by
    have := (b.getD (o + 5) 0).toNat_lt; simpa using this
  have h6 : (b.getD (o + 6) 0).toNat < 256 := by
    have := (b.getD (o + 6) 0).toNat_lt; simpa using this
  have h7 : (b.getD (o + 7) 0).toNat < 256 := by
    have := (b.getD (o + 7) 0).toNat_lt; simpa using this
  interval_cases k <;>
  · simp only [Nat.add_zero] at h0 ⊢
    generalize (b.getD o 0).toNat = x0 at h0 ⊢
    generalize (b.getD (o + 1) 0).toNat = x1 at h1 ⊢
    generalize (b.getD (o + 2) 0).toNat = x2 at h2 ⊢
    generalize (b.getD (o + 3) 0).toNat = x3 at h3 ⊢
    generalize (b.getD (o + 4) 0).toNat = x4 at h4 ⊢
    generalize (b.getD (o + 5) 0).toNat = x5 at h5 ⊢
    generalize (b.getD (o + 6) 0).toNat = x6 at h6 ⊢
    generalize (b.getD (o + 7) 0).toNat = x7 at h7 ⊢
    simp only [Nat.reducePow, pow_zero, pow_one, Nat.div_one, Nat.mul_one, Nat.zero_add]
    omega


theorem seg_append (p : List UInt8) (o a b : ℕ) : seg p o a ++ seg p (o + a) b = seg p o (a + b) := by
  simp only [seg, List.range_add, List.map_append, List.map_map, Function.comp_def, Nat.add_assoc]

theorem seg_merge (p : List UInt8) {o a o' b : ℕ} (h : o' = o + a) : seg p o a ++ seg p o' b = seg p o (a + b) := by
  subst h; exact seg_append p o a b

theorem seg_self (p : List UInt8) : seg p 0 p.length = p := by
  apply List.ext_getElem (by simp [seg])
  intro i h1 h2
  simp only [seg, List.getElem_map, List.getElem_range, Nat.zero_add, List.getD_eq_getElem _ _ h2]

theorem seg_take (p : List UInt8) {n : ℕ} (h : n ≤ p.length) : seg p 0 n = p.take n := by
  apply List.ext_getElem (by simp [seg]; omega)
  intro i h1 h2
  simp only [seg, List.length_map, List.length_range] at h1
  simp only [seg, List.getElem_map, List.getElem_range, Nat.zero_add, List.getElem_take,
    List.getD_eq_getElem _ _ (show i < p.length by omega)]

theorem kOfBytes_drop (p : List UInt8) (o : ℕ) :
    Lvm.FS.kOfBytes (p.drop o) = FK.toBF64 (QSig.w64 (le8 p o).toUInt64) := (toBF64_le8 p o).symm

theorem le64_kOfBytes (p : List UInt8) (o : ℕ) : le64 (K.lane (Lvm.FS.kOfBytes (p.drop o))) = seg p o 8 := by
  rw [kOfBytes_drop, lane_toBF64]
  simp only [le64, seg]
  apply List.map_congr_left
  intro k hk
  exact byteOf_le8 p o (List.mem_range.mp hk)

theorem le64_rdU64 (p : List UInt8) (o : ℕ) : le64 (rdU64 p o) = seg p o 8 := le64_kOfBytes p o

theorem eBytes_rdE (p : List UInt8) (o : ℕ) : eBytes (rdE p o) = seg p o 16 := by
  show le64 (K.lane (Lvm.FS.kOfBytes (p.drop o))) ++ le64 (K.lane (Lvm.FS.kOfBytes (p.drop (o + 8)))) = _
  rw [le64_kOfBytes, le64_kOfBytes, seg_append]

theorem toList_rdD (p : List UInt8) (o : ℕ) : (rdD p o).toList = seg p o 32 := by
  apply List.ext_getElem (by simp [seg])
  intro i h1 h2
  simp [rdD, Lvm.FS.dg, seg]

theorem flat_rdE (p : List UInt8) (o : ℕ) : ∀ n,
    ((List.range n).map fun i ↦ rdE p (o + 16 * i)).flatMap eBytes = seg p o (16 * n)
  | 0 => by simp [seg]
  | n + 1 => by
    rw [List.range_succ, List.map_append, List.flatMap_append, flat_rdE p o n, List.map_singleton,
      List.flatMap_singleton, eBytes_rdE, seg_append, Nat.mul_succ]

/-- **`hdrBytes ∘ hdrView = id`** on header bytes (the magic, then `128 + 16v` bytes). -/
theorem hdrBytes_hdrView (sh : Shape) (p : List UInt8) (hl : p.length = 136 + 16 * sh.phiVars)
    (hm : p.take 8 = V.magic6) : hdrBytes (hdrView sh p) = p := by
  have h8 : seg p 0 8 = V.magic6 := by rw [seg_take p (by omega), hm]
  simp only [hdrBytes, hdrView, le64_rdU64, toList_rdD]
  rw [show ((List.range sh.phiVars).map fun i ↦ rdE p (120 + 16 * i)).flatMap eBytes = seg p 120 (16 * sh.phiVars)
    from flat_rdE p 120 _, eBytes_rdE, ← h8]
  rw [seg_merge p (o := 0) (a := 8) (o' := 8) rfl, seg_merge p (o := 0) (a := 8 + 8) (o' := 16) rfl,
    seg_merge p (o := 0) (a := 8 + 8 + 8) (o' := 24) rfl, seg_merge p (o := 0) (a := 8 + 8 + 8 + 32) (o' := 56) rfl,
    seg_merge p (o := 0) (a := 8 + 8 + 8 + 32 + 32) (o' := 88) rfl,
    seg_merge p (o := 0) (a := 8 + 8 + 8 + 32 + 32 + 32) (o' := 120) rfl,
    seg_merge p (o := 0) (a := 8 + 8 + 8 + 32 + 32 + 32 + 16 * sh.phiVars) (o' := 120 + 16 * sh.phiVars)
      (by omega)]
  rw [show 8 + 8 + 8 + 32 + 32 + 32 + 16 * sh.phiVars + 16 = p.length by omega, seg_self]

/-! ## The accumulator read back from `hdrBytes` -/

theorem u8_toNat (n : ℕ) : n.toUInt8.toNat = n % 256 := by simp [Nat.toUInt8]

theorem le8_le64 (w : UInt64) (r : List UInt8) : le8 (le64 w ++ r) 0 = w.toNat := by
  have hw : w.toNat < 2 ^ 64 := w.toNat_lt
  conv_rhs => rw [← le8_word w.toNat hw]
  unfold le8
  congr 1
  apply List.map_congr_left
  intro t ht
  have ht8 := List.mem_range.mp ht
  rw [Nat.zero_add, List.getD_eq_getElem?_getD, List.getElem?_append_left (by simp [le64]; omega)]
  have e : w = UInt64.ofBitVec w.toBitVec := rfl
  simp only [le64, List.getElem?_map, List.getElem?_range ht8, Option.map_some, Option.getD_some]
  rw [e, byteOf_ofBitVec _ ht8, u8_toNat, u8_toNat, Nat.mod_mod]
  rfl

theorem kOfBytes_le64 (k : K) (r : List UInt8) : Lvm.FS.kOfBytes (le64 (K.lane k) ++ r) = k := by
  have h := toBF64_le8 (le64 (K.lane k) ++ r) 0
  rw [List.drop_zero, le8_le64, show (K.lane k).toNat.toUInt64 = K.lane k by simp] at h
  rw [← h]
  rfl

theorem eBytes_length (y : E2) : (eBytes y).length = 16 := by simp [eBytes, le64]

theorem drop_flat : ∀ (l : List E2) (i : ℕ), i ≤ l.length → (l.flatMap eBytes).drop (16 * i) = (l.drop i).flatMap eBytes
  | _, 0, _ => by simp
  | [], _ + 1, h => by simp at h
  | a :: l, i + 1, h => by
    rw [List.flatMap_cons, show 16 * (i + 1) = 16 + 16 * i by ring, ← List.drop_drop,
      List.drop_left' (eBytes_length a), drop_flat l i (by simp at h; omega), List.drop_succ_cons]

/-- Value `i` of the `E` list after a prefix of length `o`, read back. -/
theorem rdE_at (pre : List UInt8) (L : List E2) {o : ℕ} (hpre : pre.length = o) {i : ℕ} (hi : i < L.length) :
    rdE (pre ++ L.flatMap eBytes) (o + 16 * i) = L[i] := by
  have hd : (pre ++ L.flatMap eBytes).drop (o + 16 * i) =
      le64 (K.lane L[i].re) ++ (le64 (K.lane L[i].im) ++ (L.drop (i + 1)).flatMap eBytes) := by
    rw [← List.drop_drop, List.drop_left' hpre, drop_flat L i hi.le, List.drop_eq_getElem_cons hi,
      List.flatMap_cons, eBytes, List.append_assoc]
  show (⟨Lvm.FS.kOfBytes (List.drop (o + 16 * i) (pre ++ L.flatMap eBytes)),
    Lvm.FS.kOfBytes (List.drop (o + 16 * i + 8) (pre ++ L.flatMap eBytes))⟩ : E2) = _
  have h8 : (pre ++ L.flatMap eBytes).drop (o + 16 * i + 8) = ((pre ++ L.flatMap eBytes).drop (o + 16 * i)).drop 8 := by
    simp only [List.drop_drop]
  rw [h8, hd, kOfBytes_le64, List.drop_left' (by simp [le64]), kOfBytes_le64]

/-- The header's bytes before `accIn`. -/
theorem hdrBytes_split (x : Hdr) : ∃ pre : List UInt8, pre.length = 8 * hdrAccW ∧
    hdrBytes x = pre ++ (x.accIn.1 ++ [x.accIn.2]).flatMap eBytes :=
  ⟨V.magic6 ++ le64 x.b ++ le64 x.n ++ x.h.toList ++ x.c'.toList ++ x.vk.toList, by simp [le64, V.magic6, hdrAccW],
    by simp [hdrBytes, List.flatMap_append, List.append_assoc]⟩

/-- **The accumulator read back from a header's bytes is its own** (`|accIn.1| = v`). -/
theorem accIn_hdrView (sh : Shape) (x : Hdr) (hx : x.accIn.1.length = sh.phiVars) :
    (hdrView sh (hdrBytes x)).accIn = x.accIn := by
  obtain ⟨pre, hpre, he⟩ := hdrBytes_split x
  have hL : (x.accIn.1 ++ [x.accIn.2]).length = sh.phiVars + 1 := by simp [hx]
  show ((List.range sh.phiVars).map fun i ↦ rdE (hdrBytes x) (120 + 16 * i), rdE (hdrBytes x) (120 + 16 * sh.phiVars)) = _
  rw [he, show (120 : ℕ) = 8 * hdrAccW from rfl]
  refine Prod.ext ?_ ?_
  · apply List.ext_getElem (by simp [hx])
    intro i h1 h2
    simp only [List.getElem_map, List.getElem_range]
    rw [rdE_at pre _ hpre (by omega), List.getElem_append_left (by omega)]
  · simp only
    rw [rdE_at pre _ hpre (by omega), List.getElem_append_right (by omega)]
    simp [hx]

/-! ## Cells holding header words -/

/-- `accFix` of a header with `v` accumulator coordinates is its accumulator (V1c's `accFix`). -/
theorem accFix_eq (x : Hdr) (hx : x.accIn.1.length = Ty.phiVarsE) : V.accFix x = x.accIn := by
  unfold V.accFix
  rw [List.take_left' hx]

/-- **The accumulator cells** (`accW + 2i`, `accW + 2v` from a base cell `b`) holding a header's words are its
parsed accumulator. -/
theorem accIn_of_cells (sh : Shape) (H : List UInt8) (M : Mem) (b : ℕ)
    (hb : ∀ l, hdrAccW ≤ l → l < hdrAccW + 2 * sh.phiVars + 2 → M.k (b + l) = QSig.w64 (le8 H (8 * l)).toUInt64) :
    ((List.range sh.phiVars).map (fun i ↦ QK.ev2 M (Q2.ld2 (b + (hdrAccW + 2 * i)))),
      QK.ev2 M (Q2.ld2 (b + (hdrAccW + 2 * sh.phiVars)))) = (hdrView sh H).accIn := by
  have hc : ∀ j, j ≤ sh.phiVars → QK.ev2 M (Q2.ld2 (b + (hdrAccW + 2 * j))) = rdE H (120 + 16 * j) := by
    intro j hj
    show (⟨FK.toBF64 (M.k (b + (hdrAccW + 2 * j))), FK.toBF64 (M.k (b + (hdrAccW + 2 * j) + 1))⟩ : E2) = _
    rw [hb _ (by omega) (by omega), show b + (hdrAccW + 2 * j) + 1 = b + (hdrAccW + 2 * j + 1) by omega,
      hb _ (by omega) (by omega), toBF64_le8, toBF64_le8]
    show (⟨_, _⟩ : E2) = ⟨Lvm.FS.kOfBytes (H.drop (120 + 16 * j)), Lvm.FS.kOfBytes (H.drop (120 + 16 * j + 8))⟩
    rw [show 8 * (hdrAccW + 2 * j) = 120 + 16 * j by simp [hdrAccW]; ring,
      show 8 * (hdrAccW + 2 * j + 1) = 120 + 16 * j + 8 by simp [hdrAccW]; ring]
  show _ = ((List.range sh.phiVars).map fun i ↦ rdE H (120 + 16 * i), rdE H (120 + 16 * sh.phiVars))
  refine Prod.ext ?_ (hc _ le_rfl)
  exact List.map_congr_left fun j hj ↦ hc j (List.mem_range.mp hj).le

theorem le8_beyond {H : List UInt8} {o : ℕ} (h : H.length ≤ o) : le8 H o = 0 := by
  unfold le8
  have : ∀ t, H.getD (o + t) 0 = 0 := fun t ↦ List.getD_eq_default _ _ (by omega)
  simp only [this]
  simp

/-- **The public words from cells**: cells holding the header's words below `hdrLen / 8` and `0` above give CD's
`pwOf` of the header's bytes (`hdrBytes ∘ hdrView = id`). -/
theorem pwOf_of_cells (sh : Shape) (Ti : Ty.TInst6) (H : List UInt8) (hl : H.length = hdrLen sh)
    (hm : H.take 8 = V.magic6) (v : ℕ → FK)
    (hv : ∀ l, l < hdrLen sh / 8 → v l = QSig.w64 (le8 H (8 * l)).toUInt64) (hz : ∀ l, hdrLen sh / 8 ≤ l → v l = 0) :
    (fun y ↦ v (y - QD.pubBase Ti)) = QD.pwOf Ti (hdrBytes (hdrView sh H)) := by
  rw [hdrBytes_hdrView sh H (by rw [hl]; rfl) hm]
  funext y
  show _ = QSig.w64 (le8 H (8 * (y - QD.pubBase Ti))).toUInt64
  by_cases h : y - QD.pubBase Ti < hdrLen sh / 8
  · exact hv _ h
  · have e : hdrLen sh = 136 + 16 * sh.phiVars := rfl
    rw [hz _ (by omega), le8_beyond (by rw [hl]; omega)]
    rfl

/-! ## At the deployed cells (NODE3's `pubCOf`, `ainC`, `yInC`, `ownC`, `ownYC`) -/

/-- **The typed run's inputs are the cells'**: the public words `pubCOf` read are `pwOf` of the header's bytes, and
the accumulator cells `ainC`, `yInC` are `accFix` of the header. -/
structure TyIn (M : Mem) (Ti : Ty.TInst6) (x : Hdr) : Prop where
  pw : (fun y ↦ ((Dep.pubCOf Ti.lay y).val M).c₀) = QD.pwOf Ti (hdrBytes x)
  acc : (Dep.ainC.map (QK.ev2 M), QK.ev2 M Dep.yInC) = V.accFix x

theorem laneK_w64 (ws : List Word) (j : ℕ) : QLink.laneK ws j = QSig.w64 (QLink.lw ws j).toUInt64 := by
  show (⟨_⟩ : FK) = ⟨_⟩
  congr 1
  apply UInt64.toNat_inj.mp
  rw [← QLink.laneK_val]
  simp [QLink.laneK]

theorem hdrW_eq (k : ℕ) : Dep.hdrW k = Lvm6.Q.hdrW k := by
  simp only [Dep.hdrW, Lvm6.Q.hdrW, Lvm6.Q.seedW]

theorem hdrW_add (k : ℕ) : Dep.sbC + Dep.hdrW k = Dep.sbC + Dep.hdrW 0 + k := by
  simp only [Dep.hdrW]; omega

/-- **RV4 M4 (a)**: at the header `F6` replays, `hdrOf6 πW` (`πW` the reassembled child proof), the typed run's
inputs are the cells', from `LinkOk6`, the header's magic (`ChildHdr6`), the stream cells (`QIn6.stream`) and the
zero cell. -/
theorem tyIn_hdr (Ti : Ty.TInst6) {M : Mem} {ws : List Word} {c : Digest}
    (hL : LinkOk6 P6 c (decode6 P6 ws)) (hm : (Lvm6.Q.hdrOf6 (decode6 P6 ws)).take 8 = Lvm6.Q.magic6)
    (hs : ∀ j < 2 ^ Dep.lay6.m, M.k (Dep.lay6.sb + j) = QLink.laneK ws j) (hz : M.k Dep.zC = 0) :
    TyIn M Ti (Lvm6.Node.hdrOf6 (reassemble6 P6 (decode6 P6 ws))) := by
  set H := Lvm6.Q.hdrOf6 (decode6 P6 ws) with hH
  have hlen : H.length = 824 := hdrOf6_length hL
  have hx : Lvm6.Node.hdrOf6 (reassemble6 P6 (decode6 P6 ws)) = hdrView P17 H := by
    obtain ⟨rest, hr⟩ := bl_reassemble (decode6 P6 ws)
    show hdrView P17 ((Lvm.Replay.bl (reassemble6 P6 (decode6 P6 ws))).take (V.hdrLen (toV P17))) = _
    rw [hr, show V.hdrLen (toV P17) = H.length by rw [hlen]; rfl, List.take_left]
  have hcell : ∀ l, l < 103 → M.k (Dep.sbC + Dep.hdrW l) = QSig.w64 (le8 H (8 * l)).toUInt64 := by
    intro l hl
    have hk : 32 + 8 * l + 8 ≤ (P6.getD 1 default).len := by
      rw [P6_get1]
      simp only [seedLen, hdrLen, cdConsts_P17.1]
      omega
    have hj : Dep.hdrW l < 2 ^ Dep.lay6.m := by
      simp only [Dep.hdrW, Dep.lay6]
      omega
    rw [show Dep.sbC + Dep.hdrW l = Dep.lay6.sb + Dep.hdrW l from rfl, hs _ hj, laneK_w64, hdrW_eq,
      le8_hdr (P := P6) (ws := ws) (by rw [P6_get0]) P6_two hk]
  have hl8 : H.length = hdrLen P17 := by rw [hlen, hdrLen_P17]
  have hm' : H.take 8 = V.magic6 := hm
  rw [hx]
  refine ⟨?_, ?_⟩
  · have e := pwOf_of_cells P17 Ti H hl8 hm' (fun l ↦ if l < 103 then M.k (Dep.sbC + Dep.hdrW l) else M.k Dep.zC)
      (fun l hl ↦ by
        rw [hdrLen_P17] at hl
        simp only [show l < 103 by omega, ite_true]
        exact hcell l (by omega))
      (fun l hl ↦ by
        rw [hdrLen_P17] at hl
        simp only [show ¬ l < 103 by omega, ite_false, hz])
    rw [← e]
    funext y
    have hb : QD.pubBase (Dep.tiOf Ti.lay) = QD.pubBase Ti := rfl
    simp only [Dep.pubCOf, hb]
    by_cases h : y - QD.pubBase Ti < 103 <;> simp only [h, ite_true, ite_false] <;> rfl
  · have hv : (hdrView P17 H).accIn.1.length = Ty.phiVarsE := by
      simp only [hdrView, List.length_map, List.length_range, cdConsts_P17.1]
      decide
    rw [accFix_eq _ hv, ← accIn_of_cells P17 H M (Dep.sbC + Dep.hdrW 0) (fun l h1 h2 ↦ by
      rw [← hdrW_add]
      exact hcell l (by simp only [hdrAccW, cdConsts_P17.1] at h2; omega))]
    simp only [Dep.ainC, Dep.yInC, List.map_map, Function.comp_def, cdConsts_P17.1]
    refine Prod.ext ?_ ?_
    · show List.map _ _ = List.map _ _
      apply List.map_congr_left
      intro i _
      rw [hdrW_add]
      rfl
    · show QK.ev2 M (Q2.ld2 (Dep.sbC + Dep.hdrW (15 + 86))) = _
      rw [hdrW_add]
      rfl

/-- **The typed run at the header** (`dec_of_runs`/`dec_of_split`'s `hY` form): `node6E_har`'s typed run reads the
cells; with `TyIn` it is the run of the instance's `pwOf`, `accFix`. -/
theorem typedRun_hdr {M : Mem} {Ti : Ty.TInst6} {x : Hdr} {L : Lvm.M3.Lay} {lay : List QK.LEv} {P : Ty.OpenClaimsE → Prop}
    (hT : TyIn M Ti x)
    (hr : QK.Runs M lay (Ty.typedProgE Ti L (fun y ↦ ((Dep.pubCOf Ti.lay y).val M).c₀)
      (Dep.ainC.map (QK.ev2 M), QK.ev2 M Dep.yInC)) P) :
    QK.Runs M lay (Ty.typedProgE Ti L (QD.pwOf Ti (hdrBytes x)) (V.accFix x)) P := by
  rw [← hT.pw, ← hT.acc]
  exact hr

/-- **RV4 M4 (b), the A23 promise**: the node's own accumulator cells (`ownC`, `ownYC`, `pbC`'s header words)
hold its header `x` (`|x.accIn.1| = v`), and `AccOkE Ti (accFix x)` gives `Φ_Q(own) = ownY`. -/
theorem promise_of_accOk (Ti : Ty.TInst6) {M : Mem} {x : Hdr} (hx : x.accIn.1.length = Ty.phiVarsE)
    (hown : ∀ l, hdrAccW ≤ l → l < hdrAccW + 2 * Ty.phiVarsE + 2 →
      M.k (Dep.pbC + l) = QSig.w64 (le8 (hdrBytes x) (8 * l)).toUInt64)
    (hok : Ty.AccOkE Ti (V.accFix x)) :
    Ty.PhiQE Ti.Q Ti.lay (Dep.ownC.map (QK.ev2 M)) = QK.ev2 M Dep.ownYC := by
  have hv : P17.phiVars = Ty.phiVarsE := cdConsts_P17.1
  have e := accIn_of_cells P17 (hdrBytes x) M Dep.pbC (fun l h1 h2 ↦ hown l h1 (by rw [← hv]; exact h2))
  rw [accIn_hdrView P17 x (by rw [hx, hv])] at e
  rw [accFix_eq x hx, ← e] at hok
  simp only [Dep.ownC, Dep.ownYC, List.map_map, Function.comp_def, hv, Nat.add_assoc] at hok ⊢
  exact hok

end Lvm6.Node.Hdr
