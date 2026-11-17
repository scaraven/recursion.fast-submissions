-- lvm2 X-REC2 / S4-S2 (helper XA), re-ported to J2′ at J2C-INT. O5c for two `C_rec` levels (J2′:
-- `g = 14` proofs of work, `C_rec` at the Johnson radius with an OOD sample after level 1's cap),
-- generic in `V_S`: WP-13a's extractor `EX` returns the specification extractor's witness (`S.Ex K.ext`,
-- `kcertSJ`'s `extSJ`: DEC's level-1 decoder, then WP-13b's) on accepted `S` proofs over logs of
-- potential below 1, or a witness of the relation. WP-14d's `LvmCertSExq` (v1, one level) adapted: its helpers moved here unchanged
-- (but `roots_trun`, which now names the caps); the replay runs through level 1's commitment and level
-- 0's opening (`LvmCertSExq2Run`). (M′, R11-IS: `ext_eq_gen`, `LvmCertSExq.ext_eq_S` and `LvmCertT.ext_eqV` are
-- removed.)
import LvmCertSKJ
import LvmCertSGood
import LvmCertS
import LvmCertSExq2Codec
import LvmCompile
import LvmCertSExqKinds
import LvmXChainL

-- (GOLF2: 47 declarations that `certified` does not use moved verbatim to `LvmXSChildOff`, outside its import closure.)

-- ===== merged from `LvmCertSExqCodec` (GOLF module merge: `LvmCertSExqCodec.lean` is now a stub importing `LvmCertSExq2`) =====
section
-- WP-14d (EXQ). New for lvm (O5c bridges (c), (d)): WP-5's byte decoders (`kOfBytes`, `eOfBytes`,
-- `chalOf`) against WP-13a's word readers (`decLE`, `pw`, `alphaE`, `f1E`), V_S's header parser
-- (`u64At`, `digestAt`, `Header.ofProof`) against WP-13a's (`pw`, `hdD`), and WP-13b's column reading
-- (`readRow`) against WP-5's first-preimage word (`Scheme.wordOf`, O12).

/-!
# The byte-level bridges of O5c

* (the byte decoders, `f2E_eq` and O12 are in `LvmCertSExq2Codec`, which needs no certificate module);
* **`pw_toNat`**: `(pw π j).toNat = u64At π (8 j)` (`u64At` by `Nat.two_pow_add_eq_or_of_lt`);
* **`hdrOf_eq`**: the statement's header (`hdrOf`, the header from byte 8) is `Header.ofProof π`,
  and its fields are WP-13a's (`hd_b`, `hd_vk`, `hd_cL`, `hd_s`, `hd_n`, `hd_h`, `hd_sig`);
-/

set_option autoImplicit false

namespace Lvm.ASM

open RecursionFast Lvm.FS
open LeanVM.Parameters
open LeanVM.Protocol.Compile hiding Proof Bytes

/-! ## `u64At` and the packed words -/

theorem or_shift (x : UInt64) (c : UInt8) (k : ℕ) (hk : k < 8) (hx : x.toNat < 2 ^ (8 * k)) :
    (x ||| c.toUInt64 <<< (8 * k).toUInt64).toNat = x.toNat + 2 ^ (8 * k) * c.toNat := by
  have hc : c.toNat < 256 := c.toNat_lt
  have h1 : (8 * k).toUInt64.toNat % 64 = 8 * k := by
    rw [Nat.toUInt64, UInt64.toNat_ofNat', Nat.mod_eq_of_lt (by (clear * - hk; omega)), Nat.mod_eq_of_lt (by (clear * - hk; omega))]
  have h2 : c.toNat * 2 ^ (8 * k) < 2 ^ 64 := by
    calc c.toNat * 2 ^ (8 * k) < 256 * 2 ^ (8 * k) := by
          exact Nat.mul_lt_mul_of_pos_right hc (by positivity)
      _ ≤ 2 ^ 64 := by
          rw [show (256 : ℕ) = 2 ^ 8 by norm_num, ← pow_add]
          exact Nat.pow_le_pow_right (by norm_num) (by (clear * - hk; omega))
  rw [UInt64.toNat_or, UInt64.toNat_shiftLeft, h1, UInt8.toNat_toUInt64, Nat.shiftLeft_eq,
    Nat.mod_eq_of_lt h2, Nat.lor_comm, mul_comm, ← Nat.two_pow_add_eq_or_of_lt hx]
  ring

/-- **`u64At` is the little-endian number** of the eight bytes. -/
theorem u64At_eq (b : ByteArray) (o : ℕ) :
    u64At b o = ofLE ((List.range 8).map fun i => b.get! (o + i)) := by
  let g : ℕ → UInt64 := fun i => (b.get! (o + i)).toUInt64 <<< (8 * i).toUInt64
  let acc : ℕ → UInt64 := fun k => Nat.rec (g 0) (fun k a => a ||| g (k + 1)) k
  have key : ∀ k, k < 8 → (acc k).toNat =
      ∑ i ∈ Finset.range (k + 1), 2 ^ (8 * i) * (b.get! (o + i)).toNat ∧
      (acc k).toNat < 2 ^ (8 * (k + 1)) := by
    intro k hk
    induction k with
    | zero =>
      have hc := (b.get! (o + 0)).toNat_lt
      have e : (acc 0).toNat = (b.get! (o + 0)).toNat := by simp [acc, g]
      refine ⟨by rw [e]; simp, by rw [e]; norm_num; (clear * - hc; omega)⟩
    | succ k ih =>
      obtain ⟨e, l⟩ := ih (by (clear * - hk; omega))
      have s := or_shift (acc k) (b.get! (o + (k + 1))) (k + 1) hk l
      have e' : (acc (k + 1)).toNat = (acc k).toNat + 2 ^ (8 * (k + 1)) * (b.get! (o + (k + 1))).toNat :=
        s
      refine ⟨by rw [e', e]; exact (Finset.sum_range_succ _ (k + 1)).symm, ?_⟩
      rw [e']
      have hc : (b.get! (o + (k + 1))).toNat ≤ 255 := by have := (b.get! (o + (k + 1))).toNat_lt; (clear * - this; omega)
      have hp : 2 ^ (8 * (k + 1 + 1)) = 2 ^ (8 * (k + 1)) * 256 := by
        rw [show 8 * (k + 1 + 1) = 8 * (k + 1) + 8 by ring, pow_add]; norm_num
      rw [hp]
      nlinarith
  have h7 := (key 7 (by norm_num)).1
  show (acc 7).toNat = _
  rw [h7]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.range_succ, List.range_zero,
    List.nil_append, List.map_cons, List.map_nil, List.cons_append, ofLE_cons]
  simp only [ofLE, List.foldr]
  ring

/-- **WP-13a's packed word is V_S's `u64At`** at an aligned offset inside π. -/
theorem pw_toNat (π : Proof) (j : ℕ) (hj : 8 * j + 8 ≤ π.size) :
    (Lvm.X.pw π j).toNat = u64At π (8 * j) := by
  have hs : π.data.toList.length = π.size := Array.length_toList
  rw [Lvm.X.pw, Lvm.X.packBytes_getDX, if_pos (by (clear * - j π hj hs; omega)), toWord, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (ofLE_take8_lt _), u64At_eq]
  congr 1
  apply List.ext_getElem (by simp; (clear * - π j hj hs; omega))
  intro i h1 h2
  simp only [List.length_take, List.length_drop, List.length_map, List.length_range] at h1 h2
  simp only [List.getElem_take, List.getElem_drop, List.getElem_map, List.getElem_range]
  rw [get!_eq_getD, List.getD_eq_getElem _ _ (by (clear * - hj hs h2; omega))]

/-! ## The header -/

/-- Two byte arrays equal on `[8, 5984)`. -/
def HdrEq (b b' : ByteArray) : Prop := ∀ k, 8 ≤ k → k < hdrFix → b.get! k = b'.get! k

theorem u64At_congr {b b' : ByteArray} (h : HdrEq b b') {o : ℕ} (ho : 8 ≤ o) (ho' : o + 8 ≤ hdrFix) :
    u64At b o = u64At b' o := by
  rw [u64At_eq, u64At_eq]
  congr 1
  refine List.map_congr_left fun i hi => h _ (by (clear * - ho; omega)) (by simp at hi; (clear * - ho' hi; omega))

theorem digestAt_congr {b b' : ByteArray} (h : HdrEq b b') {o : ℕ} (ho : 8 ≤ o)
    (ho' : o + 32 ≤ hdrFix) : digestAt b o = digestAt b' o := by
  apply Vector.ext
  intro i hi
  simp only [digestAt, Vector.getElem_ofFn]
  exact h _ (by (clear * - ho hi; omega)) (by (clear * - ho' hi; omega))

theorem sigAt_congr {b b' : ByteArray} (h : HdrEq b b') : sigAt b offSig = sigAt b' offSig := by
  have hH : hdrFix = 4928 := rfl
  have e1 : u64At b offSig = u64At b' offSig := u64At_congr h (by decide) (by decide)
  have e2 : ((List.range wotsLen).map fun k => digestAt b (offSig + 8 + 32 * k)) =
      (List.range wotsLen).map fun k => digestAt b' (offSig + 8 + 32 * k) :=
    List.map_congr_left fun k hk => digestAt_congr h (by simp [offSig]; (clear * -; first | decide | (simp only [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]; done) | ring1 | (clear * - k; omega))) (by
      simp only [List.mem_range, wotsLen] at hk; simp only [offSig]; (clear * - hH hk; omega))
  have e3 : ((List.range sigHeight).map fun k => digestAt b (offSig + 8 + 32 * wotsLen + 32 * k)) =
      (List.range sigHeight).map fun k => digestAt b' (offSig + 8 + 32 * wotsLen + 32 * k) :=
    List.map_congr_left fun k hk => digestAt_congr h (by simp [offSig, wotsLen]; (clear * -; first | decide | (simp only [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]; done) | ring1 | (clear * - k; omega))) (by
      simp only [List.mem_range, sigHeight] at hk; simp only [offSig, wotsLen]; (clear * - hH hk; omega))
  unfold sigAt
  rw [e1, e2, e3]

theorem ofProof_congr {b b' : ByteArray} (h : HdrEq b b') : Header.ofProof b = Header.ofProof b' := by
  unfold Header.ofProof
  rw [u64At_congr h (o := offB) (by decide) (by decide), digestAt_congr h (o := offVk) (by decide) (by decide),
    digestAt_congr h (o := offCL) (by decide) (by decide), digestAt_congr h (o := offS) (by decide) (by decide),
    u64At_congr h (o := offN) (by decide) (by decide), digestAt_congr h (o := offH) (by decide) (by decide),
    sigAt_congr h]

theorem wsAt_shift (W : ℕ → RecursionFast.Word) (a u n : ℕ) :
    Lvm.X.wsAt (fun j => W (a + j)) u n = Lvm.X.wsAt W (a + u) n := by
  simp only [Lvm.X.wsAt, Nat.add_assoc]

/-- **The header's signature** is WP-13a's `σ_leaf` (words `19 …` of π). -/
theorem sig_eq (π : Proof) (hs : hdrFix ≤ π.size) :
    sigAt π offSig = Lvm.X.sigOfF fun j => Lvm.X.pw π (19 + j) := by
  have hH : hdrFix = 4928 := rfl
  have e1 : u64At π offSig = (Lvm.X.pw π (19 + 0)).toNat := (pw_toNat π 19 (by (clear * - π hs hH; omega))).symm
  have e2 : ((List.range wotsLen).map fun k => digestAt π (offSig + 8 + 32 * k)) =
      (List.range wotsLen).map fun k => Lvm.X.digW (Lvm.X.wsAt (fun j => Lvm.X.pw π (19 + j)) (1 + 4 * k) 4) :=
    List.map_congr_left fun k _ => by
      rw [wsAt_shift, ← Lvm.X.hdD, Lvm.X.hdD_eq_digestAt]
      congr 1
      simp only [offSig]
      ring
  have e3 : ((List.range sigHeight).map fun k => digestAt π (offSig + 8 + 32 * wotsLen + 32 * k)) =
      (List.range sigHeight).map fun k =>
        Lvm.X.digW (Lvm.X.wsAt (fun j => Lvm.X.pw π (19 + j)) (1 + 4 * wotsLen + 4 * k) 4) :=
    List.map_congr_left fun k _ => by
      rw [wsAt_shift, ← Lvm.X.hdD, Lvm.X.hdD_eq_digestAt]
      congr 1
      simp only [offSig, wotsLen]
      ring
  unfold sigAt Lvm.X.sigOfF
  rw [e1, e2, e3]

end Lvm.ASM
end
-- ===== end of `LvmCertSExqCodec` =====

-- ===== merged from `LvmCertSExqRun` (GOLF module merge: `LvmCertSExqRun.lean` is now a stub importing `LvmCertSExq2`) =====
section
-- WP-14d (EXQ). New for lvm (O5c bridge (a)): WP-5's replay `trun` along a run whose events have
-- known kinds (reads and samples), on a body that is a suffix of a byte string `B`: the history is
-- `simK` (each read the scalar of the next 24 bytes, each sample the challenge of the first log
-- entry for `state ‖ pending bytes`), and its samples are the first-match chain of WP-13a
-- (`fmAns`) whose targets absorb the slices `fsPreK` (WP-13a's `fsPre` on kinds).

/-!
# The replay along known kinds

* `simK S L B ks off pend st`: the history and final state the replay produces on kinds `ks` with
  the body at byte `off` of `B` and the pending bytes `B[pend, off)`;
* **`trun_simK`**: if `trun` (from that state) returns a history `h ++ pre ++ post` with
  `pre.map kindOf = ks` (no `other`), then `pre` is `simK`'s and `trun` continues from `simK`'s state;
* **`simK_chain`**: `simK`'s samples are the challenges of the first-match chain `fmAns T` from
  position `j + 1` on, when the chain's targets `T (j + 1 + i)` absorb the slices
  `fsPreK ks off pend` (WP-13a's `fsPre`, `fsPre_eq_fsPreK`);
* `simK_reads`: a run of reads is the scalars of consecutive 24-byte slices.
-/

set_option autoImplicit false

namespace Lvm.ASM

open RecursionFast Lvm.FS
open LeanVM.Parameters
open LeanVM.Protocol.Compile hiding Proof Bytes

/-- The challenge of a sample event (`LvmCertSLuck.sampleOf`, restated here so that the replay
does not import the certificate's modules). -/
def smpOf : Ev → Option E
  | .sample c => some c
  | _ => none

/-- The slice `B[a, a + n)`. -/
def sl (B : List UInt8) (a n : ℕ) : List UInt8 := (B.drop a).take n

section Sim

variable (S : Scheme) (L : Log) (B : List UInt8)

end Sim

/-! ## `trun` keeps its history's prefix -/

theorem trun_prefix (S : Scheme) (L : Log) : ∀ (p : VerifierProgram Bool) (st : Digest) (buf : Bytes)
    (caps : List CapI) (body : Bytes) (h : List Ev) (b : Bool) (hf : List Ev),
    S.trun L p st buf caps body h = some (b, hf) → h <+: hf := by
  intro p
  induction p with
  | ret a => intro st buf caps body h b hf e; simp only [Scheme.trun, Option.some.injEq,
      Prod.mk.injEq] at e; rw [← e.2]
  | fail => intro st buf caps body h b hf e; simp only [Scheme.trun, Option.some.injEq,
      Prod.mk.injEq] at e; rw [← e.2]
  | grind _ _ _ => intro st buf caps body h b hf e; simp only [Scheme.trun, Option.some.injEq,
      Prod.mk.injEq] at e; rw [← e.2]
  | read k ih =>
    intro st buf caps body h b hf e
    simp only [Scheme.trun] at e
    split_ifs at e
    · simp only [Option.some.injEq, Prod.mk.injEq] at e; rw [← e.2]
    · exact (List.prefix_append _ _).trans (ih _ _ _ _ _ _ _ _ e)
  | sample k ih =>
    intro st buf caps body h b hf e
    simp only [Scheme.trun] at e
    split_ifs at e
    · cases hfd : L.find? (fun e => decide (e.1 = toQ (st.toList ++ buf))) with
      | none => rw [hfd] at e; simp at e
      | some e' =>
        rw [hfd, Option.bind_some] at e
        exact (List.prefix_append _ _).trans (ih _ _ _ _ _ _ _ _ e)
    · simp only [Option.some.injEq, Prod.mk.injEq] at e; rw [← e.2]
  | commit ht w k ih =>
    intro st buf caps body h b hf e
    simp only [Scheme.trun] at e
    split_ifs at e
    · simp only [Option.some.injEq, Prod.mk.injEq] at e; rw [← e.2]
    · exact (List.prefix_append _ _).trans (ih _ _ _ _ _ _ _ e)
  | query i ps k ih =>
    intro st buf caps body h b hf e
    simp only [Scheme.trun] at e
    cases hc : caps[i]? with
    | none => rw [hc] at e; simp only [Option.some.injEq, Prod.mk.injEq] at e; rw [← e.2]
    | some ci =>
      rw [hc] at e
      simp only at e
      cases ho : (S.openAll ci ps body).runLog L with
      | none => rw [ho] at e; simp at e
      | some o =>
        rw [ho, Option.bind_some] at e
        rcases o with _ | ⟨rows, rest⟩
        · simp only [Option.some.injEq, Prod.mk.injEq] at e; rw [← e.2]
        · exact (List.prefix_append _ _).trans (ih _ _ _ _ _ _ _ _ e)

theorem head_of_prefix {h l post : List Ev} {e e₀ : Ev} (hp : h ++ [e] <+: h ++ e₀ :: l ++ post) :
    e = e₀ := by
  simpa using hp

/-! ## The replay is `simK` -/

theorem sl_append (B : List UInt8) {pend off : ℕ} (h1 : pend ≤ off) (n : ℕ) :
    sl B pend (off - pend) ++ (B.drop off).take n = sl B pend (off + n - pend) := by
  unfold sl
  rw [show off + n - pend = (off - pend) + n by (clear * - off n pend h1; omega), List.take_add, List.drop_drop,
    show pend + (off - pend) = off by (clear * - pend off h1; omega)]

theorem drop_drop' (B : List UInt8) (a n : ℕ) : (B.drop a).drop n = B.drop (a + n) := by
  rw [List.drop_drop]

/-! ## `simK`'s samples are the first-match chain -/

/-! ## Runs of reads -/

/-! ## Kinds of items -/

/-- Items of reads and samples only. -/
def RSItems : List Item → Bool
  | [] => true
  | .read _ :: its => RSItems its
  | .sample :: its => RSItems its
  | _ :: _ => false

end Lvm.ASM
end
-- ===== end of `LvmCertSExqRun` =====

-- ===== merged from `LvmCertSExq2Run` (GOLF module merge: `LvmCertSExq2Run.lean` is now a stub importing `LvmCertSExq2`) =====
section
-- lvm2 X-REC2 (helper XA). The O5c bridge's replay (`LvmCertSExqRun`, WP-14d) extended through a
-- commitment and an opening, for `C_rec`'s second WHIR level (lvm2 S4): v1's `simK`/`trun_simK`/
-- `simK_chain` covered reads and samples only; here also a `commit` (level 1's cap) and, as a
-- separate step, a `query` (level 0's opening), so that the chain's targets through `α₁` are
-- `trun`'s Fiat–Shamir queries.

/-!
# The replay through a commitment and an opening

* `K2`: the kinds `read`, `sample` and `commit ht w nb` (a cap of `nb` bytes); `KM e k`: the event
  `e` has the kind `k`;
* `simK2 S L B ks off pend st`: the history and the final state the replay produces on the kinds
  `ks` (a commit: the commitment's word read by `wordOf` under the cap at `B[off, …)`, the body
  advances by `nb` bytes, which stay pending, as in `LvmDriver.driveItems`);
* **`trun_simK2`**: `trun` along a history of these kinds is `simK2`'s history, the program after it
  is `p.after pre`, and `trun` continues from the slices `offK2`, `pendK2` with the caps `capsK2`;
* **`trun_query`**: one opening of `ps` positions of the commitment `ci`: the body advances by
  `|ps| · (8·wd + 32·(ht − lv))` bytes, which no query absorbs (the pending bytes are kept, so an
  opening right after a sample leaves nothing pending: `driveItems`'s `pend := off`);
* **`simK2_chain`**: `simK2`'s samples are the first-match chain's answers when the chain's targets
  absorb `fsPreK2`'s slices (WP-13a's `fsPre`);
* (`openRec_P20`, B1's P20 slices through `C_rec`'s opening, is removed at M′, R11-IS.)
-/

set_option autoImplicit false

namespace Lvm.ASM

open RecursionFast Lvm.FS
open LeanVM.Parameters
open LeanVM.Protocol.Compile hiding Proof Bytes

/-- The kinds of the replayed events: a read, a sample, a commitment of shape `(ht, w)` whose cap
is `nb` bytes. -/
inductive K2 where
  | read
  | sample
  | commit (ht w nb : ℕ)
  deriving DecidableEq, Repr

/-- The event `e` has the kind `k`. -/
def KM : Ev → K2 → Prop
  | .read _, .read => True
  | .sample _, .sample => True
  | .commit ht w _, .commit ht' w' _ => ht = ht' ∧ w = w'
  | _, _ => False

section Sim

variable (S : Scheme) (L : Log) (B : List UInt8)

end Sim

/-- The body offset after the kinds. -/
def offK2 : List K2 → ℕ → ℕ
  | [], off => off
  | .read :: ks, off => offK2 ks (off + 24)
  | .sample :: ks, off => offK2 ks off
  | .commit _ _ nb :: ks, off => offK2 ks (off + nb)

/-- The first pending byte after the kinds. -/
def pendK2 : List K2 → ℕ → ℕ → ℕ
  | [], _, pend => pend
  | .read :: ks, off, pend => pendK2 ks (off + 24) pend
  | .sample :: ks, off, _ => pendK2 ks off off
  | .commit _ _ nb :: ks, off, pend => pendK2 ks (off + nb) pend

/-- The slices the samples absorb (WP-13a's `fsPre`; a cap stays pending). -/
def fsPreK2 : List K2 → ℕ → ℕ → List (ℕ × ℕ)
  | [], _, _ => []
  | .read :: ks, off, pend => fsPreK2 ks (off + 24) pend
  | .sample :: ks, off, pend => (pend, off - pend) :: fsPreK2 ks off off
  | .commit _ _ nb :: ks, off, pend => fsPreK2 ks (off + nb) pend

/-! ## The replay is `simK2`, and the program follows the history -/

theorem after_nil {α : Type} (p : VerifierProgram α) : p.after [] = some p := by cases p <;> rfl

theorem forall₂_cons_inv {e : Ev} {pre : List Ev} {k : K2} {ks : List K2}
    (h : List.Forall₂ KM (e :: pre) (k :: ks)) : KM e k ∧ List.Forall₂ KM pre ks := by
  cases h with
  | cons a b => exact ⟨a, b⟩

/-! ## One opening -/

/-- The bytes one position of the commitment `ci` takes from the body: the leaf (the row's occupied
words, `Scheme.lb`) and the siblings. -/
def posBytes (S : Scheme) (ci : CapI) : ℕ := S.lb ci + 32 * (ci.ht - ci.lv)

theorem climb_rest (S : Scheme) (L : Log) : ∀ (n : ℕ) (d : Digest) (q : ℕ) (body rest : Bytes)
    (top : Digest), (Scheme.climb n d q body).runLog L = some (some (top, rest)) →
    32 * n ≤ body.length ∧ rest = body.drop (32 * n)
  | 0, d, q, body, rest, top, h => by
    simp only [Scheme.climb, OProg.runLog, Option.some.injEq, Prod.mk.injEq] at h
    exact ⟨by (clear * -; first | decide | (simp only [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]; done) | ring1 | (clear * - body; omega)), by rw [← h.2]; rfl⟩
  | n + 1, d, q, body, rest, top, h => by
    unfold Scheme.climb at h
    by_cases hb : body.length < 32
    · rw [if_pos hb] at h; simp [OProg.runLog] at h
    · rw [if_neg hb] at h
      simp only [OProg.runLog] at h
      cases hf : L.find? _ with
      | none => rw [hf] at h; simp at h
      | some e =>
        rw [hf, Option.bind_some] at h
        obtain ⟨h1, h2⟩ := climb_rest S L n _ _ _ _ _ h
        simp only [List.length_drop] at h1
        refine ⟨by (clear * - hb h1; omega), by rw [h2, List.drop_drop]; congr 1; ring⟩

theorem openOne_rest (S : Scheme) (L : Log) (ci : CapI) (q : ℕ) (body rest : Bytes) (row : List K)
    (h : (S.openOne ci q body).runLog L = some (some (row, rest))) :
    posBytes S ci ≤ body.length ∧ rest = body.drop (posBytes S ci) := by
  unfold Scheme.openOne at h
  split_ifs at h with hb
  · simp [OProg.runLog] at h
  · simp only [OProg.runLog] at h
    cases hf : L.find? _ with
    | none => rw [hf] at h; simp at h
    | some e =>
      rw [hf, Option.bind_some, OProgFacts.runLog_bind] at h
      cases hc : (Scheme.climb (ci.ht - ci.lv) e.2 (q % 2 ^ ci.ht) (body.drop (S.lb ci))).runLog L with
      | none => rw [hc] at h; simp at h
      | some o =>
        rw [hc, Option.bind_some] at h
        rcases o with _ | ⟨top, rest'⟩
        · simp [OProg.runLog] at h
        · simp only [OProg.runLog] at h
          split_ifs at h
          · simp only [Option.some.injEq, Prod.mk.injEq] at h
            obtain ⟨h1, h2⟩ := climb_rest S L _ _ _ _ _ _ hc
            simp only [List.length_drop] at h1
            refine ⟨by unfold posBytes; (clear * - hb h1; omega), ?_⟩
            rw [← h.2, h2, List.drop_drop]
            unfold posBytes
            congr 1
          · simp at h

theorem openAll_rest (S : Scheme) (L : Log) (ci : CapI) : ∀ (ps : List ℕ) (body rest : Bytes)
    (rows : List (List K)), (S.openAll ci ps body).runLog L = some (some (rows, rest)) →
    ps.length * posBytes S ci ≤ body.length ∧ rest = body.drop (ps.length * posBytes S ci)
  | [], body, rest, rows, h => by
    simp only [Scheme.openAll, OProg.runLog, Option.some.injEq, Prod.mk.injEq] at h
    exact ⟨by simp, by rw [← h.2]; simp⟩
  | p :: ps, body, rest, rows, h => by
    simp only [Scheme.openAll, OProgFacts.runLog_bind] at h
    cases h1 : (S.openOne ci p body).runLog L with
    | none => rw [h1] at h; simp at h
    | some o =>
      rw [h1, Option.bind_some] at h
      rcases o with _ | ⟨r, rest₁⟩
      · simp [OProg.runLog] at h
      · simp only [OProgFacts.runLog_bind] at h
        cases h2 : (S.openAll ci ps rest₁).runLog L with
        | none => rw [h2] at h; simp at h
        | some o' =>
          rw [h2, Option.bind_some] at h
          rcases o' with _ | ⟨rs, rest₂⟩
          · simp [OProg.runLog] at h
          · simp only [OProg.runLog, Option.some.injEq, Prod.mk.injEq] at h
            obtain ⟨a1, a2⟩ := openOne_rest S L ci p body rest₁ r h1
            obtain ⟨b1, b2⟩ := openAll_rest S L ci ps rest₁ rest₂ rs h2
            rw [a2, List.length_drop] at b1
            rw [a2, List.drop_drop] at b2
            simp only [List.length_cons]
            refine ⟨by rw [Nat.succ_mul]; (clear * - a1 b1; omega), by rw [← h.2, b2]; congr 1; ring⟩

/-- **One opening** of `ps` positions of the commitment `caps[i]`: the event is `query rows`, the
body advances by `|ps| · posBytes S ci`, the state and the pending bytes are kept. -/
theorem trun_query (S : Scheme) (L : Log) {i : ℕ} {ps : List ℕ}
    {k : List (List K) → VerifierProgram Bool} {st : Digest} {buf : Bytes} {caps : List CapI}
    {body : Bytes} {h : List Ev} {b : Bool} {e : Ev} {post : List Ev} {ci : CapI}
    (hc : caps[i]? = some ci)
    (ht : S.trun L (.query i ps k) st buf caps body h = some (b, h ++ e :: post)) :
    ∃ rows, e = .query rows ∧ (VerifierProgram.query i ps k).after [e] = some (k rows) ∧
      ps.length * posBytes S ci ≤ body.length ∧
      S.trun L (k rows) st buf caps (body.drop (ps.length * posBytes S ci)) (h ++ [e]) =
        some (b, h ++ e :: post) := by
  have hcon : ∀ b', some (b', h) ≠ some (b, h ++ e :: post) := fun b' he => by
    simp only [Option.some.injEq, Prod.mk.injEq] at he
    have := congrArg List.length he.2
    simp at this
  simp only [Scheme.trun, hc] at ht
  cases ho : (S.openAll ci ps body).runLog L with
  | none => rw [ho] at ht; simp at ht
  | some o =>
    rw [ho, Option.bind_some] at ht
    rcases o with _ | ⟨rows, rest⟩
    · exact absurd ht (hcon _)
    · have hpre := trun_prefix S L _ _ _ _ _ _ _ _ ht
      have he0 : Ev.query rows = e := by
        have := head_of_prefix (h := h) (l := post) (post := []) (by simpa using hpre)
        exact this
      subst he0
      obtain ⟨h1, h2⟩ := openAll_rest S L ci ps body rest rows ho
      exact ⟨rows, rfl, by simp only [VerifierProgram.after], h1,
        by rw [← h2]; exact ht⟩

/-! ## `simK2`'s samples are the first-match chain -/

/-! ## The schedule's view of `C_rec`'s opening (P20, by evaluation) -/

/-- The kinds of items without openings (`driveItems`: a cap of `2^c` nodes is a commitment of
`32 · 2^c` bytes, a positions item `nPosQ` samples). -/
def itemK2 (p : Params) (sh : Ref → ℕ × ℕ) : List Item → List K2
  | [] => []
  | .read m :: its => List.replicate m .read ++ itemK2 p sh its
  | .readW m _ :: its => List.replicate m .read ++ itemK2 p sh its
  | .sample :: its => .sample :: itemK2 p sh its
  | .cap c r :: its => .commit (sh r).1 (sh r).2 (nodeBytes * 2 ^ c) :: itemK2 p sh its
  | .positions r :: its => List.replicate (p.level r).nPosQ .sample ++ itemK2 p sh its
  | .opening _ :: its => itemK2 p sh its

-- (R11-IS, M′: `openRec_P20` is removed: B1's replay through `C_rec`'s opening, false at `S2GM`, where
-- there is no `C_rec`; its consumers in `LvmCertSExq2` went with it.)

/-! ## Kinds -/

/-- v1's kinds (reads and samples) as `K2`. -/
def toK2 : EvK → K2
  | .read => .read
  | .sample => .sample
  | .other => .read

theorem forall₂_append {a b : List Ev} {c d : List K2} (h1 : List.Forall₂ KM a c)
    (h2 : List.Forall₂ KM b d) : List.Forall₂ KM (a ++ b) (c ++ d) := by
  induction h1 with
  | nil => exact h2
  | cons h _ ih => exact .cons h ih

/-- A history of v1's kinds (no `other`) has the kinds `toK2`. -/
theorem forall₂_of_kinds : ∀ (l : List Ev) (ks : List EvK), l.map kindOf = ks →
    EvK.other ∉ ks → List.Forall₂ KM l (ks.map toK2)
  | [], _, h, _ => by subst h; exact .nil
  | e :: l, ks, h, ho => by
    subst h
    simp only [List.map_cons, List.mem_cons, not_or] at ho ⊢
    refine .cons ?_ (forall₂_of_kinds l _ rfl ho.2)
    cases e <;> simp [kindOf, toK2, KM] at ho ⊢

theorem sl_zero (B : List UInt8) (a : ℕ) : sl B a 0 = [] := by simp [sl]

end Lvm.ASM
end
-- ===== end of `LvmCertSExq2Run` =====

/-!
# O5c's helpers (B1's two-root replay)

The generic pieces of B1's O5c (`Ex_inv`, `hdrS_inv`, `byte0_of_prefix`, the kinds of the replayed events, the
chain's targets). M′ (R11-IS): B1's `ext_eq_gen` and its P20 facts are removed (`C_rec` is gone); its proof is at
ff8902c2.
-/

set_option autoImplicit false

namespace Lvm.ASM

open RecursionFast Lvm.FS Lvm.T
open LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Protocol.Compile.VerifierProgram LeanVM.Protocol.Whir.Sound LeanVM.Protocol.EndToEnd
open LeanVM.Protocol.Whir
open scoped NNReal ENNReal

/-! ## The child of WP-13a's node witness -/

/-! ## The replay of an accepted proof -/

theorem Ex_inv (S : Scheme) {c : RecursionFast.Digest} {π : RecursionFast.Proof} {L : Log} {x : S.Stmt}
    {h : List Ev}
    (hx : ∀ {W' : Type} (ext : RecursionFast.Digest → S.Stmt → List Ev → W'),
      S.Ex ext c π L = some (ext c x h)) :
    ∃ body e₀ e₁, S.hdr π = some (x, body) ∧
      L.find? (fun e => decide (e.1 = toQ S.q0)) = some e₀ ∧
      L.find? (fun e => decide (e.1 = S.seedQ e₀.2 x)) = some e₁ ∧
      S.trun L (S.P x) e₁.2 [] [] body [] = some (true, h) := by
  have hh := hx (fun _ x h => (x, h))
  unfold Scheme.Ex at hh
  rcases hhdr : S.hdr π with _ | ⟨x', body⟩
  · rw [hhdr] at hh; simp at hh
  · rw [hhdr] at hh
    simp only at hh
    split_ifs at hh
    cases h0 : L.find? (fun e => decide (e.1 = toQ S.q0)) with
    | none => rw [h0] at hh; simp at hh
    | some e₀ =>
      rw [h0, Option.bind_some] at hh
      cases h1 : L.find? (fun e => decide (e.1 = S.seedQ e₀.2 x')) with
      | none => rw [h1] at hh; simp at hh
      | some e₁ =>
        rw [h1, Option.bind_some] at hh
        cases hr : S.trun L (S.P x') e₁.2 [] [] body [] with
        | none => rw [hr] at hh; simp at hh
        | some r =>
          rw [hr, Option.bind_some] at hh
          obtain ⟨b, hf⟩ := r
          split_ifs at hh with hb
          simp only [Option.some.injEq, Prod.mk.injEq] at hh
          obtain ⟨rfl, rfl⟩ := hh
          refine ⟨body, e₀, e₁, rfl, rfl, h1, ?_⟩
          rw [hr]
          simp only at hb
          rw [hb]

theorem byte0_of_prefix {π : RecursionFast.Proof} (h : π.data.toList.take 8 = sPrefix) : π.data[0]? = some 0x53 := by
  have := congrArg (fun l : List UInt8 => l[0]?) h
  simp only [sPrefix] at this
  simpa using this

/-! ## The roots -/

/-! ## Event kinds of `C_rec`'s opening head -/

theorem read_after {l : List Ev} {c : E} (h : (readScalar).after l = some (.ret c)) :
    l = [Ev.read c] := by
  rcases l with _ | ⟨e, _ | ⟨e', es⟩⟩
  · simp [readScalar, VerifierProgram.after] at h
  · cases e <;> simp [readScalar, VerifierProgram.after] at h; subst h; rfl
  · cases e <;> cases e' <;> simp [readScalar, VerifierProgram.after] at h

theorem readScalars_after_eq : ∀ (n : ℕ) {l : List Ev} {xs : List E},
    (readScalars n).after l = some (.ret xs) → l = xs.map Ev.read
  | 0, l, xs, h => by
    cases l with
    | nil => simp [readScalars, VerifierProgram.after] at h; subst h; rfl
    | cons e es => cases e <;> simp [readScalars, VerifierProgram.after] at h
  | n + 1, l, xs, h => by
    obtain ⟨y, l₁, l₂, rfl, h1, h2⟩ := after_bind_ret (p := readScalar) h
    obtain ⟨ys, m₁, m₂, rfl, h3, h4⟩ := after_bind_ret h2
    rw [read_after h1, readScalars_after_eq n h3]
    cases m₂ with
    | nil => simp [VerifierProgram.after] at h4; subst h4; simp
    | cons e es => cases e <;> simp [VerifierProgram.after] at h4

/-- **A level's proof-of-work prefix** (`grindPre g`, `g > 0`): the separator and the nonce. -/
theorem grindPre_after {g : ℕ} (hg : g ≠ 0) {l : List Ev} (h : (grindPre g).after l = some (.ret ())) :
    ∃ c y, l = [Ev.sample c, Ev.read y] := by
  unfold grindPre at h
  rw [if_neg hg] at h
  obtain ⟨c, l₁, l₂, rfl, h1, h2⟩ := after_bind_ret (p := sampleChallenge) h
  obtain rfl := sample_after h1
  obtain ⟨y, m₁, m₂, rfl, h3, h4⟩ := after_bind_ret (p := readScalar) h2
  obtain rfl := read_after h3
  cases m₂ with
  | nil => exact ⟨c, y, rfl⟩
  | cons e es => cases e <;> simp [VerifierProgram.after] at h4

/-- **A level's PoW check** (`powCheck g`, `g > 0`): one challenge. -/
theorem powCheck_after {g : ℕ} (hg : g ≠ 0) {l : List Ev} (h : (powCheck g).after l = some (.ret ())) :
    ∃ c, l = [Ev.sample c] := by
  unfold powCheck at h
  rw [if_neg hg] at h
  obtain ⟨c, l₁, l₂, rfl, h1, h2⟩ := after_bind_ret (p := sampleChallenge) h
  obtain rfl := sample_after h1
  cases l₂ with
  | nil => exact ⟨c, rfl⟩
  | cons e es =>
    unfold VerifierProgram.require at h2
    split_ifs at h2 <;> cases e <;> simp [VerifierProgram.after] at h2

theorem roundPoly_kinds {t : E} {l : List Ev} {q : List E}
    (h : (LeanVM.Protocol.Verifier.sumcheckRoundPoly 3 t none).after l = some (.ret q)) :
    l.map kindOf = [.read, .read] := by
  unfold LeanVM.Protocol.Verifier.sumcheckRoundPoly at h
  obtain ⟨c₀, l₁, l₂, rfl, h1, h2⟩ := after_bind_ret (p := readScalar) h
  obtain ⟨tl, m₁, m₂, rfl, h3, h4⟩ := after_bind_ret h2
  have hl := readScalars_after_len _ h3
  rw [read_after h1, readScalars_after_eq _ h3]
  cases m₂ with
  | nil =>
    obtain ⟨c₂, rfl⟩ : ∃ c₂, tl = [c₂] := by
      rcases tl with _ | ⟨a, _ | ⟨b, t'⟩⟩ <;> simp at hl ⊢
    rfl
  | cons e es => cases e <;> simp [VerifierProgram.after] at h4

theorem foldRoundsT_kinds : ∀ (n : ℕ) (s : WhirStateT) (lf : List E) {l : List Ev}
    {r : WhirStateT × List E}, (foldRoundsT n s lf).after l = some (.ret r) →
      l.map kindOf = (List.replicate n [EvK.sample, .read, .read]).flatten
  | 0, s, lf, l, r, h => by
    cases l with
    | nil => rfl
    | cons e es => cases e <;> simp [foldRoundsT, VerifierProgram.after] at h
  | n + 1, s, lf, l, r, h => by
    unfold foldRoundsT at h
    obtain ⟨c, l₁, l₂, rfl, h1, h2⟩ := after_bind_ret (p := sampleChallenge) h
    obtain rfl := sample_after h1
    obtain ⟨quad, m₁, m₂, rfl, h3, h4⟩ := after_bind_ret h2
    rw [List.map_append, List.map_append, roundPoly_kinds h3, foldRoundsT_kinds n _ _ h4,
      List.replicate_succ, List.flatten_cons]
    rfl

/-- The number of samples of a history is the count of its sample kinds. -/
theorem samples_length : ∀ (l : List Ev), (l.filterMap sampleOf).length = (l.map kindOf).count .sample
  | [] => rfl
  | e :: l => by
    rw [List.map_cons, List.count_cons, ← samples_length l]
    cases e <;> simp [sampleOf, kindOf, List.filterMap_cons]

/-! ## The decoder's inputs -/

/-! ## Level 1 (lvm2 S4) -/

theorem smpOf_eq : smpOf = sampleOf := by
  funext e
  cases e <;> rfl

/-- The positions a completed run of `samplePositionsAux` returns. -/
def posLen (per : ℕ) : ℕ → ℕ → ℕ
  | 0, _ => 0
  | fuel + 1, rem => if rem = 0 then 0 else min per rem + posLen per fuel (rem - min per rem)

/-- **A run of the positions** is samples only, and returns `posLen` positions. -/
theorem samplePositionsAux_kinds (per depth : ℕ) : ∀ (fuel rem : ℕ) {l : List Ev} {qs : List ℕ},
    (samplePositionsAux per depth fuel rem).after l = some (.ret qs) →
      (∀ e ∈ l, kindOf e = .sample) ∧ qs.length = posLen per fuel rem
  | 0, rem, l, qs, h => by
    cases l with
    | nil =>
      simp only [samplePositionsAux, VerifierProgram.after, Option.some.injEq] at h
      cases h
      simp [posLen]
    | cons e es => cases e <;> simp [samplePositionsAux, VerifierProgram.after] at h
  | fuel + 1, rem, l, qs, h => by
    unfold samplePositionsAux at h
    by_cases hr : rem = 0
    · rw [if_pos hr] at h
      cases l with
      | nil =>
        simp only [VerifierProgram.after, Option.some.injEq] at h
        cases h
        simp [posLen, hr]
      | cons e es => cases e <;> simp [VerifierProgram.after] at h
    · rw [if_neg hr] at h
      obtain ⟨c, l₁, l₂, rfl, h1, h2⟩ := after_bind_ret (p := sampleChallenge) h
      obtain rfl := sample_after h1
      obtain ⟨rest, m₁, m₂, rfl, h3, h4⟩ := after_bind_ret h2
      obtain ⟨k1, k2⟩ := samplePositionsAux_kinds per depth fuel _ h3
      cases m₂ with
      | nil =>
        simp only [VerifierProgram.after, Option.some.injEq] at h4
        cases h4
        refine ⟨fun e he => ?_, ?_⟩
        · simp only [List.singleton_append, List.append_nil, List.mem_cons] at he
          rcases he with rfl | he
          · rfl
          · exact k1 e he
        · simp [posLen, hr, k2]
      | cons e es => cases e <;> simp [VerifierProgram.after] at h4

theorem bitsToNat_symmN (n v : ℕ) (hv : v < 2 ^ n) :
    bitsToNat ((bitsEquiv n).symm ⟨v, hv⟩) = v := by
  rw [← bitsEquiv_val, Equiv.apply_symm_apply]

/-- At a node `query i qs`, a `bind` stays at it. -/
theorem atQuery_bind {α β : Type} {p : VerifierProgram α} {l : List Ev} {i : ℕ} {qs : List ℕ}
    (f : α → VerifierProgram β) (h : ∃ K, p.after l = some (.query i qs K)) :
    ∃ K, (p.bind f).after l = some (.query i qs K) := by
  obtain ⟨K, hK⟩ := h
  exact ⟨_, after_bind_of_after f p l hK⟩

/-- After a return of `p`, `p.bind f` is where `f` is. -/
theorem atQuery_append {α β : Type} {p : VerifierProgram α} {f : α → VerifierProgram β} {l₁ l₂ : List Ev}
    {a : α} {i : ℕ} {qs : List ℕ} (h1 : p.after l₁ = some (.ret a))
    (h2 : ∃ K, (f a).after l₂ = some (.query i qs K)) :
    ∃ K, (p.bind f).after (l₁ ++ l₂) = some (.query i qs K) := by
  rw [after_bind_append f h1]
  exact h2

theorem not_commit_toK2 {ht w nb : ℕ} : ∀ (ks : List EvK), K2.commit ht w nb ∉ ks.map toK2
  | [] => by simp
  | k :: ks => by
    simp only [List.map_cons, List.mem_cons, not_or]
    exact ⟨by cases k <;> simp [toK2], not_commit_toK2 ks⟩

-- (R11-IS, M′: B1's `ext_eq_gen` (O5c for the two-root `PSWith` with two `C_rec` levels) and its replay facts
-- `kA1`, `kB`, `kA2`, `not_midFollows_ret` are removed: they read `openRec_P20`, false at `S2GM`. The generic helpers
-- above stay for M′'s `ext_eqM20`; B1's proof is at ff8902c2.)

end Lvm.ASM
