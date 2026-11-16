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
      refine ⟨by rw [e]; simp, by rw [e]; norm_num; omega⟩
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
  rw [Lvm.X.pw, Lvm.X.packBytes_getDX, if_pos (by omega), toWord, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (ofLE_take8_lt _), u64At_eq]
  congr 1
  apply List.ext_getElem (by simp; omega)
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
    List.map_congr_left fun k hk => digestAt_congr h (by simp [offSig]; (clear * -; omega)) (by
      simp only [List.mem_range, wotsLen] at hk; simp only [offSig]; (clear * - hH hk; omega))
  have e3 : ((List.range sigHeight).map fun k => digestAt b (offSig + 8 + 32 * wotsLen + 32 * k)) =
      (List.range sigHeight).map fun k => digestAt b' (offSig + 8 + 32 * wotsLen + 32 * k) :=
    List.map_congr_left fun k hk => digestAt_congr h (by simp [offSig, wotsLen]; (clear * -; omega)) (by
      simp only [List.mem_range, sigHeight] at hk; simp only [offSig, wotsLen]; (clear * - hH hk; omega))
  unfold sigAt
  rw [e1, e2, e3]

theorem ofProof_congr {b b' : ByteArray} (h : HdrEq b b') : Header.ofProof b = Header.ofProof b' := by
  unfold Header.ofProof
  rw [u64At_congr h (o := offB) (by decide) (by decide), digestAt_congr h (o := offVk) (by decide) (by decide),
    digestAt_congr h (o := offCL) (by decide) (by decide), digestAt_congr h (o := offS) (by decide) (by decide),
    u64At_congr h (o := offN) (by decide) (by decide), digestAt_congr h (o := offH) (by decide) (by decide),
    sigAt_congr h]

/-- **The statement's header is π's** (`hdrS`'s statement: π's bytes `8 … 4927`). -/
theorem hdrOf_eq (π : Proof) (hs : headerBytes ≤ π.size) :
    hdrOf ((π.data.toList.drop 8).take hdrLen) = Header.ofProof π := by
  unfold hdrOf
  apply ofProof_congr
  intro k hk hk'
  have hl : π.data.toList.length = π.size := Array.length_toList
  have hL : hdrLen = 5976 := rfl
  have hH : headerBytes = 5984 := rfl
  have hF : hdrFix = 4928 := rfl
  rw [get!_eq_getD, get!_eq_getD]
  rw [List.getD_append_right _ _ _ _ (by simp; omega)]
  simp only [List.length_replicate]
  rw [List.getD_eq_getElem _ _ (by simp; omega), List.getD_eq_getElem _ _ (by (clear * - hs hk hk' hl hH hF; omega))]
  simp only [List.getElem_take, List.getElem_drop]
  congr 1
  (clear * - hk hk' hH hF; omega)

theorem wsAt_shift (W : ℕ → RecursionFast.Word) (a u n : ℕ) :
    Lvm.X.wsAt (fun j => W (a + j)) u n = Lvm.X.wsAt W (a + u) n := by
  simp only [Lvm.X.wsAt, Nat.add_assoc]

/-- **The header's signature** is WP-13a's `σ_leaf` (words `19 …` of π). -/
theorem sig_eq (π : Proof) (hs : hdrFix ≤ π.size) :
    sigAt π offSig = Lvm.X.sigOfF fun j => Lvm.X.pw π (19 + j) := by
  have hH : hdrFix = 4928 := rfl
  have e1 : u64At π offSig = (Lvm.X.pw π (19 + 0)).toNat := (pw_toNat π 19 (by omega)).symm
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

/-- **The replay on kinds**: the history and the final state. -/
def simK : List EvK → ℕ → ℕ → Digest → Option (List Ev × Digest)
  | [], _, _, st => some ([], st)
  | .read :: ks, off, pend, st =>
    (simK ks (off + 24) pend st).map fun r => (.read (S.decE (sl B off 24)) :: r.1, r.2)
  | .sample :: ks, off, pend, st =>
    (L.find? fun e => e.1 = toQ (st.toList ++ sl B pend (off - pend))).bind fun e =>
      (simK ks off off e.2).map fun r => (.sample (S.chal e.2) :: r.1, r.2)
  | .other :: _, _, _, _ => none

/-- The body offset after the kinds. -/
def offK : List EvK → ℕ → ℕ
  | [], off => off
  | .read :: ks, off => offK ks (off + 24)
  | _ :: ks, off => offK ks off

/-- The first pending byte after the kinds. -/
def pendK : List EvK → ℕ → ℕ → ℕ
  | [], _, pend => pend
  | .read :: ks, off, pend => pendK ks (off + 24) pend
  | .sample :: ks, off, _ => pendK ks off off
  | .other :: ks, off, pend => pendK ks off pend

/-- The slices the samples absorb (WP-13a's `fsPre` on kinds). -/
def fsPreK : List EvK → ℕ → ℕ → List (ℕ × ℕ)
  | [], _, _ => []
  | .read :: ks, off, pend => fsPreK ks (off + 24) pend
  | .sample :: ks, off, pend => (pend, off - pend) :: fsPreK ks off off
  | .other :: ks, off, pend => fsPreK ks off pend

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

theorem not_self_append {h l : List Ev} (e : Ev) (hh : h = h ++ e :: l) : False := by
  have := congrArg List.length hh
  simp at this

theorem head_of_prefix {h l post : List Ev} {e e₀ : Ev} (hp : h ++ [e] <+: h ++ e₀ :: l ++ post) :
    e = e₀ := by
  simpa using hp

/-! ## The replay is `simK` -/

theorem sl_append (B : List UInt8) {pend off : ℕ} (h1 : pend ≤ off) (n : ℕ) :
    sl B pend (off - pend) ++ (B.drop off).take n = sl B pend (off + n - pend) := by
  unfold sl
  rw [show off + n - pend = (off - pend) + n by omega, List.take_add, List.drop_drop,
    show pend + (off - pend) = off by omega]

theorem drop_drop' (B : List UInt8) (a n : ℕ) : (B.drop a).drop n = B.drop (a + n) := by
  rw [List.drop_drop]

/-- **The replay along known kinds** (`trun` from a state whose pending bytes and body are slices
of `B`). -/
theorem trun_simK (S : Scheme) (hU : S.Uniform) (L : Log) (B : List UInt8) : ∀ (ks : List EvK)
    (p : VerifierProgram Bool) (off pend : ℕ) (st : Digest) (caps : List CapI)
    (h pre post : List Ev) (b : Bool),
    EvK.other ∉ ks → pend ≤ off → pre.map kindOf = ks →
    S.trun L p st (sl B pend (off - pend)) caps (B.drop off) h = some (b, h ++ pre ++ post) →
    ∃ st' p' caps', simK S L B ks off pend st = some (pre, st') ∧
      pendK ks off pend ≤ offK ks off ∧
      S.trun L p' st' (sl B (pendK ks off pend) (offK ks off - pendK ks off pend)) caps'
        (B.drop (offK ks off)) (h ++ pre) = some (b, h ++ pre ++ post) := by
  intro ks
  induction ks with
  | nil =>
    intro p off pend st caps h pre post b _ hle hk e
    have : pre = [] := List.map_eq_nil_iff.1 hk
    subst this
    exact ⟨st, p, caps, rfl, hle, by simpa [pendK, offK] using e⟩
  | cons k ks ih =>
    intro p off pend st caps h pre post b hno hle hk e
    obtain ⟨e₀, pre', rfl, hk0, hks⟩ : ∃ e₀ pre', pre = e₀ :: pre' ∧ kindOf e₀ = k ∧
        pre'.map kindOf = ks := by
      rcases pre with _ | ⟨e₀, pre'⟩
      · simp at hk
      · simp only [List.map_cons, List.cons.injEq] at hk
        exact ⟨e₀, pre', rfl, hk.1, hk.2⟩
    have hno' : EvK.other ∉ ks := fun hm => hno (List.mem_cons_of_mem _ hm)
    have hcon : ∀ b', some (b', h) ≠ some (b, h ++ (e₀ :: pre') ++ post) := fun b' he => by
      simp only [Option.some.injEq, Prod.mk.injEq] at he
      have := congrArg List.length he.2
      simp at this
    cases p with
    | ret a => exact absurd e (hcon _)
    | fail => exact absurd e (hcon _)
    | grind _ _ => exact absurd e (hcon _)
    | read k' =>
      simp only [Scheme.trun, show ∀ n, S.rw n = 24 from hU] at e
      split_ifs at e with hlen
      · exact absurd e (hcon _)
      have hpre := trun_prefix S L _ _ _ _ _ _ _ _ e
      have he0 := head_of_prefix hpre
      subst he0
      simp only [kindOf] at hk0
      subst hk0
      have hl : off + 24 ≤ B.length := by simp at hlen; (clear * - hlen; omega)
      rw [sl_append B hle, drop_drop'] at e
      obtain ⟨st', p', caps', hs, hle', ht⟩ := ih _ (off + 24) pend st caps
        (h ++ [Ev.read (S.decE ((B.drop off).take 24))]) pre' post b hno' (by (clear * - hle; omega)) hks
        (by rw [e]; simp)
      refine ⟨st', p', caps', ?_, hle', by simpa [pendK, offK] using ht⟩
      simp only [simK, hs, Option.map_some]
      rfl
    | sample k' =>
      simp only [Scheme.trun] at e
      split_ifs at e with hq
      · cases hfd : L.find? (fun e => decide (e.1 = toQ (st.toList ++ sl B pend (off - pend)))) with
        | none => rw [hfd] at e; simp at e
        | some e' =>
          rw [hfd, Option.bind_some] at e
          have hpre := trun_prefix S L _ _ _ _ _ _ _ _ e
          have he0 := head_of_prefix hpre
          subst he0
          simp only [kindOf] at hk0
          subst hk0
          have e2 : S.trun L (k' (S.chal e'.2)) e'.2 (sl B off (off - off)) caps (B.drop off)
              (h ++ [Ev.sample (S.chal e'.2)]) = some (b, h ++ [Ev.sample (S.chal e'.2)] ++ pre' ++ post) := by
            simpa [sl] using e
          obtain ⟨st', p', caps', hs, hle', ht⟩ := ih _ off off e'.2 caps _ pre' post b hno'
            le_rfl hks e2
          refine ⟨st', p', caps', ?_, hle', by simpa [pendK, offK] using ht⟩
          simp only [simK, hfd, Option.bind_some, hs, Option.map_some]
      · exact absurd e (hcon _)
    | commit ht w k' =>
      simp only [Scheme.trun] at e
      split_ifs at e
      · exact absurd e (hcon _)
      have hpre := trun_prefix S L _ _ _ _ _ _ _ _ e
      have he0 := head_of_prefix hpre
      subst he0
      simp only [kindOf] at hk0
      exact absurd (hk0 ▸ List.mem_cons_self) hno
    | query i ps k' =>
      simp only [Scheme.trun] at e
      cases hc : caps[i]? with
      | none => rw [hc] at e; exact absurd e (hcon _)
      | some ci =>
        rw [hc] at e
        simp only at e
        cases ho : (S.openAll ci ps (B.drop off)).runLog L with
        | none => rw [ho] at e; simp at e
        | some o =>
          rw [ho, Option.bind_some] at e
          rcases o with _ | ⟨rows, rest⟩
          · exact absurd e (hcon _)
          · have hpre := trun_prefix S L _ _ _ _ _ _ _ _ e
            have he0 := head_of_prefix hpre
            subst he0
            simp only [kindOf] at hk0
            exact absurd (hk0 ▸ List.mem_cons_self) hno

/-! ## `simK`'s samples are the first-match chain -/

/-- **The chain**: `simK`'s samples are the challenges of `fmAns T` from position `j + 1` on, when
the chain's targets absorb the slices `fsPreK`. -/
theorem simK_chain (S : Scheme) (L : Log) (B : List UInt8) (T : ℕ → Digest → ByteArray)
    (st₀ : Digest) : ∀ (ks : List EvK) (off pend : ℕ) (st : Digest) (j : ℕ) (pre : List Ev)
    (st' : Digest), simK S L B ks off pend st = some (pre, st') →
    Lvm.X.fmAns T st₀ L j = some st →
    (∀ i (hi : i < (fsPreK ks off pend).length) (s : Digest),
      T (j + 1 + i) s = toQ (s.toList ++ sl B ((fsPreK ks off pend)[i]).1 ((fsPreK ks off pend)[i]).2)) →
    (∀ i (hi : i < (pre.filterMap smpOf).length), ∃ a,
      Lvm.X.fmAns T st₀ L (j + 1 + i) = some a ∧ (pre.filterMap smpOf)[i] = S.chal a) ∧
    Lvm.X.fmAns T st₀ L (j + (pre.filterMap smpOf).length) = some st' := by
  intro ks
  induction ks with
  | nil =>
    intro off pend st j pre st' hs hj _
    simp only [simK, Option.some.injEq, Prod.mk.injEq] at hs
    obtain ⟨rfl, rfl⟩ := hs
    exact ⟨fun i hi => by simp at hi, by simpa using hj⟩
  | cons k ks ih =>
    intro off pend st j pre st' hs hj hT
    cases k with
    | read =>
      simp only [simK] at hs
      cases hr : simK S L B ks (off + 24) pend st with
      | none => rw [hr] at hs; simp at hs
      | some r =>
        obtain ⟨pre₁, st₁⟩ := r
        rw [hr, Option.map_some, Option.some.injEq, Prod.mk.injEq] at hs
        obtain ⟨rfl, rfl⟩ := hs
        have := ih (off + 24) pend st j pre₁ st₁ hr hj (fun i hi s => hT i hi s)
        have e : (Ev.read (S.decE (sl B off 24)) :: pre₁).filterMap smpOf = pre₁.filterMap smpOf := rfl
        rw [e]
        exact this
    | sample =>
      simp only [simK] at hs
      cases hfd : L.find? (fun e => decide (e.1 = toQ (st.toList ++ sl B pend (off - pend)))) with
      | none => rw [hfd] at hs; simp at hs
      | some e =>
        rw [hfd, Option.bind_some] at hs
        cases hr : simK S L B ks off off e.2 with
        | none => rw [hr] at hs; simp at hs
        | some r =>
          obtain ⟨pre₁, st₁⟩ := r
          rw [hr, Option.map_some, Option.some.injEq, Prod.mk.injEq] at hs
          obtain ⟨rfl, rfl⟩ := hs
          have hT0 := hT 0 (by simp [fsPreK]) st
          simp only [fsPreK, List.getElem_cons_zero, add_zero] at hT0
          have hj1 : Lvm.X.fmAns T st₀ L (j + 1) = some e.2 := by
            simp only [Lvm.X.fmAns, hj, Option.bind_some, hT0, hfd, Option.map_some]
          obtain ⟨h1, h2⟩ := ih off off e.2 (j + 1) pre₁ st₁ hr hj1 (fun i hi s => by
            have := hT (i + 1) (by simp [fsPreK]; omega) s
            simp only [fsPreK, List.getElem_cons_succ] at this
            rw [show j + 1 + 1 + i = j + 1 + (i + 1) by (clear * -; omega)]
            exact this)
          refine ⟨fun i hi => ?_, ?_⟩
          · rcases i with _ | i
            · exact ⟨e.2, by simpa using hj1, by simp [smpOf]⟩
            · simp only [List.filterMap_cons, smpOf, List.length_cons] at hi
              obtain ⟨a, ha, he⟩ := h1 i (by (clear * - hi; omega))
              refine ⟨a, by rw [show j + 1 + (i + 1) = j + 1 + 1 + i by (clear * -; omega)]; exact ha, ?_⟩
              simpa [smpOf] using he
          · simp only [List.filterMap_cons, smpOf, List.length_cons]
            rw [show j + (List.length (List.filterMap smpOf pre₁) + 1) =
              j + 1 + (List.filterMap smpOf pre₁).length by (clear * -; omega)]
            exact h2
    | other => simp [simK] at hs

/-! ## Runs of reads -/

theorem simK_reads (S : Scheme) (L : Log) (B : List UInt8) : ∀ (n off pend : ℕ) (st : Digest),
    simK S L B (List.replicate n .read) off pend st =
      some ((List.range n).map fun i => Ev.read (S.decE (sl B (off + 24 * i) 24)), st)
  | 0, off, pend, st => rfl
  | n + 1, off, pend, st => by
    rw [List.replicate_succ, simK, simK_reads S L B n (off + 24) pend st, Option.map_some,
      List.range_succ_eq_map]
    simp only [List.map_cons, List.map_map, Nat.mul_zero, Nat.add_zero]
    refine congrArg (fun l => some (_ :: l, st)) (List.map_congr_left fun i _ => ?_)
    simp only [Function.comp_apply, Nat.succ_eq_add_one]
    rw [show off + 24 + 24 * i = off + 24 * (i + 1) by ring]

theorem offK_reads : ∀ (n off : ℕ), offK (List.replicate n .read) off = off + 24 * n
  | 0, off => rfl
  | n + 1, off => by rw [List.replicate_succ, offK, offK_reads n]; ring

/-! ## Kinds of items -/

/-- Items of reads and samples only. -/
def RSItems : List Item → Bool
  | [] => true
  | .read _ :: its => RSItems its
  | .sample :: its => RSItems its
  | _ :: _ => false

theorem fsPreK_reads (ks : List EvK) : ∀ (m off pend : ℕ),
    fsPreK (List.replicate m .read ++ ks) off pend = fsPreK ks (off + 24 * m) pend
  | 0, off, pend => rfl
  | m + 1, off, pend => by
    rw [List.replicate_succ, List.cons_append, fsPreK, fsPreK_reads ks m]
    congr 1
    ring

/-- **WP-13a's `fsPre` is `fsPreK` on the kinds** (items of reads and samples). -/
theorem fsPre_eq_fsPreK (p : Params) : ∀ (its : List Item) (off pend : ℕ), RSItems its = true →
    Lvm.X.fsPre p its off pend = fsPreK (itemKinds its) off pend
  | [], _, _, _ => rfl
  | .read m :: its, off, pend, h => by
    rw [Lvm.X.fsPre, itemKinds, fsPreK_reads, fsPre_eq_fsPreK p its _ _ h]
    rfl
  | .sample :: its, off, pend, h => by
    rw [Lvm.X.fsPre, itemKinds, fsPreK, fsPre_eq_fsPreK p its _ _ h]
  | .readW _ _ :: _, _, _, h => by simp [RSItems] at h
  | .cap _ _ :: _, _, _, h => by simp [RSItems] at h
  | .positions _ :: _, _, _, h => by simp [RSItems] at h
  | .opening _ :: _, _, _, h => by simp [RSItems] at h

theorem other_not_mem : ∀ (its : List Item), RSItems its = true → EvK.other ∉ itemKinds its
  | [], _ => by simp [itemKinds]
  | .read m :: its, h => by simpa [itemKinds] using other_not_mem its h
  | .sample :: its, h => by simpa [itemKinds] using other_not_mem its h
  | .readW _ _ :: _, h => by simp [RSItems] at h
  | .cap _ _ :: _, h => by simp [RSItems] at h
  | .positions _ :: _, h => by simp [RSItems] at h
  | .opening _ :: _, h => by simp [RSItems] at h

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

/-- **The replay on kinds** (reads, samples, commitments): the history and the final state. -/
def simK2 : List K2 → ℕ → ℕ → Digest → Option (List Ev × Digest)
  | [], _, _, st => some ([], st)
  | .read :: ks, off, pend, st =>
    (simK2 ks (off + 24) pend st).map fun r => (.read (S.decE (sl B off 24)) :: r.1, r.2)
  | .sample :: ks, off, pend, st =>
    (L.find? fun e => e.1 = toQ (st.toList ++ sl B pend (off - pend))).bind fun e =>
      (simK2 ks off off e.2).map fun r => (.sample (S.chal e.2) :: r.1, r.2)
  | .commit ht w nb :: ks, off, pend, st =>
    (simK2 ks (off + nb) pend st).map fun r =>
      (.commit ht w (S.wordOf L (S.capI ht w (B.drop off))) :: r.1, r.2)

/-- The commitments' records the replay appends. -/
def capsK2 : List K2 → ℕ → List CapI → List CapI
  | [], _, caps => caps
  | .read :: ks, off, caps => capsK2 ks (off + 24) caps
  | .sample :: ks, off, caps => capsK2 ks off caps
  | .commit ht w nb :: ks, off, caps => capsK2 ks (off + nb) (caps ++ [S.capI ht w (B.drop off)])

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

/-- **The replay along reads, samples and commitments** (`trun` from a state whose pending bytes and
body are slices of `B`): its history is `simK2`'s, the program after it is `p.after pre`. -/
theorem trun_simK2 (S : Scheme) (hU : S.Uniform) (L : Log) (B : List UInt8) : ∀ (ks : List K2)
    (p : VerifierProgram Bool) (off pend : ℕ) (st : Digest) (caps : List CapI)
    (h pre post : List Ev) (b : Bool),
    (∀ ht w nb, K2.commit ht w nb ∈ ks → S.capBytes ht w = nb) → pend ≤ off →
    List.Forall₂ KM pre ks →
    S.trun L p st (sl B pend (off - pend)) caps (B.drop off) h = some (b, h ++ pre ++ post) →
    ∃ st' p', simK2 S L B ks off pend st = some (pre, st') ∧ p.after pre = some p' ∧
      pendK2 ks off pend ≤ offK2 ks off ∧
      S.trun L p' st' (sl B (pendK2 ks off pend) (offK2 ks off - pendK2 ks off pend))
        (capsK2 S B ks off caps) (B.drop (offK2 ks off)) (h ++ pre) = some (b, h ++ pre ++ post) := by
  intro ks
  induction ks with
  | nil =>
    intro p off pend st caps h pre post b _ hle hk e
    have : pre = [] := by cases hk; rfl
    subst this
    exact ⟨st, p, rfl, after_nil p, hle, by simpa [pendK2, offK2, capsK2] using e⟩
  | cons k ks ih =>
    intro p off pend st caps h pre post b hcb hle hk e
    obtain ⟨e₀, pre', rfl⟩ : ∃ e₀ pre', pre = e₀ :: pre' := by
      cases hk with
      | cons a b => exact ⟨_, _, rfl⟩
    obtain ⟨hk0, hks⟩ := forall₂_cons_inv hk
    have hcb' : ∀ ht w nb, K2.commit ht w nb ∈ ks → S.capBytes ht w = nb :=
      fun ht w nb hm => hcb ht w nb (List.mem_cons_of_mem _ hm)
    have hcon : ∀ b', some (b', h) ≠ some (b, h ++ (e₀ :: pre') ++ post) := fun b' he => by
      simp only [Option.some.injEq, Prod.mk.injEq] at he
      have := congrArg List.length he.2
      simp at this
    cases p with
    | ret a => exact absurd e (hcon _)
    | fail => exact absurd e (hcon _)
    | grind _ _ => exact absurd e (hcon _)
    | read k' =>
      simp only [Scheme.trun, show ∀ n, S.rw n = 24 from hU] at e
      split_ifs at e with hlen
      · exact absurd e (hcon _)
      have hpre := trun_prefix S L _ _ _ _ _ _ _ _ e
      have he0 := head_of_prefix hpre
      subst he0
      cases k with
      | sample => exact absurd hk0 (by simp [KM])
      | commit _ _ _ => exact absurd hk0 (by simp [KM])
      | read =>
        rw [sl_append B hle, drop_drop'] at e
        obtain ⟨st', p', hs, ha, hle', ht⟩ := ih _ (off + 24) pend st caps
          (h ++ [Ev.read (S.decE ((B.drop off).take 24))]) pre' post b hcb' (by (clear * - hle; omega)) hks
          (by rw [e]; simp)
        refine ⟨st', p', ?_, ?_, hle', by simpa [pendK2, offK2, capsK2] using ht⟩
        · simp only [simK2, hs, Option.map_some]
          rfl
        · simp only [VerifierProgram.after]
          exact ha
    | sample k' =>
      simp only [Scheme.trun] at e
      split_ifs at e with hq
      · cases hfd : L.find? (fun e => decide (e.1 = toQ (st.toList ++ sl B pend (off - pend)))) with
        | none => rw [hfd] at e; simp at e
        | some e' =>
          rw [hfd, Option.bind_some] at e
          have hpre := trun_prefix S L _ _ _ _ _ _ _ _ e
          have he0 := head_of_prefix hpre
          subst he0
          cases k with
          | read => exact absurd hk0 (by simp [KM])
          | commit _ _ _ => exact absurd hk0 (by simp [KM])
          | sample =>
            have e2 : S.trun L (k' (S.chal e'.2)) e'.2 (sl B off (off - off)) caps (B.drop off)
                (h ++ [Ev.sample (S.chal e'.2)]) =
                some (b, h ++ [Ev.sample (S.chal e'.2)] ++ pre' ++ post) := by
              simpa [sl] using e
            obtain ⟨st', p', hs, ha, hle', ht⟩ := ih _ off off e'.2 caps _ pre' post b hcb'
              le_rfl hks e2
            refine ⟨st', p', ?_, ?_, hle', by simpa [pendK2, offK2, capsK2] using ht⟩
            · simp only [simK2, hfd, Option.bind_some, hs, Option.map_some]
            · simp only [VerifierProgram.after]
              exact ha
      · exact absurd e (hcon _)
    | commit ht w k' =>
      simp only [Scheme.trun] at e
      split_ifs at e
      · exact absurd e (hcon _)
      have hpre := trun_prefix S L _ _ _ _ _ _ _ _ e
      have he0 := head_of_prefix hpre
      subst he0
      cases k with
      | read => exact absurd hk0 (by simp [KM])
      | sample => exact absurd hk0 (by simp [KM])
      | commit ht' w' nb =>
        obtain ⟨rfl, rfl⟩ := hk0
        have hnb : S.capBytes ht w = nb := hcb ht w nb List.mem_cons_self
        rw [hnb, sl_append B hle, drop_drop'] at e
        obtain ⟨st', p', hs, ha, hle', ht'⟩ := ih k' (off + nb) pend st
          (caps ++ [S.capI ht w (B.drop off)])
          (h ++ [Ev.commit ht w (S.wordOf L (S.capI ht w (B.drop off)))]) pre' post b hcb'
          (by (clear * - hle hnb; omega)) hks (by rw [e]; simp)
        refine ⟨st', p', ?_, ?_, hle', by simpa [pendK2, offK2, capsK2] using ht'⟩
        · simp only [simK2, hs, Option.map_some]
        · simp only [VerifierProgram.after, and_self, ite_true]
          exact ha
    | query i ps k' =>
      simp only [Scheme.trun] at e
      cases hc : caps[i]? with
      | none => rw [hc] at e; exact absurd e (hcon _)
      | some ci =>
        rw [hc] at e
        simp only at e
        cases ho : (S.openAll ci ps (B.drop off)).runLog L with
        | none => rw [ho] at e; simp at e
        | some o =>
          rw [ho, Option.bind_some] at e
          rcases o with _ | ⟨rows, rest⟩
          · exact absurd e (hcon _)
          · have hpre := trun_prefix S L _ _ _ _ _ _ _ _ e
            have he0 := head_of_prefix hpre
            subst he0
            cases k <;> simp [KM] at hk0

/-! ## One opening -/

/-- The bytes one position of the commitment `ci` takes from the body: the leaf (the row's occupied
words, `Scheme.lb`) and the siblings. -/
def posBytes (S : Scheme) (ci : CapI) : ℕ := S.lb ci + 32 * (ci.ht - ci.lv)

theorem climb_rest (S : Scheme) (L : Log) : ∀ (n : ℕ) (d : Digest) (q : ℕ) (body rest : Bytes)
    (top : Digest), (Scheme.climb n d q body).runLog L = some (some (top, rest)) →
    32 * n ≤ body.length ∧ rest = body.drop (32 * n)
  | 0, d, q, body, rest, top, h => by
    simp only [Scheme.climb, OProg.runLog, Option.some.injEq, Prod.mk.injEq] at h
    exact ⟨by (clear * -; omega), by rw [← h.2]; rfl⟩
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

/-- **The chain** (v1's `simK_chain` through commitments): `simK2`'s samples are the challenges of
`fmAns T` from position `j + 1` on, when the chain's targets absorb the slices `fsPreK2`. -/
theorem simK2_chain (S : Scheme) (L : Log) (B : List UInt8) (T : ℕ → Digest → ByteArray)
    (st₀ : Digest) : ∀ (ks : List K2) (off pend : ℕ) (st : Digest) (j : ℕ) (pre : List Ev)
    (st' : Digest), simK2 S L B ks off pend st = some (pre, st') →
    Lvm.X.fmAns T st₀ L j = some st →
    (∀ i (hi : i < (fsPreK2 ks off pend).length) (s : Digest),
      T (j + 1 + i) s = toQ (s.toList ++ sl B ((fsPreK2 ks off pend)[i]).1 ((fsPreK2 ks off pend)[i]).2)) →
    (∀ i (hi : i < (pre.filterMap smpOf).length), ∃ a,
      Lvm.X.fmAns T st₀ L (j + 1 + i) = some a ∧ (pre.filterMap smpOf)[i] = S.chal a) ∧
    Lvm.X.fmAns T st₀ L (j + (pre.filterMap smpOf).length) = some st' := by
  intro ks
  induction ks with
  | nil =>
    intro off pend st j pre st' hs hj _
    simp only [simK2, Option.some.injEq, Prod.mk.injEq] at hs
    obtain ⟨rfl, rfl⟩ := hs
    exact ⟨fun i hi => by simp at hi, by simpa using hj⟩
  | cons k ks ih =>
    intro off pend st j pre st' hs hj hT
    cases k with
    | read =>
      simp only [simK2] at hs
      cases hr : simK2 S L B ks (off + 24) pend st with
      | none => rw [hr] at hs; simp at hs
      | some r =>
        obtain ⟨pre₁, st₁⟩ := r
        rw [hr, Option.map_some, Option.some.injEq, Prod.mk.injEq] at hs
        obtain ⟨rfl, rfl⟩ := hs
        exact ih (off + 24) pend st j pre₁ st₁ hr hj (fun i hi s => hT i hi s)
    | commit ht w nb =>
      simp only [simK2] at hs
      cases hr : simK2 S L B ks (off + nb) pend st with
      | none => rw [hr] at hs; simp at hs
      | some r =>
        obtain ⟨pre₁, st₁⟩ := r
        rw [hr, Option.map_some, Option.some.injEq, Prod.mk.injEq] at hs
        obtain ⟨rfl, rfl⟩ := hs
        exact ih (off + nb) pend st j pre₁ st₁ hr hj (fun i hi s => hT i hi s)
    | sample =>
      simp only [simK2] at hs
      cases hfd : L.find? (fun e => decide (e.1 = toQ (st.toList ++ sl B pend (off - pend)))) with
      | none => rw [hfd] at hs; simp at hs
      | some e =>
        rw [hfd, Option.bind_some] at hs
        cases hr : simK2 S L B ks off off e.2 with
        | none => rw [hr] at hs; simp at hs
        | some r =>
          obtain ⟨pre₁, st₁⟩ := r
          rw [hr, Option.map_some, Option.some.injEq, Prod.mk.injEq] at hs
          obtain ⟨rfl, rfl⟩ := hs
          have hT0 := hT 0 (by simp [fsPreK2]) st
          simp only [fsPreK2, List.getElem_cons_zero, add_zero] at hT0
          have hj1 : Lvm.X.fmAns T st₀ L (j + 1) = some e.2 := by
            simp only [Lvm.X.fmAns, hj, Option.bind_some, hT0, hfd, Option.map_some]
          obtain ⟨h1, h2⟩ := ih off off e.2 (j + 1) pre₁ st₁ hr hj1 (fun i hi s => by
            have := hT (i + 1) (by simp [fsPreK2]; omega) s
            simp only [fsPreK2, List.getElem_cons_succ] at this
            rw [show j + 1 + 1 + i = j + 1 + (i + 1) by (clear * -; omega)]
            exact this)
          refine ⟨fun i hi => ?_, ?_⟩
          · rcases i with _ | i
            · exact ⟨e.2, by simpa using hj1, by simp [smpOf]⟩
            · simp only [List.filterMap_cons, smpOf, List.length_cons] at hi
              obtain ⟨a, ha, he⟩ := h1 i (by (clear * - hi; omega))
              refine ⟨a, by rw [show j + 1 + (i + 1) = j + 1 + 1 + i by (clear * -; omega)]; exact ha, ?_⟩
              simpa [smpOf] using he
          · simp only [List.filterMap_cons, smpOf, List.length_cons]
            rw [show j + (List.length (List.filterMap smpOf pre₁) + 1) =
              j + 1 + (List.filterMap smpOf pre₁).length by (clear * -; omega)]
            exact h2

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

/-- `C_rec`'s commitment shapes `(ht, w)` (level 1: `2^12` rows of `3 · 2^4` words). -/
def shRec : Ref → ℕ × ℕ
  | ⟨.crec, 1⟩ => (12, 48)
  | ⟨.crec, _⟩ => (15, 64)
  | ⟨.main, _⟩ => (21, 64)

/-- `C_rec`'s opening up to level 0's residual's place: `ρ`, the intro round, six fold rounds. -/
def recHead1 : List Item := ((phases P20).getD 7 default).2.take 14

/-- Then level 1's cap, the OOD point (`13` samples), its answer and intro polynomial, level 0's proof
of work (separator, nonce, PoW challenge), positions and `λ` (J2′). -/
def recHead2 : List Item := (((phases P20).getD 7 default).2.drop 14).take 21

/-- After level 0's opening: the intro round and level 1's four fold rounds. -/
def recHeadB : List Item := (((phases P20).getD 7 default).2.drop 36).take 9

-- (R11-IS, M′: `openRec_P20` is removed: B1's replay through `C_rec`'s opening, false at `S2GM`, where
-- there is no `C_rec`; its consumers in `LvmCertSExq2` went with it.)

/-! ## Kinds -/

/-- v1's kinds (reads and samples) as `K2`. -/
def toK2 : EvK → K2
  | .read => .read
  | .sample => .sample
  | .other => .read

theorem itemK2_append (p : Params) (sh : Ref → ℕ × ℕ) : ∀ (a b : List Item),
    itemK2 p sh (a ++ b) = itemK2 p sh a ++ itemK2 p sh b
  | [], _ => rfl
  | .read m :: a, b => by simp only [List.cons_append, itemK2, itemK2_append p sh a b, List.append_assoc]
  | .readW _ _ :: a, b => by simp only [List.cons_append, itemK2, itemK2_append p sh a b, List.append_assoc]
  | .sample :: a, b => by simp only [List.cons_append, itemK2, itemK2_append p sh a b]
  | .cap _ _ :: a, b => by simp only [List.cons_append, itemK2, itemK2_append p sh a b]
  | .positions _ :: a, b => by
    simp only [List.cons_append, itemK2, itemK2_append p sh a b, List.append_assoc]
  | .opening _ :: a, b => by simp only [List.cons_append, itemK2, itemK2_append p sh a b]

/-- On items of reads and samples, `itemK2` is v1's `itemKinds`. -/
theorem itemK2_rs (p : Params) (sh : Ref → ℕ × ℕ) : ∀ (its : List Item), RSItems its = true →
    itemK2 p sh its = (itemKinds its).map toK2
  | [], _ => rfl
  | .read m :: its, h => by
    rw [itemK2, itemKinds, itemK2_rs p sh its h, List.map_append, List.map_replicate]; rfl
  | .sample :: its, h => by rw [itemK2, itemKinds, itemK2_rs p sh its h]; rfl
  | .readW _ _ :: _, h => by simp [RSItems] at h
  | .cap _ _ :: _, h => by simp [RSItems] at h
  | .positions _ :: _, h => by simp [RSItems] at h
  | .opening _ :: _, h => by simp [RSItems] at h

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

/-- `simK2` appends to the caps. -/
theorem capsK2_prefix (S : Scheme) (B : List UInt8) : ∀ (ks : List K2) (off : ℕ) (caps : List CapI),
    ∃ l, capsK2 S B ks off caps = caps ++ l
  | [], _, caps => ⟨[], by simp [capsK2]⟩
  | .read :: ks, off, caps => capsK2_prefix S B ks _ caps
  | .sample :: ks, off, caps => capsK2_prefix S B ks _ caps
  | .commit ht w nb :: ks, off, caps => by
    obtain ⟨l, hl⟩ := capsK2_prefix S B ks (off + nb) (caps ++ [S.capI ht w (B.drop off)])
    exact ⟨_ :: l, by rw [capsK2, hl, List.append_assoc]; rfl⟩

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

/-- The words of a `C_rec` candidate (WP-14c's `wOfCol`). -/
def wOfColX (q : Column 19) (i : ℕ) : RecursionFast.Word := BF64.toBitVec (q.values.getD i 0)

/-- **`child` is WP-13a's left child** of the candidate's words (WP-14c's `childS`). -/
def ChildX (child : Column 19 → Signed) : Prop :=
  ∀ q, child q = ⟨Lvm.Replay.reassemble Lvm.X.pX (Lvm.X.readTraceL (Lvm.X.laneOf (wOfColX q))),
    Lvm.X.readTraceL (Lvm.X.laneOf (wOfColX q)), Lvm.X.sigOfF (Lvm.X.sigCol (wOfColX q))⟩

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

theorem hdrS_inv {π : RecursionFast.Proof} {x body : List UInt8} (h : hdrS π = some (x, body)) :
    π.size = piSz ∧ π.data.toList.take 8 = sPrefix ∧ x = (π.data.toList.drop 8).take hdrLen ∧
      body = π.data.toList.drop Lvm.headerBytes := by
  unfold hdrS at h
  split_ifs at h with hc
  simp only [Option.some.injEq, Prod.mk.injEq] at h
  exact ⟨hc.1, hc.2, h.1.symm, h.2.symm⟩

theorem byte0_of_prefix {π : RecursionFast.Proof} (h : π.data.toList.take 8 = sPrefix) : π.data[0]? = some 0x53 := by
  have := congrArg (fun l : List UInt8 => l[0]?) h
  simp only [sPrefix] at this
  simpa using this

/-! ## The roots -/

theorem capBytes_main (vk : RecursionFast.Digest) (P : List UInt8 → VerifierProgram Bool) :
    (schemeS vk P).capBytes 19 64 = 8192 := by
  simp only [Scheme.capBytes, schemeS, capOfS]; norm_num

theorem capBytes_rec (vk : RecursionFast.Digest) (P : List UInt8 → VerifierProgram Bool) :
    (schemeS vk P).capBytes 15 64 = 4096 := by
  simp only [Scheme.capBytes, schemeS, capOfS]; norm_num

/-- **The replay of the roots**: the two commitments' words, then the rest of `P_S` with both caps
pending and the two commitments' records. -/
theorem roots_trun {vk : RecursionFast.Digest} {mid : List UInt8 → VerifierProgram OpenClaims}
    {x : List UInt8} {L : Log} {B : List UInt8} {st : RecursionFast.Digest} {h : List Ev}
    (e : (schemeS vk (PSWith mid)).trun L (PSWith mid x) st [] [] (B.drop 5984) [] = some (true, h)) :
    ∃ k rest, PSWith mid x = .commit 19 64 (.commit 15 64 k) ∧
      h = [Ev.commit 19 64 ((schemeS vk (PSWith mid)).wordOf L
        ((schemeS vk (PSWith mid)).capI 19 64 (B.drop 5984))),
        Ev.commit 15 64 ((schemeS vk (PSWith mid)).wordOf L
          ((schemeS vk (PSWith mid)).capI 15 64 (B.drop 14176)))] ++ rest ∧
      (schemeS vk (PSWith mid)).trun L k st (sl B 5984 (18272 - 5984))
        [(schemeS vk (PSWith mid)).capI 19 64 (B.drop 5984),
          (schemeS vk (PSWith mid)).capI 15 64 (B.drop 14176)] (B.drop 18272)
        [Ev.commit 19 64 ((schemeS vk (PSWith mid)).wordOf L
          ((schemeS vk (PSWith mid)).capI 19 64 (B.drop 5984))),
        Ev.commit 15 64 ((schemeS vk (PSWith mid)).wordOf L
          ((schemeS vk (PSWith mid)).capI 15 64 (B.drop 14176)))] = some (true, h) := by
  obtain ⟨k, hk⟩ := PSWith_roots mid x
  rw [hk] at e
  simp only [Scheme.trun, capBytes_main, capBytes_rec] at e
  split_ifs at e
  · simp at e
  · simp at e
  rw [List.drop_drop] at e
  have hbuf : [] ++ List.take 8192 (List.drop 5984 B) ++ List.take 4096 (List.drop (5984 + 8192) B) =
      sl B 5984 (18272 - 5984) := by
    simp only [List.nil_append, sl]
    rw [show 18272 - 5984 = 8192 + 4096 by norm_num, List.take_add, List.drop_drop]
  rw [hbuf, List.drop_drop] at e
  simp only [List.nil_append, List.cons_append, Nat.reduceAdd] at e
  have hpre := trun_prefix _ _ _ _ _ _ _ _ _ _ e
  obtain ⟨rest, hrest⟩ := hpre
  exact ⟨k, rest, hk, by rw [← hrest], e⟩

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

theorem itemKinds_append : ∀ (a b : List Item), itemKinds (a ++ b) = itemKinds a ++ itemKinds b
  | [], b => rfl
  | .read m :: a, b => by simp only [List.cons_append, itemKinds, itemKinds_append a b, List.append_assoc]
  | .readW _ _ :: a, b => by simp only [List.cons_append, itemKinds, itemKinds_append a b, List.append_assoc]
  | .sample :: a, b => by simp only [List.cons_append, itemKinds, itemKinds_append a b, List.cons_append]
  | .cap _ _ :: a, b => by simp only [List.cons_append, itemKinds, itemKinds_append a b]
  | .positions _ :: a, b => by simp only [List.cons_append, itemKinds, itemKinds_append a b]
  | .opening _ :: a, b => by simp only [List.cons_append, itemKinds, itemKinds_append a b]

/-- The number of samples of a history is the count of its sample kinds. -/
theorem samples_length : ∀ (l : List Ev), (l.filterMap sampleOf).length = (l.map kindOf).count .sample
  | [] => rfl
  | e :: l => by
    rw [List.map_cons, List.count_cons, ← samples_length l]
    cases e <;> simp [sampleOf, kindOf, List.filterMap_cons]

/-! ## The decoder's inputs -/

theorem capI_rec (vk : RecursionFast.Digest) (P : List UInt8 → VerifierProgram Bool) (b : List UInt8) :
    (schemeS vk P).capI 15 64 b = ⟨15, 64, 7, digestsOf (b.take 4096) (2 ^ 7)⟩ := by
  unfold Scheme.capI
  rw [capBytes_rec]
  rfl

/-- **O13**: the cap `C_rec`'s commitment reads is π's `capRec`. -/
theorem capRec_eq (vk : RecursionFast.Digest) (P : List UInt8 → VerifierProgram Bool) (π : RecursionFast.Proof)
    (hs : 18272 ≤ π.size) :
    (schemeS vk P).capI 15 64 (π.data.toList.drop 14176) = ⟨15, 64, 7, Lvm.X.capRec π⟩ := by
  have hB : π.data.toList.length = π.size := Array.length_toList
  have hc : Lvm.X.capRecOff Lvm.X.pX = 14176 := Lvm.X.layout_P20.2.2.2.2.1
  rw [capI_rec]
  have e : digestsOf ((π.data.toList.drop 14176).take 4096) (2 ^ 7) = Lvm.X.capRec π := by
    unfold digestsOf Lvm.X.capRec
    rw [show (2 : ℕ) ^ 7 = 128 by norm_num]
    refine List.map_congr_left fun e he => ?_
    have he' : e < 128 := List.mem_range.1 he
    rw [Lvm.X.hdD_eq_digestAt, hc]
    apply Vector.ext
    intro i hi
    simp only [dg, digestAt, Vector.getElem_ofFn]
    rw [get!_eq_getD, List.getD_eq_getElem _ _ (by simp only [List.length_drop, List.length_take]; omega),
      List.getD_eq_getElem _ _ (by omega)]
    simp only [List.getElem_drop, List.getElem_take]
    congr 1
    omega
  rw [e]

theorem decodeRec_congr_f (wd : ℕ → ℕ → BF64) (α : ℕ → BF64.Ext3) {f f' : ℕ → BF64.Ext3}
    (h : ∀ v < 2 ^ 13, f v = f' v) : Lvm.X.decodeRec wd α f = Lvm.X.decodeRec wd α f' := by
  have he : ∀ q, Lvm.X.enc0 f q = Lvm.X.enc0 f' q := fun q =>
    Finset.sum_congr rfl fun v hv => by rw [h v (Finset.mem_range.1 hv)]
  have ha : Lvm.X.agreeL wd α f = Lvm.X.agreeL wd α f' := by
    unfold Lvm.X.agreeL
    exact List.filter_congr fun q _ => by rw [he]
  unfold Lvm.X.decodeRec Lvm.X.decWord Lvm.X.selJ
  rw [ha]

theorem values_getD_msgs (q : Column 19) (i : ℕ) :
    q.values.getD i 0 = ((List.range (2 ^ 19)).map (Lvm.X.msgOf q)).getD i 0 := by
  have hlen : ((List.range (2 ^ 19)).map (Lvm.X.msgOf q)).length = 2 ^ 19 := by
    rw [List.length_map, List.length_range]
  rcases Nat.lt_or_ge i (2 ^ 19) with hi | hi
  · rw [List.getD_eq_getElem _ _ (by rw [hlen]; exact hi), List.getElem_map, List.getElem_range]
    rfl
  · rw [List.getD_eq_default _ _ (by rw [hlen]; omega)]
    rcases q with ⟨v⟩
    show Vector.getD v i 0 = 0
    unfold Vector.getD
    rw [Array.getD_eq_getD_getElem?]
    simp only [Vector.getElem?_toArray]
    rw [Vector.getElem?_eq_none (by omega)]
    rfl

theorem wOfColX_apply (q : Column 19) (i : ℕ) : wOfColX q i = BF64.toBitVec (q.values.getD i 0) := rfl

theorem wOut_apply (l : List BF64) (i : ℕ) : Lvm.X.wOut l i = BF64.toBitVec (l.getD i 0) := rfl

/-- The candidate's words are the decoder's output words (kernel-cheap form: `rw`, no `unfold`). -/
theorem wOfColX_eq (q : Column 19) :
    wOfColX q = Lvm.X.wOut ((List.range (2 ^ 19)).map (Lvm.X.msgOf q)) := by
  funext i
  rw [wOfColX_apply, wOut_apply, values_getD_msgs]

/-- The chain's target at `p ≥ 1` absorbs the slice `msgL p`. -/
theorem fsQL_eq (π : RecursionFast.Proof) {p : ℕ} (hp : 0 < p) (s : RecursionFast.Digest) :
    Lvm.X.fsQL π p s = toQ (s.toList ++ sl π.data.toList (Lvm.X.msgL p).1 (Lvm.X.msgL p).2) := by
  have hd := Lvm.X.fsQL_data (π := π) p hp s
  rw [ByteArray.data_extract, Array.toList_extract, List.extract_eq_take_drop,
    Nat.add_sub_cancel_left] at hd
  rcases hq : Lvm.X.fsQL π p s with ⟨a⟩
  rw [hq] at hd
  simp only at hd
  unfold toQ sl
  rw [← hd, Array.toArray_toList]

theorem msgL_eq (p : ℕ) : Lvm.X.msgL p = (Lvm.X.fsMsgs Lvm.X.pX).getD (p - 1) (0, 0) := by
  unfold Lvm.X.msgL
  rfl

/-! ## Level 1 (lvm2 S4) -/

theorem smpOf_eq : smpOf = sampleOf := by
  funext e
  cases e <;> rfl

theorem capBytes_rec1 (vk : RecursionFast.Digest) (P : List UInt8 → VerifierProgram Bool) :
    (schemeS vk P).capBytes 12 48 = 4096 := by
  simp only [Scheme.capBytes, schemeS, capOfS]; norm_num

theorem capI_rec1 (vk : RecursionFast.Digest) (P : List UInt8 → VerifierProgram Bool) (b : List UInt8) :
    (schemeS vk P).capI 12 48 b = ⟨12, 48, 7, digestsOf (b.take 4096) (2 ^ 7)⟩ := by
  unfold Scheme.capI
  rw [capBytes_rec1]
  rfl

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

theorem enc1_congr {f f' : ℕ → BF64.Ext3} (h : ∀ v < 2 ^ 9, f v = f' v) (q : ℕ) :
    Lvm.X.enc1 f q = Lvm.X.enc1 f' q :=
  Finset.sum_congr rfl fun v hv => by rw [h v (Finset.mem_range.1 hv)]

/-- The level-1 decoder reads `f₂` below `2^9` only. -/
theorem decodeRec1_congr_f (wd : ℕ → ℕ → BF64) (α : ℕ → BF64.Ext3) {f f' : ℕ → BF64.Ext3}
    (h : ∀ v < 2 ^ 9, f v = f' v) : Lvm.X.decodeRec1 wd α f = Lvm.X.decodeRec1 wd α f' := by
  have ha : Lvm.X.agree1L wd α f = Lvm.X.agree1L wd α f' := by
    unfold Lvm.X.agree1L
    exact List.filter_congr fun q _ => by rw [enc1_congr h]
  unfold Lvm.X.decodeRec1 Lvm.X.dec1At Lvm.X.coef1 Lvm.X.sel1J
  rw [ha]

theorem bitsToNat_symmN (n v : ℕ) (hv : v < 2 ^ n) :
    bitsToNat ((bitsEquiv n).symm ⟨v, hv⟩) = v := by
  rw [← bitsEquiv_val, Equiv.apply_symm_apply]

theorem forall₂_reads_samples {l : List Ev} {ks : List EvK} (h : l.map kindOf = ks)
    (ho : EvK.other ∉ ks) : List.Forall₂ KM l (ks.map toK2) := forall₂_of_kinds l ks h ho

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

/-- **`P_S` after level 0's proof of work, positions and `λ`** (J2′: after the level-1 cap, the OOD
point, its answer and intro polynomial) is at level 0's opening, of commitment `1`. -/
theorem PS_after_query {mid : List UInt8 → VerifierProgram OpenClaims} {x : List UInt8}
    {hr lm lq lf lc lz ly lhy lgp l₁ : List Ev} {cl : OpenClaims} {ρ lam c₂ y : E} {quad z hy : List E}
    {r : WhirStateT × List E} {qs : List ℕ}
    (h1 : rootsProg.after hr = some (.ret ())) (h3 : (mid x).after lm = some (.ret cl))
    (h8 : (LeanVM.Protocol.Verifier.sumcheckRoundPoly 3 (batT cl.1 ρ) none).after lq =
      some (.ret quad))
    (h10 : (foldRoundsT 6 ⟨batT cl.1 ρ, quad, [], []⟩ []).after lf = some (.ret r))
    (hc : (readCommitment (19 - r.1.folds.length - 4 + 3) (3 * 2 ^ 4)).after lc = some (.ret ()))
    (hz : (VerifierProgram.sampleChallenges (19 - r.1.folds.length)).after lz = some (.ret z))
    (hyr : readScalar.after ly = some (.ret y))
    (hhy : (LeanVM.Protocol.Verifier.sumcheckRoundPoly 3 y none).after lhy = some (.ret hy))
    (hgp : (grindPre 14).after lgp = some (.ret ()))
    (hpw : (powCheck 14).after [Ev.sample c₂] = some (.ret ()))
    (hp1 : (samplePositions 8 (19 - r.1.folds.length + 2) 115).after l₁ = some (.ret qs)) :
    ∃ K, (PSWith mid x).after (hr ++ (lm ++ ([Ev.sample ρ] ++ (lq ++ (lf ++ (lc ++ (lz ++ (ly ++
      (lhy ++ (lgp ++ ([Ev.sample c₂] ++ (l₁ ++ [Ev.sample lam])))))))))))) =
        some (.query 1 qs K) := by
  have hW : ∃ K, (whirPrefixJ 19 8 1 2 14 0 [⟨6, 2, 115⟩, ⟨4, 3, 77⟩] ⟨batT cl.1 ρ, quad, [], []⟩).after
      (lf ++ (lc ++ (lz ++ (ly ++ (lhy ++ (lgp ++ ([Ev.sample c₂] ++ (l₁ ++ [Ev.sample lam])))))))) =
        some (.query 1 qs K) := by
    rw [whirPrefixJ_mid]
    refine atQuery_append h10 ?_
    unfold midTailPJ
    refine atQuery_append hc (atQuery_append hz (atQuery_append hyr (atQuery_append hhy
      (atQuery_append hgp (atQuery_append hpw (atQuery_append hp1 ⟨_, rfl⟩))))))
  rw [PSWith_eq_prefixJ]
  refine atQuery_bind _ ?_
  unfold recPrefixProg
  simp only [bind_eq]
  refine atQuery_append h1 (atQuery_append h3 (atQuery_bind _ ?_))
  unfold stackPrefixJ
  exact atQuery_append (rfl : sampleChallenge.after [Ev.sample ρ] = some (.ret ρ))
    (atQuery_append h8 (atQuery_bind _ hW))

theorem not_commit_toK2 {ht w nb : ℕ} : ∀ (ks : List EvK), K2.commit ht w nb ∉ ks.map toK2
  | [] => by simp
  | k :: ks => by
    simp only [List.map_cons, List.mem_cons, not_or]
    exact ⟨by cases k <;> simp [toK2], not_commit_toK2 ks⟩

/-- The chain's targets of positions `D + 1 + i` absorb the slices `fsMsgs[D + i]`. -/
theorem chainT (π : RecursionFast.Proof) {ks : List K2} {off pend D N : ℕ}
    (hPre : fsPreK2 ks off pend = ((Lvm.X.fsMsgs P20).drop D).take N) (hD : 0 < D + 1) :
    ∀ i (hi : i < (fsPreK2 ks off pend).length) (s : RecursionFast.Digest),
      Lvm.X.fsQL π (D + 1 + i) s =
        toQ (s.toList ++ sl π.data.toList ((fsPreK2 ks off pend)[i]).1 ((fsPreK2 ks off pend)[i]).2) := by
  intro i hi s
  rw [fsQL_eq π (by omega), msgL_eq, ← List.getD_eq_getElem _ (0, 0) hi, hPre]
  have hi' : i < N := by
    have := hi
    rw [hPre] at this
    exact lt_of_lt_of_le this (List.length_take_le _ _)
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_take, if_pos hi',
    List.getElem?_drop, show D + 1 + i - 1 = D + i by omega]

-- (R11-IS, M′: B1's `ext_eq_gen` (O5c for the two-root `PSWith` with two `C_rec` levels) and its replay facts
-- `kA1`, `kB`, `kA2`, `not_midFollows_ret` are removed: they read `openRec_P20`, false at `S2GM`. The generic helpers
-- above stay for M′'s `ext_eqM20`; B1's proof is at ff8902c2.)

end Lvm.ASM
