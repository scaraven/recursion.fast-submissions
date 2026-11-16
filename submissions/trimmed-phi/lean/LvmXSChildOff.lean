/- `LvmXSChildOff` (GOLF2 off-path move, group 40 of 48): declarations that the certificate `certified`
   does not use, moved here verbatim (same names, same namespaces and context) from LvmCertSExq2Codec, LvmCertSExq2, LvmMPXExtEq, LvmCertM20, LvmXSChild,
   so that `Solution`'s import closure need not elaborate them. Import this module where they are needed;
   the name -> module map is GOLF2's moved.tsv. -/
import LvmCertSExq2Codec
import LvmCertSExq2
import LvmMPXExtEq
import LvmCertM20
import LvmXSChild
import LvmE2QNodeChkGOff
import LvmE2QPinOpenFOff
import LvmE2VWidthsFOff
import LvmMPCertOff
import LvmMPMidTOff
import LvmMPXNodeSemOff
import LvmMPXReadOff
import LvmNodeSoundTOff
import LvmSubmissionSOff
import LvmVerifierSTOff
import LvmXTopOff
import LvmChainTablePad
import LvmJBMutual
import LvmMlListLemmas
import LvmQAsmHar47
import LvmSpecRulesCert
import LvmVEqTape
import LvmVerifierST

-- ===== from `LvmCertSExq2Codec` =====

section
set_option autoImplicit false
namespace Lvm.ASM
open RecursionFast Lvm.FS
open LeanVM.Parameters
open LeanVM.Protocol.Compile hiding Proof Bytes

/-- The all-zero digest's challenge is `0`. -/
theorem alphaE_zero : Lvm.X.alphaE Lvm.X.zeroDL = 0 := by
  have h0 : Lvm.X.decLE (List.replicate 8 0) = 0 := by
    unfold Lvm.X.decLE
    simp [ofLE, toWord]
    rfl
  rw [← chalOf_eq_alphaE, chalOf, eOfBytes_eq]
  simp only [Lvm.X.zeroDL, Vector.toList_replicate, List.take_replicate, List.drop_replicate]
  norm_num only [h0]
  apply CompPoly.Extension.Ext.coeffs_injective
  apply Vector.ext
  intro i hi
  have hi3 : i < 3 := hi
  interval_cases i <;> rfl

/-- **π's `f₂` coefficient** (bridge (a)): the scalar of the 24 bytes at `f2Off + 24 v`. -/
theorem f2E_eq (π : Proof) (v : ℕ) (hv : Lvm.X.f2Off Lvm.X.pX + 24 * v + 24 ≤ π.size) :
    Lvm.X.f2E π v = eOfBytes ((π.data.toList.drop (Lvm.X.f2Off Lvm.X.pX + 24 * v)).take 24) := by
  have h8 : Lvm.X.f2Off Lvm.X.pX % 8 = 0 := Lvm.X.layoutX.2.2.2.2.2.2.1
  have hs : π.data.toList.length = π.size := Array.length_toList
  rw [eOfBytes_eq, Lvm.X.f2E, Lvm.X.pw, Lvm.X.pw, Lvm.X.pw, wK_packBytes _ (by omega),
    wK_packBytes _ (by omega), wK_packBytes _ (by omega)]
  simp only [List.take_take, List.drop_take, List.drop_drop]
  have e0 : 8 * (Lvm.X.f2Off Lvm.X.pX / 8 + 3 * v) = Lvm.X.f2Off Lvm.X.pX + 24 * v := by omega
  have e1 : 8 * (Lvm.X.f2Off Lvm.X.pX / 8 + 3 * v + 1) = Lvm.X.f2Off Lvm.X.pX + 24 * v + 8 := by omega
  have e2 : 8 * (Lvm.X.f2Off Lvm.X.pX / 8 + 3 * v + 2) = Lvm.X.f2Off Lvm.X.pX + 24 * v + 16 := by
    omega
  rw [e0, e1, e2]
  simp [Nat.add_comm]

end Lvm.ASM
end

section
set_option autoImplicit false
namespace Lvm.ASM
open RecursionFast Lvm.FS
open LeanVM.Parameters
open LeanVM.Protocol.Compile hiding Proof Bytes

/-- **O12**: XD's `readRow L cap p` is WP-5's word under the cap `cap` (`⟨15, 64, 7, cap⟩`), for a
scheme whose word decoder is `kOfBytes` and whose `C_rec` leaves carry the reader's `crOcc` words:
both are `64 − crOcc` zero words, then the leaf's first `crOcc` words (`Scheme.padRow`). -/
theorem readRow_eq_wordOf (S : Scheme) (hK : S.decK = kOfBytes) (hO : S.occ 15 64 = Lvm.X.crOcc)
    (L : Log) (cap : List Digest) (p : ℕ) : Lvm.X.readRow L cap p = S.wordOf L ⟨15, 64, 7, cap⟩ p := by
  have hl : Lvm.X.xLeafBytes L cap p = Scheme.leafBytes L ⟨15, 64, 7, cap⟩ p := by
    simp only [Lvm.X.xLeafBytes, Scheme.leafBytes, xDescend_eq]
    rfl
  rw [Lvm.X.readRow, Scheme.wordOf, Scheme.padRow, hl, hK]
  show _ = padRowOf kOfBytes 64 (S.occ 15 64) _
  rw [hO, padRowOf, Nat.min_eq_left Lvm.X.crOcc_le]
  simp only [Lvm.X.xRowOf, rowOf, kOfBytes_eq, List.take_take, Nat.min_self]

/-- **O12 at level 1**: DEC's `readRow1 L cap p` is WP-5's word under the level-1 cap
(`⟨12, 48, 7, cap⟩`), for a scheme whose word decoder is `kOfBytes` and whose level-1 leaves carry
their whole rows. -/
theorem readRow1_eq_wordOf (S : Scheme) (hK : S.decK = kOfBytes) (ho : S.occ 12 48 = 48) (L : Log)
    (cap : List Digest) (p : ℕ) : Lvm.X.readRow1 L cap p = S.wordOf L ⟨12, 48, 7, cap⟩ p := by
  have hl : Lvm.X.xLeafBytes1 L cap p = Scheme.leafBytes L ⟨12, 48, 7, cap⟩ p := by
    simp only [Lvm.X.xLeafBytes1, Scheme.leafBytes, xDescend_eq]
    rfl
  rw [Lvm.X.readRow1, Scheme.wordOf, S.padRow_of_full _ _ ho, hl, hK]
  simp only [Lvm.X.xRowOf, rowOf, kOfBytes_eq, List.take_take, Nat.min_self]

/-- **The level-1 decoder's word** is `wdOf` of WP-5's word under the level-1 cap. -/
theorem readWd1_eq_wdOf (S : Scheme) (hK : S.decK = kOfBytes) (ho : S.occ 12 48 = 48) (L : Log)
    (cap : List Digest) : Lvm.X.readWd1 L cap = Lvm.X.wdOf (S.wordOf L ⟨12, 48, 7, cap⟩) := by
  funext p t
  unfold Lvm.X.readWd1 Lvm.X.wdOf
  rw [readRow1_eq_wordOf S hK ho]

/-- **The level-1 cap** (O13 at level 1): the 128 digests of π's 4096 bytes at `capRec1Off`. -/
theorem capRec1_eq (π : Proof) (hs : Lvm.X.capRec1Off Lvm.X.pX + 4096 ≤ π.size) :
    digestsOf ((π.data.toList.drop (Lvm.X.capRec1Off Lvm.X.pX)).take 4096) (2 ^ 7) =
      Lvm.X.capRec1 π := by
  have hB : π.data.toList.length = π.size := Array.length_toList
  have hc : Lvm.X.capRec1Off Lvm.X.pX = 141568 := Lvm.X.layout_P20.2.2.2.1
  rw [hc] at hs ⊢
  unfold digestsOf Lvm.X.capRec1
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
  have e8 : 8 * (141568 / 8 + 4 * e) + i = 141568 + (32 * e + i) := by omega
  simp only [e8]

end Lvm.ASM
end

-- ===== from `LvmCertSExq2` =====

section
section
set_option autoImplicit false
namespace Lvm.ASM
open RecursionFast Lvm.FS
open LeanVM.Parameters
open LeanVM.Protocol.Compile hiding Proof Bytes

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

end Lvm.ASM
end
end

section
section
set_option autoImplicit false
namespace Lvm.ASM
open RecursionFast Lvm.FS
open LeanVM.Parameters
open LeanVM.Protocol.Compile hiding Proof Bytes
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
end Lvm.ASM
end
end

section
section
set_option autoImplicit false
namespace Lvm.ASM
open RecursionFast Lvm.FS
open LeanVM.Parameters
open LeanVM.Protocol.Compile hiding Proof Bytes

theorem not_self_append {h l : List Ev} (e : Ev) (hh : h = h ++ e :: l) : False := by
  have := congrArg List.length hh
  simp at this

end Lvm.ASM
end
end

section
section
set_option autoImplicit false
namespace Lvm.ASM
open RecursionFast Lvm.FS
open LeanVM.Parameters
open LeanVM.Protocol.Compile hiding Proof Bytes

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

end Lvm.ASM
end
end

section
section
set_option autoImplicit false
namespace Lvm.ASM
open RecursionFast Lvm.FS
open LeanVM.Parameters
open LeanVM.Protocol.Compile hiding Proof Bytes

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
end

section
section
set_option autoImplicit false
namespace Lvm.ASM
open RecursionFast Lvm.FS
open LeanVM.Parameters
open LeanVM.Protocol.Compile hiding Proof Bytes
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
end Lvm.ASM
end
end

section
section
set_option autoImplicit false
namespace Lvm.ASM
open RecursionFast Lvm.FS
open LeanVM.Parameters
open LeanVM.Protocol.Compile hiding Proof Bytes

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

end Lvm.ASM
end
end

section
section
set_option autoImplicit false
namespace Lvm.ASM
open RecursionFast Lvm.FS
open LeanVM.Parameters
open LeanVM.Protocol.Compile hiding Proof Bytes

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

end Lvm.ASM
end
end

section
section
set_option autoImplicit false
namespace Lvm.ASM
open RecursionFast Lvm.FS
open LeanVM.Parameters
open LeanVM.Protocol.Compile hiding Proof Bytes

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

end Lvm.ASM
end
end

section
section
set_option autoImplicit false
namespace Lvm.ASM
open RecursionFast Lvm.FS
open LeanVM.Parameters
open LeanVM.Protocol.Compile hiding Proof Bytes

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

end Lvm.ASM
end
end

section
section
set_option autoImplicit false
namespace Lvm.ASM
open RecursionFast Lvm.FS
open LeanVM.Parameters
open LeanVM.Protocol.Compile hiding Proof Bytes

/-- `simK2` appends to the caps. -/
theorem capsK2_prefix (S : Scheme) (B : List UInt8) : ∀ (ks : List K2) (off : ℕ) (caps : List CapI),
    ∃ l, capsK2 S B ks off caps = caps ++ l
  | [], _, caps => ⟨[], by simp [capsK2]⟩
  | .read :: ks, off, caps => capsK2_prefix S B ks _ caps
  | .sample :: ks, off, caps => capsK2_prefix S B ks _ caps
  | .commit ht w nb :: ks, off, caps => by
    obtain ⟨l, hl⟩ := capsK2_prefix S B ks (off + nb) (caps ++ [S.capI ht w (B.drop off)])
    exact ⟨_ :: l, by rw [capsK2, hl, List.append_assoc]; rfl⟩

end Lvm.ASM
end
end

section
set_option autoImplicit false
namespace Lvm.ASM
open RecursionFast Lvm.FS Lvm.T
open LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Protocol.Compile.VerifierProgram LeanVM.Protocol.Whir.Sound LeanVM.Protocol.EndToEnd
open LeanVM.Protocol.Whir
open scoped NNReal ENNReal

/-- The words of a `C_rec` candidate (WP-14c's `wOfCol`). -/
def wOfColX (q : Column 19) (i : ℕ) : RecursionFast.Word := BF64.toBitVec (q.values.getD i 0)

/-- **`child` is WP-13a's left child** of the candidate's words (WP-14c's `childS`). -/
def ChildX (child : Column 19 → Signed) : Prop :=
  ∀ q, child q = ⟨Lvm.Replay.reassemble Lvm.X.pX (Lvm.X.readTraceL (Lvm.X.laneOf (wOfColX q))),
    Lvm.X.readTraceL (Lvm.X.laneOf (wOfColX q)), Lvm.X.sigOfF (Lvm.X.sigCol (wOfColX q))⟩

end Lvm.ASM
end

section
set_option autoImplicit false
namespace Lvm.ASM
open RecursionFast Lvm.FS Lvm.T
open LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Protocol.Compile.VerifierProgram LeanVM.Protocol.Whir.Sound LeanVM.Protocol.EndToEnd
open LeanVM.Protocol.Whir
open scoped NNReal ENNReal

theorem hdrS_inv {π : RecursionFast.Proof} {x body : List UInt8} (h : hdrS π = some (x, body)) :
    π.size = piSz ∧ π.data.toList.take 8 = sPrefix ∧ x = (π.data.toList.drop 8).take hdrLen ∧
      body = π.data.toList.drop Lvm.headerBytes := by
  unfold hdrS at h
  split_ifs at h with hc
  simp only [Option.some.injEq, Prod.mk.injEq] at h
  exact ⟨hc.1, hc.2, h.1.symm, h.2.symm⟩

end Lvm.ASM
end

section
set_option autoImplicit false
namespace Lvm.ASM
open RecursionFast Lvm.FS Lvm.T
open LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Protocol.Compile.VerifierProgram LeanVM.Protocol.Whir.Sound LeanVM.Protocol.EndToEnd
open LeanVM.Protocol.Whir
open scoped NNReal ENNReal

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

end Lvm.ASM
end

section
set_option autoImplicit false
namespace Lvm.ASM
open RecursionFast Lvm.FS Lvm.T
open LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Protocol.Compile.VerifierProgram LeanVM.Protocol.Whir.Sound LeanVM.Protocol.EndToEnd
open LeanVM.Protocol.Whir
open scoped NNReal ENNReal

theorem itemKinds_append : ∀ (a b : List Item), itemKinds (a ++ b) = itemKinds a ++ itemKinds b
  | [], b => rfl
  | .read m :: a, b => by simp only [List.cons_append, itemKinds, itemKinds_append a b, List.append_assoc]
  | .readW _ _ :: a, b => by simp only [List.cons_append, itemKinds, itemKinds_append a b, List.append_assoc]
  | .sample :: a, b => by simp only [List.cons_append, itemKinds, itemKinds_append a b, List.cons_append]
  | .cap _ _ :: a, b => by simp only [List.cons_append, itemKinds, itemKinds_append a b]
  | .positions _ :: a, b => by simp only [List.cons_append, itemKinds, itemKinds_append a b]
  | .opening _ :: a, b => by simp only [List.cons_append, itemKinds, itemKinds_append a b]

end Lvm.ASM
end

section
set_option autoImplicit false
namespace Lvm.ASM
open RecursionFast Lvm.FS Lvm.T
open LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Protocol.Compile.VerifierProgram LeanVM.Protocol.Whir.Sound LeanVM.Protocol.EndToEnd
open LeanVM.Protocol.Whir
open scoped NNReal ENNReal

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

end Lvm.ASM
end

section
set_option autoImplicit false
namespace Lvm.ASM
open RecursionFast Lvm.FS Lvm.T
open LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Protocol.Compile.VerifierProgram LeanVM.Protocol.Whir.Sound LeanVM.Protocol.EndToEnd
open LeanVM.Protocol.Whir
open scoped NNReal ENNReal

theorem capBytes_rec1 (vk : RecursionFast.Digest) (P : List UInt8 → VerifierProgram Bool) :
    (schemeS vk P).capBytes 12 48 = 4096 := by
  simp only [Scheme.capBytes, schemeS, capOfS]; norm_num

theorem capI_rec1 (vk : RecursionFast.Digest) (P : List UInt8 → VerifierProgram Bool) (b : List UInt8) :
    (schemeS vk P).capI 12 48 b = ⟨12, 48, 7, digestsOf (b.take 4096) (2 ^ 7)⟩ := by
  unfold Scheme.capI
  rw [capBytes_rec1]
  rfl

end Lvm.ASM
end

section
set_option autoImplicit false
namespace Lvm.ASM
open RecursionFast Lvm.FS Lvm.T
open LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Protocol.Compile.VerifierProgram LeanVM.Protocol.Whir.Sound LeanVM.Protocol.EndToEnd
open LeanVM.Protocol.Whir
open scoped NNReal ENNReal

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

end Lvm.ASM
end

section
set_option autoImplicit false
namespace Lvm.ASM
open RecursionFast Lvm.FS Lvm.T
open LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Protocol.Compile.VerifierProgram LeanVM.Protocol.Whir.Sound LeanVM.Protocol.EndToEnd
open LeanVM.Protocol.Whir
open scoped NNReal ENNReal

theorem forall₂_reads_samples {l : List Ev} {ks : List EvK} (h : l.map kindOf = ks)
    (ho : EvK.other ∉ ks) : List.Forall₂ KM l (ks.map toK2) := forall₂_of_kinds l ks h ho

end Lvm.ASM
end

section
set_option autoImplicit false
namespace Lvm.ASM
open RecursionFast Lvm.FS Lvm.T
open LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Protocol.Compile.VerifierProgram LeanVM.Protocol.Whir.Sound LeanVM.Protocol.EndToEnd
open LeanVM.Protocol.Whir
open scoped NNReal ENNReal

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

end Lvm.ASM
end

section
set_option autoImplicit false
namespace Lvm.ASM
open RecursionFast Lvm.FS Lvm.T
open LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Protocol.Compile.VerifierProgram LeanVM.Protocol.Whir.Sound LeanVM.Protocol.EndToEnd
open LeanVM.Protocol.Whir
open scoped NNReal ENNReal

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

end Lvm.ASM
end

-- ===== from `LvmMPXExtEq` =====

section
set_option autoImplicit false
namespace Lvm.ASM
open RecursionFast Lvm.FS Lvm.T
open LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Protocol.Compile.VerifierProgram LeanVM.Protocol.Whir.Sound LeanVM.Protocol.EndToEnd
open LeanVM.Protocol.Whir
open scoped NNReal ENNReal

/-- **π's residual coefficient** (bridge (a)): the scalar of the 24 bytes at `resOffM + 24 v`. -/
theorem resEM_eq (π : RecursionFast.Proof) (v : ℕ) (hv : Lvm.X.resOffM Lvm.X.pX + 24 * v + 24 ≤ π.size) :
    Lvm.X.resEM π v = eOfBytes ((π.data.toList.drop (Lvm.X.resOffM Lvm.X.pX + 24 * v)).take 24) := by
  have h8 : Lvm.X.resOffM Lvm.X.pX % 8 = 0 := Lvm.X.layoutXM.2.2.2.2.2.2.2.1
  have hs : π.data.toList.length = π.size := Array.length_toList
  rw [eOfBytes_eq, Lvm.X.resEM, Lvm.X.pw, Lvm.X.pw, Lvm.X.pw, wK_packBytes _ (by omega), wK_packBytes _ (by omega), wK_packBytes _ (by omega)]
  simp only [List.take_take, List.drop_take, List.drop_drop]
  have e0 : 8 * (Lvm.X.resOffM Lvm.X.pX / 8 + 3 * v) = Lvm.X.resOffM Lvm.X.pX + 24 * v := by (clear * - h8; omega)
  have e1 : 8 * (Lvm.X.resOffM Lvm.X.pX / 8 + 3 * v + 1) = Lvm.X.resOffM Lvm.X.pX + 24 * v + 8 := by (clear * - h8; omega)
  have e2 : 8 * (Lvm.X.resOffM Lvm.X.pX / 8 + 3 * v + 2) = Lvm.X.resOffM Lvm.X.pX + 24 * v + 16 := by (clear * - h8; omega)
  rw [e0, e1, e2]
  simp [Nat.add_comm]

/-- **`C_main`'s level-`i` cap** (O13 at M′): the `capNM i` digests of π's bytes at `capOffM i`. -/
theorem digestsOf_capM (π : RecursionFast.Proof) {i : ℕ} (hi : i < 3)
    (hs : Lvm.X.capOffM Lvm.X.pX i + 32 * Lvm.X.capNM i ≤ π.size) :
    digestsOf ((π.data.toList.drop (Lvm.X.capOffM Lvm.X.pX i)).take (32 * Lvm.X.capNM i)) (Lvm.X.capNM i) =
      Lvm.X.capM π i := by
  have hB : π.data.toList.length = π.size := Array.length_toList
  have h8 : Lvm.X.capOffM Lvm.X.pX i % 8 = 0 := by
    have h := Lvm.X.layoutXM
    interval_cases i
    · exact h.2.2.2.2.1
    · exact h.2.2.2.2.2.1
    · exact h.2.2.2.2.2.2.1
  unfold digestsOf Lvm.X.capM
  refine List.map_congr_left fun e he => ?_
  have he' : e < Lvm.X.capNM i := List.mem_range.1 he
  rw [Lvm.X.hdD_eq_digestAt, show 8 * (Lvm.X.capOffM Lvm.X.pX i / 8 + 4 * e) = Lvm.X.capOffM Lvm.X.pX i + 32 * e by
    (clear * - h8; omega)]
  apply Vector.ext
  intro j hj
  simp only [dg, digestAt, Vector.getElem_ofFn]
  rw [get!_eq_getD, List.getD_eq_getElem _ _ (by simp only [List.length_drop, List.length_take]; (clear * - hs hB h8 he' hj; omega)),
    List.getD_eq_getElem _ _ (by (clear * - hs hB h8 he' hj; omega))]
  simp only [List.getElem_drop, List.getElem_take]
  congr 1
  (clear * -; omega)

end Lvm.ASM
end

section
set_option autoImplicit false
namespace Lvm.ASM
open RecursionFast Lvm.FS Lvm.T
open LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Protocol.Compile.VerifierProgram LeanVM.Protocol.Whir.Sound LeanVM.Protocol.EndToEnd
open LeanVM.Protocol.Whir
open scoped NNReal ENNReal

theorem capBytes_lv (vk : RecursionFast.Digest) (P : List UInt8 → VerifierProgram Bool) {ht : ℕ} (h : ht ≠ 19)
    (w : ℕ) : (schemeS vk P).capBytes ht w = 4096 := by
  simp only [Scheme.capBytes, schemeS, capOfS, if_neg h]; norm_num

theorem capI_root (vk : RecursionFast.Digest) (P : List UInt8 → VerifierProgram Bool) (b : List UInt8) :
    (schemeS vk P).capI 19 64 b = ⟨19, 64, 8, digestsOf (b.take (32 * Lvm.X.capNM 0)) (Lvm.X.capNM 0)⟩ := by
  unfold Scheme.capI
  rw [capBytes_main]
  rfl

theorem capI_lv (vk : RecursionFast.Digest) (P : List UInt8 → VerifierProgram Bool) {ht i : ℕ} (h : ht ≠ 19)
    (hi : i ≠ 0) (w : ℕ) (b : List UInt8) :
    (schemeS vk P).capI ht w b = ⟨ht, w, 7, digestsOf (b.take (32 * Lvm.X.capNM i)) (Lvm.X.capNM i)⟩ := by
  unfold Scheme.capI
  rw [capBytes_lv vk P h]
  simp only [schemeS, capOfS, if_neg h, Lvm.X.capNM, if_neg hi]
  try norm_num

theorem fsMsg0 : (Lvm.X.fsMsgs P20).getD 0 (0, 0) = (8, hdrLen) := by decide +kernel

/-- **The replay of the root**: the root's word, then the rest of `P_S` with the cap pending. -/
theorem root_trunM {vk : RecursionFast.Digest} {mid : List UInt8 → VerifierProgram (List LeanVM.Protocol.Verifier.StackClaim)}
    {x : List UInt8} {L : Log} {B : List UInt8} {st : RecursionFast.Digest} {h : List Ev}
    (e : (schemeS vk (PSWithM mid)).trun L (PSWithM mid x) st [] [] (B.drop 5984) [] = some (true, h)) :
    ∃ k, PSWithM mid x = .commit 19 64 k ∧
      (schemeS vk (PSWithM mid)).trun L k st (sl B 5984 (14176 - 5984))
        [(schemeS vk (PSWithM mid)).capI 19 64 (B.drop 5984)] (B.drop 14176)
        [Ev.commit 19 64 ((schemeS vk (PSWithM mid)).wordOf L
          ((schemeS vk (PSWithM mid)).capI 19 64 (B.drop 5984)))] = some (true, h) := by
  obtain ⟨k, hk⟩ : ∃ k, PSWithM mid x = .commit 19 64 k := ⟨_, rfl⟩
  rw [hk] at e
  simp only [Scheme.trun, capBytes_main] at e
  split_ifs at e
  · simp at e
  have hbuf : [] ++ List.take 8192 (List.drop 5984 B) = sl B 5984 (14176 - 5984) := by
    simp only [List.nil_append, sl]
  rw [hbuf, List.drop_drop] at e
  simp only [List.nil_append, Nat.reduceAdd] at e
  exact ⟨k, hk, e⟩

/-- `capsK2` on kinds without commitments keeps the caps. -/
theorem capsK2_toK2 (S : Scheme) (B : List UInt8) : ∀ (ks : List EvK) (off : ℕ) (caps : List CapI),
    capsK2 S B (ks.map toK2) off caps = caps
  | [], _, _ => rfl
  | k :: ks, off, caps => by
    cases k <;> simp only [List.map_cons, toK2, capsK2] <;> exact capsK2_toK2 S B ks _ caps

theorem capI_capM0 (vk : RecursionFast.Digest) (P : List UInt8 → VerifierProgram Bool) (π : RecursionFast.Proof)
    (hs : π.size = 332336) :
    (schemeS vk P).capI 19 64 (π.data.toList.drop 5984) = ⟨19, 17 + 47, 8, Lvm.X.capM π 0⟩ := by
  have hc : Lvm.X.capOffM Lvm.X.pX 0 = 5984 := Lvm.X.layoutM_P20.2.2.2.2.2.1
  rw [capI_root, ← digestsOf_capM π (i := 0) (by norm_num) (by rw [hc, hs]; decide), hc]

theorem capI_capM1 (vk : RecursionFast.Digest) (P : List UInt8 → VerifierProgram Bool) (π : RecursionFast.Proof)
    (hs : π.size = 332336) :
    (schemeS vk P).capI 16 48 (π.data.toList.drop 141856) = ⟨16, 0 + 48, 7, Lvm.X.capM π 1⟩ := by
  have hc : Lvm.X.capOffM Lvm.X.pX 1 = 141856 := Lvm.X.layoutM_P20.2.2.2.2.2.2.1
  rw [capI_lv vk P (by norm_num) (i := 1) (by norm_num), ← digestsOf_capM π (i := 1) (by norm_num)
    (by rw [hc, hs]; decide), hc]

theorem capI_capM2 (vk : RecursionFast.Digest) (P : List UInt8 → VerifierProgram Bool) (π : RecursionFast.Proof)
    (hs : π.size = 332336) :
    (schemeS vk P).capI 13 48 (π.data.toList.drop 230008) = ⟨13, 0 + 48, 7, Lvm.X.capM π 2⟩ := by
  have hc : Lvm.X.capOffM Lvm.X.pX 2 = 230008 := Lvm.X.layoutM_P20.2.2.2.2.2.2.2.1
  rw [capI_lv vk P (by norm_num) (i := 2) (by norm_num), ← digestsOf_capM π (i := 2) (by norm_num)
    (by rw [hc, hs]; decide), hc]

set_option maxRecDepth 20000 in
/-- **O5c at M′**, generic in the middle phases: on an accepted `S` proof over a log of potential below 1, `EXM`
returns the specification extractor's witness, or (outside its domain) a witness of the relation. -/
theorem ext_eqM_gen {mid : List UInt8 → VerifierProgram (List LeanVM.Protocol.Verifier.StackClaim)} {Good : GoodRelM}
    {Lm : ℝ≥0∞} (hmid : MidSpecM mid Good εS Lm) (hLm : Lm ≤ εS) (hsh : MidShapeM mid) {VS : SProg}
    {child : List UInt8 → List BF64 → Signed} (hnode : ∀ vk, NodeSoundM VS vk Good child)
    (hchild : ∀ (π : RecursionFast.Proof) (x : List UInt8) (out : List BF64),
      (Lvm.VEq.pubX x).n = (Lvm.X.pw π 14).toNat → out.length = 2 ^ 20 →
        Lvm.NS.childW (Lvm.X.wStreamM π out) = child x out)
    (hfol : MidFollows mid)
    (hA : ∀ vk c p, accV VS vk c p = true → Lvm.X.SFits p) (vk : RecursionFast.Digest) (L : Log)
    (c : RecursionFast.Digest) (π : RecursionFast.Proof)
    (hμ : Scheme.μ (kcertSM hmid hLm hsh (extJM hsh (hnode vk))) L < 1)
    (hacc : ((schemeS vk (PSWithM mid)).V c π).runLog L = some true) :
    (∃ w, Lvm.X.EXM (accV VS) c π L = some w ∧ Rel (accV VS vk) c w) ∨
      Lvm.X.EXM (accV VS) c π L =
        (schemeS vk (PSWithM mid)).Ex (kcertSM hmid hLm hsh (extJM hsh (hnode vk))).ext c π L := by
  obtain ⟨x, h, hok, hreach, hafter, hB, hBp, hD, hEx⟩ :=
    Scheme.final_good (kcertSM hmid hLm hsh (extJM hsh (hnode vk))) L c π hμ hacc
  obtain ⟨body, e₀, e₁, hhdr, h0, h1, htr⟩ := Ex_inv _ hEx
  obtain ⟨hsz, hpre8, rfl, rfl⟩ := hdrS_inv hhdr
  set S := schemeS vk (PSWithM mid) with hSdef
  set B := π.data.toList with hBdef
  have hsize : π.size = Lvm.piSize Lvm.X.pX := hsz
  have hpi : π.size = 332336 := by rw [hsize]; exact Lvm.X.piSize_eq
  have hBlen : B.length = π.size := Array.length_toList
  have hb0 : π.data[0]? = some 0x53 := byte0_of_prefix hpre8
  have hhd : hdrOf ((B.drop 8).take hdrLen) = Header.ofProof π :=
    hdrOf_eq π (by rw [hpi]; decide)
  have hExK := hEx (kcertSM hmid hLm hsh (extJM hsh (hnode vk))).ext
  rw [hExK]
  have hext : (kcertSM hmid hLm hsh (extJM hsh (hnode vk))).ext = extSM mid child := rfl
  rw [hext]
  -- the header fields
  have hfb : (Header.ofProof π).b = (Lvm.X.pw π 1).toNat := (pw_toNat π 1 (by (clear * - hsz hsize hpi; omega))).symm
  have hfn : (Header.ofProof π).n = (Lvm.X.pw π 14).toNat := (pw_toNat π 14 (by (clear * - hsz hsize hpi; omega))).symm
  have hfs : (Header.ofProof π).s = Lvm.X.hdD π 10 := (Lvm.X.hdD_eq_digestAt π 10).symm
  have hfvk : (Header.ofProof π).vk = Lvm.X.hdD π 2 := (Lvm.X.hdD_eq_digestAt π 2).symm
  have hfcL : (Header.ofProof π).cL = Lvm.X.hdD π 6 := (Lvm.X.hdD_eq_digestAt π 6).symm
  have hfh : (Header.ofProof π).h = Lvm.X.hdD π 15 := (Lvm.X.hdD_eq_digestAt π 15).symm
  have hfsig : (Header.ofProof π).sig = Lvm.X.sigOfF fun j => Lvm.X.pw π (19 + j) :=
    sig_eq π (by rw [hpi]; decide)
  by_cases hb : Lvm.X.pw π 1 = 0
  · -- a leaf
    right
    rw [Lvm.X.EXM_leaf _ c π L hsize hb0 hb]
    unfold extSM witOf
    rw [hhd, if_pos (by rw [hfb, hb]; rfl), hfs, hfn]
    rfl
  have hbne : (Header.ofProof π).b ≠ 0 := by
    rw [hfb]; intro h0'; exact hb (BitVec.eq_of_toNat_eq (by rw [h0']; rfl))
  by_cases hdom : Lvm.X.InDomE c π L
  swap
  · -- a node outside the domain: the search
    left
    rw [Lvm.X.EXM_node_out _ c π L hdom hsize hb0 hb]
    have hvk : Lvm.X.hdD π 2 = vk := by
      have := hok
      simp only [schemeS, okS, Bool.and_eq_true, beq_iff_eq] at this
      rw [← hfvk, ← hhd]
      exact this.1.1.1.2
    rw [hvk]
    exact Lvm.X.search_spec_acc (fun c' p hp => hA vk c' p hp)
      ⟨_, (kcertSM hmid hLm hsh (extJM hsh (hnode vk))).extract hok hreach hafter hB hBp hD⟩
  -- a node in the domain
  right
  have hS' : ¬ Lvm.X.StateHit L := Lvm.X.notStateHit_of_notBad (Scheme.mu_lt_one hμ).1
  -- the invariant's post (`ExtIM`) and no luck at the end: the decoders succeed
  obtain ⟨hDI, hL⟩ := not_or.1 hB
  have hE : ExtIM mid Good ((B.drop 8).take hdrLen) h :=
    Spec.post _ (reach_nil_iff.2 hreach) hafter (not_not.1 hDI) rfl
  obtain ⟨h₁, cl, ⟨ρ', r', res'⟩, ⟨t, rfl⟩, hpre, hg⟩ := hE
  obtain ⟨q, -, hdec⟩ := decode_SMH (hsh.noCommit _) hpre hg (reachable_commit_ws hreach) hL
  have hd : mainDataM mid ((B.drop 8).take hdrLen) (h₁ ++ t) = some (r'.1.folds, res') := by
    unfold mainDataM
    rw [VerifierProgram.retSplit_of_after _ _ _ hpre]
  dsimp only at hdec
  -- the history, kind by kind
  obtain ⟨W₀, lm, ρ, lq, lf0, r0, W₁, pre0, w0, post0, lf1, r1, W₂, pre1, w1, post1, lf2, r2, lres, res, qs0, qs1,
    k0, k1, hh₁, ha, hmidr, fq, ff0, sf0, lf0l, hr0, fp0, fpo0, ff1, sf1, lf1l, hr1, fp1, fpo1, ff2, sf2, lf2l,
    hr2, hlres, hreslen, hq0l, hP0, hq1l, hP1⟩ := mainPrefix_splitK hpre
  obtain ⟨rfl, rfl, rfl⟩ : ρ = ρ' ∧ r2 = r' ∧ res = res' := by
    simp only [Prod.mk.injEq] at ha; exact ⟨ha.1.symm, ha.2.1.symm, ha.2.2.symm⟩
  subst hh₁
  -- the replay of the root
  have htr' := htr
  change S.trun L (PSWithM mid ((B.drop 8).take hdrLen)) e₁.2 [] [] (B.drop 5984) [] = _ at htr'
  obtain ⟨k, hk, htrk⟩ := root_trunM htr'
  obtain ⟨rest0, hrest0⟩ := trun_prefix _ _ _ _ _ _ _ _ _ _ htrk
  simp only [List.cons_append, List.cons.injEq, Ev.commit.injEq, true_and] at hrest0
  obtain ⟨hW0, -⟩ := hrest0
  subst hW0
  obtain ⟨oA1, oA1o, oA1p, oA2, oA2o, oA2p, oB1, oB1o, oB1p, oA3, oA3o, oA3p, oB2, oB2o, oB2p, oCnt, hRSm, kA1, kA2,
    kB1, kA3, kB2, oc1, oc2, ores⟩ := openMain_P20
  have fm : lm.map kindOf = itemKinds midItems := hfol _ lm cl hmidr
  -- segment A1: the middle phases, `ρ`, the intro, level 0's fold rounds
  have hkA1 : List.Forall₂ KM (lm ++ ([Ev.sample ρ] ++ (lq ++ lf0))) (itemK2 P20 shMain (midItems ++ mainHeadA1)) := by
    rw [itemK2_append, itemK2_rs _ _ _ hRSm, kA1]
    refine forall₂_append (forall₂_of_kinds lm _ fm (other_not_mem _ hRSm)) (forall₂_of_kinds _ _ ?_ (by decide))
    rw [List.map_append, List.map_append, fq, ff0]
    rfl
  obtain ⟨stA1, p1, hsA1, haA1, -, htA1⟩ :=
    trun_simK2 S (fun _ ↦ rfl) L B (itemK2 P20 shMain (midItems ++ mainHeadA1))
    k 14176 5984 e₁.2 _ _ (lm ++ ([Ev.sample ρ] ++ (lq ++ lf0)))
    ((Ev.commit 16 (3 * 2 ^ 4) W₁ :: (pre0 ++ (Ev.query w0 :: (post0 ++ (lf1 ++ (Ev.commit 13 (3 * 2 ^ 4) W₂ ::
      (pre1 ++ (Ev.query w1 :: (post1 ++ (lf2 ++ lres)))))))))) ++ t) true
    (fun ht w nb hm => by
      rw [itemK2_append, itemK2_rs _ _ _ hRSm, kA1, ← List.map_append] at hm
      exact absurd hm (not_commit_toK2 _))
    (by norm_num) hkA1 (by
      rw [htrk]; simp only [List.append_assoc, List.cons_append, List.nil_append, List.singleton_append])
  rw [oA1o, oA1p] at htA1
  have capsA1 : capsK2 S B (itemK2 P20 shMain (midItems ++ mainHeadA1)) 14176 [S.capI 19 64 (B.drop 5984)] =
      [S.capI 19 64 (B.drop 5984)] := by
    rw [itemK2_append, itemK2_rs _ _ _ hRSm, kA1, ← List.map_append, capsK2_toK2]
  rw [capsA1] at htA1
  -- segment A2: level 1's cap, the OOD point, answer and intro, level 0's proof of work, positions and `λ`
  have hkA2 : List.Forall₂ KM (Ev.commit 16 (3 * 2 ^ 4) W₁ :: pre0) (itemK2 P20 shMain mainHeadA2) := by
    rw [kA2]; exact .cons ⟨rfl, rfl⟩ (forall₂_of_kinds _ _ fp0 (by decide))
  obtain ⟨stA2, p2, hsA2, haA2, -, htA2⟩ :=
    trun_simK2 S (fun _ ↦ rfl) L B (itemK2 P20 shMain mainHeadA2) p1 141856 141808 stA1
    _ _ (Ev.commit 16 (3 * 2 ^ 4) W₁ :: pre0)
    ((Ev.query w0 :: (post0 ++ (lf1 ++ (Ev.commit 13 (3 * 2 ^ 4) W₂ ::
      (pre1 ++ (Ev.query w1 :: (post1 ++ (lf2 ++ lres)))))))) ++ t) true
    (fun ht w nb hm => by
      rw [kA2, List.mem_cons] at hm
      rcases hm with hm | hm
      · cases hm; exact capBytes_lv vk (PSWithM mid) (by norm_num) 48
      · exact absurd hm (not_commit_toK2 _))
    (by norm_num) hkA2 (by
      rw [htA1]; simp only [List.append_assoc, List.cons_append, List.nil_append, List.singleton_append])
  rw [oA2o, oA2p] at htA2
  have hW1 : W₁ = S.wordOf L (S.capI 16 48 (B.drop 141856)) := by
    rw [kA2, simK2, Option.map_eq_some_iff] at hsA2
    obtain ⟨r', -, e⟩ := hsA2
    simp only [Prod.mk.injEq, List.cons.injEq, Ev.commit.injEq] at e
    exact e.1.1.2.2.symm
  have capsA2 : capsK2 S B (itemK2 P20 shMain mainHeadA2) 141856 [S.capI 19 64 (B.drop 5984)] =
      [S.capI 19 64 (B.drop 5984), S.capI 16 48 (B.drop 141856)] := by
    rw [kA2]; simp only [capsK2]; rw [capsK2_toK2]; rfl
  rw [capsA2] at htA2
  -- the program at level 0's opening, and the opening
  have hPq : p2 = .query 0 qs0 k0 := by
    rw [hk] at hP0
    simp only [List.cons_append, List.nil_append, VerifierProgram.after, and_self, ite_true] at hP0
    have e : k.after ((lm ++ ([Ev.sample ρ] ++ (lq ++ lf0))) ++ (Ev.commit 16 (3 * 2 ^ 4) W₁ :: pre0)) = some p2 := by
      rw [VerifierProgram.after_append, haA1, Option.bind_some, haA2]
    simp only [List.append_assoc, List.cons_append, List.nil_append, List.singleton_append] at hP0 e
    rw [hP0] at e
    exact (Option.some.inj e).symm
  rw [hPq] at htA2
  obtain ⟨rows0, hrw0, hq0a, -, htQ0⟩ := trun_query S L (i := 0) (ci := S.capI 19 64 (B.drop 5984)) rfl
    (show S.trun L (.query 0 qs0 k0) stA2 (sl B 146048 (146048 - 146048)) _ (B.drop 146048) _ =
      some (true, _ ++ Ev.query w0 :: ((post0 ++ (lf1 ++ (Ev.commit 13 (3 * 2 ^ 4) W₂ ::
        (pre1 ++ (Ev.query w1 :: (post1 ++ (lf2 ++ lres))))))) ++ t)) by
      rw [htA2]; simp only [List.append_assoc, List.cons_append, List.nil_append, List.singleton_append])
  cases hrw0
  have hpb0 : qs0.length * posBytes S (S.capI 19 64 (B.drop 5984)) = 83720 := by
    have ho : S.occ 19 64 = 47 := rfl
    rw [hq0l, capI_root, posBytes, Scheme.lb]
    simp only [ho]
    decide
  rw [hpb0, List.drop_drop, show 146048 + 83720 = 229768 from rfl, sl_zero, ← sl_zero B 229768,
    ← Nat.sub_self 229768] at htQ0
  -- segment B1: level 0's opening's intro, level 1's fold rounds
  have hkB1 : List.Forall₂ KM (post0 ++ lf1) (itemK2 P20 shMain mainHeadB1) := by
    rw [kB1]
    refine forall₂_of_kinds _ _ ?_ (by decide)
    rw [List.map_append, fpo0, ff1]
    rfl
  obtain ⟨stB1, p3, hsB1, haB1, -, htB1⟩ :=
    trun_simK2 S (fun _ ↦ rfl) L B (itemK2 P20 shMain mainHeadB1) (k0 w0) 229768 229768
    stA2 _ _ (post0 ++ lf1) ((Ev.commit 13 (3 * 2 ^ 4) W₂ :: (pre1 ++ (Ev.query w1 :: (post1 ++ (lf2 ++ lres))))) ++ t)
    true (fun ht w nb hm => by rw [kB1] at hm; exact absurd hm (not_commit_toK2 _))
    le_rfl hkB1 (by
      rw [htQ0]; simp only [List.append_assoc, List.cons_append, List.nil_append, List.singleton_append])
  rw [oB1o, oB1p] at htB1
  have capsB1 : capsK2 S B (itemK2 P20 shMain mainHeadB1) 229768
      [S.capI 19 64 (B.drop 5984), S.capI 16 48 (B.drop 141856)] =
      [S.capI 19 64 (B.drop 5984), S.capI 16 48 (B.drop 141856)] := by
    rw [kB1, capsK2_toK2]
  rw [capsB1] at htB1
  -- segment A3: level 2's cap, the OOD point, answer and intro, level 1's proof of work, positions and `λ`
  have hkA3 : List.Forall₂ KM (Ev.commit 13 (3 * 2 ^ 4) W₂ :: pre1) (itemK2 P20 shMain mainHeadA3) := by
    rw [kA3]; exact .cons ⟨rfl, rfl⟩ (forall₂_of_kinds _ _ fp1 (by decide))
  obtain ⟨stA3, p4, hsA3, haA3, -, htA3⟩ :=
    trun_simK2 S (fun _ ↦ rfl) L B (itemK2 P20 shMain mainHeadA3) p3 230008 229960 stB1
    _ _ (Ev.commit 13 (3 * 2 ^ 4) W₂ :: pre1) ((Ev.query w1 :: (post1 ++ (lf2 ++ lres))) ++ t) true
    (fun ht w nb hm => by
      rw [kA3, List.mem_cons] at hm
      rcases hm with hm | hm
      · cases hm; exact capBytes_lv vk (PSWithM mid) (by norm_num) 48
      · exact absurd hm (not_commit_toK2 _))
    (by norm_num) hkA3 (by
      rw [htB1]; simp only [List.append_assoc, List.cons_append, List.nil_append, List.singleton_append])
  rw [oA3o, oA3p] at htA3
  have hW2 : W₂ = S.wordOf L (S.capI 13 48 (B.drop 230008)) := by
    rw [kA3, simK2, Option.map_eq_some_iff] at hsA3
    obtain ⟨r', -, e⟩ := hsA3
    simp only [Prod.mk.injEq, List.cons.injEq, Ev.commit.injEq] at e
    exact e.1.1.2.2.symm
  have capsA3 : capsK2 S B (itemK2 P20 shMain mainHeadA3) 230008
      [S.capI 19 64 (B.drop 5984), S.capI 16 48 (B.drop 141856)] =
      [S.capI 19 64 (B.drop 5984), S.capI 16 48 (B.drop 141856), S.capI 13 48 (B.drop 230008)] := by
    rw [kA3]; simp only [capsK2]; rw [capsK2_toK2]; rfl
  rw [capsA3] at htA3
  -- the program at level 1's opening, and the opening
  have hPq1 : p4 = .query 1 qs1 k1 := by
    rw [hk] at hP1
    simp only [List.cons_append, List.nil_append, VerifierProgram.after, and_self, ite_true] at hP1
    have e : k.after ((lm ++ ([Ev.sample ρ] ++ (lq ++ lf0))) ++ ((Ev.commit 16 (3 * 2 ^ 4) W₁ :: pre0) ++
        ([Ev.query w0] ++ ((post0 ++ lf1) ++ (Ev.commit 13 (3 * 2 ^ 4) W₂ :: pre1))))) = some p4 := by
      rw [VerifierProgram.after_append, haA1, Option.bind_some, VerifierProgram.after_append, haA2, Option.bind_some,
        hPq, VerifierProgram.after_append, hq0a, Option.bind_some, VerifierProgram.after_append, haB1,
        Option.bind_some, haA3]
    simp only [List.append_assoc, List.cons_append, List.nil_append, List.singleton_append] at hP1 e
    rw [hP1] at e
    exact (Option.some.inj e).symm
  rw [hPq1] at htA3
  obtain ⟨rows1, hrw1, -, -, htQ1⟩ := trun_query S L (i := 1) (ci := S.capI 16 48 (B.drop 141856)) rfl
    (show S.trun L (.query 1 qs1 k1) stA3 (sl B 234200 (234200 - 234200)) _ (B.drop 234200) _ =
      some (true, _ ++ Ev.query w1 :: ((post1 ++ (lf2 ++ lres)) ++ t)) by
      rw [htA3]; simp only [List.append_assoc, List.cons_append, List.nil_append, List.singleton_append])
  cases hrw1
  have hpb1 : qs1.length * posBytes S (S.capI 16 48 (B.drop 141856)) = 51744 := by
    have ho : S.occ 16 48 = 48 := rfl
    rw [hq1l, capI_lv vk (PSWithM mid) (by norm_num) (i := 1) (by norm_num), posBytes, Scheme.lb]
    simp only [ho]
    decide
  rw [hpb1, List.drop_drop, show 234200 + 51744 = 285944 from rfl, sl_zero, ← sl_zero B 285944,
    ← Nat.sub_self 285944] at htQ1
  -- segment B2: level 1's opening's intro, level 2's fold rounds
  have hkB2 : List.Forall₂ KM (post1 ++ lf2) (itemK2 P20 shMain mainHeadB2) := by
    rw [kB2]
    refine forall₂_of_kinds _ _ ?_ (by decide)
    rw [List.map_append, fpo1, ff2]
    rfl
  obtain ⟨stB2, p5, hsB2, -, -, htB2⟩ :=
    trun_simK2 S (fun _ ↦ rfl) L B (itemK2 P20 shMain mainHeadB2) (k1 w1) 285944 285944
    stA3 _ _ (post1 ++ lf2) (lres ++ t) true
    (fun ht w nb hm => by rw [kB2] at hm; exact absurd hm (not_commit_toK2 _))
    le_rfl hkB2 (by
      rw [htQ1]; simp only [List.append_assoc, List.cons_append, List.nil_append, List.singleton_append])
  rw [oB2o, oB2p] at htB2
  -- the residual
  have hk2 : lres.map kindOf = List.replicate (2 ^ 9) .read := by
    rw [hlres, List.map_map, ← hreslen]
    show List.map (fun _ => EvK.read) res = _
    exact List.map_const'
  obtain ⟨stR, -, -, hsimR, -, -⟩ := trun_simK S (fun _ ↦ rfl) L B _ p5 286184 286136 stB2 _ _ lres t true
    (fun hm => by cases (List.mem_replicate.1 hm).2) (by norm_num) hk2 (by
      rw [htB2]; simp only [List.append_assoc, List.cons_append, List.nil_append])
  rw [simK_reads] at hsimR
  have hresv : res = (List.range (2 ^ 9)).map fun i => eOfBytes (sl B (286184 + 24 * i) 24) := by
    have e := (Prod.mk.inj (Option.some.inj hsimR)).1
    rw [hlres] at e
    apply List.map_injective_iff.2 (fun a b hab => Ev.read.inj hab)
    rw [← e, List.map_map]
    rfl
  -- the chain
  have hfm1 : Lvm.X.fmAns (Lvm.X.fsQL π) Lvm.X.zeroDL L 1 = some e₁.2 := by
    have hq0 : Lvm.X.fsQL π 0 Lvm.X.zeroDL = toQ S.q0 := rfl
    have hseed : Lvm.X.fsQL π 1 e₀.2 = S.seedQ e₀.2 ((B.drop 8).take hdrLen) := by
      rw [fsQL_eq π (by norm_num), msgL_eq, show 1 - 1 = 0 from rfl, fsMsg0]
      rfl
    simp only [Lvm.X.fmAns, hq0, h0, Option.map_some, Option.bind_some, zero_add, hseed]
    exact congrArg (Option.map Prod.snd) h1
  have nos : ∀ (l : List Ev), l.map kindOf = [.read, .read] → l.filterMap sampleOf = [] := fun l hl => by
    have := samples_length l
    rw [hl] at this
    exact List.length_eq_zero_iff.1 (by simpa using this)
  have cA1 := simK2_chain S L B (Lvm.X.fsQL π) Lvm.X.zeroDL _ 14176 5984 e₁.2 1 _ stA1 hsA1 hfm1
    (chainT π (D := 1) (N := 1248) oA1 (by norm_num))
  simp only [smpOf_eq] at cA1
  obtain ⟨cA1, fA1⟩ := cA1
  have hlm : (lm.filterMap sampleOf).length = 1241 := by rw [samples_length, fm]; exact oCnt
  have hpreS : (lm ++ ([Ev.sample ρ] ++ (lq ++ lf0))).filterMap sampleOf = lm.filterMap sampleOf ++ (ρ :: r0.2) := by
    simp only [List.filterMap_append, nos lq fq, sf0, List.nil_append]
    rfl
  have hA1n : ((lm ++ ([Ev.sample ρ] ++ (lq ++ lf0))).filterMap sampleOf).length = 1248 := by
    rw [hpreS, List.length_append, hlm, List.length_cons, lf0l]
  rw [hA1n] at fA1
  have cA2 := simK2_chain S L B (Lvm.X.fsQL π) Lvm.X.zeroDL _ 141856 141808 stA1 1249 _ stA2 hsA2 fA1
    (chainT π (D := 1249) (N := 35) oA2 (by norm_num))
  simp only [smpOf_eq] at cA2
  obtain ⟨-, fA2⟩ := cA2
  have hA2n : ((Ev.commit 16 (3 * 2 ^ 4) W₁ :: pre0).filterMap sampleOf).length = 35 := by
    rw [show (Ev.commit 16 (3 * 2 ^ 4) W₁ :: pre0).filterMap sampleOf = pre0.filterMap sampleOf from rfl,
      samples_length, fp0]
    decide
  rw [hA2n] at fA2
  have cB1 := simK2_chain S L B (Lvm.X.fsQL π) Lvm.X.zeroDL _ 229768 229768 stA2 1284 _ stB1 hsB1 fA2
    (chainT π (D := 1284) (N := 4) oB1 (by norm_num))
  simp only [smpOf_eq] at cB1
  obtain ⟨cB1, fB1⟩ := cB1
  have hpreB1 : (post0 ++ lf1).filterMap sampleOf = r1.2 := by
    rw [List.filterMap_append, nos post0 fpo0, List.nil_append, sf1]
  rw [hpreB1, lf1l] at fB1
  have cA3 := simK2_chain S L B (Lvm.X.fsQL π) Lvm.X.zeroDL _ 230008 229960 stB1 1288 _ stA3 hsA3 fB1
    (chainT π (D := 1288) (N := 26) oA3 (by norm_num))
  simp only [smpOf_eq] at cA3
  obtain ⟨-, fA3⟩ := cA3
  have hA3n : ((Ev.commit 13 (3 * 2 ^ 4) W₂ :: pre1).filterMap sampleOf).length = 26 := by
    rw [show (Ev.commit 13 (3 * 2 ^ 4) W₂ :: pre1).filterMap sampleOf = pre1.filterMap sampleOf from rfl,
      samples_length, fp1]
    decide
  rw [hA3n] at fA3
  have cB2 := simK2_chain S L B (Lvm.X.fsQL π) Lvm.X.zeroDL _ 285944 285944 stA3 1314 _ stB2 hsB2 fA3
    (chainT π (D := 1314) (N := 4) oB2 (by norm_num))
  simp only [smpOf_eq] at cB2
  obtain ⟨cB2, -⟩ := cB2
  have hpreB2 : (post1 ++ lf2).filterMap sampleOf = r2.2 := by
    rw [List.filterMap_append, nos post1 fpo1, List.nil_append, sf2]
  -- the fold challenges are the chain's answers
  have hfolds : r2.1.folds = r0.2 ++ r1.2 ++ r2.2 := by rw [hr2, hr1, hr0]
  have hfold : ∀ k < 14, ∃ a, Lvm.X.fmAns (Lvm.X.fsQL π) Lvm.X.zeroDL L (Lvm.X.foldPosK Lvm.X.pX k) = some a ∧
      r2.1.folds.getD k 0 = chalOf a := by
    intro k hk
    rw [hfolds]
    by_cases k0' : k < 6
    · have hlen : 1242 + k < ((lm ++ ([Ev.sample ρ] ++ (lq ++ lf0))).filterMap sampleOf).length := by
        rw [hA1n]; (clear * - hk k0'; omega)
      obtain ⟨a, ha, hea⟩ := cA1 (1242 + k) hlen
      refine ⟨a, by rw [Lvm.X.foldPosK_0 k0', Lvm.X.fp0_v, show 1244 + k = 1 + 1 + (1242 + k) by (clear * -; omega)]; exact ha, ?_⟩
      have e1 : (r0.2 ++ r1.2 ++ r2.2).getD k 0 = r0.2.getD k 0 := by
        rw [List.append_assoc, List.getD_append _ _ _ _ (by rw [lf0l]; exact k0')]
      have e2 : (List.filterMap sampleOf lm ++ ρ :: r0.2).getD (1242 + k) 0 = r0.2.getD k 0 := by
        rw [List.getD_append_right _ _ _ _ (by (clear * - hlm hk k0'; omega)), hlm, show 1242 + k - 1241 = k + 1 by (clear * - hk k0'; omega)]
        rfl
      rw [e1, show chalOf a = S.chal a from rfl, ← hea, ← List.getD_eq_getElem _ 0 hlen, hpreS, e2]
    by_cases k1' : k < 10
    · have hlen : k - 6 < ((post0 ++ lf1).filterMap sampleOf).length := by rw [hpreB1, lf1l]; (clear * - hk k0' k1'; omega)
      obtain ⟨a, ha, hea⟩ := cB1 (k - 6) hlen
      refine ⟨a, by
        rw [show k = 6 + (k - 6) by (clear * - hk k0' k1'; omega), Lvm.X.foldPosK_1 (by (clear * - hk k0' k1'; omega)), Lvm.X.fp1_v,
          show 1285 + (k - 6) = 1284 + 1 + (k - 6) by (clear * -; omega)]; exact ha, ?_⟩
      have e1 : (r0.2 ++ r1.2 ++ r2.2).getD k 0 = r1.2.getD (k - 6) 0 := by
        rw [List.append_assoc, List.getD_append_right _ _ _ _ (by rw [lf0l]; (clear * - hk k0' k1'; omega)), lf0l,
          List.getD_append _ _ _ _ (by rw [lf1l]; (clear * - hk k0' k1'; omega))]
      rw [e1, show chalOf a = S.chal a from rfl, ← hea, ← List.getD_eq_getElem _ 0 hlen, hpreB1]
    · have hlen : k - 10 < ((post1 ++ lf2).filterMap sampleOf).length := by rw [hpreB2, lf2l]; (clear * - hk k0' k1'; omega)
      obtain ⟨a, ha, hea⟩ := cB2 (k - 10) hlen
      refine ⟨a, by
        rw [show k = 10 + (k - 10) by (clear * - hk k0' k1'; omega), Lvm.X.foldPosK_2 (by (clear * - hk k0' k1'; omega)), Lvm.X.fp2_v,
          show 1315 + (k - 10) = 1314 + 1 + (k - 10) by (clear * -; omega)]; exact ha, ?_⟩
      have e1 : (r0.2 ++ r1.2 ++ r2.2).getD k 0 = r2.2.getD (k - 10) 0 := by
        rw [List.getD_append_right _ _ _ _ (by rw [List.length_append, lf0l, lf1l]; (clear * - hk k0' k1'; omega)), List.length_append, lf0l,
          lf1l]
      rw [e1, show chalOf a = S.chal a from rfl, ← hea, ← List.getD_eq_getElem _ 0 hlen, hpreB2]
  let αk : ℕ → RecursionFast.Digest := fun k => if k < 14 then
    (Lvm.X.fmAns (Lvm.X.fsQL π) Lvm.X.zeroDL L (Lvm.X.foldPosK Lvm.X.pX k)).getD Lvm.X.zeroDL else Lvm.X.zeroDL
  have hα : ∀ k < 14, Lvm.X.fmAns (Lvm.X.fsQL π) Lvm.X.zeroDL L (Lvm.X.foldPosK Lvm.X.pX k) = some (αk k) := by
    intro k hk
    obtain ⟨a, ha, -⟩ := hfold k hk
    simp only [αk, if_pos hk, ha, Option.getD_some]
  have hfv : ∀ k < 14, r2.1.folds.getD k 0 = Lvm.X.alphaE (αk k) := by
    intro k hk
    obtain ⟨a, ha, hra⟩ := hfold k hk
    simp only [αk, if_pos hk, ha, Option.getD_some]
    rw [hra, chalOf_eq_alphaE]
  -- the history's commitments
  have hcm : commits ((Ev.commit 19 64 (S.wordOf L (S.capI 19 64 (B.drop 5984))) :: (lm ++ (Ev.sample ρ ::
      (lq ++ (lf0 ++ (Ev.commit 16 (3 * 2 ^ 4) W₁ :: (pre0 ++ (Ev.query w0 :: (post0 ++ (lf1 ++
        (Ev.commit 13 (3 * 2 ^ 4) W₂ :: (pre1 ++ (Ev.query w1 :: (post1 ++ (lf2 ++ lres))))))))))))))) ++ t) =
      [(19, 64, S.wordOf L (S.capI 19 64 (B.drop 5984))), (16, 3 * 2 ^ 4, W₁), (13, 3 * 2 ^ 4, W₂)] ++ commits t := by
    have c1 := NoCommit.after_commits (hsh.noCommit _) hmidr
    have c2 := commits_nil_of_kindsEq fq (by decide)
    have c3 := commits_nil_of_kindsEq ff0 (by decide)
    have c4 := commits_nil_of_kindsEq fp0 (by decide)
    have c5 := commits_nil_of_kindsEq fpo0 (by decide)
    have c6 := commits_nil_of_kindsEq ff1 (by decide)
    have c7 := commits_nil_of_kindsEq fp1 (by decide)
    have c8 := commits_nil_of_kindsEq fpo1 (by decide)
    have c9 := commits_nil_of_kindsEq ff2 (by decide)
    have c10 := commits_nil_of_kindsEq hk2 (by simp)
    simp only [List.cons_append, List.append_assoc, LeanVM.Protocol.Whir.Sound.commits_append, commits, c1, c2, c3,
      c4, c5, c6, c7, c8, c9, c10, List.nil_append]
  have hw0 : wordOf ([(19, 64, S.wordOf L (S.capI 19 64 (B.drop 5984))), (16, 3 * 2 ^ 4, W₁), (13, 3 * 2 ^ 4, W₂)] ++
      commits t) 0 = S.wordOf L (S.capI 19 64 (B.drop 5984)) := by
    rw [wordOf_append_of_lt _ _ (by simp)]; rfl
  have hw1 : wordOf ([(19, 64, S.wordOf L (S.capI 19 64 (B.drop 5984))), (16, 3 * 2 ^ 4, W₁), (13, 3 * 2 ^ 4, W₂)] ++
      commits t) 1 = W₁ := by
    rw [wordOf_append_of_lt _ _ (by simp)]; rfl
  have hw2 : wordOf ([(19, 64, S.wordOf L (S.capI 19 64 (B.drop 5984))), (16, 3 * 2 ^ 4, W₁), (13, 3 * 2 ^ 4, W₂)] ++
      commits t) 2 = W₂ := by
    rw [wordOf_append_of_lt _ _ (by simp)]; rfl
  rw [hcm, hw0, hw1, hw2] at hdec
  obtain ⟨m₂, hd₂, hrest⟩ := Option.bind_eq_some_iff.1 hdec
  obtain ⟨m₁, hd₁, hd₀⟩ := Option.bind_eq_some_iff.1 hrest
  -- π's caps are the history's
  have cp0 : S.capI 19 64 (B.drop 5984) = ⟨19, 17 + 47, 8, Lvm.X.capM π 0⟩ := capI_capM0 vk (PSWithM mid) π hpi
  have cp1 : S.capI 16 48 (B.drop 141856) = ⟨16, 0 + 48, 7, Lvm.X.capM π 1⟩ := capI_capM1 vk (PSWithM mid) π hpi
  have cp2 : S.capI 13 48 (B.drop 230008) = ⟨13, 0 + 48, 7, Lvm.X.capM π 2⟩ := capI_capM2 vk (PSWithM mid) π hpi
  -- the extractor's run
  rw [Lvm.X.EXM_node (accV VS) c π L hdom hsize hb0 hb hS' αk hα _ _ _
    (fun q' _ t' _ => by
      rw [Lvm.X.wdOf, cp0, readRowG_eq_wordOf S rfl (show S.occ 19 (17 + 47) = 47 from rfl)])
    (fun q' _ t' _ => by
      rw [Lvm.X.wdOf, hW1, cp1, readRowG_eq_wordOf S rfl (show S.occ 16 (0 + 48) = 48 from rfl)])
    (fun q' _ t' _ => by
      rw [Lvm.X.wdOf, hW2, cp2, readRowG_eq_wordOf S rfl (show S.occ 13 (0 + 48) = 48 from rfl)])
    _ _ _ (fun j hj => by rw [Lvm.X.alphaN, dif_pos hj]; exact hfv j (by (clear * - hj; omega)))
    (fun j hj => by rw [Lvm.X.alphaN1, dif_pos hj]; exact hfv (6 + j) (by (clear * - hj; omega)))
    (fun j hj => by rw [Lvm.X.alphaN1, dif_pos hj]; exact hfv (10 + j) (by (clear * - hj; omega)))
    _ (fun v hv => by
      rw [resEM_eq π v (by rw [ores, hpi]; (clear * - hv; omega)), ores]
      unfold Lvm.X.fNk
      rw [dif_pos hv]
      unfold resMsg
      erw [bitsToNat_symmN 9 v hv]
      rw [hresv, List.getD_eq_getElem _ _ (by simp only [List.length_map, List.length_range]; omega),
        List.getElem_map, List.getElem_range]
      rfl)
    m₂ hd₂ m₁ hd₁ _ hd₀]
  -- the specification's witness
  unfold extSM
  rw [hd, Option.bind_some]
  dsimp only
  rw [hcm, hw0, hw1, hw2, hd₂, Option.bind_some, hd₁, Option.bind_some, hd₀, Option.getD_some]
  have hn : (Lvm.VEq.pubX ((B.drop 8).take hdrLen)).n = (Lvm.X.pw π 14).toNat := by rw [pubX_n, hhd, hfn]
  have hlen : (Lvm.X.winOf q).length = 2 ^ 20 := by simp [Lvm.X.winOf, Lvm.X.winC]
  rw [Lvm.NS.xwit_childW, hchild π _ (Lvm.X.winOf q) hn hlen]
  unfold witOf
  rw [hhd, if_neg hbne, hfcL, hfh, hfn, hfs, hfsig]

end Lvm.ASM
end

-- ===== from `LvmCertM20` =====

section
section
set_option autoImplicit false
namespace Lvm.CT
open RecursionFast Lvm Lvm.T Lvm.ASM Lvm.FS
open RecursionFast.WitnessSending (encode decode encodeF)
open LeanVM.Protocol.Compile hiding Proof Bytes
open scoped NNReal ENNReal

/-- **The query bound of the typed `V_S`** on every oracle path (`queries_VS_le`'s proof: the decision is a
`.ret`). -/
theorem queries_VST_le (p : Params) (N : TypedV.TNat) (vk c : Digest) (π : RecursionFast.Proof)
    (H : ByteArray → Digest) :
    ((VST p N vk c π).queries H).length ≤ 2 + qcItems p (schedule p) 0 := by
  unfold VST
  split
  · simp only [drive, OProg.queries, List.length_cons]
    refine (Nat.add_le_add_right (Nat.add_le_add_right (q_driveItems H π p _ 0 (fun s ↦ by
      simp [OProg.queries]) (schedule p) 0 _ (by simp)) 1) 1).trans ?_
    omega
  · simp [OProg.queries]

/-- **O1** for the typed `V_S` at `P20`, any instance. -/
theorem hq_VST20 (N : TypedV.TNat) (H : ByteArray → Digest) (vk c : Digest) (π : RecursionFast.Proof) :
    ((VST P20 N vk c π).queries H).length ≤ qVlvm :=
  (queries_VST_le P20 N vk c π H).trans qcItems_P20

/-- O4 for `EX (accV VS)`: on witness-sending proofs it decodes. -/
theorem EX_Wv (VS : SProg) (c : Digest) (π : RecursionFast.Proof) (L : Log) (h : isS π = false) :
    Lvm.X.EX (accV VS) c π L = decode π := by
  refine Lvm.X.EX_W _ c π L fun h0 ↦ ?_
  have : π.data.getD 0 0 = 0x53 := by
    rw [Array.getD_eq_getD_getElem?, h0]; rfl
  simp [isS, this, sByte] at h

/-- **The certificate of `subWith VS (EX (accV VS)) extX`** from O1 and the open obligations. -/
theorem certificateR_openV (VS : SProg)
    (hq : ∀ H vk c π, ((VS vk c π).queries H).length ≤ qVlvm) (o : OpenS VS (Lvm.X.EX (accV VS))) :
    CertificateR ⟨(1 : ℝ≥0) / 340282366920938463463374607431768211456, (0 : ℝ≥0) / 1, 16384,
      fun t => 70368744177664 + 8192 * t⟩ (subWith VS (Lvm.X.EX (accV VS)) Lvm.X.extX) :=
  certificateR_claim VS _ Lvm.X.extX
    ⟨fun H vk c π _ ↦ hq H vk c π, Lvm.X.computesX _, Lvm.X.extX_caps.2, EX_Wv VS, sSound_of_openS o⟩

/-- The guarded submission with the guard on is the plain one. -/
theorem subG_true (VS : SProg) : Lvm.Fin.subG true VS = subWith VS (Lvm.X.EX (accV VS)) Lvm.X.extX := rfl

/-- **The certificate of the guarded submission `subG b VS`** from O1 and the open obligations under
`b = true` (`certificateR_guardT`'s, any `V_S`). -/
theorem certificateR_guardV (VS : SProg) (hq : ∀ H vk c π, ((VS vk c π).queries H).length ≤ qVlvm) {b : Bool}
    (h : b = true → OpenS VS (Lvm.X.EX (accV VS))) :
    CertificateR ⟨(1 : ℝ≥0) / 340282366920938463463374607431768211456, (0 : ℝ≥0) / 1, 16384,
      fun t => 70368744177664 + 8192 * t⟩ (Lvm.Fin.subG b VS) := by
  cases b with
  | false => exact Lvm.Fin.certificateR_reject _
  | true => rw [subG_true]; exact certificateR_openV VS hq (h rfl)

end Lvm.CT
end
end

section
section
set_option autoImplicit false
namespace Lvm.CT
open Lvm Lvm.Typed Lvm.QTyped Lvm.TypedV Lvm.M3 Lvm.QAsm
open Lvm.VEq (pubX)
open scoped ENNReal NNReal

/-- `acc_in` has `phiVars = 43` coordinates on every statement (`pubOf` reads `accVars = 43`). -/
theorem accLen : ∀ x, (pubX x).accIn.pt.length = phiVars := by
  intro x
  simp only [pubX, pubOf, List.length_map, List.length_range]
  rfl

end Lvm.CT
end
end

section
section
set_option autoImplicit false
namespace Lvm.CT
open Lvm Lvm.Typed Lvm.QTyped Lvm.TypedV Lvm.M3 Lvm.QAsm
open Lvm.VEq (pubX)
open scoped ENNReal NNReal

open LeanVM.Protocol.KeccakGkr (errE errE_mono) in
open LeanVM.Protocol.EndToEnd.Front in
open Lvm.ASM in
/-- **The typed phases' error terms** (`TErrs`) at `L₀ = 37,696` against `εS` with follower `LkSJ`, for an instance
of depth `12` (M′ `S2GM`; B1: 13) without constraints: every term is `errE d` with `d ≤ 2^63` (`errE_le_εS`). -/
theorem errs_at (I : LeanVM.Protocol.M3Instance) (hμ : I.μBus = 12) (hB : I.B = 0) :
    TErrs 37696 I εS LkSJ := by
  have hab : abError I 37696 = errE (37696 * (4 * 2 ^ 12)) := by
    rw [abError, coe_overE, errE_smul, hμ]
  have hr : ∀ d, roundError 37696 d = errE (37696 * d) := fun d ↦ by
    rw [roundError, coe_div_card, errE_smul]
  have hl : lambdaError 37696 = errE (37696 * 2) := by
    rw [lambdaError, coe_div_card, errE_smul]
  have hu : unitError 37696 = errE (37696 * 1) := by
    rw [← errE_smul]; simp [unitError, errE]
  have hx : xiError I 37696 = errE (37696 * (I.B + 3 - 1)) := by
    rw [xiError, coe_div_card, errE_smul]
  have hlead : leadT 37696 = errE (20 * (37696 * 1)) := by
    simp only [leadT, add_zero, errE_smul, Lvm.Typed.xVars]
  have h2 : (2 : ℝ≥0∞) * errE 1 = errE (2 * 1) := by rw [← errE_smul]; norm_num
  have hM : leadMaxT 37696 I LkSJ ≤ errE (37696 * (4 * 2 ^ 12)) := by
    unfold leadMaxT
    rw [hlead, hab, add_zero, h2, LkSJ_eq]
    exact max_le (errE_mono (by norm_num)) (max_le le_rfl (max_le (errE_mono (by norm_num))
      (errE_mono (by norm_num))))
  have fin : ∀ a : ℕ, a ≤ 2 ^ 62 → errE a + leadMaxT 37696 I LkSJ ≤ εS := by
    intro a ha
    calc errE a + leadMaxT 37696 I LkSJ ≤ errE a + errE (37696 * (4 * 2 ^ 12)) := by gcongr
      _ = errE (a + 37696 * (4 * 2 ^ 12)) := errE_add _ _
      _ ≤ εS := errE_le_εS (Nat.le_trans (Nat.add_le_add_right ha _) (by norm_num))
  refine ⟨?_, fun d hd ↦ ?_, ?_, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ?_, ?_⟩
  · rw [hlead]; exact errE_le_εS (by norm_num)
  · rw [hr]; exact fin _ (by (clear * - hd; omega))
  · exact fin _ (by norm_num [Lvm.Typed.phiVars, Lvm.Typed.xVars, Lvm.Typed.yVars])
  · rw [hab]; exact lt_of_le_of_lt (errE_le_εS (by norm_num)) εS_lt_one
  · rw [hab]; exact fin _ (by norm_num)
  · rw [interpLead_eq, hu, hl, errE_smul, errE_add]; exact fin _ (by norm_num)
  · rw [hl]; exact fin _ (by norm_num)
  · rw [hx, hB]; exact fin _ (by norm_num)
  · exact hM.trans (errE_le_εS (by norm_num))

end Lvm.CT
end
end

section
section
set_option autoImplicit false
namespace Lvm.NS
open RecursionFast Lvm Lvm.T Lvm.ASM Lvm.Replay Lvm.Loop Lvm.Loop.Build Lvm.QLink Lvm.QSig Lvm.M3
open Lvm.QAsm Lvm.QTyped Lvm.Typed Lvm.TypedV LeanVM.Protocol
open Lvm.VEq (pubX)

theorem mbT_TiB : TiB.mbT = mbTOf cfg20 frz20 := rfl

end Lvm.NS
end
end

section
section
set_option autoImplicit false
namespace Lvm.NS
open RecursionFast Lvm Lvm.T Lvm.ASM Lvm.Replay Lvm.Loop Lvm.Loop.Build Lvm.QLink Lvm.QSig Lvm.M3
open Lvm.QAsm Lvm.QTyped Lvm.Typed Lvm.TypedV LeanVM.Protocol
open Lvm.VEq (pubX)

/-- **The non-`readd` rows hold** on a good pair's memory (L-B's `rowDef_of_wiring`). -/
theorem hlinT (S : Lvm.CT.SF20) {H : THyp TiB} {x : List UInt8} {qm : Column CMain.nu20} {qr : Column 19}
    (hG : GoodT TiB H x qm qr) : NonReaddHolds QB20 (memT x qm qr) :=
  fun _ hi hop ↦ rowDef_of_wiring QB20 layT20 (zT x qm qr) S.wf S.hlay (zT_one H x qm qr) (goodT_wiring hG) hi hop
    (S.noE2 _ hi)

/-- `V_S`'s regions fit `ν = 23`, `ν_rec = 19` (the guard's `regs`). -/
theorem okB20 (S : Lvm.CT.SF20) : NT20.okB 23 19 = true := by
  have h := S.regs
  rwa [show Lvm.QAsm.cfg20.p = P20 from rfl, show P20.nuMain = 23 by decide +kernel,
    show P20.nuRec = 19 by decide +kernel] at h

end Lvm.NS
end
end

section
section
set_option autoImplicit false
namespace Lvm.NS
open RecursionFast Lvm Lvm.T Lvm.ASM Lvm.Replay Lvm.Loop Lvm.Loop.Build Lvm.QLink Lvm.QSig Lvm.M3
open Lvm.QAsm Lvm.QTyped Lvm.Typed Lvm.TypedV LeanVM.Protocol
open Lvm.VEq (pubX)

/-- `readdTGL` at `PUB`'s 3-lane layout (`TNat.inst`). -/
theorem readdTG (C : QCfg) (F : TFrz) (Q : Program) (tl : Typed.Lay) (N : TNat) (pub : Lvm.Pub) (B nPub : ℕ)
    (hlay : tl.Ok Q) (hreg : N.okB 23 19 = true) (hl : N.layOk tl = true) (hσ : SigInS N)
    (hchk : nodeChkBG B nPub C F Q tl N = true) (hrl : C.rl = 14) (hs0 : (layout0 C.p).s = CMain.sOff20)
    (hrr : C.p.recRowsLog = 14) (hnK : 17 * 2 ^ 14 ≤ nK C) (hc : nK C ≤ Q.cells .K)
    {qm : Column CMain.nu20} {qr : Column 19} (hτ : ∀ t ∈ mbTOf C F, t.τ ≤ lay26.μ)
    (hLay : LayOk lay26 (mbTOf C F)) (hM : M3Holds (inst lay26 (mbTOf C F) hτ) () (stackOf lay26 qm qr))
    (hSB : SBlk qm qr) (hlin : NonReaddHolds Q (memOf tl ((N.inst Q tl).zOf lay26 pub qm qr))) :
    ReaddOk Q (memOf tl ((N.inst Q tl).zOf lay26 pub qm qr)) :=
  readdTGL C F Q tl N Pub.hdrLanes pub B nPub hlay hreg hl hσ hchk hrl hs0 hrr hnK hc hτ hLay hM hSB hlin

/-- **`ReaddOk` on a good pair's memory** from the guard's checks (M′ `S2GM`: on a stream-block pair, `SBlk`; the
seeds are `S`'s `C_main` words). -/
theorem readdT (S : Lvm.CT.SF20) (H : THyp TiB) (hchk : nodeChkB cfg20 frz20 QB20 layT20 NT20 = true)
    {x : List UInt8} {qm : Column CMain.nu20} {qr : Column 19} (hG : GoodT TiB H x qm qr) (hSB : SBlk qm qr) :
    ReaddOk QB20 (memT x qm qr) := by
  have hτ : ∀ t ∈ mbTOf cfg20 frz20, t.τ ≤ lay26.μ := fun t ht ↦ H.hτ t (by rw [mbT_TiB]; exact ht)
  have hlay : LayOk lay26 (mbTOf cfg20 frz20) := by have := H.layOk; rwa [mbT_TiB] at this
  rw [nodeChkB_eq] at hchk
  exact readdTG cfg20 frz20 QB20 layT20 NT20 (pubX x) _ _ S.hlay (okB20 S) S.hlayOk S.sig hchk rfl
    (by show (layout0 P20).s = _; rw [Lvm.layout0_P20]) (by decide) (by decide)
    (by rw [QB20_qn]; exact nK_le_cells _ _ _) hτ hlay (m3Holds_eq mbT_TiB hG.1.1.1.2) hSB (hlinT S hG)

/-- `Φ_Q` at the incoming accumulator is its claim (`AccOkT`), through the cache (`PhiQC_eq`, `cacheT20_eq`). -/
theorem phi_accIn (S : Lvm.CT.SF20) (H : THyp TiB) (x : List UInt8) (hacc : AccOkT TiB (pubX x)) :
    PhiQC cacheT20 (pubX x).accIn.pt = (pubX x).accIn.y := by
  have hc := S.cache
  rw [cacheT20_eq] at hc ⊢
  rw [PhiQC_eq QB20 layT20 S.hlay hc _ (H.acc x)]
  have h := hacc
  unfold AccOkT PhiQ at h
  rw [Q_TiB, lay_TiB, List.map_map] at h
  simp only [Function.comp_def, FE.ofExt3_toExt3, List.map_id'] at h
  exact FE.toExt3_injective h

theorem NT20_phi : NT20.phi = PhiQC cacheT20 := rfl

/-- **`decideFT` from the HAR and the incoming accumulator.** -/
theorem decideFT_of (S : Lvm.CT.SF20) (H : THyp TiB) {vk cL : RecursionFast.Digest} {sig : ByteArray}
    {x : List UInt8} (hacc : AccOkT TiB (pubX x)) (hc : decideCoreT P20 NT20 vk cL sig = true)
    (ha : accOutOfT P20 NT20 vk cL sig = (pubX x).accIn) : decideFT P20 NT20 vk cL sig = true := by
  rw [decideFT_eq, hc, ha, NT20_phi, phi_accIn S H x hacc]
  simp

end Lvm.NS
end
end

section
section
set_option autoImplicit false
namespace Lvm.NS
open RecursionFast Lvm Lvm.T Lvm.ASM Lvm.Replay Lvm.Loop Lvm.Loop.Build Lvm.QLink Lvm.QSig Lvm.M3
open Lvm.QAsm Lvm.QTyped Lvm.Typed Lvm.TypedV Lvm.BitsTab Lvm.Bits Lvm.SigBits Lvm.Har LeanVM.Protocol
open Lvm.VEq (pubX)

/-- **Q_sig's `ChildOk` on a good node pair's memory.** -/
theorem childOkT (S : Lvm.CT.SF20) (H : THyp TiB) (hchk : nodeChkB cfg20 frz20 QB20 layT20 NT20 = true)
    {vk c : RecursionFast.Digest} {x : List UInt8} {qm : Column CMain.nu20} {qr : Column 19}
    (hok : okS vk c x = true) (hb : (hdrOf x).b = 1) (hG : GoodT TiB H x qm qr) (hSB : SBlk qm qr) :
    ChildOk (sigIn cfg20) (memT x qm qr).k := by
  have hin : inMapB cfg20 QB20 layT20 NT20 = true := by
    simp only [nodeChkB, Bool.and_eq_true] at hchk; exact hchk.1.1
  obtain ⟨hH, hA⟩ := holds_memT S.toStaticFactsT hG (readdT S H hchk hG hSB)
  have hinj := S.inj
  rw [QB20_qn] at hH hA hinj
  have P := parts_of_holds hH hA
  have mp := inMapT S.toStaticFactsT hin S.sig qm qr hSB hok hb
  have hks := sigKSin_of_goodK (goodK_of hok hG) mp.xs mp.ys mp.yc mp.yls mp.yns
  exact (qsig_sound_in (by rw [hln20]; omega) P.2.1 mp.flag hks (sigBitsT S H hG)
    fun a b ha hb h => FK.FKx_pow_inj (by omega) (by omega) h).2

theorem cfg20_pT : cfg20.p = P20 := rfl

/-- **Q_link's position cells hold `kOf (posL …)` of the child's stream** on a good pair's memory
(`posCells20`: Q_link's `qlink_pos` and `posVal_on`). -/
theorem posCellsT (S : Lvm.CT.SF20) (H : THyp TiB) (hchk : nodeChkB cfg20 frz20 QB20 layT20 NT20 = true)
    {vk c : RecursionFast.Digest} {x : List UInt8} {qm : Column CMain.nu20} {qr : Column 19}
    (hok : okS vk c x = true) (hb : (hdrOf x).b = 1) (hG : GoodT TiB H x qm qr) (hSB : SBlk qm qr) :
    ∀ k < (opens P20).length, ((opens P20).getD k default).L.height ≤ 64 →
      ∀ j < ((opens P20).getD k default).L.t,
      (memT x qm qr).k (nK cfg20 + posIdx P20 k j) =
        kOf (posL P20 (wsC qr) (((opens P20).getD k default).pe + j / 8)
          (j % 8 * ((opens P20).getD k default).L.height) ((opens P20).getD k default).L.height) := by
  intro k hk hH j hj
  have hin : inMapB cfg20 QB20 layT20 NT20 = true := by
    simp only [nodeChkB, Bool.and_eq_true] at hchk; exact hchk.1.1
  obtain ⟨hH', hA⟩ := holds_memT S.toStaticFactsT hG (readdT S H hchk hG hSB)
  rw [QB20_qn] at hH' hA
  have P := parts_of_holds hH' hA
  have mp := inMapT S.toStaticFactsT hin S.sig qm qr hSB hok hb
  have hk' : k < (opens cfg20.p).length := by rw [cfg20_pT]; exact hk
  have hH'' : ((opens cfg20.p).getD k default).L.height ≤ 64 := by rw [cfg20_pT]; exact hH
  have hj' : j < ((opens cfg20.p).getD k default).L.t := by rw [cfg20_pT]; exact hj
  have hv := posVal_onT (outsOn_memT S H hG) (by rw [cfg20_pT]; exact hS20) (by rw [cfg20_pT]; exact hQ20)
    mp.stream hk' hH'' hj'
  rw [cfg20_pT] at hv
  have hq := qlink_pos (pt := p0 (nK cfg20) 0) hQ20 P.1.1 hk hj
  exact hq.trans hv

end Lvm.NS
end
end

section
section
set_option autoImplicit false
namespace Lvm.CT
open RecursionFast Lvm Lvm.T Lvm.ASM Lvm.FS Lvm.Typed Lvm.QTyped
open Lvm.M3 (Tab inst AllSc LayOk KeysOk FixOk lay26)
open Lvm.VEq (pubX)
open scoped NNReal ENNReal

/-- The layout's word `1` lies in the `1` region (`TInst.Ok`'s second half), from the guard's `oneOkB`. -/
theorem one20 (h : Lvm.T.oneOkB layT20 = true) : Ti20.src? layT20.one = some .one :=
  src_one_of NT20 QB20 layT20 h

/-- **The region maps land in the commitments** at `lay26` (`NT20.okB`, `NT20`'s regions are the layout's). -/
theorem maps20 (S : SF20) : Ti20.MapsFit lay26 :=
  mapsFit_inst NT20 QB20 layT20 S.hlayOk (by
    have h := S.regs
    rwa [show Lvm.QAsm.cfg20.p = P20 from rfl, p20_facts.1, p20_facts.2.1] at h)

/-- `acc_in` has `phiVars = 43` coordinates on every statement (`accVars = 43`). -/
theorem acc20 : ∀ x, (pubX x).accIn.pt.length = phiVars := accLen

/-- **The mini-bus's table facts at `P20`** (`THyp`'s `hτ` … `μBus`, as roll 7's `MidHyp` on the bus tables). -/
structure MbHyp20 : Prop where
  hτ : ∀ t ∈ mbT20, t.τ ≤ lay26.μ
  sc : AllSc mbT20
  layOk : LayOk lay26 mbT20
  keys : KeysOk mbT20
  width : ∀ t ∈ mbT20, 0 < t.w
  fix : FixOk mbT20
  widths : (mbT20.map (·.w)).sum ≤ 2 ^ 38
  μBus : ∀ (h : ∀ t ∈ mbT20, t.τ ≤ lay26.μ), (inst lay26 mbT20 h).μBus = miniDepth

/-- **The mini-bus's table facts hold at `P20`**: the shape of `mbT` (`tabsOkB`, `FixOk`, a `C_main` column per
table) and the guard's `fitsMiniB` (heights, `LayOk`, depth `12`, `633` evaluations; M′ `S2GM`). -/
theorem mbHyp20 (S : SF20) : MbHyp20 := by
  have hm : TypedV.fitsMiniB P20 mbT20 = true := S.mini
  unfold TypedV.fitsMiniB at hm
  simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hm
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨-, hb⟩, -⟩, -⟩, -⟩, hf⟩, hg⟩, hh⟩, -⟩ := hm
  have ht : Lvm.M3.tabsOkB mbT20 = true := tabsOkB_mbT _ _ _ _
  have hsc : AllSc mbT20 := Lvm.M3.allSc_of_B ht
  have hsum : Lvm.M3.sumcheckTabs mbT20 = mbT20 := sc_all _ hsc
  refine ⟨hτ_of_hi (com_mbT _ _ _ _ fun _ ↦ rfl) hh, hsc, layOk_of_fit ⟨p20_facts.1, p20_facts.2.1⟩ hg,
    Lvm.M3.keys_of_B ht, Lvm.M3.width_pos_of_B ht, fixOk_mbT _ _ _ _, ?_, fun h ↦ ?_⟩
  · rw [hsum] at hf
    rw [← hf, p20_facts.2.2.2]
    norm_num
  · have e : (inst lay26 mbT20 h).μBus = P20.busDepth := by
      rw [LeanVM.Protocol.M3Instance.μBus, Lvm.VEq.pushLeaves_inst, hb, Lvm.VEq.log2Ceil_eq_clog,
        Lvm.M3.pushLeavesR, hsum]
    rw [e, p20_facts.2.2.1]

/-- **The typed phases' error terms at `P20`** (`L₀ = 37,696`, against `εS`, follower `LkSJ`): the mini-bus has
depth `12` (M′ `S2GM`; B1: 13) and no constraints (`B = 0`). -/
theorem errs20 (S : SF20) (h : ∀ t ∈ mbT20, t.τ ≤ lay26.μ) : TErrs 37696 (inst lay26 mbT20 h) εS LkSJ :=
  errs_at _ ((mbHyp20 S).μBus h)
    (Nat.le_zero.mp ((B_inst_le lay26 mbT20 h).trans (cons_mbT _ _ _ _).le))

/-- **`THyp` of the typed instance at `P20`** from the guard's facts. -/
theorem thyp20 (S : SF20) : THyp Ti20 where
  ok := ⟨S.hlay, one20 S.one⟩
  maps := maps20 S
  acc := acc20
  hτ := (mbHyp20 S).hτ
  sc := (mbHyp20 S).sc
  layOk := (mbHyp20 S).layOk
  keys := (mbHyp20 S).keys
  width := (mbHyp20 S).width
  fix := (mbHyp20 S).fix
  widths := (mbHyp20 S).widths
  μBus := (mbHyp20 S).μBus
  errs := errs20 S

/-- **The typed middle phases follow the schedule** (`midFollows_midS₂`'s, against the typed `phases P20`).
Owner **L-C**. -/
theorem midFollowsT20 (S : SF20) (H : THyp Ti20) : MidFollows (midT₂ Ti20) :=
  Lvm.VEq.midFollowsT20L S H

end Lvm.CT
end
end

section
section
set_option autoImplicit false
namespace Lvm.ASM
open RecursionFast LeanVM.Protocol

theorem nodeSoundM_of {VS : Lvm.T.SProg} {vk : RecursionFast.Digest} {G : GoodRel}
    {recOf : List UInt8 → Column CMain.nu20 → Column 19} {childS : Column 19 → RecursionFast.Signed}
    {childM : List UInt8 → List BF64 → RecursionFast.Signed}
    (hch : ∀ x q, childM x (Lvm.X.winOf q) = childS (recOf x q)) (h : NodeSound VS vk G childS) :
    NodeSoundM VS vk (GoodOfM recOf G) childM := fun c x q hok hG ↦ by
  rw [hch]
  exact h c x q (recOf x q) hok hG

end Lvm.ASM
end
end

section
set_option autoImplicit false
namespace Lvm.CT
open RecursionFast Lvm Lvm.T Lvm.ASM Lvm.FS Lvm.Typed Lvm.QTyped
open LeanVM.Protocol LeanVM.Protocol.Verifier
open scoped NNReal ENNReal

/-- **The left child read from the stream window.** -/
def childM20 (x : List UInt8) (w : List BF64) : Signed :=
  Lvm.NS.childW fun i ↦ if i < 2 ^ 19 then BF64.toBitVec (w.getD (sIdx x i) 0) else BF64.toBitVec 0

end Lvm.CT
end

section
set_option autoImplicit false
namespace Lvm.CT
open RecursionFast Lvm Lvm.T Lvm.ASM Lvm.FS Lvm.Typed Lvm.QTyped
open LeanVM.Protocol LeanVM.Protocol.Verifier
open scoped NNReal ENNReal

/-- **The window fact**: the window's child is the stream block's (both shapes; `LvmMPWin`, `bigOf`). -/
theorem win20 (x : List UInt8) (q : Column CMain.nu20) :
    childM20 x (Lvm.X.winOf q) = Lvm.NS.childS (recOf20 x q) := by
  unfold childM20 Lvm.NS.childS
  rw [winW20]

/-- **O5b at M′**: `VST P20 NT20` refines the compiled verifier of `PSWithM (midM reloc20 (midT₂ Ti20))`. -/
theorem refinesM20 (S : SF20) (H : THyp Ti20) :
    ∀ (vk : RecursionFast.Digest) (L : Log) (c : RecursionFast.Digest) (π : RecursionFast.Proof), isS π = true →
      (VSB20 vk c π).runLog L = some true →
      ((schemeS vk (PSWithM (midM reloc20 (midT₂ Ti20)))).V c π).runLog L = some true :=
  Lvm.VEq.refinesM20L S H

/-- **The stream block `EXM` reads is `childM20`'s** (both shapes): window word `2i` (small, `n ≤ 2^18`) or
`2^19 + i` (big) of a `2^20`-word window. -/
theorem childW_stream20 (π : RecursionFast.Proof) (x : List UInt8) (out : List BF64)
    (hn : (Lvm.VEq.pubX x).n = (Lvm.X.pw π 14).toNat) (hl : out.length = 2 ^ 20) :
    Lvm.NS.childW (Lvm.X.wStreamM π out) = childM20 x out := by
  unfold childM20
  congr 1
  funext i
  have hc : (Lvm.X.pw π 14 < RecursionFast.toWord (2 ^ 18 + 1)) ↔ Lvm.Shape.small x = true := by
    rw [BitVec.lt_def, RecursionFast.toNat_toWord (by norm_num), Lvm.Shape.small, hn, decide_eq_true_iff]
    (clear * - hn; omega)
  unfold Lvm.X.wStreamM sIdx
  by_cases hi : i < 2 ^ 19
  · rw [ite_eq_left hi]
    by_cases hs : Lvm.Shape.small x = true
    · rw [if_pos (hc.2 hs), if_pos hs,
        show 2 * (CMain.sOff20s + i) - Lvm.X.winLo * 2 ^ 17 = 2 * i by simp only [CMain.sOff20s, Lvm.X.winLo]; (clear * - hi; omega)]
    · rw [if_neg (fun h => hs (hc.1 h)), if_neg hs,
        show CMain.sOff20 + i - Lvm.X.winLo * 2 ^ 17 = 2 ^ 19 + i by simp only [CMain.sOff20, Lvm.X.winLo]; (clear * - hi; omega)]
  · rw [ite_eq_right hi]
    rw [List.getD_eq_default _ _ (by split_ifs <;> (clear * - hl hi; omega))]

/-- O4 for `EXM (accV VS)`: on witness-sending proofs it decodes. -/
theorem EXM_Wv (VS : SProg) (c : RecursionFast.Digest) (π : RecursionFast.Proof) (L : Log) (h : isS π = false) :
    Lvm.X.EXM (accV VS) c π L = RecursionFast.WitnessSending.decode π := by
  refine Lvm.X.EXM_W _ c π L fun h0 ↦ ?_
  have : π.data.getD 0 0 = 0x53 := by
    rw [Array.getD_eq_getD_getElem?, h0]; rfl
  simp [isS, this, sByte] at h

/-- The certificate of `subWith VS (EXM (accV VS)) extXM` from O1 and M′'s open obligations. -/
theorem certificateR_openVM (VS : SProg)
    (hq : ∀ H vk c π, ((VS vk c π).queries H).length ≤ qVlvm) (o : OpenSM VS (Lvm.X.EXM (accV VS))) :
    CertificateR ⟨(1 : ℝ≥0) / 340282366920938463463374607431768211456, (0 : ℝ≥0) / 1, 16384,
      fun t => 70368744177664 + 8192 * t⟩ (subWith VS (Lvm.X.EXM (accV VS)) Lvm.X.extXM) :=
  certificateR_claim VS _ Lvm.X.extXM
    ⟨fun H vk c π _ ↦ hq H vk c π, Lvm.X.computesXM _, Lvm.X.extXM_caps.2, EXM_Wv VS, sSound_of_openSM o⟩

/-- **`certificateR_openVM` at a format `f`** (the stage's `schemeSW f`). -/
theorem certificateR_openVMW (f : SFmt) (VS : SProg)
    (hq : ∀ H vk c π, ((VS vk c π).queries H).length ≤ qVlvm) (o : OpenSMW f VS (Lvm.X.EXM (accV VS))) :
    CertificateR ⟨(1 : ℝ≥0) / 340282366920938463463374607431768211456, (0 : ℝ≥0) / 1, 16384,
      fun t => 70368744177664 + 8192 * t⟩ (subWith VS (Lvm.X.EXM (accV VS)) Lvm.X.extXM) :=
  certificateR_claim VS _ Lvm.X.extXM
    ⟨fun H vk c π _ ↦ hq H vk c π, Lvm.X.computesXM _, Lvm.X.extXM_caps.2, EXM_Wv VS, sSound_of_openSMW f o⟩

end Lvm.CT
end

-- ===== from `LvmXSChild` =====

section
set_option autoImplicit false
namespace Lvm.CT
open RecursionFast Lvm Lvm.XS

/-- **S2GF's left child read from the stream window** (`childM20` at `stF20`). -/
def childF20 (x : List UInt8) (w : List BF64) : Signed :=
  childWS stF20 fun i ↦ if i < 2 ^ 19 then BF64.toBitVec (w.getD (sIdx x i) 0) else BF64.toBitVec 0

end Lvm.CT
end
