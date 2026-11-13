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
import LvmCertSExqCodec
import LvmCertSExq2Run

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
