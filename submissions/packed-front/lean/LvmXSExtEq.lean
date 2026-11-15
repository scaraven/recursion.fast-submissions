-- New for lvm2 E2F (E2F-L, 2026-11-13): O5c generic in the stage (`LvmMPXExtEq.ext_eqM_gen` at a stage `st` and a
-- format `f` that agrees with it): the replay with read widths (`trun_simK2W`), the stage's offsets
-- (`replayOkB`), the stage's extractor (`EXS_node`).
import LvmXSExtRun
import LvmXSNodeSem
import LvmMPXExtEq

/-!
# O5c at a stage: `EXS st = S.Ex K.ext` on good logs

**`ext_eqS_gen`**: `ext_eqM_gen` with the scheme `schemeSW f` of a format agreeing with the stage (`FmtOK st f`:
the read widths are the stage's, its size, header and occupied words), the stage's replay facts (`ReplayOK st`), the
extractor's program and output facts (`ProgOK st`, `OutOK st`), and the middle phases following the stage's middle
items (`MidFollowsS`).
-/

set_option autoImplicit false

namespace Lvm.ASM

open RecursionFast Lvm.FS Lvm.T Lvm.XS
open LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Protocol.Compile.VerifierProgram LeanVM.Protocol.Whir.Sound LeanVM.Protocol.EndToEnd
open LeanVM.Protocol.Whir
open scoped NNReal ENNReal

/-- **A format agreeing with a stage**: its widths are the stage's reads', its size, header and occupied words. -/
def FmtOK (st : XStage) (f : SFmt) : Prop :=
  (∀ n, f.rw n = (readWidthsS st).getD n eBytes) ∧ f.pz = st.pz ∧ f.hb = st.hb ∧ f.occ 19 64 = st.occ0 ∧
    f.occ 16 48 = 48 ∧ f.occ 13 48 = 48

/-! ## The header -/

theorem hdrSW_inv {pz hb : ℕ} {π : RecursionFast.Proof} {x body : List UInt8} (h : hdrSW pz hb π = some (x, body)) :
    π.size = pz ∧ π.data.toList.take 8 = sPrefix ∧ x = (π.data.toList.drop 8).take (hb - 8) ∧
      body = π.data.toList.drop hb := by
  unfold hdrSW at h
  split_ifs at h with hc
  simp only [Option.some.injEq, Prod.mk.injEq] at h
  exact ⟨hc.1, hc.2, h.1.symm, h.2.symm⟩

/-- **The statement's header is π's** for a statement of at least `hdrLen` bytes (`hdrOf_eq`). -/
theorem hdrOf_eqW (π : RecursionFast.Proof) {n : ℕ} (hn : hdrLen ≤ n) (hs : headerBytes ≤ π.size) :
    hdrOf ((π.data.toList.drop 8).take n) = Header.ofProof π := by
  unfold hdrOf
  apply ofProof_congr
  intro k hk hk'
  have hl : π.data.toList.length = π.size := Array.length_toList
  have hL : hdrLen = 5976 := rfl
  have hH : headerBytes = 5984 := rfl
  rw [get!_eq_getD, get!_eq_getD]
  rw [List.getD_append_right _ _ _ _ (by simp; omega)]
  simp only [List.length_replicate]
  rw [List.getD_eq_getElem _ _ (by simp; omega), List.getD_eq_getElem _ _ (by omega)]
  simp only [List.getElem_take, List.getElem_drop]
  congr 1
  omega

/-! ## The scheme's caps at a format -/

theorem capBytes_mainW (f : SFmt) (vk : RecursionFast.Digest) (P : List UInt8 → VerifierProgram Bool) :
    (schemeSW f vk P).capBytes 19 64 = 8192 := by
  simp only [Scheme.capBytes, schemeSW, schemeS, capOfS]; norm_num

theorem capBytes_lvW (f : SFmt) (vk : RecursionFast.Digest) (P : List UInt8 → VerifierProgram Bool) {ht : ℕ}
    (h : ht ≠ 19) (w : ℕ) : (schemeSW f vk P).capBytes ht w = 4096 := by
  simp only [Scheme.capBytes, schemeSW, schemeS, capOfS, if_neg h]; norm_num

theorem capI_rootW (f : SFmt) (vk : RecursionFast.Digest) (P : List UInt8 → VerifierProgram Bool) (b : List UInt8) :
    (schemeSW f vk P).capI 19 64 b = ⟨19, 64, 8, digestsOf (b.take (32 * Lvm.X.capNM 0)) (Lvm.X.capNM 0)⟩ := by
  unfold Scheme.capI
  rw [capBytes_mainW]
  rfl

theorem capI_lvW (f : SFmt) (vk : RecursionFast.Digest) (P : List UInt8 → VerifierProgram Bool) {ht i : ℕ}
    (h : ht ≠ 19) (hi : i ≠ 0) (w : ℕ) (b : List UInt8) :
    (schemeSW f vk P).capI ht w b = ⟨ht, w, 7, digestsOf (b.take (32 * Lvm.X.capNM i)) (Lvm.X.capNM i)⟩ := by
  unfold Scheme.capI
  rw [capBytes_lvW f vk P h]
  simp only [schemeSW, schemeS, capOfS, if_neg h, Lvm.X.capNM, if_neg hi]
  try norm_num

/-- **`C_main`'s level-`i` cap from π at a stage** (`digestsOf_capM`). -/
theorem digestsOf_capS (st : XStage) (π : RecursionFast.Proof) {i : ℕ} (h8 : capOffS st i % 8 = 0)
    (hs : capOffS st i + 32 * Lvm.X.capNM i ≤ π.size) :
    digestsOf ((π.data.toList.drop (capOffS st i)).take (32 * Lvm.X.capNM i)) (Lvm.X.capNM i) = capS st π i := by
  have hB : π.data.toList.length = π.size := Array.length_toList
  unfold digestsOf capS
  refine List.map_congr_left fun e he => ?_
  have he' : e < Lvm.X.capNM i := List.mem_range.1 he
  rw [Lvm.X.hdD_eq_digestAt, show 8 * (capOffS st i / 8 + 4 * e) = capOffS st i + 32 * e by omega]
  apply Vector.ext
  intro j hj
  simp only [dg, digestAt, Vector.getElem_ofFn]
  rw [get!_eq_getD, List.getD_eq_getElem _ _ (by simp only [List.length_drop, List.length_take]; omega),
    List.getD_eq_getElem _ _ (by omega)]
  simp only [List.getElem_drop, List.getElem_take]
  congr 1
  omega

/-- **π's residual coefficient at a stage** (`resEM_eq`). -/
theorem resES_eq (st : XStage) (π : RecursionFast.Proof) (v : ℕ) (h8 : resOffS st % 8 = 0)
    (hv : resOffS st + 24 * v + 24 ≤ π.size) :
    resES st π v = eOfBytes ((π.data.toList.drop (resOffS st + 24 * v)).take 24) := by
  have hs : π.data.toList.length = π.size := Array.length_toList
  rw [eOfBytes_eq, resES, Lvm.X.pw, Lvm.X.pw, Lvm.X.pw, wK_packBytes _ (by omega), wK_packBytes _ (by omega),
    wK_packBytes _ (by omega)]
  simp only [List.take_take, List.drop_take, List.drop_drop]
  have e0 : 8 * (resOffS st / 8 + 3 * v) = resOffS st + 24 * v := by omega
  have e1 : 8 * (resOffS st / 8 + 3 * v + 1) = resOffS st + 24 * v + 8 := by omega
  have e2 : 8 * (resOffS st / 8 + 3 * v + 2) = resOffS st + 24 * v + 16 := by omega
  rw [e0, e1, e2]
  simp [Nat.add_comm]

/-! ## The chain at a stage -/

theorem fsQLS_eq (st : XStage) (π : RecursionFast.Proof) {p : ℕ} (hp : 0 < p) (s : RecursionFast.Digest) :
    fsQLS st π p s = toQ (s.toList ++ sl π.data.toList (msgLS st p).1 (msgLS st p).2) := by
  have hd : (fsQLS st π p s).data.toList =
      s.toList ++ (π.extract (msgLS st p).1 ((msgLS st p).1 + (msgLS st p).2)).data.toList := by
    rw [fsQLS, if_neg (by omega), ByteArray.data_append, Array.toList_append]
    rfl
  rw [ByteArray.data_extract, Array.toList_extract, List.extract_eq_take_drop,
    Nat.add_sub_cancel_left] at hd
  rcases hq : fsQLS st π p s with ⟨a⟩
  rw [hq] at hd
  simp only at hd
  unfold toQ sl
  rw [← hd, Array.toArray_toList]

/-- The chain's targets of positions `D + 1 + i` absorb the slices `fsMsgsS st` entry `D + i` (`chainT`). -/
theorem chainTS (st : XStage) (π : RecursionFast.Proof) {rw : ℕ → ℕ} {ks : List K2} {n off pend D N : ℕ}
    (hPre : fsPreK2W rw ks n off pend = ((fsMsgsS st).drop D).take N) :
    ∀ i (hi : i < (fsPreK2W rw ks n off pend).length) (s : RecursionFast.Digest),
      fsQLS st π (D + 1 + i) s =
        toQ (s.toList ++ sl π.data.toList ((fsPreK2W rw ks n off pend)[i]).1 ((fsPreK2W rw ks n off pend)[i]).2) := by
  intro i hi s
  rw [fsQLS_eq st π (by omega), msgLS, ← List.getD_eq_getElem _ (0, 0) hi, hPre]
  have hi' : i < N := by
    have := hi
    rw [hPre] at this
    exact lt_of_lt_of_le this (List.length_take_le _ _)
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_take, if_pos hi',
    List.getElem?_drop, show D + 1 + i - 1 = D + i by omega]

theorem foldPosS_add (st : XStage) (i j : ℕ) : foldPosS st i j = foldPosS st i 0 + j := by
  unfold foldPosS; omega

theorem foldPosKS_0 (st : XStage) {j : ℕ} (hj : j < 6) : foldPosKS st j = foldPosS st 0 0 + j := by
  rw [foldPosKS, if_pos hj, foldPosS_add]
theorem foldPosKS_1 (st : XStage) {j : ℕ} (hj : j < 4) : foldPosKS st (6 + j) = foldPosS st 1 0 + j := by
  rw [foldPosKS, if_neg (by omega), if_pos (by omega), foldPosS_add, Nat.add_sub_cancel_left]
theorem foldPosKS_2 (st : XStage) {j : ℕ} (hj : j < 4) : foldPosKS st (10 + j) = foldPosS st 2 0 + j := by
  rw [foldPosKS, if_neg (by omega), if_neg (by omega), foldPosS_add, Nat.add_sub_cancel_left]

/-! ## The replay's bookkeeping -/

theorem nReads_of_forall₂ : ∀ {pre : List Ev} {ks : List K2}, List.Forall₂ KM pre ks → nReads pre = readsK2 ks
  | [], [], _ => rfl
  | e :: pre, k :: ks, h => by
    obtain ⟨hk, hs⟩ := forall₂_cons_inv h
    have ih := nReads_of_forall₂ hs
    rw [show e :: pre = [e] ++ pre from rfl, nReads_append, ih]
    cases e <;> cases k <;> simp_all [KM, nReads, readsK2] <;> omega

theorem capsK2W_toK2 (S : Scheme) (B : List UInt8) (rw : ℕ → ℕ) : ∀ (ks : List EvK) (n off : ℕ) (caps : List CapI),
    capsK2W S B rw (ks.map toK2) n off caps = caps
  | [], _, _, _ => rfl
  | k :: ks, n, off, caps => by
    cases k <;> simp only [List.map_cons, toK2, capsK2W] <;> exact capsK2W_toK2 S B rw ks _ _ caps

theorem getD_drop' (ws : List ℕ) (n i : ℕ) : (ws.drop n).getD i eBytes = ws.getD (n + i) eBytes := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_drop]

/-- The widths from index `n` on are the list's tail from `n`. -/
theorem rw_drop {st : XStage} {f : SFmt} (hf : FmtOK st f) (n : ℕ) :
    ∀ i, f.rw (n + i) = ((readWidthsS st).drop n).getD i eBytes := fun i => by
  rw [hf.1, getD_drop']

/-- Reads of 24 bytes advance by 24 each. -/
theorem offK2W_reads24 (rw : ℕ → ℕ) : ∀ (i n : ℕ), (∀ j < i, rw (n + j) = 24) →
    ∀ off, offK2W rw (List.replicate i .read) n off = off + 24 * i
  | 0, _, _, off => rfl
  | i + 1, n, h, off => by
    have h0 := h 0 (by omega)
    rw [Nat.add_zero] at h0
    rw [List.replicate_succ, offK2W, offK2W_reads24 rw i (n + 1)
      (fun j hj => by rw [Nat.add_assoc, Nat.add_comm 1 j]; exact h _ (by omega)), h0]
    ring

/-! ## The root at a format -/

/-- **The replay of the root** at a format (`root_trunM`). -/
theorem root_trunW {f : SFmt} {vk : RecursionFast.Digest}
    {mid : List UInt8 → VerifierProgram (List LeanVM.Protocol.Verifier.StackClaim)}
    {x : List UInt8} {L : Log} {B : List UInt8} {st : RecursionFast.Digest} {h : List Ev}
    (e : (schemeSW f vk (PSWithM mid)).trun L (PSWithM mid x) st [] [] (B.drop f.hb) [] = some (true, h)) :
    ∃ k, PSWithM mid x = .commit 19 64 k ∧
      (schemeSW f vk (PSWithM mid)).trun L k st (sl B f.hb (f.hb + 8192 - f.hb))
        [(schemeSW f vk (PSWithM mid)).capI 19 64 (B.drop f.hb)] (B.drop (f.hb + 8192))
        [Ev.commit 19 64 ((schemeSW f vk (PSWithM mid)).wordOf L
          ((schemeSW f vk (PSWithM mid)).capI 19 64 (B.drop f.hb)))] = some (true, h) := by
  obtain ⟨k, hk⟩ : ∃ k, PSWithM mid x = .commit 19 64 k := ⟨_, rfl⟩
  rw [hk] at e
  simp only [Scheme.trun, capBytes_mainW] at e
  split_ifs at e
  · simp at e
  have hbuf : [] ++ List.take 8192 (List.drop f.hb B) = sl B f.hb (f.hb + 8192 - f.hb) := by
    simp only [List.nil_append, sl, Nat.add_sub_cancel_left]
  rw [hbuf, List.drop_drop] at e
  simp only [List.nil_append] at e
  exact ⟨k, hk, e⟩

/-! ## O5c at a stage -/

set_option maxRecDepth 20000 in
/-- **O5c at a stage**, generic in the middle phases (`ext_eqM_gen` at `schemeSW f`, `f` agreeing with `st`). -/
theorem ext_eqS_gen (st : XStage) (f : SFmt) (hf : FmtOK st f) (hr : ReplayOK st) (hp : ProgOK st) (ho : OutOK st)
    {mid : List UInt8 → VerifierProgram (List LeanVM.Protocol.Verifier.StackClaim)} {Good : GoodRelM}
    {Lm : ℝ≥0∞} (hmid : MidSpecM mid Good εS Lm) (hLm : Lm ≤ εS) (hsh : MidShapeM mid) {VS : SProg}
    {child : List UInt8 → List BF64 → Signed} (hnode : ∀ vk, NodeSoundM VS vk Good child)
    (hchild : ∀ (π : RecursionFast.Proof) (x : List UInt8) (out : List BF64),
      (Lvm.VEq.pubX x).n = (Lvm.X.pw π 14).toNat → out.length = 2 ^ 20 →
        childWS st (Lvm.X.wStreamM π out) = child x out)
    (hfol : MidFollowsS (midItemsS st) mid)
    (hA : ∀ vk c p, accV VS vk c p = true → Lvm.X.SFits p) (vk : RecursionFast.Digest) (L : Log)
    (c : RecursionFast.Digest) (π : RecursionFast.Proof)
    (hμ : Scheme.μ (kcertSMW f hmid hLm hsh (extJM hsh (hnode vk))) L < 1)
    (hacc : ((schemeSW f vk (PSWithM mid)).V c π).runLog L = some true) :
    (∃ w, EXS st (accV VS) c π L = some w ∧ Rel (accV VS vk) c w) ∨
      EXS st (accV VS) c π L =
        (schemeSW f vk (PSWithM mid)).Ex (kcertSMW f hmid hLm hsh (extJM hsh (hnode vk))).ext c π L := by
  obtain ⟨hrw, hpz, hhb, ho0, ho1, ho2⟩ := hf
  obtain ⟨x, h, hok, hreach, hafter, hB, hBp, hD, hEx⟩ :=
    Scheme.final_good (kcertSMW f hmid hLm hsh (extJM hsh (hnode vk))) L c π hμ hacc
  obtain ⟨body, e₀, e₁, hhdr, h0, h1, htr⟩ := Ex_inv _ hEx
  obtain ⟨hsz, hpre8, rfl, rfl⟩ := hdrSW_inv hhdr
  set S := schemeSW f vk (PSWithM mid) with hSdef
  set B := π.data.toList with hBdef
  have hsize : π.size = st.pz := hsz.trans hpz
  have hBlen : B.length = π.size := Array.length_toList
  have hb0 : π.data[0]? = some 0x53 := byte0_of_prefix hpre8
  have hH : headerBytes = 5984 := rfl
  have hL0 : hdrLen = 5976 := rfl
  have hhb8 : headerBytes ≤ π.size := by
    have := hr.hl; have := hr.s0; simp only [o1S] at *; omega
  have hhd : hdrOf ((B.drop 8).take (f.hb - 8)) = Header.ofProof π :=
    hdrOf_eqW π (by rw [hhb]; exact hr.hl) hhb8
  have hExK := hEx (kcertSMW f hmid hLm hsh (extJM hsh (hnode vk))).ext
  rw [hExK]
  have hext : (kcertSMW f hmid hLm hsh (extJM hsh (hnode vk))).ext = extSM mid child := rfl
  rw [hext]
  -- the header fields
  have hfb : (Header.ofProof π).b = (Lvm.X.pw π 1).toNat := (pw_toNat π 1 (by omega)).symm
  have hfn : (Header.ofProof π).n = (Lvm.X.pw π 14).toNat := (pw_toNat π 14 (by omega)).symm
  have hfs : (Header.ofProof π).s = Lvm.X.hdD π 10 := (Lvm.X.hdD_eq_digestAt π 10).symm
  have hfvk : (Header.ofProof π).vk = Lvm.X.hdD π 2 := (Lvm.X.hdD_eq_digestAt π 2).symm
  have hfcL : (Header.ofProof π).cL = Lvm.X.hdD π 6 := (Lvm.X.hdD_eq_digestAt π 6).symm
  have hfh : (Header.ofProof π).h = Lvm.X.hdD π 15 := (Lvm.X.hdD_eq_digestAt π 15).symm
  have hfsig : (Header.ofProof π).sig = Lvm.X.sigOfF fun j => Lvm.X.pw π (19 + j) := sig_eq π hhb8
  by_cases hb : Lvm.X.pw π 1 = 0
  · -- a leaf
    right
    rw [EXS_leaf st hp _ c π L hsize hb0 hb]
    unfold extSM witOf
    rw [hhd, if_pos (by rw [hfb, hb]; rfl), hfs, hfn]
    rfl
  have hbne : (Header.ofProof π).b ≠ 0 := by
    rw [hfb]; intro h0'; exact hb (BitVec.eq_of_toNat_eq (by rw [h0']; rfl))
  by_cases hdom : Lvm.X.InDomE c π L
  swap
  · -- a node outside the domain: the search
    left
    rw [EXS_node_out st _ c π L hdom hsize hb0 hb]
    have hvk : Lvm.X.hdD π 2 = vk := by
      have := hok
      simp only [schemeSW, schemeS, okS, Bool.and_eq_true, beq_iff_eq] at this
      rw [← hfvk, ← hhd]
      exact this.1.1.1.2
    rw [hvk]
    exact Lvm.X.search_spec_acc (fun c' p hp => hA vk c' p hp)
      ⟨_, (kcertSMW f hmid hLm hsh (extJM hsh (hnode vk))).extract hok hreach hafter hB hBp hD⟩
  -- a node in the domain
  right
  have hS' : ¬ Lvm.X.StateHit L := Lvm.X.notStateHit_of_notBad (Scheme.mu_lt_one hμ).1
  obtain ⟨hDI, hL⟩ := not_or.1 hB
  have hE : ExtIM mid Good ((B.drop 8).take (f.hb - 8)) h :=
    Spec.post _ (reach_nil_iff.2 hreach) hafter (not_not.1 hDI) rfl
  obtain ⟨h₁, cl, ⟨ρ', r', res'⟩, ⟨t, rfl⟩, hpre, hg⟩ := hE
  obtain ⟨q, -, hdec⟩ := decode_SMH (hsh.noCommit _) hpre hg (reachable_commit_ws hreach) hL
  have hd : mainDataM mid ((B.drop 8).take (f.hb - 8)) (h₁ ++ t) = some (r'.1.folds, res') := by
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
  change S.trun L (PSWithM mid ((B.drop 8).take (f.hb - 8))) e₁.2 [] [] (B.drop f.hb) [] = _ at htr'
  obtain ⟨k, hk, htrk⟩ := root_trunW htr'
  obtain ⟨rest0, hrest0⟩ := trun_prefix _ _ _ _ _ _ _ _ _ _ htrk
  simp only [List.cons_append, List.cons.injEq, Ev.commit.injEq, true_and] at hrest0
  obtain ⟨hW0, -⟩ := hrest0
  subst hW0
  rw [hhb] at htrk
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, kA1, kA2, kB1, kA3, kB2, -, -, -⟩ := openMain_P20
  have hws : ∀ n i, S.rw (n + i) = ((readWidthsS st).drop n).getD i eBytes := fun n i => by
    show f.rw (n + i) = _
    rw [hrw, getD_drop']
  have fm : lm.map kindOf = itemKindsS (midItemsS st) := hfol _ lm cl hmidr
  have hkM : kMS st = (itemKindsS (midItemsS st)).map toK2 := itemK2F_rs _ _ _ hr.rs
  -- segment A1: the middle phases, `ρ`, the intro, level 0's fold rounds
  have hkA1 : List.Forall₂ KM (lm ++ ([Ev.sample ρ] ++ (lq ++ lf0))) (kA1S st) := by
    rw [kA1S, hkM, kA1]
    refine forall₂_append (forall₂_of_kinds lm _ fm (other_not_mem_F _ hr.rs)) (forall₂_of_kinds _ _ ?_ (by decide))
    rw [List.map_append, List.map_append, fq, ff0]
    rfl
  have hcA1 : ∀ ht w nb, K2.commit ht w nb ∈ kA1S st → S.capBytes ht w = nb := fun ht w nb hm => by
    rw [kA1S, hkM, kA1, ← List.map_append] at hm
    exact absurd hm (not_commit_toK2 _)
  obtain ⟨stA1, p1, hsA1, haA1, hleA1, htA1⟩ :=
    trun_simK2W S L B (kA1S st) k 0 (o1S st) st.hb e₁.2 _ _ (lm ++ ([Ev.sample ρ] ++ (lq ++ lf0)))
    ((Ev.commit 16 (3 * 2 ^ 4) W₁ :: (pre0 ++ (Ev.query w0 :: (post0 ++ (lf1 ++ (Ev.commit 13 (3 * 2 ^ 4) W₂ ::
      (pre1 ++ (Ev.query w1 :: (post1 ++ (lf2 ++ lres)))))))))) ++ t) true rfl hcA1
    (by simp only [o1S]; omega) hkA1 (by
      rw [show o1S st = st.hb + 8192 from rfl, htrk]
      (simp only [List.append_assoc, List.cons_append, List.nil_append, List.singleton_append] <;> rfl))
  obtain ⟨eoA1, epA1, efA1⟩ := offK2W_eq_L S.rw (kA1S st) 0 (readWidthsS st) (o1S st) st.hb
    (fun i => by rw [hws 0 i, List.drop_zero])
  rw [eoA1, epA1] at htA1 hleA1
  rw [show offK2L (readWidthsS st) (kA1S st) (o1S st) = offA1 st from rfl,
    show pendK2L (readWidthsS st) (kA1S st) (o1S st) st.hb = pendA1 st from rfl] at htA1 hleA1
  have capsA1 : capsK2W S B S.rw (kA1S st) 0 (o1S st) [S.capI 19 64 (B.drop st.hb)] =
      [S.capI 19 64 (B.drop st.hb)] := by
    rw [kA1S, hkM, kA1, ← List.map_append, capsK2W_toK2]
  rw [capsA1] at htA1
  have hn1 : nReads ([Ev.commit 19 64 (S.wordOf L (S.capI 19 64 (B.drop st.hb)))] ++
      (lm ++ ([Ev.sample ρ] ++ (lq ++ lf0)))) = nr1 st := by
    rw [nReads_append, nReads_of_forall₂ hkA1, show nReads [Ev.commit 19 64 (S.wordOf L (S.capI 19 64
      (B.drop st.hb)))] = 0 from rfl, Nat.zero_add]; rfl
  -- segment A2
  have hkA2 : List.Forall₂ KM (Ev.commit 16 (3 * 2 ^ 4) W₁ :: pre0) (itemK2 P20 shMain mainHeadA2) := by
    rw [kA2]; exact .cons ⟨rfl, rfl⟩ (forall₂_of_kinds _ _ fp0 (by decide))
  obtain ⟨stA2, p2, hsA2, haA2, -, htA2⟩ :=
    trun_simK2W S L B (itemK2 P20 shMain mainHeadA2) p1 (nr1 st) (offA1 st) (pendA1 st) stA1
    _ _ (Ev.commit 16 (3 * 2 ^ 4) W₁ :: pre0)
    ((Ev.query w0 :: (post0 ++ (lf1 ++ (Ev.commit 13 (3 * 2 ^ 4) W₂ ::
      (pre1 ++ (Ev.query w1 :: (post1 ++ (lf2 ++ lres)))))))) ++ t) true hn1
    (fun ht w nb hm => by
      rw [kA2, List.mem_cons] at hm
      rcases hm with hm | hm
      · cases hm; exact capBytes_lvW f vk (PSWithM mid) (by norm_num) 48
      · exact absurd hm (not_commit_toK2 _))
    hleA1
    hkA2 (by
      rw [htA1]; (simp only [List.append_assoc, List.cons_append, List.nil_append, List.singleton_append] <;> rfl))
  obtain ⟨eoA2, epA2, efA2⟩ := offK2W_eq_L S.rw (itemK2 P20 shMain mainHeadA2) (nr1 st)
    ((readWidthsS st).drop (nr1 st)) (offA1 st) (pendA1 st) (hws (nr1 st))
  rw [eoA2, epA2] at htA2
  have capsA2 : capsK2W S B S.rw (itemK2 P20 shMain mainHeadA2) (nr1 st) (offA1 st) [S.capI 19 64 (B.drop st.hb)] =
      [S.capI 19 64 (B.drop st.hb), S.capI 16 48 (B.drop (capOffS st 1))] := by
    rw [kA2]; simp only [capsK2W]; rw [capsK2W_toK2, hr.oA1]; rfl
  rw [capsA2] at htA2
  rw [show offK2L ((readWidthsS st).drop (nr1 st)) (itemK2 P20 shMain mainHeadA2) (offA1 st) = offA2 st from rfl,
    show pendK2L ((readWidthsS st).drop (nr1 st)) (itemK2 P20 shMain mainHeadA2) (offA1 st) (pendA1 st) =
      pendA2 st from rfl, hr.oA2] at htA2
  have hW1 : W₁ = S.wordOf L (S.capI 16 48 (B.drop (capOffS st 1))) := by
    rw [kA2, simK2W, Option.map_eq_some_iff] at hsA2
    obtain ⟨r', -, e⟩ := hsA2
    simp only [Prod.mk.injEq, List.cons.injEq, Ev.commit.injEq] at e
    rw [hr.oA1] at e
    exact e.1.1.2.2.symm
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
  obtain ⟨rows0, hrw0, hq0a, -, htQ0⟩ := trun_query S L (i := 0) (ci := S.capI 19 64 (B.drop st.hb)) rfl
    (show S.trun L (.query 0 qs0 k0) stA2 (sl B (pendA2 st) (pendA2 st - pendA2 st)) _ (B.drop (pendA2 st)) _ =
      some (true, _ ++ Ev.query w0 :: ((post0 ++ (lf1 ++ (Ev.commit 13 (3 * 2 ^ 4) W₂ ::
        (pre1 ++ (Ev.query w1 :: (post1 ++ (lf2 ++ lres))))))) ++ t)) by
      rw [htA2]; (simp only [List.append_assoc, List.cons_append, List.nil_append, List.singleton_append] <;> rfl))
  cases hrw0
  have hpb0 : qs0.length * posBytes S (S.capI 19 64 (B.drop st.hb)) = 115 * (8 * st.occ0 + 32 * 11) := by
    have ho : S.occ 19 64 = st.occ0 := ho0
    rw [hq0l, capI_rootW, posBytes, Scheme.lb]
    simp only [ho, Nat.min_eq_left hr.oc]
  rw [hpb0, List.drop_drop, Nat.sub_self, sl_zero, ← sl_zero B (pendA2 st + 115 * (8 * st.occ0 + 32 * 11)),
    ← Nat.sub_self (pendA2 st + 115 * (8 * st.occ0 + 32 * 11)),
    show pendA2 st + 115 * (8 * st.occ0 + 32 * 11) = q0End st by rw [q0End, hr.oA2]] at htQ0
  have hn2 : nReads (([Ev.commit 19 64 (S.wordOf L (S.capI 19 64 (B.drop st.hb)))] ++
      (lm ++ ([Ev.sample ρ] ++ (lq ++ lf0)))) ++ (Ev.commit 16 (3 * 2 ^ 4) W₁ :: pre0) ++ [Ev.query w0]) = nr2 st := by
    rw [nReads_append, nReads_append, hn1, nReads_of_forall₂ hkA2]; rfl
  -- segment B1: level 0's opening's intro, level 1's fold rounds
  have hkB1 : List.Forall₂ KM (post0 ++ lf1) (itemK2 P20 shMain mainHeadB1) := by
    rw [kB1]
    refine forall₂_of_kinds _ _ ?_ (by decide)
    rw [List.map_append, fpo0, ff1]
    rfl
  obtain ⟨stB1, p3, hsB1, haB1, hleB1, htB1⟩ :=
    trun_simK2W S L B (itemK2 P20 shMain mainHeadB1) (k0 w0) (nr2 st) (q0End st) (q0End st)
    stA2 _ _ (post0 ++ lf1) ((Ev.commit 13 (3 * 2 ^ 4) W₂ :: (pre1 ++ (Ev.query w1 :: (post1 ++ (lf2 ++ lres))))) ++ t)
    true hn2
    (fun ht w nb hm => by rw [kB1] at hm; exact absurd hm (not_commit_toK2 _))
    le_rfl hkB1 (by
      rw [htQ0]; (simp only [List.append_assoc, List.cons_append, List.nil_append, List.singleton_append] <;> rfl))
  obtain ⟨eoB1, epB1, efB1⟩ := offK2W_eq_L S.rw (itemK2 P20 shMain mainHeadB1) (nr2 st)
    ((readWidthsS st).drop (nr2 st)) (q0End st) (q0End st) (hws (nr2 st))
  rw [eoB1, epB1] at htB1 hleB1
  rw [show offK2L ((readWidthsS st).drop (nr2 st)) (itemK2 P20 shMain mainHeadB1) (q0End st) = offB1 st from rfl,
    show pendK2L ((readWidthsS st).drop (nr2 st)) (itemK2 P20 shMain mainHeadB1) (q0End st) (q0End st) =
      pendB1 st from rfl] at htB1 hleB1
  have capsB1 : capsK2W S B S.rw (itemK2 P20 shMain mainHeadB1) (nr2 st) (q0End st)
      [S.capI 19 64 (B.drop st.hb), S.capI 16 48 (B.drop (capOffS st 1))] =
      [S.capI 19 64 (B.drop st.hb), S.capI 16 48 (B.drop (capOffS st 1))] := by
    rw [kB1, capsK2W_toK2]
  rw [capsB1] at htB1
  have hn3 : nReads ((([Ev.commit 19 64 (S.wordOf L (S.capI 19 64 (B.drop st.hb)))] ++
      (lm ++ ([Ev.sample ρ] ++ (lq ++ lf0)))) ++ (Ev.commit 16 (3 * 2 ^ 4) W₁ :: pre0) ++ [Ev.query w0]) ++
        (post0 ++ lf1)) = nr3 st := by
    rw [nReads_append, hn2, nReads_of_forall₂ hkB1]; rfl
  -- segment A3: level 2's cap, the OOD point, answer and intro, level 1's proof of work, positions and `λ`
  have hkA3 : List.Forall₂ KM (Ev.commit 13 (3 * 2 ^ 4) W₂ :: pre1) (itemK2 P20 shMain mainHeadA3) := by
    rw [kA3]; exact .cons ⟨rfl, rfl⟩ (forall₂_of_kinds _ _ fp1 (by decide))
  obtain ⟨stA3, p4, hsA3, haA3, -, htA3⟩ :=
    trun_simK2W S L B (itemK2 P20 shMain mainHeadA3) p3 (nr3 st) (offB1 st) (pendB1 st) stB1
    _ _ (Ev.commit 13 (3 * 2 ^ 4) W₂ :: pre1) ((Ev.query w1 :: (post1 ++ (lf2 ++ lres))) ++ t) true
    hn3
    (fun ht w nb hm => by
      rw [kA3, List.mem_cons] at hm
      rcases hm with hm | hm
      · cases hm; exact capBytes_lvW f vk (PSWithM mid) (by norm_num) 48
      · exact absurd hm (not_commit_toK2 _))
    hleB1 hkA3 (by
      rw [htB1]; (simp only [List.append_assoc, List.cons_append, List.nil_append, List.singleton_append] <;> rfl))
  obtain ⟨eoA3, epA3, efA3⟩ := offK2W_eq_L S.rw (itemK2 P20 shMain mainHeadA3) (nr3 st)
    ((readWidthsS st).drop (nr3 st)) (offB1 st) (pendB1 st) (hws (nr3 st))
  rw [eoA3, epA3] at htA3
  rw [show offK2L ((readWidthsS st).drop (nr3 st)) (itemK2 P20 shMain mainHeadA3) (offB1 st) = offA3 st from rfl,
    show pendK2L ((readWidthsS st).drop (nr3 st)) (itemK2 P20 shMain mainHeadA3) (offB1 st) (pendB1 st) =
      pendA3 st from rfl, hr.oA3] at htA3
  have hW2 : W₂ = S.wordOf L (S.capI 13 48 (B.drop (capOffS st 2))) := by
    rw [kA3, simK2W, Option.map_eq_some_iff] at hsA3
    obtain ⟨r', -, e⟩ := hsA3
    simp only [Prod.mk.injEq, List.cons.injEq, Ev.commit.injEq] at e
    rw [hr.oB1] at e
    exact e.1.1.2.2.symm
  have capsA3 : capsK2W S B S.rw (itemK2 P20 shMain mainHeadA3) (nr3 st) (offB1 st)
      [S.capI 19 64 (B.drop st.hb), S.capI 16 48 (B.drop (capOffS st 1))] =
      [S.capI 19 64 (B.drop st.hb), S.capI 16 48 (B.drop (capOffS st 1)), S.capI 13 48 (B.drop (capOffS st 2))] := by
    rw [kA3]; simp only [capsK2W]; rw [capsK2W_toK2, hr.oB1]; rfl
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
  obtain ⟨rows1, hrw1, -, -, htQ1⟩ := trun_query S L (i := 1) (ci := S.capI 16 48 (B.drop (capOffS st 1))) rfl
    (show S.trun L (.query 1 qs1 k1) stA3 (sl B (pendA3 st) (pendA3 st - pendA3 st)) _ (B.drop (pendA3 st)) _ =
      some (true, _ ++ Ev.query w1 :: ((post1 ++ (lf2 ++ lres)) ++ t)) by
      rw [htA3]; (simp only [List.append_assoc, List.cons_append, List.nil_append, List.singleton_append] <;> rfl))
  cases hrw1
  have hpb1 : qs1.length * posBytes S (S.capI 16 48 (B.drop (capOffS st 1))) = 77 * (8 * 48 + 32 * 9) := by
    have ho : S.occ 16 48 = 48 := ho1
    rw [hq1l, capI_lvW f vk (PSWithM mid) (by norm_num) (i := 1) (by norm_num), posBytes, Scheme.lb]
    simp only [ho, Nat.min_self]
  rw [hpb1, List.drop_drop, Nat.sub_self, sl_zero, ← sl_zero B (pendA3 st + 77 * (8 * 48 + 32 * 9)),
    ← Nat.sub_self (pendA3 st + 77 * (8 * 48 + 32 * 9)),
    show pendA3 st + 77 * (8 * 48 + 32 * 9) = q1End st by rw [q1End, hr.oA3]] at htQ1
  have hn4 : nReads (((([Ev.commit 19 64 (S.wordOf L (S.capI 19 64 (B.drop st.hb)))] ++
      (lm ++ ([Ev.sample ρ] ++ (lq ++ lf0)))) ++ (Ev.commit 16 (3 * 2 ^ 4) W₁ :: pre0) ++ [Ev.query w0]) ++
        (post0 ++ lf1)) ++ (Ev.commit 13 (3 * 2 ^ 4) W₂ :: pre1) ++ [Ev.query w1]) = nr4 st := by
    rw [nReads_append, nReads_append, hn3, nReads_of_forall₂ hkA3]; rfl
  -- segment B2: level 1's opening's intro, level 2's fold rounds
  have hkB2 : List.Forall₂ KM (post1 ++ lf2) (itemK2 P20 shMain mainHeadB2) := by
    rw [kB2]
    refine forall₂_of_kinds _ _ ?_ (by decide)
    rw [List.map_append, fpo1, ff2]
    rfl
  obtain ⟨stB2, p5, hsB2, -, hleB2, htB2⟩ :=
    trun_simK2W S L B (itemK2 P20 shMain mainHeadB2) (k1 w1) (nr4 st) (q1End st) (q1End st)
    stA3 _ _ (post1 ++ lf2) (lres ++ t) true
    hn4
    (fun ht w nb hm => by rw [kB2] at hm; exact absurd hm (not_commit_toK2 _))
    le_rfl hkB2 (by
      rw [htQ1]; (simp only [List.append_assoc, List.cons_append, List.nil_append, List.singleton_append] <;> rfl))
  obtain ⟨eoB2, epB2, efB2⟩ := offK2W_eq_L S.rw (itemK2 P20 shMain mainHeadB2) (nr4 st)
    ((readWidthsS st).drop (nr4 st)) (q1End st) (q1End st) (hws (nr4 st))
  rw [eoB2, epB2] at htB2 hleB2
  rw [show offK2L ((readWidthsS st).drop (nr4 st)) (itemK2 P20 shMain mainHeadB2) (q1End st) = offB2 st from rfl,
    show pendK2L ((readWidthsS st).drop (nr4 st)) (itemK2 P20 shMain mainHeadB2) (q1End st) (q1End st) =
      pendB2 st from rfl, hr.oB2] at htB2 hleB2
  have hn5 : nReads ((((([Ev.commit 19 64 (S.wordOf L (S.capI 19 64 (B.drop st.hb)))] ++
      (lm ++ ([Ev.sample ρ] ++ (lq ++ lf0)))) ++ (Ev.commit 16 (3 * 2 ^ 4) W₁ :: pre0) ++ [Ev.query w0]) ++
        (post0 ++ lf1)) ++ (Ev.commit 13 (3 * 2 ^ 4) W₂ :: pre1) ++ [Ev.query w1]) ++ (post1 ++ lf2)) = nr5 st := by
    rw [nReads_append, hn4, nReads_of_forall₂ hkB2]; rfl
  -- the residual
  have hk2 : lres.map kindOf = List.replicate (2 ^ 9) .read := by
    rw [hlres, List.map_map, ← hreslen]
    show List.map (fun _ => EvK.read) res = _
    exact List.map_const'
  have h24 : ∀ i < 2 ^ 9, S.rw (nr5 st + i) = 24 := fun i hi => by
    have e := congrArg (fun l : List ℕ => l.getD i eBytes) hr.r24
    simp only [List.getD_eq_getElem?_getD, List.getElem?_take, if_pos hi, List.getElem?_replicate] at e
    rw [hws (nr5 st) i, List.getD_eq_getElem?_getD, e]; rfl
  obtain ⟨stR, -, hsimR, -, -, -⟩ :=
    trun_simK2W S L B (List.replicate (2 ^ 9) .read) p5 (nr5 st) (resOffS st) (pendB2 st) stB2 _ _ lres t true
    hn5
    (fun ht w nb hm => by cases (List.mem_replicate.1 hm).2)
    hleB2
    (by
      rw [show List.replicate (2 ^ 9) K2.read = (List.replicate (2 ^ 9) EvK.read).map toK2 by
        rw [List.map_replicate]; rfl]
      exact forall₂_of_kinds _ _ hk2 (by simp))
    (by rw [htB2]; (simp only [List.append_assoc, List.cons_append, List.nil_append] <;> rfl))
  rw [simK2W_reads] at hsimR
  have hresv : res = (List.range (2 ^ 9)).map fun i => eOfBytes (sl B (resOffS st + 24 * i) 24) := by
    have e := (Prod.mk.inj (Option.some.inj hsimR)).1
    rw [hlres] at e
    apply List.map_injective_iff.2 (fun a b hab => Ev.read.inj hab)
    rw [← e, List.map_map]
    refine List.map_congr_left fun i hi => ?_
    have hi' : i < 2 ^ 9 := List.mem_range.1 hi
    simp only [Function.comp]
    rw [offK2W_reads24 S.rw i (nr5 st) (fun j hj => h24 j (by omega)), h24 i hi']
    rfl
  -- the chain
  have hfm1 : Lvm.X.fmAns (fsQLS st π) Lvm.X.zeroDL L 1 = some e₁.2 := by
    have hq0 : fsQLS st π 0 Lvm.X.zeroDL = toQ S.q0 := rfl
    have hseed : fsQLS st π 1 e₀.2 = S.seedQ e₀.2 ((B.drop 8).take (f.hb - 8)) := by
      rw [fsQLS_eq st π (by norm_num), hhb]
      rfl
    simp only [Lvm.X.fmAns, hq0, h0, Option.map_some, Option.bind_some, zero_add, hseed]
    exact congrArg (Option.map Prod.snd) h1
  have nos : ∀ (l : List Ev), l.map kindOf = [.read, .read] → l.filterMap sampleOf = [] := fun l hl => by
    have := samples_length l
    rw [hl] at this
    exact List.length_eq_zero_iff.1 (by simpa using this)
  have cA1 := simK2W_chain S L B (fsQLS st π) Lvm.X.zeroDL _ 0 (o1S st) st.hb e₁.2 1 _ stA1 hsA1 hfm1
    (chainTS st π (D := 1) (N := nMidS st + 7) (efA1.trans hr.fA1))
  simp only [smpOf_eq] at cA1
  obtain ⟨cA1, fA1⟩ := cA1
  have hlm : (lm.filterMap sampleOf).length = nMidS st := by rw [samples_length, fm]; rfl
  have hpreS : (lm ++ ([Ev.sample ρ] ++ (lq ++ lf0))).filterMap sampleOf = lm.filterMap sampleOf ++ (ρ :: r0.2) := by
    simp only [List.filterMap_append, nos lq fq, sf0, List.nil_append]
    rfl
  have hA1n : ((lm ++ ([Ev.sample ρ] ++ (lq ++ lf0))).filterMap sampleOf).length = nMidS st + 7 := by
    rw [hpreS, List.length_append, hlm, List.length_cons, lf0l]
  rw [hA1n, show 1 + (nMidS st + 7) = nMidS st + 8 by omega] at fA1
  have cA2 := simK2W_chain S L B (fsQLS st π) Lvm.X.zeroDL _ (nr1 st) (offA1 st) (pendA1 st) stA1 (nMidS st + 8) _
    stA2 hsA2 fA1 (chainTS st π (D := nMidS st + 8) (N := 35) (efA2.trans hr.fA2))
  simp only [smpOf_eq] at cA2
  obtain ⟨-, fA2⟩ := cA2
  have hA2n : ((Ev.commit 16 (3 * 2 ^ 4) W₁ :: pre0).filterMap sampleOf).length = 35 := by
    rw [show (Ev.commit 16 (3 * 2 ^ 4) W₁ :: pre0).filterMap sampleOf = pre0.filterMap sampleOf from rfl,
      samples_length, fp0]
    decide
  rw [hA2n, show nMidS st + 8 + 35 = nMidS st + 43 by omega] at fA2
  have cB1 := simK2W_chain S L B (fsQLS st π) Lvm.X.zeroDL _ (nr2 st) (q0End st) (q0End st) stA2 (nMidS st + 43) _
    stB1 hsB1 fA2 (chainTS st π (D := nMidS st + 43) (N := 4) (efB1.trans hr.fB1))
  simp only [smpOf_eq] at cB1
  obtain ⟨cB1, fB1⟩ := cB1
  have hpreB1 : (post0 ++ lf1).filterMap sampleOf = r1.2 := by
    rw [List.filterMap_append, nos post0 fpo0, List.nil_append, sf1]
  rw [hpreB1, lf1l, show nMidS st + 43 + 4 = nMidS st + 47 by omega] at fB1
  have cA3 := simK2W_chain S L B (fsQLS st π) Lvm.X.zeroDL _ (nr3 st) (offB1 st) (pendB1 st) stB1 (nMidS st + 47) _
    stA3 hsA3 fB1 (chainTS st π (D := nMidS st + 47) (N := 26) (efA3.trans hr.fA3))
  simp only [smpOf_eq] at cA3
  obtain ⟨-, fA3⟩ := cA3
  have hA3n : ((Ev.commit 13 (3 * 2 ^ 4) W₂ :: pre1).filterMap sampleOf).length = 26 := by
    rw [show (Ev.commit 13 (3 * 2 ^ 4) W₂ :: pre1).filterMap sampleOf = pre1.filterMap sampleOf from rfl,
      samples_length, fp1]
    decide
  rw [hA3n, show nMidS st + 47 + 26 = nMidS st + 73 by omega] at fA3
  have cB2 := simK2W_chain S L B (fsQLS st π) Lvm.X.zeroDL _ (nr4 st) (q1End st) (q1End st) stA3 (nMidS st + 73) _
    stB2 hsB2 fA3 (chainTS st π (D := nMidS st + 73) (N := 4) (efB2.trans hr.fB2))
  simp only [smpOf_eq] at cB2
  obtain ⟨cB2, -⟩ := cB2
  have hpreB2 : (post1 ++ lf2).filterMap sampleOf = r2.2 := by
    rw [List.filterMap_append, nos post1 fpo1, List.nil_append, sf2]
  -- the fold challenges are the chain's answers
  have hfolds : r2.1.folds = r0.2 ++ r1.2 ++ r2.2 := by rw [hr2, hr1, hr0]
  have hfold : ∀ k < 14, ∃ a, Lvm.X.fmAns (fsQLS st π) Lvm.X.zeroDL L (foldPosKS st k) = some a ∧
      r2.1.folds.getD k 0 = chalOf a := by
    intro k hk
    rw [hfolds]
    by_cases k0' : k < 6
    · have hlen : nMidS st + 1 + k < ((lm ++ ([Ev.sample ρ] ++ (lq ++ lf0))).filterMap sampleOf).length := by
        rw [hA1n]; omega
      obtain ⟨a, ha, hea⟩ := cA1 (nMidS st + 1 + k) hlen
      refine ⟨a, by
        rw [foldPosKS_0 st k0', hr.fp0, show nMidS st + 3 + k = 1 + 1 + (nMidS st + 1 + k) by omega]; exact ha, ?_⟩
      have e1 : (r0.2 ++ r1.2 ++ r2.2).getD k 0 = r0.2.getD k 0 := by
        rw [List.append_assoc, List.getD_append _ _ _ _ (by rw [lf0l]; exact k0')]
      have e2 : (List.filterMap sampleOf lm ++ ρ :: r0.2).getD (nMidS st + 1 + k) 0 = r0.2.getD k 0 := by
        rw [List.getD_append_right _ _ _ _ (by omega), hlm, show nMidS st + 1 + k - nMidS st = k + 1 by omega]
        rfl
      rw [e1, show chalOf a = S.chal a from rfl, ← hea, ← List.getD_eq_getElem _ 0 hlen, hpreS, e2]
    by_cases k1' : k < 10
    · have hlen : k - 6 < ((post0 ++ lf1).filterMap sampleOf).length := by rw [hpreB1, lf1l]; omega
      obtain ⟨a, ha, hea⟩ := cB1 (k - 6) hlen
      refine ⟨a, by
        rw [show k = 6 + (k - 6) by omega, foldPosKS_1 st (by omega), hr.fp1,
          show nMidS st + 44 + (k - 6) = nMidS st + 43 + 1 + (k - 6) by omega]; exact ha, ?_⟩
      have e1 : (r0.2 ++ r1.2 ++ r2.2).getD k 0 = r1.2.getD (k - 6) 0 := by
        rw [List.append_assoc, List.getD_append_right _ _ _ _ (by rw [lf0l]; omega), lf0l,
          List.getD_append _ _ _ _ (by rw [lf1l]; omega)]
      rw [e1, show chalOf a = S.chal a from rfl, ← hea, ← List.getD_eq_getElem _ 0 hlen, hpreB1]
    · have hlen : k - 10 < ((post1 ++ lf2).filterMap sampleOf).length := by rw [hpreB2, lf2l]; omega
      obtain ⟨a, ha, hea⟩ := cB2 (k - 10) hlen
      refine ⟨a, by
        rw [show k = 10 + (k - 10) by omega, foldPosKS_2 st (by omega), hr.fp2,
          show nMidS st + 74 + (k - 10) = nMidS st + 73 + 1 + (k - 10) by omega]; exact ha, ?_⟩
      have e1 : (r0.2 ++ r1.2 ++ r2.2).getD k 0 = r2.2.getD (k - 10) 0 := by
        rw [List.getD_append_right _ _ _ _ (by rw [List.length_append, lf0l, lf1l]; omega), List.length_append, lf0l,
          lf1l]
      rw [e1, show chalOf a = S.chal a from rfl, ← hea, ← List.getD_eq_getElem _ 0 hlen, hpreB2]
  let αk : ℕ → RecursionFast.Digest := fun k => if k < 14 then
    (Lvm.X.fmAns (fsQLS st π) Lvm.X.zeroDL L (foldPosKS st k)).getD Lvm.X.zeroDL else Lvm.X.zeroDL
  have hα : ∀ k < 14, Lvm.X.fmAns (fsQLS st π) Lvm.X.zeroDL L (foldPosKS st k) = some (αk k) := by
    intro k hk
    obtain ⟨a, ha, -⟩ := hfold k hk
    simp only [αk, if_pos hk, ha, Option.getD_some]
  have hfv : ∀ k < 14, r2.1.folds.getD k 0 = Lvm.X.alphaE (αk k) := by
    intro k hk
    obtain ⟨a, ha, hra⟩ := hfold k hk
    simp only [αk, if_pos hk, ha, Option.getD_some]
    rw [hra, chalOf_eq_alphaE]
  -- the history's commitments
  have hcm : commits ((Ev.commit 19 64 (S.wordOf L (S.capI 19 64 (B.drop f.hb))) :: (lm ++ (Ev.sample ρ ::
      (lq ++ (lf0 ++ (Ev.commit 16 (3 * 2 ^ 4) W₁ :: (pre0 ++ (Ev.query w0 :: (post0 ++ (lf1 ++
        (Ev.commit 13 (3 * 2 ^ 4) W₂ :: (pre1 ++ (Ev.query w1 :: (post1 ++ (lf2 ++ lres))))))))))))))) ++ t) =
      [(19, 64, S.wordOf L (S.capI 19 64 (B.drop f.hb))), (16, 3 * 2 ^ 4, W₁), (13, 3 * 2 ^ 4, W₂)] ++
        commits t := by
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
  have hw0 : wordOf ([(19, 64, S.wordOf L (S.capI 19 64 (B.drop f.hb))), (16, 3 * 2 ^ 4, W₁),
      (13, 3 * 2 ^ 4, W₂)] ++ commits t) 0 = S.wordOf L (S.capI 19 64 (B.drop f.hb)) := by
    rw [wordOf_append_of_lt _ _ (by simp)]; rfl
  have hw1 : wordOf ([(19, 64, S.wordOf L (S.capI 19 64 (B.drop f.hb))), (16, 3 * 2 ^ 4, W₁),
      (13, 3 * 2 ^ 4, W₂)] ++ commits t) 1 = W₁ := by
    rw [wordOf_append_of_lt _ _ (by simp)]; rfl
  have hw2 : wordOf ([(19, 64, S.wordOf L (S.capI 19 64 (B.drop f.hb))), (16, 3 * 2 ^ 4, W₁),
      (13, 3 * 2 ^ 4, W₂)] ++ commits t) 2 = W₂ := by
    rw [wordOf_append_of_lt _ _ (by simp)]; rfl
  rw [hcm, hw0, hw1, hw2] at hdec
  obtain ⟨m₂, hd₂, hrest⟩ := Option.bind_eq_some_iff.1 hdec
  obtain ⟨m₁, hd₁, hd₀⟩ := Option.bind_eq_some_iff.1 hrest
  -- π's caps are the history's
  have hoc : 64 - st.occ0 + st.occ0 = 64 := Nat.sub_add_cancel hr.oc
  have cp0 : S.capI 19 64 (B.drop f.hb) = ⟨19, (64 - st.occ0) + st.occ0, 8, capS st π 0⟩ := by
    rw [hoc, capI_rootW, hhb, ← show capOffS st 0 = st.hb from rfl, digestsOf_capS st π (i := 0) hr.a0 (by
      rw [show Lvm.X.capNM 0 = 2 ^ 8 from rfl, show capOffS st 0 = st.hb from rfl]
      have := hr.s0; simp only [o1S] at this; omega)]
  have cp1 : S.capI 16 48 (B.drop (capOffS st 1)) = ⟨16, 0 + 48, 7, capS st π 1⟩ := by
    rw [capI_lvW f vk (PSWithM mid) (by norm_num) (i := 1) (by norm_num), digestsOf_capS st π (i := 1) hr.a1 (by
      rw [show Lvm.X.capNM 1 = 2 ^ 7 from rfl]; have := hr.s1; omega)]
  have cp2 : S.capI 13 48 (B.drop (capOffS st 2)) = ⟨13, 0 + 48, 7, capS st π 2⟩ := by
    rw [capI_lvW f vk (PSWithM mid) (by norm_num) (i := 2) (by norm_num), digestsOf_capS st π (i := 2) hr.a2 (by
      rw [show Lvm.X.capNM 2 = 2 ^ 7 from rfl]; have := hr.s2; omega)]
  -- the extractor's run
  rw [EXS_node st hp ho (accV VS) c π L hdom hsize hb0 hb hS' αk hα _ _ _
    (fun q' _ t' _ => by
      rw [Lvm.X.wdOf, cp0, readRowG_eq_wordOf S rfl (by rw [hoc]; exact ho0)])
    (fun q' _ t' _ => by
      rw [Lvm.X.wdOf, hW1, cp1, readRowG_eq_wordOf S rfl (show S.occ 16 (0 + 48) = 48 from ho1)])
    (fun q' _ t' _ => by
      rw [Lvm.X.wdOf, hW2, cp2, readRowG_eq_wordOf S rfl (show S.occ 13 (0 + 48) = 48 from ho2)])
    _ _ _ (fun j hj => by rw [Lvm.X.alphaN, dif_pos hj]; exact hfv j (by omega))
    (fun j hj => by rw [Lvm.X.alphaN1, dif_pos hj]; exact hfv (6 + j) (by omega))
    (fun j hj => by rw [Lvm.X.alphaN1, dif_pos hj]; exact hfv (10 + j) (by omega))
    _ (fun v hv => by
      rw [resES_eq st π v hr.ar (by have := hr.sr; omega)]
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
  have hn : (Lvm.VEq.pubX ((B.drop 8).take (f.hb - 8))).n = (Lvm.X.pw π 14).toNat := by rw [pubX_n, hhd, hfn]
  have hlen : (Lvm.X.winOf q).length = 2 ^ 20 := by simp [Lvm.X.winOf, Lvm.X.winC]
  rw [XwitS, hchild π _ (Lvm.X.winOf q) hn hlen]
  unfold witOf
  rw [hhd, if_neg hbne, hfcL, hfh, hfn, hfs, hfsig]

end Lvm.ASM
