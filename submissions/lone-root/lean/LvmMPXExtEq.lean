-- New for lvm2 roll 11 (M′, R11-X, `ext_eqM20` step (iv)): O5c at M′, generic in the middle phases. Adapted from B1's
-- `LvmCertSExq2.ext_eq_gen` (ff8902c2): the replay of an accepted proof's history (now one root, `C_main`'s three
-- levels and two openings, `openMain_P20`), the decoders' inputs from the history (`decode_SMH`), `EXM_node`.
import LvmMPXExtRun
import LvmMPXNodeSem
import LvmCertSExq2Codec

/-!
# O5c at M′: `EXM = S.Ex K.ext` on good logs

**`ext_eqM_gen`**: for `mid` with `MidSpecM`, `MidShapeM`, `MidFollows`, `NodeSoundM` with a `child` that reads the
stream block of the decoded window as `wStreamM` does (`hchild`), on an accepted `'S'` proof over a log with
`μ K L < 1`, `EXM (accV VS) = S.Ex K.ext` or `EXM` returns a witness of the relation (an `S` node outside the
extractor's domain: the search).

In the domain, `EXM_node`'s inputs are the replayed history's: the chain answers at `foldPosK k` are the history's
fold samples (`simK2_chain` on the five segments of `openMain_P20`); `C_main`'s three words under π's caps
(`readRowG … (capM π i)`) are the history's committed words (`readRowG_eq_wordOf`, `capI_capM0`, `capI_capM1`, `capI_capM2`); `resEM π` is the
replayed residual; the decoders succeed there (`decode_SMH`, from `psInvM`'s post `ExtIM` and no luck at the end).
-/

set_option autoImplicit false

namespace Lvm.ASM

open RecursionFast Lvm.FS Lvm.T
open LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Protocol.Compile.VerifierProgram LeanVM.Protocol.Whir.Sound LeanVM.Protocol.EndToEnd
open LeanVM.Protocol.Whir
open scoped NNReal ENNReal

/-! ## π's values -/

/-- **π's residual coefficient** (bridge (a)): the scalar of the 24 bytes at `resOffM + 24 v`. -/
theorem resEM_eq (π : RecursionFast.Proof) (v : ℕ) (hv : Lvm.X.resOffM Lvm.X.pX + 24 * v + 24 ≤ π.size) :
    Lvm.X.resEM π v = eOfBytes ((π.data.toList.drop (Lvm.X.resOffM Lvm.X.pX + 24 * v)).take 24) := by
  have h8 : Lvm.X.resOffM Lvm.X.pX % 8 = 0 := Lvm.X.layoutXM.2.2.2.2.2.2.2.1
  have hs : π.data.toList.length = π.size := Array.length_toList
  rw [eOfBytes_eq, Lvm.X.resEM, Lvm.X.pw, Lvm.X.pw, Lvm.X.pw, wK_packBytes _ (by omega), wK_packBytes _ (by omega), wK_packBytes _ (by omega)]
  simp only [List.take_take, List.drop_take, List.drop_drop]
  have e0 : 8 * (Lvm.X.resOffM Lvm.X.pX / 8 + 3 * v) = Lvm.X.resOffM Lvm.X.pX + 24 * v := by omega
  have e1 : 8 * (Lvm.X.resOffM Lvm.X.pX / 8 + 3 * v + 1) = Lvm.X.resOffM Lvm.X.pX + 24 * v + 8 := by omega
  have e2 : 8 * (Lvm.X.resOffM Lvm.X.pX / 8 + 3 * v + 2) = Lvm.X.resOffM Lvm.X.pX + 24 * v + 16 := by omega
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
    omega]
  apply Vector.ext
  intro j hj
  simp only [dg, digestAt, Vector.getElem_ofFn]
  rw [get!_eq_getD, List.getD_eq_getElem _ _ (by simp only [List.length_drop, List.length_take]; omega),
    List.getD_eq_getElem _ _ (by omega)]
  simp only [List.getElem_drop, List.getElem_take]
  congr 1
  omega

/-- **O12 at M′**: the generic reading `readRowG` is WP-5's word under the cap, for a scheme whose word decoder is
`kOfBytes` and whose leaves of shape `(ht, z + occ)` carry `occ` words. -/
theorem readRowG_eq_wordOf (S : Scheme) (hK : S.decK = kOfBytes) {ht lv z occ : ℕ} (hO : S.occ ht (z + occ) = occ)
    (L : Log) (cap : List RecursionFast.Digest) (p : ℕ) :
    Lvm.X.readRowG ht lv z occ L cap p = S.wordOf L ⟨ht, z + occ, lv, cap⟩ p := by
  have hl : Lvm.X.xLeafBytesG ht lv L cap p = Scheme.leafBytes L ⟨ht, z + occ, lv, cap⟩ p := by
    simp only [Lvm.X.xLeafBytesG, Scheme.leafBytes, xDescend_eq]
    rfl
  rw [Lvm.X.readRowG, Scheme.wordOf, Scheme.padRow, hl, hK]
  show _ = padRowOf kOfBytes (z + occ) (S.occ ht (z + occ)) _
  rw [hO, padRowOf, Nat.min_eq_left (Nat.le_add_left _ _), Nat.add_sub_cancel]
  simp only [Lvm.X.xRowOf, rowOf, kOfBytes_eq, List.take_take, Nat.min_self]

/-! ## The history's commitments -/

theorem commits_nil_of_kinds : ∀ (l : List Ev), EvK.other ∉ l.map kindOf → commits l = []
  | [], _ => rfl
  | e :: l, h => by
    simp only [List.map_cons, List.mem_cons, not_or] at h
    cases e with
    | read _ => exact commits_nil_of_kinds l h.2
    | sample _ => exact commits_nil_of_kinds l h.2
    | commit _ _ _ => exact absurd rfl h.1
    | query _ => exact absurd rfl h.1
    | grind _ => exact absurd rfl h.1

theorem commits_nil_of_kindsEq {l : List Ev} {ks : List EvK} (h : l.map kindOf = ks) (ho : EvK.other ∉ ks) :
    commits l = [] := commits_nil_of_kinds l (h ▸ ho)

/-! ## The scheme's caps at M′ -/

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

/-! ## O5c at M′ -/

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
  have hfb : (Header.ofProof π).b = (Lvm.X.pw π 1).toNat := (pw_toNat π 1 (by omega)).symm
  have hfn : (Header.ofProof π).n = (Lvm.X.pw π 14).toNat := (pw_toNat π 14 (by omega)).symm
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
  obtain ⟨stA1, p1, hsA1, haA1, -, htA1⟩ := trun_simK2 S L B (itemK2 P20 shMain (midItems ++ mainHeadA1))
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
  obtain ⟨stA2, p2, hsA2, haA2, -, htA2⟩ := trun_simK2 S L B (itemK2 P20 shMain mainHeadA2) p1 141856 141808 stA1
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
  obtain ⟨stB1, p3, hsB1, haB1, -, htB1⟩ := trun_simK2 S L B (itemK2 P20 shMain mainHeadB1) (k0 w0) 229768 229768
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
  obtain ⟨stA3, p4, hsA3, haA3, -, htA3⟩ := trun_simK2 S L B (itemK2 P20 shMain mainHeadA3) p3 230008 229960 stB1
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
  obtain ⟨stB2, p5, hsB2, -, -, htB2⟩ := trun_simK2 S L B (itemK2 P20 shMain mainHeadB2) (k1 w1) 285944 285944
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
  obtain ⟨stR, -, -, hsimR, -, -⟩ := trun_simK S L B _ p5 286184 286136 stB2 _ _ lres t true
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
        rw [hA1n]; omega
      obtain ⟨a, ha, hea⟩ := cA1 (1242 + k) hlen
      refine ⟨a, by rw [Lvm.X.foldPosK_0 k0', Lvm.X.fp0_v, show 1244 + k = 1 + 1 + (1242 + k) by omega]; exact ha, ?_⟩
      have e1 : (r0.2 ++ r1.2 ++ r2.2).getD k 0 = r0.2.getD k 0 := by
        rw [List.append_assoc, List.getD_append _ _ _ _ (by rw [lf0l]; exact k0')]
      have e2 : (List.filterMap sampleOf lm ++ ρ :: r0.2).getD (1242 + k) 0 = r0.2.getD k 0 := by
        rw [List.getD_append_right _ _ _ _ (by omega), hlm, show 1242 + k - 1241 = k + 1 by omega]
        rfl
      rw [e1, show chalOf a = S.chal a from rfl, ← hea, ← List.getD_eq_getElem _ 0 hlen, hpreS, e2]
    by_cases k1' : k < 10
    · have hlen : k - 6 < ((post0 ++ lf1).filterMap sampleOf).length := by rw [hpreB1, lf1l]; omega
      obtain ⟨a, ha, hea⟩ := cB1 (k - 6) hlen
      refine ⟨a, by
        rw [show k = 6 + (k - 6) by omega, Lvm.X.foldPosK_1 (by omega), Lvm.X.fp1_v,
          show 1285 + (k - 6) = 1284 + 1 + (k - 6) by omega]; exact ha, ?_⟩
      have e1 : (r0.2 ++ r1.2 ++ r2.2).getD k 0 = r1.2.getD (k - 6) 0 := by
        rw [List.append_assoc, List.getD_append_right _ _ _ _ (by rw [lf0l]; omega), lf0l,
          List.getD_append _ _ _ _ (by rw [lf1l]; omega)]
      rw [e1, show chalOf a = S.chal a from rfl, ← hea, ← List.getD_eq_getElem _ 0 hlen, hpreB1]
    · have hlen : k - 10 < ((post1 ++ lf2).filterMap sampleOf).length := by rw [hpreB2, lf2l]; omega
      obtain ⟨a, ha, hea⟩ := cB2 (k - 10) hlen
      refine ⟨a, by
        rw [show k = 10 + (k - 10) by omega, Lvm.X.foldPosK_2 (by omega), Lvm.X.fp2_v,
          show 1315 + (k - 10) = 1314 + 1 + (k - 10) by omega]; exact ha, ?_⟩
      have e1 : (r0.2 ++ r1.2 ++ r2.2).getD k 0 = r2.2.getD (k - 10) 0 := by
        rw [List.getD_append_right _ _ _ _ (by rw [List.length_append, lf0l, lf1l]; omega), List.length_append, lf0l,
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
    _ _ _ (fun j hj => by rw [Lvm.X.alphaN, dif_pos hj]; exact hfv j (by omega))
    (fun j hj => by rw [Lvm.X.alphaN1, dif_pos hj]; exact hfv (6 + j) (by omega))
    (fun j hj => by rw [Lvm.X.alphaN1, dif_pos hj]; exact hfv (10 + j) (by omega))
    _ (fun v hv => by
      rw [resEM_eq π v (by rw [ores, hpi]; omega), ores]
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
