-- New for lvm2 MP-B cap pruning (CAP-X5, 2026-11-17): O5c at S2GB generic in the stage (`ext_eqS_genS`'s port over
-- the expanded proof `fillB`); `ext_eqB_gen` instantiates it at `stB20`. Proof help, no frozen statement here.
import LvmS2GBExtRep
import LvmS2GBExtNode

/-!
# O5c at S2GB, generic in the stage

**`ext_eqB_genG`**: `ext_eqS_genS` with the scheme `schemeSWB f` reading `π' = fillB st.p π w` and the extractor
reading π. The replay runs on π' at the offsets of `ReplayOKB` (root cap 64 bytes, level caps 32, paths 18/16
levels); the chain's messages, the sent caps and the residual are π's bytes, which π' copies with their shifts
(`copyB`, `chainTB`). The extractor's values are hypotheses (`hleaf`, `hout`, `hnd`: `EXB_leaf`, `EXB_node_out`,
`EXB_node` at `stB20`), so the stage stays a variable here.
-/

set_option autoImplicit false

namespace Lvm.ASM

open RecursionFast Lvm.FS Lvm.T Lvm.XS Lvm.XB
open LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Protocol.Compile.VerifierProgram LeanVM.Protocol.Whir.Sound LeanVM.Protocol.EndToEnd
open LeanVM.Protocol.Whir
open scoped NNReal ENNReal

/-! ## The sent caps of `schemeSWB` -/

theorem capBytes_mainWB (f : SFmt) (vk : RecursionFast.Digest) (P : List UInt8 → VerifierProgram Bool) :
    (schemeSWB f vk P).capBytes 19 64 = 64 := by
  simp only [Scheme.capBytes, schemeSWB, capOfB]; norm_num

theorem capBytes_lvWB (f : SFmt) (vk : RecursionFast.Digest) (P : List UInt8 → VerifierProgram Bool) {ht : ℕ}
    (h : ht ≠ 19) (w : ℕ) : (schemeSWB f vk P).capBytes ht w = 32 := by
  simp only [Scheme.capBytes, schemeSWB, capOfB, if_neg h]; norm_num

theorem capI_rootWB (f : SFmt) (vk : RecursionFast.Digest) (P : List UInt8 → VerifierProgram Bool) (b : List UInt8) :
    (schemeSWB f vk P).capI 19 64 b = ⟨19, 64, 1, digestsOf (b.take 64) 2⟩ := by
  unfold Scheme.capI
  rw [capBytes_mainWB]
  simp only [schemeSWB, capOfB]
  rfl

theorem capI_lvWB (f : SFmt) (vk : RecursionFast.Digest) (P : List UInt8 → VerifierProgram Bool) {ht : ℕ}
    (h : ht ≠ 19) (w : ℕ) (b : List UInt8) :
    (schemeSWB f vk P).capI ht w b = ⟨ht, w, 0, digestsOf (b.take 32) 1⟩ := by
  unfold Scheme.capI
  rw [capBytes_lvWB f vk P h]
  simp only [schemeSWB, capOfB, if_neg h]
  rfl

/-- **The replay of the root** at S2GB (`root_trunWS` with the two-node root cap). -/
theorem root_trunWB {f : SFmt} {vk : RecursionFast.Digest}
    {mid : List UInt8 → VerifierProgram (List LeanVM.Protocol.Verifier.StackClaim)}
    {x : List UInt8} {L : Log} {B : List UInt8} {st : RecursionFast.Digest} {h : List Ev}
    (e : (schemeSWB f vk (PSWithM mid)).trun L (PSWithM mid x) st [] [] (B.drop f.hb) [] = some (true, h)) :
    ∃ k, PSWithM mid x = .commit 19 64 k ∧
      (schemeSWB f vk (PSWithM mid)).trun L k st (sl B f.hb (f.hb + 64 - f.hb))
        [(schemeSWB f vk (PSWithM mid)).capI 19 64 (B.drop f.hb)] (B.drop (f.hb + 64))
        [Ev.commit 19 64 ((schemeSWB f vk (PSWithM mid)).wordOf L
          ((schemeSWB f vk (PSWithM mid)).capI 19 64 (B.drop f.hb)))] = some (true, h) := by
  obtain ⟨k, hk⟩ : ∃ k, PSWithM mid x = .commit 19 64 k := ⟨_, rfl⟩
  rw [hk] at e
  simp only [Scheme.trun, capBytes_mainWB] at e
  split_ifs at e
  · simp at e
  have hbuf : [] ++ List.take 64 (List.drop f.hb B) = sl B f.hb (f.hb + 64 - f.hb) := by
    simp only [List.nil_append, sl, Nat.add_sub_cancel_left]
  rw [hbuf, List.drop_drop] at e
  simp only [List.nil_append] at e
  exact ⟨k, hk, e⟩

/-! ## The kinds with the sent caps -/

theorem map_fixK_toK2 (nb : ℕ) (l : List EvK) : (l.map toK2).map (fixK nb) = l.map toK2 := by
  rw [List.map_map]
  exact List.map_congr_left fun k _ => by cases k <;> rfl

theorem readsK2_map_fixK (nb : ℕ) : ∀ (l : List K2), readsK2 (l.map (fixK nb)) = readsK2 l
  | [] => rfl
  | .read :: l => by simp only [List.map_cons, fixK, readsK2, readsK2_map_fixK nb l]
  | .sample :: l => by simp only [List.map_cons, fixK, readsK2, readsK2_map_fixK nb l]
  | .commit _ _ _ :: l => by simp only [List.map_cons, fixK, readsK2, readsK2_map_fixK nb l]

/-! ## The extractor's values, generic -/

/-- `C_main`'s level-`i` sent cap from π at a stage (`capSB` generic). -/
def capSBG (st : XStage) (π : RecursionFast.Proof) (i : ℕ) : List RecursionFast.Digest :=
  (List.range (2 ^ capBB i)).map fun e => Lvm.X.hdD π (capOffS st i / 8 + 4 * e)

/-- The node witness at a stage under `capPrune` (`XwitB` generic). -/
def XwitBG (st : XStage) (π : RecursionFast.Proof) (w : ℕ → RecursionFast.Word) : RecursionFast.Wit :=
  .node (Lvm.X.hdD π 6) (leafStmt (Lvm.X.hdD π 15) (Lvm.X.pw π 14).toNat) (childWB st w)
    ⟨WitnessSending.encode (.leaf (Lvm.X.hdD π 10) (Lvm.X.pw π 14).toNat), [], sigRS st π w⟩

/-! ## O5c at S2GB -/

set_option maxRecDepth 20000 in
/-- **O5c over the expanded proof**, generic in the stage: `ext_eqS_genS` with `schemeSWB f` reading
`fillB st.p π w`, the extractor's value `E` given by its leaf, outside and node facts. -/
theorem ext_eqB_genG (st : XStage) (f : SFmt) (hf : FmtOKB st f) (hr : ReplayOKB st)
    {mid : List UInt8 → VerifierProgram (List LeanVM.Protocol.Verifier.StackClaim)} {Good : GoodRelM}
    {Lm τ : ℝ≥0∞} (hmid : MidSpecMτ mid Good εS Lm τ) (hτ : leadOpenM ≤ τ) (hLm : Lm ≤ εS) (hsh : MidShapeM mid)
    {VS : SProg}
    {child : List UInt8 → List BF64 → Signed} {slf : List UInt8 → List BF64 → Sig} (lo : List UInt8 → ℕ)
    (hlo : ∀ x, lo x + Lvm.X.winC ≤ 64)
    (hloP : ∀ (π : RecursionFast.Proof) (x : List UInt8), (Lvm.VEq.pubX x).n = (Lvm.X.pw π 14).toNat →
      lo x = loP st π)
    (hnode : ∀ vk, NodeSoundMLS lo VS vk Good child slf)
    (hchild : ∀ (π : RecursionFast.Proof) (x : List UInt8) (out : List BF64),
      (Lvm.VEq.pubX x).n = (Lvm.X.pw π 14).toNat → out.length = 2 ^ 20 →
        childWB st (wStreamS st π out) = child x out)
    (hsl : ∀ (π : RecursionFast.Proof) (x : List UInt8) (out : List BF64),
      (Lvm.VEq.pubX x).n = (Lvm.X.pw π 14).toNat → out.length = 2 ^ 20 →
        Lvm.CT.sigOfP (fun j => wStreamS st π out (17 * 2 ^ 14 + 1024 + j)) = slf x out)
    (hfol : MidFollowsS (midItemsS st) mid)
    (hA : ∀ vk c p, accV VS vk c p = true → Lvm.X.SFits p) (vk : RecursionFast.Digest) (L : Log)
    (c : RecursionFast.Digest) (π : RecursionFast.Proof) (w : List UInt8) (E : Option RecursionFast.Wit)
    (hπ : 269336 ≤ π.size)
    (hleaf : Lvm.X.pw π 1 = 0 → π.data[0]? = some 0x53 → E = some (Lvm.X.leafW π))
    (hout : ¬ Lvm.X.InDomE c π L → π.data[0]? = some 0x53 → Lvm.X.pw π 1 ≠ 0 →
      E = Lvm.X.search (accV VS) (Lvm.X.hdD π 2) c)
    (hnd : Lvm.X.InDomE c π L → π.data[0]? = some 0x53 → Lvm.X.pw π 1 ≠ 0 → ¬ Lvm.X.StateHit L →
      ∀ (αk : ℕ → RecursionFast.Digest),
      (∀ k < 14, Lvm.X.fmAns (fsQLS st π) Lvm.X.zeroDL L (foldPosKS st k) = some (αk k)) →
      ∀ (wd₀ wd₁ wd₂ : ℕ → ℕ → BF64),
      (∀ q < 2 ^ 19, ∀ t < 64,
        wd₀ q t = (Lvm.X.readRowG 19 1 (64 - st.occ0) st.occ0 L (capSBG st π 0) q).getD t 0) →
      (∀ q < 2 ^ 16, ∀ t < 48, wd₁ q t = (Lvm.X.readRowG 16 0 0 48 L (capSBG st π 1) q).getD t 0) →
      (∀ q < 2 ^ 13, ∀ t < 48, wd₂ q t = (Lvm.X.readRowG 13 0 0 48 L (capSBG st π 2) q).getD t 0) →
      ∀ (α₀ α₁ α₂ : ℕ → BF64.Ext3), (∀ j < 6, α₀ j = Lvm.X.alphaE (αk j)) →
      (∀ j < 4, α₁ j = Lvm.X.alphaE (αk (6 + j))) → (∀ j < 4, α₂ j = Lvm.X.alphaE (αk (10 + j))) →
      ∀ (f₂ : ℕ → BF64.Ext3), (∀ v < 2 ^ 9, f₂ v = resES st π v) →
      ∀ (m₂ : ℕ → BF64.Ext3), Lvm.X.decodeMP2 wd₂ α₂ f₂ = some m₂ →
      ∀ (m₁ : ℕ → BF64.Ext3), Lvm.X.decodeMP1 wd₁ α₁ m₂ = some m₁ →
      ∀ (out : List BF64), Lvm.X.decodeMP0L (loP st π) wd₀ α₀ m₁ = some out →
      E = some (XwitBG st π (wStreamS st π out)))
    (hμ : Scheme.μ (kcertSMWBτ f hmid hτ hLm hsh (extJMLS lo hlo hsh (hnode vk))) L < 1)
    (hacc : ((schemeSWB f vk (PSWithM mid)).V c (fillB st.p π w)).runLog L = some true)
    (hli : st.p.leafOut = true) :
    (∃ wt, E = some wt ∧ Rel (accV VS vk) c wt) ∨
      E = (schemeSWB f vk (PSWithM mid)).Ex (kcertSMWBτ f hmid hτ hLm hsh (extJMLS lo hlo hsh (hnode vk))).ext c
        (fillB st.p π w) L := by
  have hrl : hdrFixS ≤ st.hb := by have := hr.hl; rwa [hli, if_pos rfl] at this
  obtain ⟨hrw, hpz, hhb, ho0, ho1, ho2⟩ := hf
  obtain ⟨x, h, hok, hreach, hafter, hB, hBp, hD, hEx⟩ :=
    Scheme.final_good (kcertSMWBτ f hmid hτ hLm hsh (extJMLS lo hlo hsh (hnode vk))) L c (fillB st.p π w) hμ hacc
  obtain ⟨body, e₀, e₁, hhdr, h0, h1, htr⟩ := Ex_inv _ hEx
  obtain ⟨hsz, hpre8, rfl, rfl⟩ := hdrSW_inv hhdr
  set S := schemeSWB f vk (PSWithM mid) with hSdef
  set B := (fillB st.p π w).data.toList with hBdef
  set Bπ := π.data.toList with hBπdef
  have hBlen : Bπ.length = π.size := Array.length_toList
  have hhP : headerBytesP st.p = st.hb := hr.hh.trans hr.hb.symm
  have hhdr : B.take st.hb = Bπ.take st.hb := by
    rw [← hhP]; exact fillB_take_hdr st.p π w (by rw [hhP, hr.hb]; omega)
  have hb0 : π.data[0]? = some 0x53 := by
    refine byte0_of_prefix ?_
    rw [← hpre8, show (8 : ℕ) = min 8 st.hb by rw [hr.hb]; rfl, ← List.take_take, ← List.take_take, hhdr]
  have hx8 : (B.drop 8).take (f.hb - 8) = (Bπ.drop 8).take (f.hb - 8) := by
    rw [hhb, ← List.drop_take, ← List.drop_take, hhdr]
  have hH : headerBytes = 5984 := rfl
  have hL0 : hdrLen = 5976 := rfl
  have hF : hdrFixS = 152 := rfl
  have hhb8 : hdrFixS ≤ π.size := by
    have := hrl; rw [hr.hb] at this; omega
  obtain ⟨hxb, hxvk, hxcL, hxs, hxn, hxh⟩ := hdrOf_fieldsS π ((B.drop 8).take (f.hb - 8)) hx8
    (by rw [hhb]; have := hrl; clear * - this; omega) hhb8
  have hExK := hEx (kcertSMWBτ f hmid hτ hLm hsh (extJMLS lo hlo hsh (hnode vk))).ext
  rw [hExK]
  have hext : (kcertSMWBτ f hmid hτ hLm hsh (extJMLS lo hlo hsh (hnode vk))).ext = extSMLS lo mid child slf := rfl
  rw [hext]
  -- the header fields
  have hfb : (Header.ofProof π).b = (Lvm.X.pw π 1).toNat := (pw_toNat π 1 (by omega)).symm
  have hfn : (Header.ofProof π).n = (Lvm.X.pw π 14).toNat := (pw_toNat π 14 (by omega)).symm
  have hfs : (Header.ofProof π).s = Lvm.X.hdD π 10 := (Lvm.X.hdD_eq_digestAt π 10).symm
  have hfvk : (Header.ofProof π).vk = Lvm.X.hdD π 2 := (Lvm.X.hdD_eq_digestAt π 2).symm
  have hfcL : (Header.ofProof π).cL = Lvm.X.hdD π 6 := (Lvm.X.hdD_eq_digestAt π 6).symm
  have hfh : (Header.ofProof π).h = Lvm.X.hdD π 15 := (Lvm.X.hdD_eq_digestAt π 15).symm
  by_cases hb : Lvm.X.pw π 1 = 0
  · -- a leaf
    right
    rw [hleaf hb hb0]
    unfold extSMLS witOfL
    dsimp only
    rw [hxb, if_pos (by rw [hfb, hb]; rfl), hxs, hxn, hfs, hfn]
    rfl
  have hbne : (Header.ofProof π).b ≠ 0 := by
    rw [hfb]; intro h0'; exact hb (BitVec.eq_of_toNat_eq (by rw [h0']; rfl))
  by_cases hdom : Lvm.X.InDomE c π L
  swap
  · -- a node outside the domain: the search
    left
    rw [hout hdom hb0 hb]
    have hvk : Lvm.X.hdD π 2 = vk := by
      have := hok
      simp only [schemeSWB, schemeSWS, schemeSW, schemeS, okSL, Bool.and_eq_true, beq_iff_eq] at this
      rw [← hfvk, ← hxvk]
      exact this.1.1.1.2
    rw [hvk]
    exact Lvm.X.search_spec_acc (fun c' p hp => hA vk c' p hp)
      ⟨_, (kcertSMWBτ f hmid hτ hLm hsh (extJMLS lo hlo hsh (hnode vk))).extract hok hreach hafter hB hBp hD⟩
  -- a node in the domain
  right
  have hS' : ¬ Lvm.X.StateHit L := Lvm.X.notStateHit_of_notBad (Scheme.mu_lt_one hμ).1
  obtain ⟨hDI, hL⟩ := not_or.1 hB
  have hE : ExtIM mid Good ((B.drop 8).take (f.hb - 8)) h :=
    Spec.post _ (reach_nil_iff.2 hreach) hafter (not_not.1 hDI) rfl
  obtain ⟨h₁, cl, ⟨ρ', r', res'⟩, ⟨t, rfl⟩, hpre, hg⟩ := hE
  obtain ⟨q, -, hdec⟩ := decode_SMHL (lo ((B.drop 8).take (f.hb - 8))) (hlo _) (hsh.noCommit _) hpre hg
    (reachable_commit_ws hreach) hL
  have hn : (Lvm.VEq.pubX ((B.drop 8).take (f.hb - 8))).n = (Lvm.X.pw π 14).toNat := by rw [pubX_n, hxn, hfn]
  have hlP := hloP π _ hn
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
  obtain ⟨k, hk, htrk⟩ := root_trunWB htr'
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
    trun_simK2W S L B (kA1S st) k 0 (o1B st) st.hb e₁.2 _ _ (lm ++ ([Ev.sample ρ] ++ (lq ++ lf0)))
    ((Ev.commit 16 (3 * 2 ^ 4) W₁ :: (pre0 ++ (Ev.query w0 :: (post0 ++ (lf1 ++ (Ev.commit 13 (3 * 2 ^ 4) W₂ ::
      (pre1 ++ (Ev.query w1 :: (post1 ++ (lf2 ++ lres)))))))))) ++ t) true rfl hcA1
    (by unfold o1B; omega) hkA1 (by
      rw [show o1B st = st.hb + 64 from rfl, htrk]
      (simp only [List.append_assoc, List.cons_append, List.nil_append, List.singleton_append] <;> rfl))
  obtain ⟨eoA1, epA1, efA1⟩ := offK2W_eq_L S.rw (kA1S st) 0 (readWidthsS st) (o1B st) st.hb
    (fun i => by rw [hws 0 i, List.drop_zero])
  rw [eoA1, epA1] at htA1 hleA1
  rw [show offK2L (readWidthsS st) (kA1S st) (o1B st) = offA1B st from rfl,
    show pendK2L (readWidthsS st) (kA1S st) (o1B st) st.hb = pendA1B st from rfl] at htA1 hleA1
  have capsA1 : capsK2W S B S.rw (kA1S st) 0 (o1B st) [S.capI 19 64 (B.drop st.hb)] =
      [S.capI 19 64 (B.drop st.hb)] := by
    rw [kA1S, hkM, kA1, ← List.map_append, capsK2W_toK2]
  rw [capsA1] at htA1
  have hn1 : nReads ([Ev.commit 19 64 (S.wordOf L (S.capI 19 64 (B.drop st.hb)))] ++
      (lm ++ ([Ev.sample ρ] ++ (lq ++ lf0)))) = nr1 st := by
    rw [nReads_append, nReads_of_forall₂ hkA1, show nReads [Ev.commit 19 64 (S.wordOf L (S.capI 19 64
      (B.drop st.hb)))] = 0 from rfl, Nat.zero_add]; rfl
  -- segment A2
  have hkA2 : List.Forall₂ KM (Ev.commit 16 (3 * 2 ^ 4) W₁ :: pre0) (kA2B) := by
    rw [kA2B, kA2, List.map_cons, map_fixK_toK2]; exact .cons ⟨rfl, rfl⟩ (forall₂_of_kinds _ _ fp0 (by decide))
  obtain ⟨stA2, p2, hsA2, haA2, -, htA2⟩ :=
    trun_simK2W S L B (kA2B) p1 (nr1 st) (offA1B st) (pendA1B st) stA1
    _ _ (Ev.commit 16 (3 * 2 ^ 4) W₁ :: pre0)
    ((Ev.query w0 :: (post0 ++ (lf1 ++ (Ev.commit 13 (3 * 2 ^ 4) W₂ ::
      (pre1 ++ (Ev.query w1 :: (post1 ++ (lf2 ++ lres)))))))) ++ t) true hn1
    (fun ht w nb hm => by
      rw [kA2B, kA2, List.map_cons, fixK, map_fixK_toK2, List.mem_cons] at hm
      rcases hm with hm | hm
      · cases hm; exact capBytes_lvWB f vk (PSWithM mid) (by norm_num) 48
      · exact absurd hm (not_commit_toK2 _))
    hleA1
    hkA2 (by
      rw [htA1]; (simp only [List.append_assoc, List.cons_append, List.nil_append, List.singleton_append] <;> rfl))
  obtain ⟨eoA2, epA2, efA2⟩ := offK2W_eq_L S.rw (kA2B) (nr1 st)
    ((readWidthsS st).drop (nr1 st)) (offA1B st) (pendA1B st) (hws (nr1 st))
  rw [eoA2, epA2] at htA2
  have capsA2 : capsK2W S B S.rw (kA2B) (nr1 st) (offA1B st) [S.capI 19 64 (B.drop st.hb)] =
      [S.capI 19 64 (B.drop st.hb), S.capI 16 48 (B.drop (capOffS st 1))] := by
    rw [kA2B, kA2, List.map_cons, fixK, map_fixK_toK2]; simp only [capsK2W]; rw [capsK2W_toK2, hr.oA1]; rfl
  rw [capsA2] at htA2
  rw [show offK2L ((readWidthsS st).drop (nr1 st)) (kA2B) (offA1B st) = offA2B st from rfl,
    show pendK2L ((readWidthsS st).drop (nr1 st)) (kA2B) (offA1B st) (pendA1B st) =
      pendA2B st from rfl, hr.oA2] at htA2
  have hW1 : W₁ = S.wordOf L (S.capI 16 48 (B.drop (capOffS st 1))) := by
    rw [kA2B, kA2, List.map_cons, fixK, map_fixK_toK2, simK2W, Option.map_eq_some_iff] at hsA2
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
    (show S.trun L (.query 0 qs0 k0) stA2 (sl B (pendA2B st) (pendA2B st - pendA2B st)) _ (B.drop (pendA2B st)) _ =
      some (true, _ ++ Ev.query w0 :: ((post0 ++ (lf1 ++ (Ev.commit 13 (3 * 2 ^ 4) W₂ ::
        (pre1 ++ (Ev.query w1 :: (post1 ++ (lf2 ++ lres))))))) ++ t)) by
      rw [htA2]; (simp only [List.append_assoc, List.cons_append, List.nil_append, List.singleton_append] <;> rfl))
  cases hrw0
  have hpb0 : qs0.length * posBytes S (S.capI 19 64 (B.drop st.hb)) = 115 * (8 * st.occ0 + 32 * 18) := by
    have ho : S.occ 19 64 = st.occ0 := ho0
    rw [hq0l, capI_rootWB, posBytes, Scheme.lb]
    simp only [ho, Nat.min_eq_left hr.oc]
  rw [hpb0, List.drop_drop, Nat.sub_self, sl_zero, ← sl_zero B (pendA2B st + 115 * (8 * st.occ0 + 32 * 18)),
    ← Nat.sub_self (pendA2B st + 115 * (8 * st.occ0 + 32 * 18)),
    show pendA2B st + 115 * (8 * st.occ0 + 32 * 18) = q0EndB st by rw [q0EndB, hr.oA2]] at htQ0
  have hn2 : nReads (([Ev.commit 19 64 (S.wordOf L (S.capI 19 64 (B.drop st.hb)))] ++
      (lm ++ ([Ev.sample ρ] ++ (lq ++ lf0)))) ++ (Ev.commit 16 (3 * 2 ^ 4) W₁ :: pre0) ++ [Ev.query w0]) = nr2 st := by
    rw [nReads_append, nReads_append, hn1, nReads_of_forall₂ hkA2, kA2B, readsK2_map_fixK]; rfl
  -- segment B1: level 0's opening's intro, level 1's fold rounds
  have hkB1 : List.Forall₂ KM (post0 ++ lf1) (itemK2 P20 shMain mainHeadB1) := by
    rw [kB1]
    refine forall₂_of_kinds _ _ ?_ (by decide)
    rw [List.map_append, fpo0, ff1]
    rfl
  obtain ⟨stB1, p3, hsB1, haB1, hleB1, htB1⟩ :=
    trun_simK2W S L B (itemK2 P20 shMain mainHeadB1) (k0 w0) (nr2 st) (q0EndB st) (q0EndB st)
    stA2 _ _ (post0 ++ lf1) ((Ev.commit 13 (3 * 2 ^ 4) W₂ :: (pre1 ++ (Ev.query w1 :: (post1 ++ (lf2 ++ lres))))) ++ t)
    true hn2
    (fun ht w nb hm => by rw [kB1] at hm; exact absurd hm (not_commit_toK2 _))
    le_rfl hkB1 (by
      rw [htQ0]; (simp only [List.append_assoc, List.cons_append, List.nil_append, List.singleton_append] <;> rfl))
  obtain ⟨eoB1, epB1, efB1⟩ := offK2W_eq_L S.rw (itemK2 P20 shMain mainHeadB1) (nr2 st)
    ((readWidthsS st).drop (nr2 st)) (q0EndB st) (q0EndB st) (hws (nr2 st))
  rw [eoB1, epB1] at htB1 hleB1
  rw [show offK2L ((readWidthsS st).drop (nr2 st)) (itemK2 P20 shMain mainHeadB1) (q0EndB st) = offB1B st from rfl,
    show pendK2L ((readWidthsS st).drop (nr2 st)) (itemK2 P20 shMain mainHeadB1) (q0EndB st) (q0EndB st) =
      pendB1B st from rfl] at htB1 hleB1
  have capsB1 : capsK2W S B S.rw (itemK2 P20 shMain mainHeadB1) (nr2 st) (q0EndB st)
      [S.capI 19 64 (B.drop st.hb), S.capI 16 48 (B.drop (capOffS st 1))] =
      [S.capI 19 64 (B.drop st.hb), S.capI 16 48 (B.drop (capOffS st 1))] := by
    rw [kB1, capsK2W_toK2]
  rw [capsB1] at htB1
  have hn3 : nReads ((([Ev.commit 19 64 (S.wordOf L (S.capI 19 64 (B.drop st.hb)))] ++
      (lm ++ ([Ev.sample ρ] ++ (lq ++ lf0)))) ++ (Ev.commit 16 (3 * 2 ^ 4) W₁ :: pre0) ++ [Ev.query w0]) ++
        (post0 ++ lf1)) = nr3 st := by
    rw [nReads_append, hn2, nReads_of_forall₂ hkB1]; rfl
  -- segment A3: level 2's cap, the OOD point, answer and intro, level 1's proof of work, positions and `λ`
  have hkA3 : List.Forall₂ KM (Ev.commit 13 (3 * 2 ^ 4) W₂ :: pre1) (kA3B) := by
    rw [kA3B, kA3, List.map_cons, map_fixK_toK2]; exact .cons ⟨rfl, rfl⟩ (forall₂_of_kinds _ _ fp1 (by decide))
  obtain ⟨stA3, p4, hsA3, haA3, -, htA3⟩ :=
    trun_simK2W S L B (kA3B) p3 (nr3 st) (offB1B st) (pendB1B st) stB1
    _ _ (Ev.commit 13 (3 * 2 ^ 4) W₂ :: pre1) ((Ev.query w1 :: (post1 ++ (lf2 ++ lres))) ++ t) true
    hn3
    (fun ht w nb hm => by
      rw [kA3B, kA3, List.map_cons, fixK, map_fixK_toK2, List.mem_cons] at hm
      rcases hm with hm | hm
      · cases hm; exact capBytes_lvWB f vk (PSWithM mid) (by norm_num) 48
      · exact absurd hm (not_commit_toK2 _))
    hleB1 hkA3 (by
      rw [htB1]; (simp only [List.append_assoc, List.cons_append, List.nil_append, List.singleton_append] <;> rfl))
  obtain ⟨eoA3, epA3, efA3⟩ := offK2W_eq_L S.rw (kA3B) (nr3 st)
    ((readWidthsS st).drop (nr3 st)) (offB1B st) (pendB1B st) (hws (nr3 st))
  rw [eoA3, epA3] at htA3
  rw [show offK2L ((readWidthsS st).drop (nr3 st)) (kA3B) (offB1B st) = offA3B st from rfl,
    show pendK2L ((readWidthsS st).drop (nr3 st)) (kA3B) (offB1B st) (pendB1B st) =
      pendA3B st from rfl, hr.oA3] at htA3
  have hW2 : W₂ = S.wordOf L (S.capI 13 48 (B.drop (capOffS st 2 + 25760))) := by
    rw [kA3B, kA3, List.map_cons, fixK, map_fixK_toK2, simK2W, Option.map_eq_some_iff] at hsA3
    obtain ⟨r', -, e⟩ := hsA3
    simp only [Prod.mk.injEq, List.cons.injEq, Ev.commit.injEq] at e
    rw [hr.oB1] at e
    exact e.1.1.2.2.symm
  have capsA3 : capsK2W S B S.rw (kA3B) (nr3 st) (offB1B st)
      [S.capI 19 64 (B.drop st.hb), S.capI 16 48 (B.drop (capOffS st 1))] =
      [S.capI 19 64 (B.drop st.hb), S.capI 16 48 (B.drop (capOffS st 1)),
        S.capI 13 48 (B.drop (capOffS st 2 + 25760))] := by
    rw [kA3B, kA3, List.map_cons, fixK, map_fixK_toK2]; simp only [capsK2W]; rw [capsK2W_toK2, hr.oB1]; rfl
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
    (show S.trun L (.query 1 qs1 k1) stA3 (sl B (pendA3B st) (pendA3B st - pendA3B st)) _ (B.drop (pendA3B st)) _ =
      some (true, _ ++ Ev.query w1 :: ((post1 ++ (lf2 ++ lres)) ++ t)) by
      rw [htA3]; (simp only [List.append_assoc, List.cons_append, List.nil_append, List.singleton_append] <;> rfl))
  cases hrw1
  have hpb1 : qs1.length * posBytes S (S.capI 16 48 (B.drop (capOffS st 1))) = 77 * (8 * 48 + 32 * 16) := by
    have ho : S.occ 16 48 = 48 := ho1
    rw [hq1l, capI_lvWB f vk (PSWithM mid) (by norm_num), posBytes, Scheme.lb]
    simp only [ho, Nat.min_self]
  rw [hpb1, List.drop_drop, Nat.sub_self, sl_zero, ← sl_zero B (pendA3B st + 77 * (8 * 48 + 32 * 16)),
    ← Nat.sub_self (pendA3B st + 77 * (8 * 48 + 32 * 16)),
    show pendA3B st + 77 * (8 * 48 + 32 * 16) = q1EndB st by rw [q1EndB, hr.oA3]] at htQ1
  have hn4 : nReads (((([Ev.commit 19 64 (S.wordOf L (S.capI 19 64 (B.drop st.hb)))] ++
      (lm ++ ([Ev.sample ρ] ++ (lq ++ lf0)))) ++ (Ev.commit 16 (3 * 2 ^ 4) W₁ :: pre0) ++ [Ev.query w0]) ++
        (post0 ++ lf1)) ++ (Ev.commit 13 (3 * 2 ^ 4) W₂ :: pre1) ++ [Ev.query w1]) = nr4 st := by
    rw [nReads_append, nReads_append, hn3, nReads_of_forall₂ hkA3, kA3B, readsK2_map_fixK]; rfl
  -- segment B2: level 1's opening's intro, level 2's fold rounds
  have hkB2 : List.Forall₂ KM (post1 ++ lf2) (itemK2 P20 shMain mainHeadB2) := by
    rw [kB2]
    refine forall₂_of_kinds _ _ ?_ (by decide)
    rw [List.map_append, fpo1, ff2]
    rfl
  obtain ⟨stB2, p5, hsB2, -, hleB2, htB2⟩ :=
    trun_simK2W S L B (itemK2 P20 shMain mainHeadB2) (k1 w1) (nr4 st) (q1EndB st) (q1EndB st)
    stA3 _ _ (post1 ++ lf2) (lres ++ t) true
    hn4
    (fun ht w nb hm => by rw [kB2] at hm; exact absurd hm (not_commit_toK2 _))
    le_rfl hkB2 (by
      rw [htQ1]; (simp only [List.append_assoc, List.cons_append, List.nil_append, List.singleton_append] <;> rfl))
  obtain ⟨eoB2, epB2, efB2⟩ := offK2W_eq_L S.rw (itemK2 P20 shMain mainHeadB2) (nr4 st)
    ((readWidthsS st).drop (nr4 st)) (q1EndB st) (q1EndB st) (hws (nr4 st))
  rw [eoB2, epB2] at htB2 hleB2
  rw [show offK2L ((readWidthsS st).drop (nr4 st)) (itemK2 P20 shMain mainHeadB2) (q1EndB st) = offB2B st from rfl,
    show pendK2L ((readWidthsS st).drop (nr4 st)) (itemK2 P20 shMain mainHeadB2) (q1EndB st) (q1EndB st) =
      pendB2B st from rfl, hr.oB2] at htB2 hleB2
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
    trun_simK2W S L B (List.replicate (2 ^ 9) .read) p5 (nr5 st) (resOffS st + 43008) (pendB2B st) stB2 _ _ lres t true
    hn5
    (fun ht w nb hm => by cases (List.mem_replicate.1 hm).2)
    hleB2
    (by
      rw [show List.replicate (2 ^ 9) K2.read = (List.replicate (2 ^ 9) EvK.read).map toK2 by
        rw [List.map_replicate]; rfl]
      exact forall₂_of_kinds _ _ hk2 (by simp))
    (by rw [htB2]; (simp only [List.append_assoc, List.cons_append, List.nil_append] <;> rfl))
  rw [simK2W_reads] at hsimR
  have hresv : res = (List.range (2 ^ 9)).map fun i => eOfBytes (sl B (resOffS st + 43008 + 24 * i) 24) := by
    have e := (Prod.mk.inj (Option.some.inj hsimR)).1
    rw [hlres] at e
    apply List.map_injective_iff.2 (fun a b hab => Ev.read.inj hab)
    rw [← e, List.map_map]
    refine List.map_congr_left fun i hi => ?_
    have hi' : i < 2 ^ 9 := List.mem_range.1 hi
    simp only [Function.comp]
    rw [offK2W_reads24 S.rw i (nr5 st) (fun j hj => h24 j (by clear * - hi' hj; omega)), h24 i hi']
    rfl
  -- π' copies π's static stretches; the chain's messages lie in them
  obtain ⟨R0a, R0s, R1s, R1e, R1a, R1y, R2s, R2e, R2a, R2y, RT, RTE⟩ := regionsB st.p hr.osc
  have hwl : 56000 ≤ w.length := by
    have := fillB_w_long st.p π w (by
      rw [show (fillB st.p π w).size = f.pz from hsz, hpz, hr.hh]; simp only [statS, expS] at RT RTE; rw [RT, RTE])
    simp only [expS] at RTE; clear * - this RTE; omega
  have cpy0 : ∀ o m, st.hb ≤ o → o + m ≤ 88032 → sl B (o + 0) m = sl Bπ o m := fun o m h1 h2 =>
    copyB st.p π w 0 2698 (a := 0) (s := 0) (y := 87144) (by rw [List.drop_zero]; exact R0a) (by simp [statS])
      (by simp [expS]) (by rw [List.drop_zero]; exact R0s) (by rw [hr.hh]; omega) (by clear * - hwl; omega)
      (by rw [hr.hh]; rw [hr.hb] at h1; omega) (by rw [hr.hh]; omega)
  have cpy1 : ∀ o m, 170832 ≤ o → o + m ≤ 171200 → sl B (o + 25760) m = sl Bπ o m := fun o m h1 h2 =>
    copyB st.p π w 2699 30 (a := 169944) (s := 25760) (y := 368) R1a R1s R1e R1y (by rw [hr.hh]; omega) (by clear * - hwl; omega)
      (by rw [hr.hh]; omega) (by rw [hr.hh]; omega)
  have cpy2 : ∀ o m, 222944 ≤ o → o + m ≤ 235496 → sl B (o + 43008) m = sl Bπ o m := fun o m h1 h2 =>
    copyB st.p π w 2730 15 (a := 222056) (s := 43008) (y := 12552) R2a R2s R2e R2y (by rw [hr.hh]; omega) (by clear * - hwl; omega)
      (by rw [hr.hh]; omega) (by rw [hr.hh]; omega)
  have mA1 := K2L_mono (kA1S st) (readWidthsS st) (o1B st) st.hb (by simp only [o1B]; omega)
  have hcpA1 : ∀ m ∈ ((fsMsgsS st).drop 1).take (nMidS st + 7), sl B (m.1 + 0) m.2 = sl Bπ m.1 m.2 := fun m hm => by
    rw [← hr.fA1] at hm
    obtain ⟨h1, h2⟩ := mA1.2.2.2 m hm
    change _ ≤ offA1B st at h2
    exact cpy0 _ _ h1 (by have a1 := hr.oA1; have a2 := hr.c1; clear * - h2 a1 a2; omega)
  have mA2 := K2L_mono kA2B ((readWidthsS st).drop (nr1 st)) (offA1B st) (pendA1B st) mA1.2.1
  have hcpA2 : ∀ m ∈ ((fsMsgsS st).drop (nMidS st + 8)).take 35, sl B (m.1 + 0) m.2 = sl Bπ m.1 m.2 :=
    fun m hm => by
    rw [← hr.fA2] at hm
    obtain ⟨h1, h2⟩ := mA2.2.2.2 m hm
    have h0 := mA1.1
    change _ ≤ offA2B st at h2
    change st.hb ≤ pendA1B st at h0
    exact cpy0 _ _ (by clear * - h0 h1; omega) (by have a := hr.e0; clear * - h2 a; omega)
  have mB1 := K2L_mono (itemK2 P20 shMain mainHeadB1) ((readWidthsS st).drop (nr2 st)) (q0EndB st) (q0EndB st) le_rfl
  have hcpB1 : ∀ m ∈ ((fsMsgsS st).drop (nMidS st + 43)).take 4, sl B (m.1 + 25760) m.2 = sl Bπ m.1 m.2 :=
    fun m hm => by
    have hm' : (m.1 + 25760, m.2) ∈ shM 25760 (((fsMsgsS st).drop (nMidS st + 43)).take 4) :=
      List.mem_map.2 ⟨m, hm, rfl⟩
    rw [← hr.fB1] at hm'
    obtain ⟨h1, h2⟩ := mB1.2.2.2 _ hm'
    change _ ≤ offB1B st at h2
    dsimp only at h1 h2
    exact cpy1 _ _ (by have a := hr.e1; clear * - h1 a; omega)
      (by have a1 := hr.oB1; have a2 := hr.c2; clear * - h2 a1 a2; omega)
  have mA3 := K2L_mono kA3B ((readWidthsS st).drop (nr3 st)) (offB1B st) (pendB1B st) mB1.2.1
  have hcpA3 : ∀ m ∈ ((fsMsgsS st).drop (nMidS st + 47)).take 26, sl B (m.1 + 25760) m.2 = sl Bπ m.1 m.2 :=
    fun m hm => by
    have hm' : (m.1 + 25760, m.2) ∈ shM 25760 (((fsMsgsS st).drop (nMidS st + 47)).take 26) :=
      List.mem_map.2 ⟨m, hm, rfl⟩
    rw [← hr.fA3] at hm'
    obtain ⟨h1, h2⟩ := mA3.2.2.2 _ hm'
    have h0 := mB1.1
    change _ ≤ offA3B st at h2
    change q0EndB st ≤ pendB1B st at h0
    dsimp only at h1 h2
    exact cpy1 _ _ (by have a := hr.e1; clear * - h0 h1 a; omega) (by have a := hr.e2; clear * - h2 a; omega)
  have mB2 := K2L_mono (itemK2 P20 shMain mainHeadB2) ((readWidthsS st).drop (nr4 st)) (q1EndB st) (q1EndB st) le_rfl
  have hcpB2 : ∀ m ∈ ((fsMsgsS st).drop (nMidS st + 73)).take 4, sl B (m.1 + 43008) m.2 = sl Bπ m.1 m.2 :=
    fun m hm => by
    have hm' : (m.1 + 43008, m.2) ∈ shM 43008 (((fsMsgsS st).drop (nMidS st + 73)).take 4) :=
      List.mem_map.2 ⟨m, hm, rfl⟩
    rw [← hr.fB2] at hm'
    obtain ⟨h1, h2⟩ := mB2.2.2.2 _ hm'
    change _ ≤ offB2B st at h2
    dsimp only at h1 h2
    exact cpy2 _ _ (by have a := hr.e3; clear * - h1 a; omega)
      (by have a1 := hr.oB2; have a2 := hr.sr; clear * - h2 a1 a2; omega)
  -- the chain
  have hfm1 : Lvm.X.fmAns (fsQLS st π) Lvm.X.zeroDL L 1 = some e₁.2 := by
    have hq0 : fsQLS st π 0 Lvm.X.zeroDL = toQ S.q0 := rfl
    have hseed : fsQLS st π 1 e₀.2 = S.seedQ e₀.2 ((B.drop 8).take (f.hb - 8)) := by
      rw [fsQLS_eq st π (by norm_num), hx8, hhb]
      rfl
    simp only [Lvm.X.fmAns, hq0, h0, Option.map_some, Option.bind_some, zero_add, hseed]
    exact congrArg (Option.map Prod.snd) h1
  have nos : ∀ (l : List Ev), l.map kindOf = [.read, .read] → l.filterMap sampleOf = [] := fun l hl => by
    have := samples_length l
    rw [hl] at this
    exact List.length_eq_zero_iff.1 (by simpa using this)
  have cA1 := simK2W_chain S L B (fsQLS st π) Lvm.X.zeroDL _ 0 (o1B st) st.hb e₁.2 1 _ stA1 hsA1 hfm1
    (chainTB st π B (D := 1) (N := nMidS st + 7) (s := 0) ((efA1.trans hr.fA1).trans (shM_zero _).symm) hcpA1)
  simp only [smpOf_eq] at cA1
  obtain ⟨cA1, fA1⟩ := cA1
  have hlm : (lm.filterMap sampleOf).length = nMidS st := by rw [samples_length, fm]; rfl
  have hpreS : (lm ++ ([Ev.sample ρ] ++ (lq ++ lf0))).filterMap sampleOf = lm.filterMap sampleOf ++ (ρ :: r0.2) := by
    simp only [List.filterMap_append, nos lq fq, sf0, List.nil_append]
    rfl
  have hA1n : ((lm ++ ([Ev.sample ρ] ++ (lq ++ lf0))).filterMap sampleOf).length = nMidS st + 7 := by
    rw [hpreS, List.length_append, hlm, List.length_cons, lf0l]
  rw [hA1n, show 1 + (nMidS st + 7) = nMidS st + 8 by clear * -; omega] at fA1
  have cA2 := simK2W_chain S L B (fsQLS st π) Lvm.X.zeroDL _ (nr1 st) (offA1B st) (pendA1B st) stA1 (nMidS st + 8) _
    stA2 hsA2 fA1 (chainTB st π B (D := nMidS st + 8) (N := 35) (s := 0) ((efA2.trans hr.fA2).trans (shM_zero _).symm) hcpA2)
  simp only [smpOf_eq] at cA2
  obtain ⟨-, fA2⟩ := cA2
  have hA2n : ((Ev.commit 16 (3 * 2 ^ 4) W₁ :: pre0).filterMap sampleOf).length = 35 := by
    rw [show (Ev.commit 16 (3 * 2 ^ 4) W₁ :: pre0).filterMap sampleOf = pre0.filterMap sampleOf from rfl,
      samples_length, fp0]
    decide
  rw [hA2n, show nMidS st + 8 + 35 = nMidS st + 43 by clear * -; omega] at fA2
  have cB1 := simK2W_chain S L B (fsQLS st π) Lvm.X.zeroDL _ (nr2 st) (q0EndB st) (q0EndB st) stA2 (nMidS st + 43) _
    stB1 hsB1 fA2 (chainTB st π B (D := nMidS st + 43) (N := 4) (s := 25760) (efB1.trans hr.fB1) hcpB1)
  simp only [smpOf_eq] at cB1
  obtain ⟨cB1, fB1⟩ := cB1
  have hpreB1 : (post0 ++ lf1).filterMap sampleOf = r1.2 := by
    rw [List.filterMap_append, nos post0 fpo0, List.nil_append, sf1]
  rw [hpreB1, lf1l, show nMidS st + 43 + 4 = nMidS st + 47 by clear * -; omega] at fB1
  have cA3 := simK2W_chain S L B (fsQLS st π) Lvm.X.zeroDL _ (nr3 st) (offB1B st) (pendB1B st) stB1 (nMidS st + 47) _
    stA3 hsA3 fB1 (chainTB st π B (D := nMidS st + 47) (N := 26) (s := 25760) (efA3.trans hr.fA3) hcpA3)
  simp only [smpOf_eq] at cA3
  obtain ⟨-, fA3⟩ := cA3
  have hA3n : ((Ev.commit 13 (3 * 2 ^ 4) W₂ :: pre1).filterMap sampleOf).length = 26 := by
    rw [show (Ev.commit 13 (3 * 2 ^ 4) W₂ :: pre1).filterMap sampleOf = pre1.filterMap sampleOf from rfl,
      samples_length, fp1]
    decide
  rw [hA3n, show nMidS st + 47 + 26 = nMidS st + 73 by clear * -; omega] at fA3
  have cB2 := simK2W_chain S L B (fsQLS st π) Lvm.X.zeroDL _ (nr4 st) (q1EndB st) (q1EndB st) stA3 (nMidS st + 73) _
    stB2 hsB2 fA3 (chainTB st π B (D := nMidS st + 73) (N := 4) (s := 43008) (efB2.trans hr.fB2) hcpB2)
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
        rw [hA1n]; clear * - k0'; omega
      obtain ⟨a, ha, hea⟩ := cA1 (nMidS st + 1 + k) hlen
      refine ⟨a, by
        rw [foldPosKS_0 st k0', hr.fp0, show nMidS st + 3 + k = 1 + 1 + (nMidS st + 1 + k) by clear * -; omega]; exact ha, ?_⟩
      have e1 : (r0.2 ++ r1.2 ++ r2.2).getD k 0 = r0.2.getD k 0 := by
        rw [List.append_assoc, List.getD_append _ _ _ _ (by rw [lf0l]; exact k0')]
      have e2 : (List.filterMap sampleOf lm ++ ρ :: r0.2).getD (nMidS st + 1 + k) 0 = r0.2.getD k 0 := by
        rw [List.getD_append_right _ _ _ _ (by clear * - hlm; omega), hlm, show nMidS st + 1 + k - nMidS st = k + 1 by clear * -; omega]
        rfl
      rw [e1, show chalOf a = S.chal a from rfl, ← hea, ← List.getD_eq_getElem _ 0 hlen, hpreS, e2]
    by_cases k1' : k < 10
    · have hlen : k - 6 < ((post0 ++ lf1).filterMap sampleOf).length := by rw [hpreB1, lf1l]; clear * - k0' k1'; omega
      obtain ⟨a, ha, hea⟩ := cB1 (k - 6) hlen
      refine ⟨a, by
        rw [show k = 6 + (k - 6) by clear * - k0'; omega, foldPosKS_1 st (by clear * - k0' k1'; omega), hr.fp1,
          show nMidS st + 44 + (k - 6) = nMidS st + 43 + 1 + (k - 6) by clear * -; omega]; exact ha, ?_⟩
      have e1 : (r0.2 ++ r1.2 ++ r2.2).getD k 0 = r1.2.getD (k - 6) 0 := by
        rw [List.append_assoc, List.getD_append_right _ _ _ _ (by rw [lf0l]; clear * - k0'; omega), lf0l,
          List.getD_append _ _ _ _ (by rw [lf1l]; clear * - k1'; omega)]
      rw [e1, show chalOf a = S.chal a from rfl, ← hea, ← List.getD_eq_getElem _ 0 hlen, hpreB1]
    · have hlen : k - 10 < ((post1 ++ lf2).filterMap sampleOf).length := by rw [hpreB2, lf2l]; clear * - hk k1'; omega
      obtain ⟨a, ha, hea⟩ := cB2 (k - 10) hlen
      refine ⟨a, by
        rw [show k = 10 + (k - 10) by clear * - k1'; omega, foldPosKS_2 st (by clear * - hk k1'; omega), hr.fp2,
          show nMidS st + 74 + (k - 10) = nMidS st + 73 + 1 + (k - 10) by clear * -; omega]; exact ha, ?_⟩
      have e1 : (r0.2 ++ r1.2 ++ r2.2).getD k 0 = r2.2.getD (k - 10) 0 := by
        rw [List.getD_append_right _ _ _ _ (by rw [List.length_append, lf0l, lf1l]; clear * - k1'; omega), List.length_append, lf0l,
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
  have hA1c : st.hb ≤ capOffS st 1 := by
    have a1 := mA1.1; have a2 := mA1.2.1; have a3 := hr.oA1
    change st.hb ≤ pendA1B st at *
    change pendA1B st ≤ offA1B st at *
    clear * - a1 a2 a3; omega
  have hcap0 : digestsOf ((B.drop st.hb).take 64) 2 = capSBG st π 0 := by
    have e := cpy0 st.hb 64 le_rfl (by rw [hr.hb]; omega)
    have d := digestsOf_off π st.hb 2 hr.a0 (by rw [hr.hb]; omega)
    simp only [Nat.add_zero, sl, Nat.reduceMul] at e d
    rw [e, d]
    rfl
  have hcap1 : digestsOf ((B.drop (capOffS st 1)).take 32) 1 = capSBG st π 1 := by
    have e := cpy0 (capOffS st 1) 32 hA1c hr.c1
    have d := digestsOf_off π (capOffS st 1) 1 hr.a1 (by have a := hr.c1; clear * - hπ a; omega)
    simp only [Nat.add_zero, sl, Nat.mul_one] at e d
    rw [e, d]
    rfl
  have hcap2 : digestsOf ((B.drop (capOffS st 2 + 25760)).take 32) 1 = capSBG st π 2 := by
    have e := cpy1 (capOffS st 2) 32 hr.c2l hr.c2
    have d := digestsOf_off π (capOffS st 2) 1 hr.a2 (by have a := hr.c2; clear * - hπ a; omega)
    simp only [sl, Nat.mul_one] at e d
    rw [e, d]
    rfl
  have cp0 : S.capI 19 64 (B.drop f.hb) = ⟨19, (64 - st.occ0) + st.occ0, 1, capSBG st π 0⟩ := by
    rw [hoc, capI_rootWB, hhb, hcap0]
  have cp1 : S.capI 16 48 (B.drop (capOffS st 1)) = ⟨16, 0 + 48, 0, capSBG st π 1⟩ := by
    rw [capI_lvWB f vk (PSWithM mid) (by norm_num), hcap1]
  have cp2 : S.capI 13 48 (B.drop (capOffS st 2 + 25760)) = ⟨13, 0 + 48, 0, capSBG st π 2⟩ := by
    rw [capI_lvWB f vk (PSWithM mid) (by norm_num), hcap2]
  have hd₀P := hd₀
  rw [hlP] at hd₀P
  -- the extractor's run
  rw [hnd hdom hb0 hb hS' αk hα _ _ _
    (fun q' _ t' _ => by
      rw [Lvm.X.wdOf, cp0, readRowG_eq_wordOf S rfl (by rw [hoc]; exact ho0)])
    (fun q' _ t' _ => by
      rw [Lvm.X.wdOf, hW1, cp1, readRowG_eq_wordOf S rfl (show S.occ 16 (0 + 48) = 48 from ho1)])
    (fun q' _ t' _ => by
      rw [Lvm.X.wdOf, hW2, cp2, readRowG_eq_wordOf S rfl (show S.occ 13 (0 + 48) = 48 from ho2)])
    _ _ _ (fun j hj => by rw [Lvm.X.alphaN, dif_pos hj]; exact hfv j (by clear * - hj; omega))
    (fun j hj => by rw [Lvm.X.alphaN1, dif_pos hj]; exact hfv (6 + j) (by clear * - hj; omega))
    (fun j hj => by rw [Lvm.X.alphaN1, dif_pos hj]; exact hfv (10 + j) (by clear * - hj; omega))
    _ (fun v hv => by
      rw [resES_eq st π v hr.ar (by have a := hr.sr; clear * - hπ hv a; omega)]
      unfold Lvm.X.fNk
      rw [dif_pos hv]
      unfold resMsg
      erw [bitsToNat_symmN 9 v hv]
      rw [hresv, List.getD_eq_getElem _ _ (by simp only [List.length_map, List.length_range]; omega),
        List.getElem_map, List.getElem_range]
      rw [show resOffS st + 43008 + 24 * v = resOffS st + 24 * v + 43008 by clear * -; omega,
        cpy2 _ _ (by have a := hr.rl; clear * - hv a; omega) (by have a := hr.sr; clear * - hv a; omega)]
      rfl)
    m₂ hd₂ m₁ hd₁ _ hd₀P]
  -- the specification's witness
  unfold extSMLS
  dsimp only
  rw [hd, Option.bind_some]
  dsimp only
  rw [hcm, hw0, hw1, hw2, hd₂, Option.bind_some, hd₁, Option.bind_some, hd₀, Option.getD_some]
  have hlen : (Lvm.X.winOfL (lo ((B.drop 8).take (f.hb - 8))) q).length = 2 ^ 20 := by
    simp [Lvm.X.winOfL, Lvm.X.winC]
  rw [XwitBG, sigRS_li hli, ← hlP, hchild π _ (Lvm.X.winOfL (lo ((B.drop 8).take (f.hb - 8))) q) hn hlen,
    hsl π _ (Lvm.X.winOfL (lo ((B.drop 8).take (f.hb - 8))) q) hn hlen]
  unfold witOfL
  dsimp only
  rw [hxb, if_neg hbne, hxcL, hxh, hxn, hxs, hfcL, hfh, hfn, hfs]

end Lvm.ASM

namespace Lvm.XB

open RecursionFast Lvm Lvm.X Lvm.XS

/-- `wStreamS` at `stB20` is the window's stream block (`wStreamS_S20`'s twin). -/
theorem wStreamS_B20 (π : RecursionFast.Proof) (x : List UInt8) (out : List BF64)
    (hn : (Lvm.VEq.pubX x).n = (Lvm.X.pw π 14).toNat) (i : ℕ) :
    wStreamS stB20 π out i =
      if i < 2 ^ 19 then BF64.toBitVec (out.getD (Lvm.CT.sIdxU x i) 0) else BF64.toBitVec 0 := by
  have hc : (Lvm.X.pw π 14 < RecursionFast.toWord (2 ^ 18 + 1)) ↔ Lvm.Shape.small x = true := by
    rw [BitVec.lt_def, RecursionFast.toNat_toWord (by norm_num), Lvm.Shape.small, hn, decide_eq_true_iff]
    omega
  unfold wStreamS Lvm.CT.sIdxU
  rw [if_pos (show stB20.p.stage = 3 from rfl)]
  by_cases hi : i < 2 ^ 19
  · rw [ite_eq_left hi, ite_eq_left hi]
    by_cases hs : Lvm.Shape.small x = true
    · rw [if_pos (hc.2 hs), if_pos hs]
    · rw [if_neg (fun h => hs (hc.1 h)), if_neg hs]
  · rw [ite_eq_right hi, ite_eq_right hi]

/-- `loU x` is the extractor's lane `loP stB20 π` (`loU_eqS`'s twin). -/
theorem loU_eqB (π : RecursionFast.Proof) (x : List UInt8) (hn : (Lvm.VEq.pubX x).n = (Lvm.X.pw π 14).toNat) :
    Lvm.CT.loU x = Lvm.XS.loP stB20 π := by
  have hc : (Lvm.X.pw π 14 < RecursionFast.toWord (2 ^ 18 + 1)) ↔ Lvm.Shape.small x = true := by
    rw [BitVec.lt_def, RecursionFast.toNat_toWord (by norm_num), Lvm.Shape.small, hn, decide_eq_true_iff]
    omega
  have h3 : stB20.p.stage = 3 := rfl
  unfold Lvm.CT.loU Lvm.XS.loP
  by_cases hs : Lvm.Shape.small x = true
  · rw [if_pos hs, if_pos ⟨h3, hc.2 hs⟩]
  · rw [if_neg hs, if_neg fun h => hs (hc.1 h.2)]

/-- **The stream block `EXB20` reads is `childB20`'s.** -/
theorem childWB_streamB20 (π : RecursionFast.Proof) (x : List UInt8) (out : List BF64)
    (hn : (Lvm.VEq.pubX x).n = (Lvm.X.pw π 14).toNat) :
    childWB stB20 (wStreamS stB20 π out) = childB20 x out := by
  rw [childB20]
  congr 1
  funext i
  exact wStreamS_B20 π x out hn i

/-- **The right leaf's signature `EXB20` outputs is `sigLeafS20` of the window.** -/
theorem sigLeaf_streamB20 (π : RecursionFast.Proof) (x : List UInt8) (out : List BF64)
    (hn : (Lvm.VEq.pubX x).n = (Lvm.X.pw π 14).toNat) :
    Lvm.CT.sigOfP (fun j => wStreamS stB20 π out (17 * 2 ^ 14 + 1024 + j)) = Lvm.CT.sigLeafS20 x out := by
  rw [Lvm.CT.sigLeafS20]
  refine Lvm.ASM.sigOfP_congr fun j hj => ?_
  rw [wStreamS_B20 π x out hn, if_pos (by omega)]

end Lvm.XB
