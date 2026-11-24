-- New for lvm2 σ_LEAF (SLF-C, stage S2GS, lead decisions D2/D8): `Q_sig` at S2GS is sound. DAY-0 STATEMENTS: every
-- `sorry` is tagged `-- SLF-STMT <n>`; a proof never changes its statement (changes go to the lead, old → new).
import LvmQSigLeaf
import LvmQSigSound
import RecursionFast.Library.Fast

/-!
# `Q_sig` at S2GS is sound (SLF-STMT 4, 5)

* **`ChildOkS`**: `ChildOk` without `σ_leaf'` (the child's header carries none); **`qsigNoSl_sound`** (SLF-STMT 5): the
  child's trace signature and `ChildOkS` from `qsigNoSl` (`qsig_sound_in` without `gSl`).
* **`sigAtP v a`**: the signature on the cells from `a` with its chain values in `permC` order (chain `i`'s lanes at
  `a + 1 + 4·posC i`); the window's `σ_leaf` read the same way (SLF-L's `sigOfP`).
* **`SigKSinC`**, **`SigBitsC`**: the `KS` rows (padded steps, key leaf, path) and the `BITS` outputs of the
  specialised walk `qsigC`; **`qSigLeaf_sound`** (SLF-STMT 4): `SigOk vk (traceDigest []) (sigAtP v I.sg)`.
* **`sigBitsC_of_outs`** (SLF-STMT 4b): `SigBitsC` from the classes `sigSpecsC` (`sigBits_of_outs`'s twin).
-/

set_option autoImplicit false

namespace Lvm.QSig

open RecursionFast RecursionFast.Keccak Lvm Lvm.Loop Lvm.Loop.Build Lvm.Bits Lvm.BitsTab Lvm.KSponge Lvm.Wots

/-! ## The child (walk 1, no `σ_leaf'`) -/

/-- **The child's header passes `V_S`'s executable checks at S2GS** (`ChildOk` without `σ_leaf'`): the stream lanes from
`I.hd` are `b'`, `vk'` (4), `c_L'` (4), `s'` (4), `n'`, `h'` (4). -/
def ChildOkS (I : SigIn) (v : Nat → FK) : Prop :=
  let b := (v I.hd).val.toNat
  let n := (v (I.hd + 13)).val.toNat
  (b = 0 ∨ b = 1) ∧ digAt v (I.hd + 1) = digAt v I.vk ∧ 1 ≤ n ∧ n ≤ 2 ^ I.ln ∧
    (b = 0 → digAt v (I.hd + 5) = zeroDig) ∧
    digAt v I.cL = (if b = 0 then leafStmt (digAt v (I.hd + 14)) n
      else nodeStmt (digAt v (I.hd + 5)) (leafStmt (digAt v (I.hd + 14)) n))

/-! ### `qsigNoSl`'s parts and soundness (`qsig`'s proofs without `gSl`) -/

section NoSl

open Lvm.QSig.SigH

set_option maxRecDepth 100000 in
/-- **The parts of `Q_sig`.** -/
theorem qsigNoSl_parts {c : Ctx} {M : Mem} {p : Ptr} {I : SigIn} (h : Ok c M (qsigNoSl I) p) :
    let o := (qsigNoSl I p).1
    (∃ q, Ok c M (gPre I) q ∧ (gPre I q).1 = o.pre) ∧
    (∃ q, Ok c M (loop [7] (chainM I o.pre.1.n o.pre.2.1.n)) q ∧
      (loop [7] (chainM I o.pre.1.n o.pre.2.1.n) q).1 = o.cm) ∧
    (∀ u < 5, ∃ q, Ok c M (loop [] (chainC I o.pre.1.n o.pre.2.1.n u)) q ∧
      (loop [] (chainC I o.pre.1.n o.pre.2.1.n u) q).1 = o.cc.getD u dLoop) ∧
    (∃ q, Ok c M (gCheck I o.pre.1 o.pre.2.1) q) ∧
    (∃ q, Ok c M (loop [4] (pathTpl I)) q ∧ (loop [4] (pathTpl I) q).1 = o.pa) ∧
    (∃ q, Ok c M (header I o.pre.1 o.pre.2.1) q) ∧
    (∃ q, Ok c M (assert0 (kc (I.bi + 17)) (kc I.flag)) q) ∧
    (∃ q, Ok c M (gMsg I o.pre.1.n (Tbase o.pre)) q ∧ (gMsg I o.pre.1.n (Tbase o.pre) q).1 = o.msg) := by
  unfold qsigNoSl at h ⊢
  intro o
  obtain ⟨o1, h, e1⟩ := ok_bind' h
  obtain ⟨o2, h, e2⟩ := ok_bind' h
  obtain ⟨o3, h, e3⟩ := ok_bind' h
  obtain ⟨o4, h, e4⟩ := ok_bind' h
  obtain ⟨o5, h, e5⟩ := ok_bind' h
  obtain ⟨o6, h, e6⟩ := ok_bind' h
  obtain ⟨o7, h, e7⟩ := ok_bind' h
  obtain ⟨o8, h, e8⟩ := ok_bind' h
  obtain ⟨o9, h, e9⟩ := ok_bind' h
  refine ⟨⟨_, o1, rfl⟩, ⟨_, o2, rfl⟩, fun u hu => ?_, ⟨_, o4⟩, ⟨_, o5, rfl⟩, ⟨_, o6⟩, ⟨_, o7⟩,
    ⟨_, o9, ?_⟩⟩
  · obtain ⟨q, hq, e⟩ := ok_forN_get o3 u hu
    exact ⟨q, hq, e.symm⟩
  -- `o.msg` through the bind equations (a bare `rfl` makes the kernel unfold the whole builder: 16 s).
  have E := e1.trans (e2.trans (e3.trans (e4.trans (e5.trans (e6.trans (e7.trans (e8.trans e9)))))))
  rw [show o.pre = (gPre I p).1 from congrArg SigOut.pre E]
  exact (congrArg SigOut.msg E).symm


/-- **The child's header checks** (A3). -/
theorem qsigNoSl_child {c : Ctx} {M : Mem} {p : Ptr} {I : SigIn} (hln : 1 ≤ I.ln ∧ I.ln ≤ 62) (h : Ok c M (qsigNoSl I) p)
    (hg : M.k I.flag = 1) (hks : SigKS I (qsigNoSl I p).1 M.k) (hbits : SigBits I (qsigNoSl I p).1 M.k) :
    ChildOkS I M.k := by
  obtain ⟨⟨qP, hP, eP⟩, -, -, -, -, ⟨qH, hH⟩, -, ⟨qM, hM, eM⟩⟩ := qsigNoSl_parts h
  have pre := gPre_spec hP.1
  rw [eP] at pre
  obtain ⟨tZ, tO, eZ, eO, -⟩ := pre
  obtain ⟨hvk, -, hbb, hb0, htop, hmul, hprod, hsel⟩ := header_spec tZ tO hH.1 hH.2 hg eZ eO
  obtain ⟨-, -, -, -, -, -, ⟨qls, hls, els⟩, ⟨qns, hns, ens⟩⟩ := gMsg_parts hM
  rw [eM] at els ens
  set o := (qsigNoSl I p).1 with ho
  -- the leaf statement
  have hLS : digAt M.k I.yls = leafStmt (digAt M.k (I.hd + 14)) (M.k (I.hd + 13)).val.toNat := by
    obtain ⟨s, hperm, hdig⟩ := hks.ls
    obtain ⟨L0, Lk, L4, L5, Lz, L16⟩ := leafStmt_spec hls.1 (jf := 0) (by simp) eZ
    beta_reduce at L0 Lk L4 L5 Lz L16
    have e : ∀ l, lanesW M.k (xcell o 447) l = V M ((loop [] (leafStmtLanes I o.pre.1.n) qls).1.cell l 0).n :=
      fun l => by rw [els]; simp [lanesW, xcell]
    have B := leafStmt_lanes (fun l => (M.k (I.hd + 14 + l)).val) (M.k (I.hd + 13)).val
      (lanesW M.k (xcell o 447)) ?_ ?_ ?_ ?_ ?_ ?_
    · rw [hdig]
      exact leafStmt_block _ _ _ s B.1 B.2.1 B.2.2.1 B.2.2.2 hperm
    · rw [e, L0]
      have := out1_val (hbits.h 0 (by decide)).1
      simp only [Nat.mul_zero, Nat.add_zero] at this
      exact congrArg (· ^^^ _) this
    · intro k hk1 hk2
      rw [e, Lk k hk1 hk2, show I.bh + 2 * k - 1 = I.bh + 2 * (k - 1) + 1 by (clear * - hk1 hk2; omega)]
      exact congrArg₂ (· ^^^ ·) (out1_val (hbits.h (k - 1) (by (clear * - hk1 hk2; omega))).2)
        (out1_val (hbits.h k hk2).1)
    · rw [e, L4]
      exact congrArg₂ (· ^^^ ·) (out1_val (hbits.h 3 (by decide)).2) (out1_val hbits.n_lo)
    · rw [e, L5]
      exact congrArg (· ^^^ _) (out1_val hbits.n_hi)
    · intro l hl1 hl2; rw [e, Lz l hl1 hl2]
    · rw [e, L16]
  -- the node statement
  have hNS : digAt M.k I.yns = nodeStmt (digAt M.k (I.hd + 5)) (digAt M.k I.yls) := by
    obtain ⟨s, hperm, hdig⟩ := hks.ns
    obtain ⟨L0, La, L4, Lb, L8, Lz, L16⟩ := two_spec hns.1 (jf := 0) (by simp) eZ
    beta_reduce at L0 La L4 Lb L8 Lz L16
    have e : ∀ l, lanesW M.k (xcell o 448) l = V M ((loop [] (twoLanes o.pre.1.n 0x4E I.bcl I.bls 0) qns).1.cell l 0).n :=
      fun l => by rw [ens]; simp [lanesW, xcell]
    have hA : ∀ n, OV M (loop [] (twoLanes o.pre.1.n 0x4E I.bcl I.bls 0) qns).1 0 (oS n 0) = V M n :=
      fun n => congrArg FK.val (ov_oS_nil M _ rfl n 0)
    simp only [hA] at L0 La L4 Lb L8
    have B := two_lanes tagNode (fun l => (M.k (I.hd + 5 + l)).val) (fun l => (M.k (I.yls + l)).val)
      (lanesW M.k (xcell o 448)) ?_ ?_ ?_ ?_ ?_ ?_ ?_
    · rw [hdig]
      exact nodeStmt_block _ _ _ s B.1 B.2.1 B.2.2.1 B.2.2.2 hperm
    · rw [e, L0]
      have := out1_val (hbits.cl 0 (by decide)).1
      simp only [Nat.mul_zero, Nat.add_zero] at this
      exact congrArg₂ (· ^^^ ·) this rfl
    · intro k hk1 hk2
      rw [e, La k hk1 hk2, show I.bcl + (2 * k - 1) = I.bcl + 2 * (k - 1) + 1 by (clear * - hk1 hk2; omega)]
      exact congrArg₂ (· ^^^ ·) (out1_val (hbits.cl (k - 1) (by (clear * - hk1 hk2; omega))).2)
        (out1_val (hbits.cl k hk2).1)
    · rw [e, L4]
      have := out1_val (hbits.ls 0 (by decide)).1
      simp only [Nat.mul_zero, Nat.add_zero] at this
      exact congrArg₂ (· ^^^ ·) (out1_val (hbits.cl 3 (by decide)).2) this
    · intro k hk1 hk2
      rw [e, Lb k hk1 hk2, show I.bls + (2 * k - 1) = I.bls + 2 * (k - 1) + 1 by (clear * - hk1 hk2; omega)]
      exact congrArg₂ (· ^^^ ·) (out1_val (hbits.ls (k - 1) (by (clear * - hk1 hk2; omega))).2)
        (out1_val (hbits.ls k hk2).1)
    · rw [e, L8]
      exact congrArg (· ^^^ _) (out1_val (hbits.ls 3 (by decide)).2)
    · intro l hl1 hl2; rw [e, Lz l hl1 hl2]
    · rw [e, L16]
  -- `n'`
  have hn : 1 ≤ (M.k (I.hd + 13)).val.toNat ∧ (M.k (I.hd + 13)).val.toNat ≤ 2 ^ I.ln := by
    refine n_range _ I.ln hln ?_ ?_ ?_
    · have := out1_val hbits.n_top
      rw [htop] at this
      exact this.symm
    · rw [hbits.n_bit I.ln le_rfl, hbits.n_low] at hmul
      exact hmul
    · obtain ⟨z, hz, h0⟩ := List.mem_map.mp (List.prod_eq_zero_iff.mp hprod)
      have hzl : z ≤ I.ln := by simp at hz; (clear * - hz; omega)
      refine ⟨z, hzl, ?_⟩
      have := FK.eq_neg_of_add h0
      rw [hbits.n_bit z hzl] at this
      exact w64_inj this
  have z0 : (0 : FK).val.toNat = 0 := rfl
  have z1 : (1 : FK).val.toNat = 1 := rfl
  dsimp only [ChildOkS]
  rcases bool_of_idem hbb with hb | hb
  · have hcl : digAt M.k I.cL = digAt M.k I.yls := digAt_congr fun l hl => by
      have := hsel l hl; rw [hb, zero_mul, zero_add] at this; exact this.symm
    rw [hb, z0, ite_eq_left rfl, hcl, hLS]
    exact ⟨Or.inl rfl, digAt_congr hvk, hn.1, hn.2, fun _ => digAt_zero (hb0 hb), rfl⟩
  · have hcl : digAt M.k I.cL = digAt M.k I.yns := digAt_congr fun l hl => by
      have := hsel l hl
      rw [hb, one_mul, add_assoc, FK.add_self, add_zero] at this; exact this.symm
    rw [hb, z1, ite_eq_right (by decide), hcl, hNS, hLS]
    exact ⟨Or.inr rfl, digAt_congr hvk, hn.1, hn.2, fun h => absurd h (by decide), rfl⟩


/-- **The child's signature** (the one WOTS walk, A2). -/
theorem qsigNoSl_sigOk {c : Ctx} {M : Mem} {p : Ptr} {I : SigIn} (h : Ok c M (qsigNoSl I) p)
    (hg : M.k I.flag = 1) (hks : SigKS I (qsigNoSl I p).1 M.k) (hbits : SigBits I (qsigNoSl I p).1 M.k)
    (hinj : ∀ a b, a < 1024 → b < 1024 → FK.x ^ a = FK.x ^ b → a = b) :
    SigOk (digAt M.k I.vk) (digAt M.k I.md) (sigAt' M.k I.sg) = true := by
  obtain ⟨⟨q1, hpre, epre⟩, ⟨q2, hcm, ecm⟩, hcc, ⟨q4, hck⟩, ⟨q5, hpa, epa⟩, ⟨q6, hhd⟩, ⟨q7, has⟩,
    ⟨q9, hmsg, emsg⟩⟩ := qsigNoSl_parts h
  obtain ⟨⟨r1, hxm, exm⟩, hxc, ⟨r3, hla, ela⟩, ⟨r4, hlb, elb⟩, ⟨r5, hlc, elc⟩, ⟨r6, hxp, exp⟩, -, -⟩ :=
    gMsg_parts hmsg
  rw [emsg] at exm hxc ela elb elc exp
  have pre := gPre_spec hpre.1
  rw [epre] at pre
  obtain ⟨hZt, hOt, hZ, hO, hT⟩ := pre
  clear h hpre epre hmsg emsg
  generalize (qsigNoSl I p).1 = o at *
  have hj := idx_lt has hg hbits
  have hbd : ∀ q < 256, M.k (I.bd + q) = 0 ∨ M.k (I.bd + q) = 1 := fun q hq => by
    rw [hbits.md q hq]; exact bit_bool _ (Nat.mod_lt _ (by norm_num))
  have hbc : ∀ k < 10, M.k (I.bc + k) = 0 ∨ M.k (I.bc + k) = 1 := by
    obtain ⟨w, hw⟩ := hbits.cs
    exact fun k hk => by rw [hw k hk]; exact bit_bool w (by (clear * - hk; omega))
  have hx := gCheck_spec hZt hOt hck.1 hck.2 hg hZ hO hbd hbc
  rw [range_mdig hbits] at hx
  have hC := checksum_of_pow _ _ hinj hx
  have hdr := header_spec hZt hOt hhd.1 hhd.2 hg hZ hO
  refine wots_sound (σ := sigAt' M.k I.sg) hj (by simp [sigAt']) (by simp [sigAt'])
    (ends := (List.range wotsLen).map fun i => digOfW (lanesW M.k (endc o i))) (by simp)
    (fun i hi => ?_) (cur := fun t => digAt M.k (I.yc + 4 * t)) ?_ (fun t ht => ?_) ?_
  · -- one chain
    simp only [sigAt', List.getElem_map, List.getElem_range]
    by_cases hi' : i < 128
    · rw [wdig_lt _ hi', ← mdig_eq hbits hi']
      obtain ⟨hm, he⟩ := sel_m hcm.1 ecm hZ hO hbd hi'
      have hle : mdig M I i ≤ 3 := by
        unfold mdig; have := bnat_le (M.k (I.bd + 2 * i)); have := bnat_le (M.k (I.bd + 2 * i + 1))
        (clear ecm ela elb elc epa exm exp hC hO hOt hT hZ hZt has hbc hbd hbits hcc hck hcm hdr he hg hhd hi hi' hinj hj hks hla hlb hlc hm hpa hx hxc hxm hxp; omega)
      exact chain_end hle (fun s hs => step_m hks hbits hZ hT hj hxm.1 exm hi' hs) hm he
    · obtain ⟨u, rfl⟩ : ∃ u, i = 128 + u := ⟨i - 128, by (clear * - hi'; omega)⟩
      have hu : u < 5 := by simp [wotsLen] at hi; (clear * - hi; omega)
      rw [← cdig_eq _ hC hu]
      obtain ⟨q, hq, eq⟩ := hcc u hu
      obtain ⟨r, hr, er⟩ := hxc u hu
      obtain ⟨hm, he⟩ := sel_c hq.1 eq hZ hO hbc hu
      have hle : cdig M I u ≤ 3 := by
        unfold cdig; have := bnat_le (M.k (I.bc + 2 * u)); have := bnat_le (M.k (I.bc + 2 * u + 1))
        (clear ecm ela elb elc epa eq er exm exp hC hO hOt hT hZ hZt has hbc hbd hbits hcc hck hcm hdr he hg hhd hi hi' hinj hj hks hla hlb hlc hm hpa hq hr hu hx hxc hxm hxp; omega)
      exact chain_end hle (fun s hs => step_c hks hbits hZ hj hu hr.1 er hs) hm he
  · -- the leaf
    show digAt M.k (I.yc + 4 * 0) = _
    rw [Nat.mul_zero, Nat.add_zero]
    exact leaf_digest hks hbits hZ hj hla.1 ela hlb.1 elb hlc.1 elc
  · -- the walk
    have ht' : t < 16 := by simpa [sigAt', sigHeight] using ht
    show digAt M.k (I.yc + 4 * (t + 1)) = _
    rw [node_digest hks hbits hZ hxp.1 exp ht']
    have hb := hbits.idx_bit t ht'
    unfold Out1 at hb
    have hbool : M.k (I.bi + 1 + t) = 0 ∨ M.k (I.bi + 1 + t) = 1 := by
      rw [hb]; exact bit_bool _ (by (clear * - ht'; omega))
    have hA : (digOfW fun l => (M.k (o.pa.cell (4 + l) t).n).val) =
        if M.k (I.bi + 1 + t) = 1 then digAt M.k (I.sg + 533 + 4 * t) else digAt M.k (I.yc + 4 * t) :=
      digOfW_ite fun l hl => by
        rw [← epa, (path_spec hpa.1 ht' hl hbool).1]
        split_ifs <;> exact kval_congr M (by (clear * -; first | decide | (simp only [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]; done) | ring1 | omega))
    have hB : (digOfW fun l => (M.k (o.pa.cell (8 + l) t).n).val) =
        if M.k (I.bi + 1 + t) = 1 then digAt M.k (I.yc + 4 * t) else digAt M.k (I.sg + 533 + 4 * t) :=
      digOfW_ite fun l hl => by
        rw [← epa, (path_spec hpa.1 ht' hl hbool).2]
        split_ifs <;> exact kval_congr M (by (clear * -; first | decide | (simp only [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]; done) | ring1 | omega))
    have key : M.k (I.bi + 1 + t) = 1 ↔ ¬ ((M.k I.sg).val.toNat / 2 ^ t % 2 = 0) := by
      rw [hb, w64_bit _ (by (clear * - ht'; omega)), ubit_testBit, Nat.testBit_eq_decide_div_mod_eq]
      have h01 : ¬ ((0 : FK) = 1) := by decide
      by_cases hq : (M.k I.sg).val.toNat / 2 ^ t % 2 = 1
      · simp [hq]
      · simp [hq, h01]
    simp only [sigAt', List.getElem_map, List.getElem_range]
    rw [hA, hB]
    by_cases hc : M.k (I.bi + 1 + t) = 1
    · have := key.mp hc
      simp only [hc, ↓reduceIte, this]
    · have : (M.k I.sg).val.toNat / 2 ^ t % 2 = 0 := by
        by_contra hn; exact hc (key.mpr hn)
      simp only [hc, ↓reduceIte, this]
  · -- the root
    show digAt M.k (I.yc + 4 * 16) = digAt M.k I.vk
    unfold digAt
    exact digOfW_congr fun l hl => by
      rw [show I.yc + 4 * 16 + l = I.yc + 64 + l by ring, hdr.2.1 l hl]


theorem qsigNoSl_msg (I : SigIn) (p : Ptr) : ∃ q : Ptr, (qsigNoSl I p).1.x0 = q.k ∧
    (qsigNoSl I p).1.msg = (gMsg I (qsigNoSl I p).1.pre.1.n (Tbase (qsigNoSl I p).1.pre) q).1 := by
  unfold qsigNoSl
  simp only [out_bind_eq, getPtr_apply_eq, pure_apply_eq, Ptr.adv_nil]
  exact ⟨_, rfl, rfl⟩

/-- **KS row `r`'s lane `l` is the cell `x0 + 17 r + l`.** -/
theorem xcell_eqN {I : SigIn} {p : Ptr} {r l : Nat} (hr : r < 449) (hl : l < 17) :
    xcell (qsigNoSl I p).1 r l = (qsigNoSl I p).1.x0 + 17 * r + l := by
  obtain ⟨q, e1, e2⟩ := qsigNoSl_msg I p
  rw [e1]
  exact gMsg_xcell e2 hr hl

set_option maxRecDepth 100000 in
theorem qsigNoSl_gXeq {c : Ctx} {M : Mem} {p : Ptr} {I : SigIn} (h : Ok c M (qsigNoSl I) p) :
    ∃ q, Ok c M (gXeq I (qsigNoSl I p).1.x0) q := by
  unfold qsigNoSl at h ⊢
  obtain ⟨-, h, -⟩ := ok_bind' h
  obtain ⟨-, h, -⟩ := ok_bind' h
  obtain ⟨-, h, -⟩ := ok_bind' h
  obtain ⟨-, h, -⟩ := ok_bind' h
  obtain ⟨-, h, -⟩ := ok_bind' h
  obtain ⟨-, h, -⟩ := ok_bind' h
  obtain ⟨-, h, -⟩ := ok_bind' h
  obtain ⟨-, h, -⟩ := ok_bind' h
  obtain ⟨-, h, -⟩ := ok_bind' h
  obtain ⟨o, -, -⟩ := ok_bind' h
  simp only [getPtr_apply_eq, Ptr.adv_nil] at o
  simp only [out_bind_eq, getPtr_apply_eq, pure_apply_eq, Ptr.adv_nil]
  exact ⟨_, o⟩

/-- **The message lanes are the `KS` input lanes** (A19): with the node flag `1`, cell
`x0 + j` equals cell `xs + j` for every `j < 7633`. -/
theorem qsigNoSl_xeq {c : Ctx} {M : Mem} {p : Ptr} {I : SigIn} (h : Ok c M (qsigNoSl I) p)
    (hg : M.k I.flag = 1) : ∀ j < 7633, M.k ((qsigNoSl I p).1.x0 + j) = M.k (I.xs + j) := by
  obtain ⟨q, hq⟩ := qsigNoSl_gXeq h
  exact gXeq_spec hq hg

/-- `SigKSin` gives `SigKS`. -/
theorem sigKS_of_inN {c : Ctx} {M : Mem} {p : Ptr} {I : SigIn} (h : Ok c M (qsigNoSl I) p)
    (hg : M.k I.flag = 1) (hks : SigKSin I M.k) : SigKS I (qsigNoSl I p).1 M.k := by
  have hx : ∀ r < 449, ∀ l < 17, M.k (xcell (qsigNoSl I p).1 r l) = M.k (I.xs + 17 * r + l) :=
    fun r hr l hl => by
      rw [xcell_eqN hr hl, Nat.add_assoc, qsigNoSl_xeq h hg _ (by (clear * - hr hl; omega)), Nat.add_assoc]
  obtain ⟨sIn, sOut, h0, h1, h2, h3⟩ := hks.leaf
  refine ⟨fun r hr => oneHash_lanes (hx r (by (clear * - hr; omega))) (hks.step r hr),
    ⟨sIn, sOut, h0, fun u hu => ?_, h2, h3⟩,
    fun t ht => oneHash_lanes (hx _ (by (clear * - ht; omega))) (hks.path t ht),
    oneHash_lanes (hx _ (by (clear * -; first | decide | (simp only [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]; done) | ring1 | omega))) hks.ls, oneHash_lanes (hx _ (by (clear * -; first | decide | (simp only [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]; done) | ring1 | omega))) hks.ns⟩
  rw [xorMsg_lanes (hx _ (by (clear * - hu; omega)))]
  exact h1 u hu

end NoSl

/-- **SLF-STMT 5** (owner C): **`qsigNoSl` is sound, `KS` on the input array** (`qsig_sound_in` without `gSl`): the
child's trace signature and `ChildOkS`. -/
theorem qsigNoSl_sound {c : Ctx} {M : Mem} {p : Ptr} {I : SigIn} (hln : 1 ≤ I.ln ∧ I.ln ≤ 62)
    (h : Ok c M (qsigNoSl I) p) (hg : M.k I.flag = 1) (hks : SigKSin I M.k)
    (hbits : SigBits I (qsigNoSl I p).1 M.k) (hinj : ∀ a b, a < 1024 → b < 1024 → FK.x ^ a = FK.x ^ b → a = b) :
    SigOk (digAt M.k I.vk) (digAt M.k I.md) (sigAt' M.k I.sg) = true ∧ ChildOkS I M.k :=
  ⟨qsigNoSl_sigOk h hg (sigKS_of_inN h hg hks) hbits hinj, qsigNoSl_child hln h hg (sigKS_of_inN h hg hks) hbits⟩

/-! ## The node's own leaf signature (walk 2, variant C) -/

/-- **The signature on the cells from `a`, chain values in `permC` order**: `idx`, chain `i`'s value at
`a + 1 + 4·posC i`, the 16 siblings from `a + 533`. -/
def sigAtP (v : Nat → FK) (a : Nat) : Sig :=
  ⟨(v a).val.toNat, (List.range wotsLen).map fun i => digAt v (a + 1 + 4 * posC i),
    (List.range sigHeight).map fun t => digAt v (a + 533 + 4 * t)⟩

/-- **The `KS` rows of the specialised walk, on the input array**: the padded steps' rows `r < nStepRowsC` (one block
each), the key leaf's 32 blocks from row `nStepRowsC`, the 16 path nodes; row `r`'s lanes the cells `I.xs + 17 r + l`,
its digest the cells `I.ys + 4 r` (the key leaf's at `I.yc`, path node `t`'s at `I.yc + 4 (t + 1)`). -/
structure SigKSinC (I : SigIn) (v : Nat → FK) : Prop where
  step : ∀ r < nStepRowsC, OneHash v (fun l => I.xs + 17 * r + l) (I.ys + 4 * r)
  leaf : ∃ sIn sOut : Nat → State, sIn 0 = zeroSt ∧
    (∀ u < 32, BlockPerm (xorMsg (sIn u) (laneByte (lanesW v (fun l => I.xs + 17 * (nStepRowsC + u) + l))))
      (sOut u)) ∧
    (∀ u, u + 1 < 32 → sIn (u + 1) = sOut u) ∧ digAt v I.yc = stDigest (sOut 31)
  path : ∀ t < 16, OneHash v (fun l => I.xs + 17 * (nStepRowsC + 32 + t) + l) (I.yc + 4 * (t + 1))

/-- **The `BITS` outputs the specialised walk reads** (`sigSpecsC`'s classes): `σ_leaf.idx`; every real step input
(`stepsC`, word `s24wcC`, outputs from `s24ocC`); every chain end (`endC`) and path half (`shl 8`/`shr 56`). -/
structure SigBitsC (I : SigIn) (pa : LoopOut) (v : Nat → FK) : Prop where
  idx_lo : Out1 v I.sg (.shl 8) I.bi
  idx_bit : ∀ z < 16, Out1 v I.sg (.bit z) (I.bi + 1 + z)
  idx_hi : Out1 v I.sg (.shr 16) (I.bi + 17)
  x : ∀ y < 4 * stepsC.length, Out1 v (s24wcC I I.ys stepsC.toArray y) (.shl 24) (s24ocC I stepsC.toArray y) ∧
    Out1 v (s24wcC I I.ys stepsC.toArray y) (.shr 40) (s24ocC I stepsC.toArray y + 1)
  e : ∀ i < 133, ∀ l < 4, Out1 v (endC I I.ys i l) (.shl 8) (I.be + 2 * (4 * i + l)) ∧
    Out1 v (endC I I.ys i l) (.shr 56) (I.be + 2 * (4 * i + l) + 1)
  p : ∀ t < 16, ∀ u < 2, ∀ l < 4,
    Out1 v (pa.cell (4 + 4 * u + l) t).n (.shl 8) (I.bp + 2 * (8 * t + 4 * u + l)) ∧
      Out1 v (pa.cell (4 + 4 * u + l) t).n (.shr 56) (I.bp + 2 * (8 * t + 4 * u + l) + 1)

/-! ### The specialised walk's soundness (SLF-STMT 4, 4b): layout, steps, chain ends, key leaf, path -/

section LeafC

open Lvm.QSig.SigH

/-- Consecutive constants: the `i`-th is the cell `q.k + i`, holding `g ls[i]`. -/
private theorem consts_spec {c : Ctx} {M : Mem} {a : Nat} {g : Nat → FK} :
    ∀ (ls : List Nat) (q : Ptr), SegsHold c M q (seqAll (ls.map fun k => const .K (g k) (kc a)) q).2 →
      ∀ i < ls.length, ((seqAll (ls.map fun k => const .K (g k) (kc a)) q).1.getD i (kc 0)).n = q.k + i ∧
        M.k (q.k + i) = g (ls.getD i 0)
  | [], _, _, i, hi => absurd hi (by simp)
  | z :: ls, q, h, i, hi => by
    rw [List.map_cons, seqAll_cons_apply, segsHold_append, segsHold_append] at h
    have hadv : (q.adv (const .K (g z) (kc a) q).2).k = q.k + 1 := rfl
    rw [List.map_cons, seqAll_cons_apply]
    cases i with
    | zero => exact ⟨rfl, const_K_spec h.1⟩
    | succ i =>
      obtain ⟨e1, e2⟩ := consts_spec ls _ h.2.1 i (by simpa using hi)
      rw [hadv] at e1 e2
      refine ⟨by simpa [Nat.add_assoc, Nat.add_comm 1] using e1, ?_⟩
      rw [show q.k + (i + 1) = q.k + 1 + i by omega, e2]; rfl

/-- Loops of varying sizes in sequence: loop `i` sits after the cells of the loops before it. -/
private theorem ok_seqAll_loopsV {c : Ctx} {M : Mem} {ds : Nat → List Nat} {tp : Nat → List LRow}
    (hw : ∀ u, AllK (tp u)) :
    ∀ (ls : List Nat) (q : Ptr), Ok c M (seqAll (ls.map fun u => loop (ds u) (tp u))) q →
      ∀ i < ls.length, ∃ q' : Ptr, q'.k = q.k + ((ls.take i).map fun u => (tp u).length * 2 ^ (ds u).sum).sum ∧
        Ok c M (loop (ds (ls.getD i 0)) (tp (ls.getD i 0))) q'
  | [], _, _, i, hi => absurd hi (by simp)
  | z :: ls, q, h, i, hi => by
    obtain ⟨h1, h2⟩ := h
    rw [List.map_cons, seqAll_cons_apply, segsHold_append, segsHold_append] at h1
    rw [List.map_cons, seqAll_cons_apply, segsAssert_append, segsAssert_append] at h2
    cases i with
    | zero => exact ⟨q, by simp, h1.1, h2.1⟩
    | succ i =>
      obtain ⟨q', e, hq⟩ := ok_seqAll_loopsV hw ls _ ⟨h1.2.1, h2.2.1⟩ i (by simpa using hi)
      refine ⟨q', ?_, by simpa using hq⟩
      rw [e, loop_advK q (hw z)]
      simp [Nat.add_assoc]

/-- The pointer after loops of varying sizes. -/
private theorem seqAll_loopsV_adv {ds : Nat → List Nat} {tp : Nat → List LRow} (hw : ∀ u, AllK (tp u)) :
    ∀ (ls : List Nat) (q : Ptr), (q.adv (seqAll (ls.map fun u => loop (ds u) (tp u)) q).2).k =
      q.k + (ls.map fun u => (tp u).length * 2 ^ (ds u).sum).sum
  | [], q => by simp [seqAll, pure_apply]
  | z :: ls, q => by
    rw [List.map_cons, seqAll_cons_apply, List.append_nil, Ptr.adv_append,
      seqAll_loopsV_adv hw ls, loop_advK q (hw z)]
    simp [Nat.add_assoc]


/-- **A step message's 17 lanes** at template rows `b … b + 16` (`steps_spec` for one `stepLanes` block). -/
theorem stepAt_spec {c : Ctx} {M : Mem} {dims : List Nat} {tpl : List LRow} {p : Ptr} {I : SigIn} {Zn : Nat}
    {T : Opd} {c1 : UInt64} {xb st b : Nat} (h : SegsHold c M p (loop dims tpl p).2) {jf : Nat}
    (hjf : jf < 2 ^ dims.sum) (hT : OpdK (loop dims tpl p).1 T) (hZ : M.k Zn = 0) (hb : b + 17 ≤ tpl.length)
    (hrow : ∀ l < 17, tpl.getD (b + l) default = (stepLanes I Zn T c1 xb st).getD l default) :
    let o := (loop dims tpl p).1
    let L := fun l => V M (o.cell (b + l) jf).n
    let X := fun k => OV M o jf (oS (xb + k) st)
    L 0 = V M I.bi ^^^ 0x57 ∧ L 1 = (OV M o jf T ^^^ X 0) ^^^ c1 ∧
      (∀ k, 1 ≤ k → k < 4 → L (k + 1) = X (2 * k - 1) ^^^ X (2 * k)) ∧
      L 5 = X 7 ^^^ 0x1000000 ∧ (∀ l, 6 ≤ l → l < 16 → L l = 0) ∧ L 16 = 0x8000000000000000 := by
  dsimp only
  refine ⟨?_, ?_, fun k hk1 hk2 => ?_, ?_, fun l hl1 hl2 => ?_, ?_⟩
  · exact lane0 h hjf (by omega) (by rw [hrow 0 (by omega)]; rfl) (by rfl) (by rfl) (by rfl) (by rfl)
  · exact lane1 h hjf (by omega) (by rw [hrow 1 (by omega)]; rfl) hT (by rfl) (by rfl) (by rfl) (by rfl)
  · interval_cases k
    · exact lane1z h hjf (by omega) (by rw [hrow 2 (by omega)]; rfl) (by rfl) (by rfl) (by rfl) (by rfl)
    · exact lane1z h hjf (by omega) (by rw [hrow 3 (by omega)]; rfl) (by rfl) (by rfl) (by rfl) (by rfl)
    · exact lane1z h hjf (by omega) (by rw [hrow 4 (by omega)]; rfl) (by rfl) (by rfl) (by rfl) (by rfl)
  · exact lane0 h hjf (by omega) (by rw [hrow 5 (by omega)]; rfl) (by rfl) (by rfl) (by rfl) (by rfl)
  · exact laneZ h hjf (by omega) (by rw [hrow l (by omega)]; interval_cases l <;> rfl) hZ
  · exact lanePad h hjf (by omega) (by rw [hrow 16 (by omega)]; rfl) hZ

theorem stepLanes_len (I : SigIn) (Zn : Nat) (T : Opd) (c1 : UInt64) (xb st : Nat) :
    (stepLanes I Zn T c1 xb st).length = 17 := by simp [stepLanes, zeroLanes]

theorem stepLanes_allK (I : SigIn) (Zn : Nat) (T : Opd) (c1 : UInt64) (xb st : Nat) :
    AllK (stepLanes I Zn T c1 xb st) := by
  simp only [AllK, stepLanes, zeroLanes, padLane, List.forall_mem_append, List.forall_mem_cons,
    List.forall_mem_map]
  simp

/-- Blocks of 17 rows: row `17 t + l` of `(range n).flatMap f` is row `l` of `f t`. -/
private theorem flatMap17_getD {α : Type} (d : α) (f : Nat → List α) (hf : ∀ t, (f t).length = 17) :
    ∀ n, ∀ t < n, ∀ l < 17, ((List.range n).flatMap f).getD (17 * t + l) d = (f t).getD l d
  | 0, t, ht, _, _ => absurd ht (by omega)
  | n + 1, t, ht, l, hl => by
    have hlen : ((List.range n).flatMap f).length = 17 * n := by
      simp [List.length_flatMap, hf, List.sum_replicate, Nat.mul_comm]
    rw [List.range_succ, List.flatMap_append]
    by_cases htn : t < n
    · rw [List.getD_eq_getElem?_getD, List.getElem?_append_left (by rw [hlen]; nlinarith),
        ← List.getD_eq_getElem?_getD, flatMap17_getD d f hf n t htn l hl]
    · obtain rfl : t = n := by omega
      rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by rw [hlen]; omega), hlen,
        show 17 * t + l - 17 * t = l by omega]
      simp [List.getD_eq_getElem?_getD]

theorem gStepsTplC_len (I : SigIn) (Zn cT d : Nat) : (gStepsTplC I Zn cT d).length = 17 * (3 - d) := by
  simp [gStepsTplC, List.length_flatMap, stepLanes_len, List.sum_replicate, Nat.mul_comm]

theorem gStepsTplC_allK (I : SigIn) (Zn cT d : Nat) : AllK (gStepsTplC I Zn cT d) := by
  intro r hr
  simp only [gStepsTplC, List.mem_flatMap] at hr
  obtain ⟨t, -, hr⟩ := hr
  exact stepLanes_allK _ _ _ _ _ _ r hr

theorem gStepsTplC_row (I : SigIn) (Zn cT d : Nat) {t l : Nat} (ht : t < 3 - d) (hl : l < 17) :
    (gStepsTplC I Zn cT d).getD (17 * t + l) default =
      (stepLanes I Zn (oS (cT + gOffC d) 1) ((d + t).toUInt64 <<< (16 : Nat).toUInt64) (I.bx + gBxC d + 8 * t)
        (8 * (3 - d))).getD l default :=
  flatMap17_getD _ _ (fun _ => stepLanes_len _ _ _ _ _ _) _ t ht l hl

private theorem headD_eq_getD {α : Type} (l : List α) (d : α) : l.headD d = l.getD 0 d := by cases l <;> rfl

theorem gRow_take {I : SigIn} {Zn cT d : Nat} (hd : d ≤ 3) :
    (((List.range 3).take d).map fun u => (gStepsTplC I Zn cT u).length * 2 ^ ([gLogC u] : List Nat).sum).sum =
      17 * gRowC d := by
  rw [List.take_range, Nat.min_eq_left hd, gRowC, ← List.sum_map_mul_left]
  congr 1
  apply List.map_congr_left
  intro u _
  rw [gStepsTplC_len]
  simp only [List.sum_cons, List.sum_nil, Nat.add_zero]
  ring

/-- `ok_bind'` with the first output and the next pointer as variables (small terms). -/
private theorem ok_bindK {c : Ctx} {M : Mem} {α β : Type} {m : BM α} {f : α → BM β} {p : Ptr}
    (h : Ok c M (m >>= f) p) : ∃ (x : α) (p' : Ptr), x = (m p).1 ∧ p' = p.adv (m p).2 ∧ Ok c M m p ∧
      Ok c M (f x) p' ∧ ((m >>= f) p).1 = (f x p').1 := by
  obtain ⟨h1, h2, e⟩ := ok_bind' h
  exact ⟨_, _, rfl, rfl, h1, h2, e⟩

/-- **The parts of the specialised walk**, with the message loops' positions from `x0`. -/
theorem qsigC_parts {c : Ctx} {M : Mem} {p : Ptr} {I : SigIn} {Zn : Nat} (h : Ok c M (qsigC I Zn) p) :
    let o := (qsigC I Zn p).1
    (∀ k < 133, M.k (o.cT + k) = w64 ((permC.getD k 0).toUInt64 <<< (8 : Nat).toUInt64)) ∧
    (∃ q, Ok c M (loop [4] (pathTpl I)) q ∧ (loop [4] (pathTpl I) q).1 = o.pa) ∧
    (∃ q, Ok c M (forN 4 fun l => assertEq (kc (I.yc + 64 + l)) (kc (I.vk + l)) (kc I.flag)) q) ∧
    (∃ q, Ok c M (assert0 (kc (I.bi + 17)) (kc I.flag)) q) ∧
    (∀ d < 3, ∃ q : Ptr, q.k = o.x0 + 17 * gRowC d ∧ Ok c M (loop [gLogC d] (gStepsTplC I Zn o.cT d)) q) ∧
    (∃ q : Ptr, q.k = o.x0 + 17 * nStepRowsC ∧ Ok c M (loop [] (leafA I)) q) ∧
    (∃ q : Ptr, q.k = o.x0 + 17 * nStepRowsC + 2 ∧ Ok c M (loop [9] (leafB I)) q) ∧
    (∃ q : Ptr, q.k = o.x0 + 17 * nStepRowsC + 514 ∧ Ok c M (loop [] (leafC I Zn)) q) ∧
    (∃ q : Ptr, q.k = o.x0 + 17 * (nStepRowsC + 32) ∧ Ok c M (loop [4] (twoLanes Zn 0x4D I.bp (I.bp + 8) 16)) q) ∧
    (∃ q, Ok c M (gXeqN I o.x0 (17 * (nStepRowsC + 48))) q) := by
  unfold qsigC at h ⊢
  intro o
  obtain ⟨x1, p1, ex1, -, o1, h, e1⟩ := ok_bindK h
  obtain ⟨x2, p2, ex2, -, o2, h, e2⟩ := ok_bindK h
  obtain ⟨x3, p3, -, -, o3, h, e3⟩ := ok_bindK h
  obtain ⟨x4, p4, -, -, o4, h, e4⟩ := ok_bindK h
  obtain ⟨x5, p5, ex5, ep5, -, h, e5⟩ := ok_bindK h
  obtain ⟨x6, p6, -, ep6, o6, h, e6⟩ := ok_bindK h
  obtain ⟨x7, p7, -, ep7, o7, h, e7⟩ := ok_bindK h
  obtain ⟨x8, p8, -, ep8, o8, h, e8⟩ := ok_bindK h
  obtain ⟨x9, p9, -, ep9, o9, h, e9⟩ := ok_bindK h
  obtain ⟨x10, p10, -, -, o10, h, e10⟩ := ok_bindK h
  obtain ⟨x11, p11, -, -, o11, -, e11⟩ := ok_bindK h
  have E : o = ⟨(x1.headD (kc 0)).n, x2, x6, x7, x8, x9, x10, x5.k⟩ :=
    (e1.trans (e2.trans (e3.trans (e4.trans (e5.trans (e6.trans (e7.trans (e8.trans (e9.trans
      (e10.trans e11)))))))))).trans rfl
  have hx5 : x5 = p4 := ex5
  have hp5 : p5 = p4 := by rw [ep5]; exact Ptr.adv_nil p4
  have C := consts_spec (g := fun k => w64 ((permC.getD k 0).toUInt64 <<< (8 : Nat).toUInt64)) (List.range 133) p o1.1
  have hcT : o.cT = p.k := by
    rw [E]; show (x1.headD (kc 0)).n = p.k
    rw [ex1, headD_eq_getD]; exact (C 0 (by simp)).1
  have hx0 : o.x0 = p5.k := by rw [E, hx5, hp5]
  have hw : ∀ u, AllK (gStepsTplC I Zn (x1.headD (kc 0)).n u) := fun u => gStepsTplC_allK _ _ _ _
  have hcT' : (x1.headD (kc 0)).n = o.cT := by rw [E]
  have hall := seqAll_loopsV_adv (ds := fun u => [gLogC u]) hw (List.range 3) p5
  have h3 := gRow_take (I := I) (Zn := Zn) (cT := (x1.headD (kc 0)).n) (d := 3) le_rfl
  rw [show (List.range 3).take 3 = List.range 3 from by simp] at h3
  have hp6 : p6.k = o.x0 + 17 * nStepRowsC := by
    rw [ep6, hx0]; exact hall.trans (by rw [h3, nStepRowsC])
  have hp7 : p7.k = o.x0 + 17 * nStepRowsC + 2 := by
    rw [ep7, loop_advK p6 (leafA_allK I), hp6]
    simp only [leafA, List.length_cons, List.length_nil, List.sum_nil, pow_zero]; omega
  have hp8 : p8.k = o.x0 + 17 * nStepRowsC + 514 := by
    rw [ep8, loop_advK p7 (leafB_allK I), hp7]
    simp only [leafB, List.length_cons, List.length_nil, List.sum_cons, List.sum_nil]
    omega
  have hp9 : p9.k = o.x0 + 17 * (nStepRowsC + 32) := by
    rw [ep9, loop_advK p8 (leafC_allK I Zn), hp8, leafC_len]; simp only [List.sum_nil, pow_zero]; omega
  refine ⟨fun k hk => ?_, ⟨p1, o2, by rw [E, ex2]⟩, ⟨p2, o3⟩, ⟨p3, o4⟩, fun d hd => ?_, ⟨p6, hp6, o7⟩,
    ⟨p7, hp7, o8⟩, ⟨p8, hp8, o9⟩, ⟨p9, hp9, o10⟩, ⟨p10, by rw [hx0, hp5, ← hx5]; exact o11⟩⟩
  · rw [hcT, (C k (by simpa using hk)).2]
    simp [hk]
  · obtain ⟨q, eq, hq⟩ := ok_seqAll_loopsV (ds := fun u => [gLogC u]) hw (List.range 3) p5 o6 d (by simpa using hd)
    rw [show (List.range 3).getD d 0 = d by simp [hd], hcT'] at hq
    refine ⟨q, ?_, hq⟩
    rw [eq, hx0, gRow_take (by omega)]

/-- The first real step of group `d` in `stepsC`. -/
def sOffC (d : Nat) : Nat := ((List.range d).map fun e => (grpC e).length * (3 - e)).sum

/-- **The walk's layout constants** (one small kernel evaluation). -/
theorem layC : (grpC 0).length = 36 ∧ (grpC 1).length = 33 ∧ (grpC 2).length = 30 ∧ (grpC 3).length = 34 ∧
    gLogC 0 = 6 ∧ gLogC 1 = 6 ∧ gLogC 2 = 5 ∧ gRowC 1 = 192 ∧ gRowC 2 = 320 ∧ nStepRowsC = 352 ∧
    gBxC 1 = 1536 ∧ gBxC 2 = 2560 ∧ sOffC 1 = 108 ∧ sOffC 2 = 174 ∧ stepsC.length = 204 := by
  decide +kernel

/-- The walk's `KS` message lanes: `17·400 = 6800` (`4096 + 2048 + 512 + 128 + 16`). -/
theorem nMsgC : 17 * (nStepRowsC + 48) = 6800 := by rw [layC.2.2.2.2.2.2.2.2.2.1]

/-- **`gXeqN` at the walk's size**: the 6,800 message lanes equal the input array when the gate is on. -/
theorem gXeqC_spec {c : Ctx} {M : Mem} {q : Ptr} {I : SigIn} {x0 : Nat}
    (h : Ok c M (gXeqN I x0 (17 * (nStepRowsC + 48))) q) (hg : M.k I.flag = 1) :
    ∀ j < 17 * (nStepRowsC + 48), M.k (x0 + j) = M.k (I.xs + j) := by
  rw [nMsgC] at h ⊢
  have h' : Ok c M (forN 5 fun l => loop [[12, 11, 9, 7, 4].getD l 0]
      (xeqTpl I x0 ([0, 4096, 6144, 6656, 6784].getD l 0))) q := (ok_bind' h).1
  have key : ∀ l < 5, ∀ j < 2 ^ [12, 11, 9, 7, 4].getD l 0,
      M.k (x0 + [0, 4096, 6144, 6656, 6784].getD l 0 + j) = M.k (I.xs + [0, 4096, 6144, 6656, 6784].getD l 0 + j) :=
    fun l hl => by
      obtain ⟨q', hq⟩ := ok_forN h' l hl
      exact xeq_loop hq.1 hq.2 hg
  intro j hj
  have go : ∀ l < 5, [0, 4096, 6144, 6656, 6784].getD l 0 ≤ j → j < [0, 4096, 6144, 6656, 6784].getD l 0 +
      2 ^ [12, 11, 9, 7, 4].getD l 0 → M.k (x0 + j) = M.k (I.xs + j) := fun l hl h1 h2 => by
    have := key l hl (j - [0, 4096, 6144, 6656, 6784].getD l 0) (by omega)
    rwa [Nat.add_assoc, Nat.add_sub_cancel' h1, Nat.add_assoc, Nat.add_sub_cancel' h1] at this
  by_cases k0 : j < 4096
  · exact go 0 (by norm_num) (by simp) (by simp; omega)
  by_cases k1 : j < 6144
  · exact go 1 (by norm_num) (by simp; omega) (by simp; omega)
  by_cases k2 : j < 6656
  · exact go 2 (by norm_num) (by simp; omega) (by simp; omega)
  by_cases k3 : j < 6784
  · exact go 3 (by norm_num) (by simp; omega) (by simp; omega)
  · exact go 4 (by norm_num) (by simp; omega) (by simp; omega)


/-- Group `d`'s block of `n` chains in `stepsC`: its length and its places (proof help for `stepsC_at`). -/
private theorem blkC (d : Nat) : ∀ n,
    ((List.range n).flatMap fun k => (List.range (3 - d)).map fun t => (d, k, t)).length = (3 - d) * n ∧
    ∀ k < n, ∀ t < 3 - d,
      ((List.range n).flatMap fun k => (List.range (3 - d)).map fun t => (d, k, t)).getD ((3 - d) * k + t) (0, 0, 0) =
        (d, k, t)
  | 0 => ⟨rfl, fun _ hk => absurd hk (Nat.not_lt_zero _)⟩
  | n + 1 => by
    obtain ⟨hl, hg⟩ := blkC d n
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton]
    refine ⟨by simp only [List.length_append, hl, List.length_map, List.length_range, Nat.mul_succ], fun k hk t ht => ?_⟩
    rcases Nat.lt_succ_iff_lt_or_eq.mp hk with hk | rfl
    · have h1 : (3 - d) * (k + 1) ≤ (3 - d) * n := Nat.mul_le_mul_left _ hk
      rw [Nat.mul_succ] at h1
      rw [List.getD_append _ _ _ _ (by omega), hg k hk t ht]
    · rw [List.getD_append_right _ _ _ _ (by omega), hl, Nat.add_sub_cancel_left,
        List.getD_eq_getElem _ _ (by simpa using ht)]
      simp

/-- **The real steps' places in `stepsC`** (structurally, from the group blocks and `layC`). -/
theorem stepsC_at : ∀ d < 3, ∀ k < (grpC d).length, ∀ t < 3 - d,
    stepsC.toArray.getD (sOffC d + (3 - d) * k + t) (0, 0, 0) = (d, k, t) := by
  intro d hd k hk t ht
  obtain ⟨l0, l1, l2, -, -, -, -, -, -, -, -, -, s1, s2, -⟩ := layC
  have hs0 : sOffC 0 = 0 := rfl
  have e : stepsC = ((List.range (grpC 0).length).flatMap fun k => (List.range (3 - 0)).map fun t => (0, k, t)) ++
      (((List.range (grpC 1).length).flatMap fun k => (List.range (3 - 1)).map fun t => (1, k, t)) ++
      ((List.range (grpC 2).length).flatMap fun k => (List.range (3 - 2)).map fun t => (2, k, t))) := by
    simp only [stepsC, show List.range 3 = [0, 1, 2] from rfl, List.flatMap_cons, List.flatMap_nil, List.append_nil]
  rw [Array.getD_eq_getD_getElem?, List.getElem?_toArray, ← List.getD_eq_getElem?_getD, e]
  have b0 := blkC 0 (grpC 0).length
  have b1 := blkC 1 (grpC 1).length
  have b2 := blkC 2 (grpC 2).length
  rw [l0] at b0; rw [l1] at b1; rw [l2] at b2
  interval_cases d
  · rw [l0] at hk
    rw [List.getD_append _ _ _ _ (by rw [l0, b0.1]; omega), hs0, Nat.zero_add, l0]; exact b0.2 k hk t ht
  · rw [l1] at hk
    rw [List.getD_append_right _ _ _ _ (by rw [l0, b0.1]; omega), l0, b0.1, s1,
      List.getD_append _ _ _ _ (by rw [l1, b1.1]; omega), show 108 + (3 - 1) * k + t - (3 - 0) * 36 = (3 - 1) * k + t by omega, l1]
    exact b1.2 k hk t ht
  · rw [l2] at hk
    rw [List.getD_append_right _ _ _ _ (by rw [l0, b0.1]; omega), l0, b0.1, s2,
      List.getD_append_right _ _ _ _ (by rw [l1, b1.1]; omega), l1, b1.1,
      show 174 + (3 - 2) * k + t - (3 - 0) * 36 - (3 - 1) * 33 = (3 - 2) * k + t by omega, l2]
    exact b2.2 k hk t ht

theorem gOffC_succ (d : Nat) : gOffC (d + 1) = gOffC d + (grpC d).length := by
  simp [gOffC, List.range_succ]

theorem mem_grpC {x d : Nat} : x ∈ grpC d ↔ x < 133 ∧ dLeaf.getD x 0 = d := by
  simp [grpC]

private theorem getD_mem {l : List Nat} {p : Nat} (h : p < l.length) : l.getD p 0 ∈ l := by
  rw [List.getD_eq_getElem _ _ h]; exact List.getElem_mem h

/-- Position `p` of group `d` in `permC` holds the group's chain `p − gOffC d`. -/
theorem permC_getD {d p : Nat} (hd : d < 4) (h1 : gOffC d ≤ p) (h2 : p < gOffC d + (grpC d).length) :
    permC.getD p 0 = (grpC d).getD (p - gOffC d) 0 := by
  have g1 : gOffC 1 = (grpC 0).length :=
    (gOffC_succ 0).trans (by rw [show gOffC 0 = 0 from rfl, Nat.zero_add])
  have g2 : gOffC 2 = gOffC 1 + (grpC 1).length := gOffC_succ 1
  have g3 : gOffC 3 = gOffC 2 + (grpC 2).length := gOffC_succ 2
  have g0 : gOffC 0 = 0 := rfl
  rw [permC]
  simp only [List.getD_eq_getElem?_getD]
  interval_cases d
  · rw [List.getElem?_append_left (by simp; omega), List.getElem?_append_left (by simp; omega),
      List.getElem?_append_left (by omega), g0, Nat.sub_zero]
  · rw [List.getElem?_append_left (by simp; omega), List.getElem?_append_left (by simp; omega),
      List.getElem?_append_right (by omega), g1]
  · rw [List.getElem?_append_left (by simp; omega), List.getElem?_append_right (by simp; omega)]
    simp only [List.length_append]; rw [g2, g1]
  · rw [List.getElem?_append_right (by simp; omega)]
    simp only [List.length_append]; rw [g3, g2, g1]

private theorem dLeaf_le : ∀ x ∈ dLeaf, x ≤ 3 := by decide +kernel

/-- **Chain `i`'s place**: `posC i` lies in the group of `i`'s digit, and `permC` holds `i` there. -/
theorem posC_spec {i : Nat} (hi : i < 133) :
    dLeaf.getD i 0 ≤ 3 ∧ gOffC (dLeaf.getD i 0) ≤ posC i ∧
      posC i < gOffC (dLeaf.getD i 0) + (grpC (dLeaf.getD i 0)).length ∧ permC.getD (posC i) 0 = i := by
  have hd : dLeaf.getD i 0 ≤ 3 := by
    rw [List.getD_eq_getElem _ _ (by simp [dLeaf]; omega)]
    exact dLeaf_le _ (List.getElem_mem _)
  have hm : i ∈ permC := by
    have : i ∈ grpC (dLeaf.getD i 0) := mem_grpC.mpr ⟨hi, rfl⟩
    rw [permC, List.mem_append, List.mem_append, List.mem_append]
    interval_cases h : dLeaf.getD i 0 <;> simp_all
  have hlt : posC i < permC.length := List.idxOf_lt_length_iff.mpr hm
  have hget : permC.getD (posC i) 0 = i := by
    rw [List.getD_eq_getElem _ _ hlt]; exact List.getElem_idxOf hlt
  obtain ⟨l0, l1, l2, l3, -⟩ := layC
  have g1 : gOffC 1 = (grpC 0).length :=
    (gOffC_succ 0).trans (by rw [show gOffC 0 = 0 from rfl, Nat.zero_add])
  have g2 : gOffC 2 = gOffC 1 + (grpC 1).length := gOffC_succ 1
  have g3 : gOffC 3 = gOffC 2 + (grpC 2).length := gOffC_succ 2
  have g4 : gOffC 4 = gOffC 3 + (grpC 3).length := gOffC_succ 3
  have g0 : gOffC 0 = 0 := rfl
  have hlen : permC.length = (grpC 0).length + (grpC 1).length + (grpC 2).length + (grpC 3).length := by
    simp [permC, Nat.add_assoc]
  -- the group of the position
  have key : ∀ e < 4, gOffC e ≤ posC i → posC i < gOffC e + (grpC e).length → dLeaf.getD i 0 = e := by
    intro e he h1 h2
    have := getD_mem (l := grpC e) (p := posC i - gOffC e) (by omega)
    rw [← permC_getD he h1 h2, hget] at this
    exact (mem_grpC.mp this).2
  refine ⟨hd, ?_⟩
  by_cases c0 : posC i < gOffC 1
  · rw [key 0 (by norm_num) (by omega) (by omega)]; exact ⟨by omega, by omega, hget⟩
  by_cases c1 : posC i < gOffC 2
  · rw [key 1 (by norm_num) (by omega) (by omega)]; exact ⟨by omega, by omega, hget⟩
  by_cases c2 : posC i < gOffC 3
  · rw [key 2 (by norm_num) (by omega) (by omega)]; exact ⟨by omega, by omega, hget⟩
  · rw [key 3 (by norm_num) (by omega) (by omega)]; exact ⟨by omega, by omega, hget⟩

/-- Group `d`'s chain `k` is a chain `< 133` with digit `d`. -/
theorem grp_chain {d k : Nat} (hd : d < 4) (hk : k < (grpC d).length) :
    permC.getD (gOffC d + k) 0 < 133 ∧ dLeaf.getD (permC.getD (gOffC d + k) 0) 0 = d := by
  rw [permC_getD hd (by omega) (by omega), Nat.add_sub_cancel_left]
  exact mem_grpC.mp (getD_mem hk)



/-- **A real step of the walk** (group `d`, chain `k` of the group, step `t`): its `KS` row's digest is the WOTS step
`d + t` of chain `permC[gOffC d + k]` on the step input's word cells. -/
theorem stepC_digest {c : Ctx} {M : Mem} {I : SigIn} {pa : LoopOut} {Zn cT x0 : Nat} {q : Ptr} {d k t : Nat}
    (hks : SigKSinC I M.k) (hbits : SigBitsC I pa M.k) (hZ : M.k Zn = 0)
    (hT : ∀ k < 133, M.k (cT + k) = w64 ((permC.getD k 0).toUInt64 <<< (8 : Nat).toUInt64))
    (hj : (M.k I.sg).val.toNat < 2 ^ 16)
    (hxe : ∀ j < 17 * (nStepRowsC + 48), M.k (x0 + j) = M.k (I.xs + j))
    (hq : q.k = x0 + 17 * gRowC d) (h : SegsHold c M q (loop [gLogC d] (gStepsTplC I Zn cT d) q).2)
    (hd : d < 3) (hk : k < (grpC d).length) (ht : t < 3 - d) :
    digAt M.k (I.ys + 4 * (gRowC d + (3 - d) * k + t)) =
      wotsStep (M.k I.sg).val.toNat (permC.getD (gOffC d + k) 0) (d + t)
        (digOfW (lanesW M.k (fun l => s24wcC I I.ys stepsC.toArray (4 * (sOffC d + (3 - d) * k + t) + l)))) := by
  obtain ⟨l0, l1, l2, -, g0, g1, g2, r1, r2, nS, -, -, s1, s2, sL⟩ := layC
  have hO1 : gOffC 1 = (grpC 0).length :=
    (gOffC_succ 0).trans (by rw [show gOffC 0 = 0 from rfl, Nat.zero_add])
  have hO2 : gOffC 2 = gOffC 1 + (grpC 1).length := gOffC_succ 1
  have hO0 : gOffC 0 = 0 := rfl
  have hR0 : gRowC 0 = 0 := rfl
  have hS0 : sOffC 0 = 0 := rfl
  have hB : k < 2 ^ gLogC d ∧ gRowC d + (3 - d) * k + t < nStepRowsC ∧ gOffC d + k < 133 ∧
      sOffC d + (3 - d) * k + t < stepsC.length := by
    interval_cases d <;> simp only [g0, g1, g2, hR0, r1, r2, nS, hO0, hO1, hO2, l0, l1, l2, hS0, s1, s2, sL] at hk ht ⊢ <;>
      omega
  obtain ⟨hk2, hr, hgk, hidx⟩ := hB
  obtain ⟨st, hp, hdg⟩ := hks.step _ hr
  rw [hdg]
  have hjf : k < 2 ^ ([gLogC d] : List Nat).sum := by simpa using hk2
  have hlen := gStepsTplC_len I Zn cT d
  obtain ⟨L0, L1, Lk, L5, Lz, L16⟩ := stepAt_spec (I := I) (T := oS (cT + gOffC d) 1) (b := 17 * t) h hjf (by rfl) hZ (by rw [hlen]; omega)
    (fun l hl => gStepsTplC_row I Zn cT d ht hl)
  beta_reduce at L0 L1 Lk L5 Lz L16
  set o := (loop [gLogC d] (gStepsTplC I Zn cT d) q).1 with ho
  have hdo : o.dims = [gLogC d] := rfl
  have hlane : ∀ l < 17, lanesW M.k (fun l => I.xs + 17 * (gRowC d + (3 - d) * k + t) + l) l =
      V M (o.cell (17 * t + l) k).n := fun l hl => by
    show (M.k _).val = (M.k _).val
    rw [ho, loop_cellK q (gStepsTplC_allK I Zn cT d) k (by rw [hlen]; omega), hlen, hq,
      show x0 + 17 * gRowC d + (17 * t + l) + 17 * (3 - d) * k = x0 + (17 * (gRowC d + (3 - d) * k + t) + l) by ring,
      hxe _ (by omega)]
    exact congrArg (fun a => (M.k a).val) (by beta_reduce; ring)
  have hbi : V M I.bi = (M.k I.sg).val <<< (8 : Nat).toUInt64 := by
    show (M.k I.bi).val = _; rw [hbits.idx_lo]; rfl
  have hS : stepsC.toArray.getD (sOffC d + (3 - d) * k + t) (0, 0, 0) = (d, k, t) := stepsC_at d hd k hk t ht
  have hoc : ∀ l < 4, s24ocC I stepsC.toArray (4 * (sOffC d + (3 - d) * k + t) + l) =
      I.bx + gBxC d + 8 * (3 - d) * k + 8 * t + 2 * l := fun l hl => by
    rw [s24ocC, show (4 * (sOffC d + (3 - d) * k + t) + l) / 4 = sOffC d + (3 - d) * k + t by omega, hS,
      show (4 * (sOffC d + (3 - d) * k + t) + l) % 4 = l by omega]
  have hy : ∀ l < 4, 4 * (sOffC d + (3 - d) * k + t) + l < 4 * stepsC.length := fun l hl => by omega
  refine step_of_lanes (lane := lanesW M.k (fun l => I.xs + 17 * (gRowC d + (3 - d) * k + t) + l))
    (X := fun k' => OV M o k (oS (I.bx + gBxC d + 8 * t + k') (8 * (3 - d)))) hj (Nat.lt_trans (grp_chain (by omega) hk).1 (by norm_num)) (by omega)
    ?_ (fun l hl => ⟨?_, ?_⟩) (by rw [hlane 0 (by norm_num), L0, hbi])
    (by rw [hlane 1 (by norm_num)]; exact L1)
    (fun k' h1 h2 => by rw [hlane (k' + 1) (by omega), ← Nat.add_assoc]; exact Lk k' h1 h2)
    (by rw [hlane 5 (by norm_num)]; exact L5)
    (fun l h1 h2 => by rw [hlane l (by omega)]; exact Lz l h1 h2) (by rw [hlane 16 (by norm_num)]; exact L16) hp
  · rw [ovS_V hdo hk2 (show cT + gOffC d + 1 * k = cT + (gOffC d + k) by ring)]
    show (M.k (cT + (gOffC d + k))).val ^^^ _ = _
    rw [hT _ hgk]
  · have := (hbits.x _ (hy l hl)).1
    rw [hoc l hl] at this
    rw [ovS_V hdo hk2 (show I.bx + gBxC d + 8 * t + 2 * l + 8 * (3 - d) * k =
      I.bx + gBxC d + 8 * (3 - d) * k + 8 * t + 2 * l by ring)]
    dsimp only [V]; rw [sOut1_val this]; rfl
  · have := (hbits.x _ (hy l hl)).2
    rw [hoc l hl] at this
    rw [ovS_V hdo hk2 (show I.bx + gBxC d + 8 * t + (2 * l + 1) + 8 * (3 - d) * k =
      I.bx + gBxC d + 8 * (3 - d) * k + 8 * t + 2 * l + 1 by ring)]
    dsimp only [V]; rw [sOut1_val this]; rfl


private theorem wotsChain_zero (j i s : Nat) (x : Digest) : wotsChain j i s 0 x = x := rfl

theorem wotsChain_succ' (j i : Nat) : ∀ (n s : Nat) (x : Digest),
    wotsChain j i s (n + 1) x = wotsStep j i (s + n) (wotsChain j i s n x)
  | 0, s, x => rfl
  | n + 1, s, x => by
    rw [wotsChain, wotsChain_succ' j i n (s + 1), wotsChain, show s + 1 + n = s + (n + 1) by omega]

/-- A step input's word cells: the signed value (`t = 0`) or the previous row's digest. -/
theorem s24wcC_at {I : SigIn} {d k t : Nat} (hd : d < 3) (hk : k < (grpC d).length) (ht : t < 3 - d) {l : Nat}
    (hl : l < 4) : s24wcC I I.ys stepsC.toArray (4 * (sOffC d + (3 - d) * k + t) + l) =
      if t = 0 then I.sg + 1 + 4 * (gOffC d + k) + l else I.ys + 4 * (gRowC d + (3 - d) * k + t - 1) + l := by
  rw [s24wcC, show (4 * (sOffC d + (3 - d) * k + t) + l) / 4 = sOffC d + (3 - d) * k + t by omega,
    stepsC_at d hd k hk t ht, show (4 * (sOffC d + (3 - d) * k + t) + l) % 4 = l by omega]

/-- **Chain `i`'s end** from the walk's steps: the chain from `σ`'s value at `posC i`, from `i`'s digit to `3`. -/
theorem chainC_end {v : Nat → FK} {I : SigIn} {j i : Nat} (hi : i < 133)
    (hs : ∀ d < 3, ∀ k < (grpC d).length, ∀ t < 3 - d,
      digAt v (I.ys + 4 * (gRowC d + (3 - d) * k + t)) = wotsStep j (permC.getD (gOffC d + k) 0) (d + t)
        (digOfW (lanesW v (fun l => s24wcC I I.ys stepsC.toArray (4 * (sOffC d + (3 - d) * k + t) + l))))) :
    digOfW (lanesW v (endC I I.ys i)) =
      wotsChain j i (dLeaf.getD i 0) (3 - dLeaf.getD i 0) (digAt v (I.sg + 1 + 4 * posC i)) := by
  obtain ⟨hd3, h1, h2, hget⟩ := posC_spec hi
  have hE : ∀ l, endC I I.ys i l = if dLeaf.getD i 0 = 3 then I.sg + 1 + 4 * posC i + l else
      I.ys + 4 * (gRowC (dLeaf.getD i 0) + (3 - dLeaf.getD i 0) * (posC i - gOffC (dLeaf.getD i 0)) +
        (2 - dLeaf.getD i 0)) + l := fun l => rfl
  generalize dLeaf.getD i 0 = d at hd3 h1 h2 hE ⊢
  obtain ⟨k, hp⟩ : ∃ k, posC i = gOffC d + k := ⟨posC i - gOffC d, by omega⟩
  rw [hp, Nat.add_sub_cancel_left] at hE
  rw [hp] at h2 hget ⊢
  have hk : k < (grpC d).length := by omega
  by_cases e3 : d = 3
  · have : lanesW v (endC I I.ys i) = fun l => (v (I.sg + 1 + 4 * (gOffC d + k) + l)).val := by
      funext l; simp only [lanesW, hE, e3, ↓reduceIte]
    rw [this, e3, Nat.sub_self, wotsChain_zero]; rfl
  have hd : d < 3 := by omega
  have key : ∀ t < 3 - d, digAt v (I.ys + 4 * (gRowC d + (3 - d) * k + t)) =
      wotsChain j i d (t + 1) (digAt v (I.sg + 1 + 4 * (gOffC d + k))) := by
    intro t ht
    induction t with
    | zero =>
      have hin : digOfW (lanesW v (fun l => s24wcC I I.ys stepsC.toArray (4 * (sOffC d + (3 - d) * k + 0) + l))) =
          digAt v (I.sg + 1 + 4 * (gOffC d + k)) := digOfW_congr fun l hl => by
        simp only [lanesW, s24wcC_at hd hk ht hl, ↓reduceIte]
      rw [hs d hd k hk 0 ht, hget, hin, wotsChain_succ' j i 0 d, wotsChain_zero]
    | succ t ih =>
      have hin : digOfW (lanesW v (fun l => s24wcC I I.ys stepsC.toArray (4 * (sOffC d + (3 - d) * k + (t + 1)) + l))) =
          digAt v (I.ys + 4 * (gRowC d + (3 - d) * k + t)) := digOfW_congr fun l hl => by
        simp only [lanesW, s24wcC_at hd hk ht hl, Nat.add_one_ne_zero, ↓reduceIte]
        rw [show gRowC d + (3 - d) * k + (t + 1) - 1 = gRowC d + (3 - d) * k + t by omega]
      rw [hs d hd k hk (t + 1) ht, hget, hin, ih (by omega), wotsChain_succ' j i (t + 1) d]
  have : lanesW v (endC I I.ys i) = fun l => (v (I.ys + 4 * (gRowC d + (3 - d) * k + (2 - d)) + l)).val := by
    funext l; simp only [lanesW, hE, e3, ↓reduceIte]
  have hk2 := key (2 - d) (by omega)
  rw [show 2 - d + 1 = 3 - d by omega] at hk2
  rw [this]
  exact hk2


/-- **The walk's key leaf** of the chain ends `endC` (`leaf_digest`'s twin; the leaf's lanes are the input array's
from row `nStepRowsC`, equal to the loops `leafA`, `leafB`, `leafC` placed after the steps). -/
theorem leaf_digestC {c : Ctx} {M : Mem} {I : SigIn} {pa : LoopOut} {Zn x0 : Nat} {qa qb qc : Ptr}
    (hks : SigKSinC I M.k) (hbits : SigBitsC I pa M.k) (hZ : M.k Zn = 0)
    (hj : (M.k I.sg).val.toNat < 2 ^ 16)
    (hxe : ∀ j < 17 * (nStepRowsC + 48), M.k (x0 + j) = M.k (I.xs + j))
    (ea : qa.k = x0 + 17 * nStepRowsC) (hla : SegsHold c M qa (loop [] (leafA I) qa).2)
    (eb : qb.k = x0 + 17 * nStepRowsC + 2) (hlb : SegsHold c M qb (loop [9] (leafB I) qb).2)
    (ec : qc.k = x0 + 17 * nStepRowsC + 514) (hlc : SegsHold c M qc (loop [] (leafC I Zn) qc).2) :
    digAt M.k I.yc = wotsLeaf (M.k I.sg).val.toNat
      ((List.range wotsLen).map fun i => digOfW (lanesW M.k (endC I I.ys i))) := by
  obtain ⟨sIn, sOut, hstart, hperm, hlink, hdig⟩ := hks.leaf
  rw [hdig]
  have hx : ∀ m < 544, (M.k (I.xs + 17 * nStepRowsC + m)).val = (M.k (x0 + 17 * nStepRowsC + m)).val :=
    fun m hm => by rw [Nat.add_assoc, Nat.add_assoc, hxe _ (by omega)]
  have hEk : ∀ k < 532, (M.k (I.be + 2 * k)).val = (M.k (endC I I.ys (k / 4) (k % 4))).val <<< (8 : Nat).toUInt64 ∧
      (M.k (I.be + 2 * k + 1)).val = (M.k (endC I I.ys (k / 4) (k % 4))).val >>> (56 : Nat).toUInt64 := by
    intro k hk
    have := hbits.e (k / 4) (by omega) (k % 4) (by omega)
    rw [show 2 * (4 * (k / 4) + k % 4) = 2 * k by omega] at this
    exact ⟨sOut1_val this.1, sOut1_val this.2⟩
  have hbi : (M.k I.bi).val = (M.k I.sg).val <<< (8 : Nat).toUInt64 := by rw [hbits.idx_lo]; rfl
  obtain ⟨A0, A1⟩ := leafA_spec hla (jf := 0) (by simp)
  have hB : ∀ m < 512, V M ((loop [9] (leafB I) qb).1.cell 0 m).n =
      V M (I.be + 2 * m + 1) ^^^ V M (I.be + 2 * (m + 1)) := fun m hm => leafB_spec hlb (by simpa using hm)
  obtain ⟨C1, C2, C3, C4⟩ := leafC_spec hlc (jf := 0) (by simp) hZ
  beta_reduce at C1 C2 C3 C4
  dsimp only [V] at A0 A1 hB C1 C2 C3 C4
  have ca : ∀ m < 2, ((loop [] (leafA I) qa).1.cell m 0).n = x0 + 17 * nStepRowsC + m := fun m hm => by
    rw [loop_cellK _ (leafA_allK I) _ (by simp [leafA]; omega), ea]; simp
  have cb : ∀ m, ((loop [9] (leafB I) qb).1.cell 0 m).n = x0 + 17 * nStepRowsC + (2 + m) := fun m => by
    rw [loop_cellK _ (leafB_allK I) _ (by simp [leafB]), eb]; simp [leafB]; omega
  have cc : ∀ k < 30, ((loop [] (leafC I Zn) qc).1.cell k 0).n = x0 + 17 * nStepRowsC + (514 + k) := fun k hk => by
    rw [loop_cellK _ (leafC_allK I Zn) _ (by rw [leafC_len]; omega), ec]; omega
  refine leaf_of_lanes (lane := fun m => (M.k (I.xs + 17 * nStepRowsC + m)).val)
    (E := fun k => (M.k (endC I I.ys (k / 4) (k % 4))).val) hj ?_ ?_ (fun m h1 h2 => ?_) ?_
    (fun l h1 h2 => ?_) ?_ (by simp [wotsLen]) (fun i hi k hk => ?_) hstart (fun u hu => ?_) hlink
  · rw [hx 0 (by norm_num), ← ca 0 (by norm_num), A0, hbi]
  · rw [hx 1 (by norm_num), ← ca 1 (by norm_num), A1]; exact (hEk 0 (by norm_num)).1
  · rw [hx m (by omega)]
    by_cases hm : m < 514
    · rw [show x0 + 17 * nStepRowsC + m = x0 + 17 * nStepRowsC + (2 + (m - 2)) by omega, ← cb, hB (m - 2) (by omega),
        show m - 2 + 1 = m - 1 by omega]
      exact congrArg₂ _ (hEk (m - 2) (by omega)).2 (hEk (m - 1) (by omega)).1
    · rw [show x0 + 17 * nStepRowsC + m = x0 + 17 * nStepRowsC + (514 + (m - 514)) by omega, ← cc _ (by omega),
        C1 (m - 514) (by omega), show 512 + (m - 514) = m - 2 by omega, show 513 + (m - 514) = m - 1 by omega]
      exact congrArg₂ _ (hEk (m - 2) (by omega)).2 (hEk (m - 1) (by omega)).1
  · rw [hx 533 (by norm_num), show x0 + 17 * nStepRowsC + 533 = x0 + 17 * nStepRowsC + (514 + 19) by omega,
      ← cc 19 (by norm_num), C2]
    exact congrArg (· ^^^ _) (hEk 531 (by norm_num)).2
  · rw [hx l (by omega), show x0 + 17 * nStepRowsC + l = x0 + 17 * nStepRowsC + (514 + (l - 514)) by omega,
      ← cc _ (by omega)]
    exact C3 (l - 514) (by omega) (by omega)
  · rw [hx 543 (by norm_num), show x0 + 17 * nStepRowsC + 543 = x0 + 17 * nStepRowsC + (514 + 29) by omega,
      ← cc 29 (by norm_num), C4]
  · simp only [List.getElem_map, List.getElem_range]
    rw [digOfW_get _ hk, show (4 * i + k / 8) / 4 = i by omega, show (4 * i + k / 8) % 4 = k / 8 by omega]
    rfl
  · have := hperm u hu
    have e : lanesW M.k (fun l => I.xs + 17 * (nStepRowsC + u) + l) =
        fun l => (M.k (I.xs + 17 * nStepRowsC + (17 * u + l))).val := by
      funext l; simp only [lanesW]; congr 2; ring
    rwa [e] at this


/-- **A path node** of the walk (level `t`; `node_digest`'s twin on the input array). -/
theorem node_digestC {c : Ctx} {M : Mem} {I : SigIn} {pa : LoopOut} {Zn x0 : Nat} {r : Ptr}
    (hks : SigKSinC I M.k) (hbits : SigBitsC I pa M.k) (hZ : M.k Zn = 0)
    (hxe : ∀ j < 17 * (nStepRowsC + 48), M.k (x0 + j) = M.k (I.xs + j))
    (er : r.k = x0 + 17 * (nStepRowsC + 32))
    (h : SegsHold c M r (loop [4] (twoLanes Zn 0x4D I.bp (I.bp + 8) 16) r).2) {t : Nat} (ht : t < 16) :
    digAt M.k (I.yc + 4 * (t + 1)) = sigNode (digOfW fun l => (M.k (pa.cell (4 + l) t).n).val)
      (digOfW fun l => (M.k (pa.cell (8 + l) t).n).val) := by
  obtain ⟨st, hp, hd⟩ := hks.path t ht
  rw [hd]
  have hjf : t < 2 ^ ([4] : List Nat).sum := by simpa using ht
  have ht4 : t < 2 ^ 4 := by simpa using ht
  have hd4 := loop_dims_eq [4] (twoLanes Zn 0x4D I.bp (I.bp + 8) 16) r
  obtain ⟨L0, Lk, L4, Lb, L8, Lz, L16⟩ := two_spec h hjf hZ
  beta_reduce at L0 Lk L4 Lb L8 Lz L16
  have hlane : ∀ l < 17, lanesW M.k (fun l => I.xs + 17 * (nStepRowsC + 32 + t) + l) l =
      V M ((loop [4] (twoLanes Zn 0x4D I.bp (I.bp + 8) 16) r).1.cell l t).n := fun l hl => by
    show (M.k _).val = (M.k _).val
    rw [loop_cellK _ (twoLanes_allK _ _ _ _ _) _ (by rw [twoLanes_len]; omega), twoLanes_len, er,
      show x0 + 17 * (nStepRowsC + 32) + l + 17 * t = x0 + (17 * (nStepRowsC + 32 + t) + l) by omega,
      hxe _ (by omega)]
    exact congrArg (fun a => (M.k a).val) (by beta_reduce; omega)
  refine node_of_lanes (lane := lanesW M.k (fun l => I.xs + 17 * (nStepRowsC + 32 + t) + l))
    (A := fun k => OV M (loop [4] (twoLanes Zn 0x4D I.bp (I.bp + 8) 16) r).1 t (oS (I.bp + k) 16))
    (B := fun k => OV M (loop [4] (twoLanes Zn 0x4D I.bp (I.bp + 8) 16) r).1 t (oS (I.bp + 8 + k) 16))
    (fun l hl => ⟨?_, ?_⟩) (fun l hl => ⟨?_, ?_⟩) (by rw [hlane 0 (by norm_num)]; exact L0)
    (fun k h1 h2 => by rw [hlane k (by omega)]; exact Lk k h1 h2) (by rw [hlane 4 (by norm_num)]; exact L4)
    (fun k h1 h2 => by rw [hlane (4 + k) (by omega)]; exact Lb k h1 h2) (by rw [hlane 8 (by norm_num)]; exact L8)
    (fun l h1 h2 => by rw [hlane l (by omega)]; exact Lz l h1 h2) (by rw [hlane 16 (by norm_num)]; exact L16)
    hp
  · have := (hbits.p t ht 0 (by norm_num) l hl).1
    simp only [Nat.mul_zero, Nat.add_zero] at this
    rw [ovS_V hd4 ht4 (show I.bp + 2 * l + 16 * t = I.bp + 2 * (8 * t + l) by ring)]
    dsimp only [V]; rw [sOut1_val this]; rfl
  · have := (hbits.p t ht 0 (by norm_num) l hl).2
    simp only [Nat.mul_zero, Nat.add_zero] at this
    rw [ovS_V hd4 ht4 (show I.bp + (2 * l + 1) + 16 * t = I.bp + 2 * (8 * t + l) + 1 by ring)]
    dsimp only [V]; rw [sOut1_val this]; rfl
  · have := (hbits.p t ht 1 (by norm_num) l hl).1
    rw [show 4 + 4 * 1 + l = 8 + l by ring] at this
    rw [ovS_V hd4 ht4 (show I.bp + 8 + 2 * l + 16 * t = I.bp + 2 * (8 * t + 4 * 1 + l) by ring)]
    dsimp only [V]; rw [sOut1_val this]; rfl
  · have := (hbits.p t ht 1 (by norm_num) l hl).2
    rw [show 4 + 4 * 1 + l = 8 + l by ring] at this
    rw [ovS_V hd4 ht4
      (show I.bp + 8 + (2 * l + 1) + 16 * t = I.bp + 2 * (8 * t + 4 * 1 + l) + 1 by ring)]
    dsimp only [V]; rw [sOut1_val this]; rfl

/-- `idx < 2^16` from the gated `shr 16` output. -/
theorem idx_ltC {c : Ctx} {M : Mem} {I : SigIn} {pa : LoopOut} {q : Ptr}
    (has : Ok c M (assert0 (kc (I.bi + 17)) (kc I.flag)) q) (hg : M.k I.flag = 1)
    (hbits : SigBitsC I pa M.k) : (M.k I.sg).val.toNat < 2 ^ 16 := by
  have a := ok_assert0 (a := kc (I.bi + 17)) rfl has
  rw [hg, one_mul] at a
  have hb := hbits.idx_hi
  unfold Out1 at hb
  rw [a] at hb
  have hw : (M.k I.sg).val >>> (16 : Nat).toUInt64 = 0 := (congrArg FK.val hb).symm
  have := congrArg UInt64.toNat hw
  simp only [UInt64.toNat_shiftRight, Nat.shiftRight_eq_div_pow, UInt64.toNat_zero] at this
  have h16 : (16 : Nat).toUInt64.toNat % 64 = 16 := by decide
  rw [h16] at this
  exact Nat.lt_of_div_eq_zero (by norm_num) this


/-- The step-input class's outputs, for any array of steps `S`. -/
theorem s24C_outs (v : ℕ → FK) (I : SigIn) (S : Array (Nat × Nat × Nat)) (pl : Nat → Bool × Nat) (Ss : List BSpec)
    (hB : (⟨clogC (4 * S.size), 4 * S.size, [.shl 24, .shr 40], true, s24wcC I I.ys S, fun j x => s24ocC I S x + j,
      pl, 2, by intros; omega⟩ : BSpec) ∈ Ss)
    (hws : ∀ B ∈ Ss, ∀ y < B.n, ∃ w : FK, (B.rd = true → v (B.wc y) = w) ∧
      ∀ j < B.outs.length, (B.out j).Valid → v (B.oc j y) = ⟨(B.out j).word w.val⟩) :
    ∀ y < 4 * S.size, Out1 v (s24wcC I I.ys S y) (.shl 24) (s24ocC I S y) ∧
      Out1 v (s24wcC I I.ys S y) (.shr 40) (s24ocC I S y + 1) := by
  intro y hy
  obtain ⟨w, h1, h2⟩ := hws _ hB y hy
  have e0 := h2 0 (by simp) (by simp [BSpec.out, BOut.Valid])
  have e1 := h2 1 (by simp) (by simp [BSpec.out, BOut.Valid])
  have hw := h1 rfl
  simp only [BSpec.out] at e0 e1 hw
  refine ⟨?_, ?_⟩ <;> unfold Out1
  · rw [show s24ocC I S y = s24ocC I S y + 0 from rfl, e0, hw]; rfl
  · rw [e1, hw]; rfl

end LeafC

/-- `dLeaf_eq` through the library's word-level `traceDigestF` (proof help: one fast Keccak in the kernel). -/
private theorem dLeaf_eqF : dLeaf = wotsDigits (traceDigest []) := by
  rw [← RecursionFast.traceDigestF_eq]
  decide +kernel

open Lvm.QSig.SigH in
/-- **SLF-STMT 4** (owner C): **the specialised walk is sound**: with the gate on, `Zn` zero, its `KS` rows and `BITS`
outputs, the cells from `I.sg` (chain values in `permC` order) are a signature of `traceDigest []` under the key in
the cells `I.vk`. -/
theorem qSigLeaf_sound {c : Ctx} {M : Mem} {p : Ptr} {I : SigIn} {Zn : Nat} (h : Ok c M (qsigC I Zn) p)
    (hg : M.k I.flag = 1) (hZ : M.k Zn = 0) (hks : SigKSinC I M.k) (hbits : SigBitsC I (qsigC I Zn p).1.pa M.k) :
    SigOk (digAt M.k I.vk) (traceDigest []) (sigAtP M.k I.sg) = true := by
  obtain ⟨hT, ⟨qp, hpa, epa⟩, ⟨qr, hro⟩, ⟨qi, has⟩, hgs, ⟨qa, ea, hla⟩, ⟨qb, eb, hlb⟩, ⟨qc, ec, hlc⟩,
    ⟨qx, ex, hxp⟩, ⟨qq, hxq⟩⟩ := qsigC_parts h
  have hxe := gXeqC_spec hxq hg
  generalize (qsigC I Zn p).1 = o at *
  have hj := idx_ltC has hg hbits
  have hs : ∀ d < 3, ∀ k < (grpC d).length, ∀ t < 3 - d,
      digAt M.k (I.ys + 4 * (gRowC d + (3 - d) * k + t)) = wotsStep (M.k I.sg).val.toNat
        (permC.getD (gOffC d + k) 0) (d + t)
        (digOfW (lanesW M.k (fun l => s24wcC I I.ys stepsC.toArray (4 * (sOffC d + (3 - d) * k + t) + l)))) :=
    fun d hd k hk t ht => by
      obtain ⟨q, eq, hq⟩ := hgs d hd
      exact stepC_digest hks hbits hZ hT hj hxe eq hq.1 hd hk ht
  have hdig : ∀ i (hi : i < (wotsDigits (traceDigest [])).length),
      (wotsDigits (traceDigest []))[i] = dLeaf.getD i 0 := fun i hi => by
    rw [List.getElem_of_eq dLeaf_eqF.symm hi, List.getD_eq_getElem]
  refine wots_sound (σ := sigAtP M.k I.sg) (by simpa [sigAtP, sigHeight] using hj) (by simp [sigAtP]) (by simp [sigAtP])
    (ends := (List.range wotsLen).map fun i => digOfW (lanesW M.k (endC I I.ys i))) (by simp)
    (fun i hi => ?_) (cur := fun t => digAt M.k (I.yc + 4 * t)) ?_ (fun t ht => ?_) ?_
  · -- one chain
    simp only [sigAtP, List.getElem_map, List.getElem_range, hdig]
    exact chainC_end (by simpa [wotsLen] using hi) hs
  · -- the leaf
    show digAt M.k (I.yc + 4 * 0) = _
    rw [Nat.mul_zero, Nat.add_zero]
    exact leaf_digestC hks hbits hZ hj hxe ea hla.1 eb hlb.1 ec hlc.1
  · -- the walk
    have ht' : t < 16 := by simpa [sigAtP, sigHeight] using ht
    show digAt M.k (I.yc + 4 * (t + 1)) = _
    rw [node_digestC hks hbits hZ hxe ex hxp.1 ht']
    have hb := hbits.idx_bit t ht'
    unfold Out1 at hb
    have hbool : M.k (I.bi + 1 + t) = 0 ∨ M.k (I.bi + 1 + t) = 1 := by
      rw [hb]; exact bit_bool _ (by omega)
    have hA : (digOfW fun l => (M.k (o.pa.cell (4 + l) t).n).val) =
        if M.k (I.bi + 1 + t) = 1 then digAt M.k (I.sg + 533 + 4 * t) else digAt M.k (I.yc + 4 * t) :=
      digOfW_ite fun l hl => by
        rw [← epa, (path_spec hpa.1 ht' hl hbool).1]
        split_ifs <;> exact kval_congr M (by omega)
    have hB : (digOfW fun l => (M.k (o.pa.cell (8 + l) t).n).val) =
        if M.k (I.bi + 1 + t) = 1 then digAt M.k (I.yc + 4 * t) else digAt M.k (I.sg + 533 + 4 * t) :=
      digOfW_ite fun l hl => by
        rw [← epa, (path_spec hpa.1 ht' hl hbool).2]
        split_ifs <;> exact kval_congr M (by omega)
    have key : M.k (I.bi + 1 + t) = 1 ↔ ¬ ((M.k I.sg).val.toNat / 2 ^ t % 2 = 0) := by
      rw [hb, w64_bit _ (by omega), ubit_testBit, Nat.testBit_eq_decide_div_mod_eq]
      have h01 : ¬ ((0 : FK) = 1) := by decide
      by_cases hq : (M.k I.sg).val.toNat / 2 ^ t % 2 = 1
      · simp [hq]
      · simp [hq, h01]
    simp only [sigAtP, List.getElem_map, List.getElem_range]
    rw [hA, hB]
    by_cases hc : M.k (I.bi + 1 + t) = 1
    · have := key.mp hc
      simp only [hc, ↓reduceIte, this]
    · have : (M.k I.sg).val.toNat / 2 ^ t % 2 = 0 := by
        by_contra hn; exact hc (key.mpr hn)
      simp only [hc, ↓reduceIte, this]
  · -- the root
    show digAt M.k (I.yc + 4 * 16) = digAt M.k I.vk
    unfold digAt
    exact digOfW_congr fun l hl => by
      obtain ⟨q', hq'⟩ := ok_forN hro l hl
      rw [show I.yc + 4 * 16 + l = I.yc + 64 + l by ring, ok_assertEq hq' hg]

/-- **SLF-STMT 4b** (owner C): **`SigBitsC` from the classes' outputs** (`sigBits_of_outs`'s twin on `sigSpecsC`). -/
theorem sigBitsC_of_outs (v : ℕ → FK) (I : SigIn) (pa : LoopOut) (bpl : Nat → Nat → Bool × Nat) (Ss : List BSpec)
    (hT : ∀ B ∈ sigSpecsC I I.ys pa bpl, B ∈ Ss)
    (hws : ∀ B ∈ Ss, ∀ y < B.n, ∃ w : FK, (B.rd = true → v (B.wc y) = w) ∧
      ∀ j < B.outs.length, (B.out j).Valid → v (B.oc j y) = ⟨(B.out j).word w.val⟩) :
    SigBitsC I pa v := by
  have o1 : ∀ (B : BSpec), B ∈ Ss → B.rd = true → ∀ (y j : ℕ), y < B.n → j < B.outs.length →
      ∀ {A Bc : ℕ} {b : BOut}, B.wc y = A → B.oc j y = Bc → B.out j = b → b.Valid → Out1 v A b Bc := by
    intro B hB hrd y j hy hj A Bc b hA hBc hb hv
    obtain ⟨w, h1, h2⟩ := hws B hB y hy
    have := h2 j hj (hb ▸ hv)
    unfold Out1
    rw [← hA, ← hBc, this, h1 hrd, hb]
  have tI := hT _ (List.mem_cons_self ..)
  have t24 := s24C_outs v I stepsC.toArray (bpl 1) Ss (hT _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))) hws
  have t8 := hT _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)))
  refine ⟨?_, fun z hz => ?_, ?_, fun y hy => ⟨?_, ?_⟩, fun i hi l hl => ⟨?_, ?_⟩, fun t ht u hu l hl => ⟨?_, ?_⟩⟩
  · exact o1 _ tI rfl 0 0 (by simp [SigBits.sIdx]) (by simp [SigBits.sIdx]) rfl (by simp [SigBits.sIdx]) rfl
      (by simp [BOut.Valid])
  · exact o1 _ tI rfl 0 (1 + z) (by simp [SigBits.sIdx]) (by simp [SigBits.sIdx]; omega) rfl
      (by simp [SigBits.sIdx]; omega) (SigBits.getD_idx hz) (show z < 64 by omega)
  · exact o1 _ tI rfl 0 17 (by simp [SigBits.sIdx]) (by simp [SigBits.sIdx]) rfl (by simp [SigBits.sIdx]) rfl
      (by simp [BOut.Valid])
  · exact (t24 y (by rw [List.size_toArray]; exact hy)).1
  · exact (t24 y (by rw [List.size_toArray]; exact hy)).2
  · exact o1 _ t8 rfl (4 * i + l) 0 (by simp only; omega) (by simp)
      (by simp only; rw [if_pos (by omega), show (4 * i + l) / 4 = i by omega, show (4 * i + l) % 4 = l by omega])
      (by simp only; rw [if_pos (by omega)] <;> omega) rfl (by simp [BOut.Valid])
  · exact o1 _ t8 rfl (4 * i + l) 1 (by simp only; omega) (by simp)
      (by simp only; rw [if_pos (by omega), show (4 * i + l) / 4 = i by omega, show (4 * i + l) % 4 = l by omega])
      (by simp only; rw [if_pos (by omega)] <;> omega) rfl (by simp [BOut.Valid])
  · exact o1 _ t8 rfl (532 + (8 * t + 4 * u + l)) 0 (by simp only; omega) (by simp)
      (by simp only; rw [if_neg (by omega), Nat.add_sub_cancel_left,
        show (8 * t + 4 * u + l) / 4 % 2 = u by omega, show (8 * t + 4 * u + l) % 4 = l by omega,
        show (8 * t + 4 * u + l) / 8 = t by omega])
      (by simp only; rw [if_neg (by omega)] <;> omega) rfl (by simp [BOut.Valid])
  · exact o1 _ t8 rfl (532 + (8 * t + 4 * u + l)) 1 (by simp only; omega) (by simp)
      (by simp only; rw [if_neg (by omega), Nat.add_sub_cancel_left,
        show (8 * t + 4 * u + l) / 4 % 2 = u by omega, show (8 * t + 4 * u + l) % 4 = l by omega,
        show (8 * t + 4 * u + l) / 8 = t by omega])
      (by simp only; rw [if_neg (by omega)] <;> omega) rfl (by simp [BOut.Valid])

-- STEP

end Lvm.QSig
