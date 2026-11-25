import LvmQSigDefs

-- ===== merged from `LvmQSigChild` (GOLF module merge: `LvmQSigChild.lean` is now a stub importing `LvmQSigSound`) =====
section

/-!
# `Q_sig`: the child's header checks (`ChildOk`)

New for lvm (WP-12). See `LvmQSigDefs` for the hypotheses.
-/

set_option autoImplicit false

namespace Lvm.QSig

open RecursionFast RecursionFast.Keccak Lvm Lvm.Loop Lvm.Loop.Build Lvm.Bits Lvm.KSponge Lvm.Wots

/-! ## Helpers -/

theorem out1_val {v : Nat → FK} {w : Nat} {b : BOut} {c : Nat} (h : Out1 v w b c) :
    (v c).val = b.word (v w).val := by rw [h]

theorem digAt_congr {v : Nat → FK} {a b : Nat} (h : ∀ l < 4, v (a + l) = v (b + l)) :
    digAt v a = digAt v b := by
  unfold digAt digOfW
  congr 1; funext k
  dsimp only
  rw [h (k.val / 8) (by (clear * -; first | decide | (simp only [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]; done) | ring1 | (clear * - k; omega)))]

theorem digAt_zero {v : Nat → FK} {a : Nat} (h : ∀ l < 4, v (a + l) = 0) : digAt v a = zeroDig := by
  apply Vector.ext; intro k hk
  rw [digAt, digOfW_get _ hk, h _ (by (clear * - hk; omega))]
  simp only [zeroDig, Vector.getElem_replicate]
  exact byteW_zero _

theorem ov_oS_nil (M : Mem) (o : LoopOut) (hd : o.dims = []) (n s : Nat) :
    ov M o 0 (oS n s) = M.k n := by
  simp [ov, Opd.resolve, Addr.at, dot, hd, unflat]

theorem w64_inj {a b : UInt64} (h : w64 a = w64 b) : a = b := congrArg FK.val h

/-- `n'`'s range from its `BITS` fields (WP-11b-QL: for any bound `2^ln`, `1 ≤ ln ≤ 62`). -/
theorem n_range (w : UInt64) (ln : Nat) (hln : 1 ≤ ln ∧ ln ≤ 62) (htop : w >>> (ln + 1 : Nat).toUInt64 = 0)
    (hmul : w64 ((w >>> (ln : Nat).toUInt64) &&& 1) * w64 (w <<< (64 - ln : Nat).toUInt64) = 0)
    (hz : ∃ z ≤ ln, (w >>> z.toUInt64) &&& 1 = 1) : 1 ≤ w.toNat ∧ w.toNat ≤ 2 ^ ln := by
  have hs : ∀ n, n < 64 → (n.toUInt64).toNat % 64 = n := fun n hn => by
    rw [Nat.toUInt64_eq, UInt64.toNat_ofNat']; (clear * - hz hn; omega)
  have t1 := congrArg UInt64.toNat htop
  rw [UInt64.toNat_shiftRight, hs _ (by (clear * - hln hz; omega)), Nat.shiftRight_eq_div_pow] at t1
  have hlt : w.toNat < 2 ^ (ln + 1) := by
    rw [UInt64.toNat_zero, Nat.div_eq_zero_iff] at t1
    rcases t1 with h | h
    · exact absurd h (Nat.two_pow_pos _).ne'
    · exact h
  obtain ⟨z, hzl, hz⟩ := hz
  have t2 := congrArg UInt64.toNat hz
  rw [UInt64.toNat_and, UInt64.toNat_shiftRight, hs _ (by (clear * - hln hzl; omega)), Nat.shiftRight_eq_div_pow] at t2
  refine ⟨?_, ?_⟩
  · rcases Nat.eq_zero_or_pos w.toNat with h0 | h0
    · rw [h0, Nat.zero_div] at t2; simp at t2
    · exact h0
  have hp : 2 ^ (ln + 1) = 2 * 2 ^ ln := by rw [Nat.pow_succ, Nat.mul_comm]
  rcases mul_eq_zero.mp hmul with h | h
  · have t3 := congrArg UInt64.toNat (w64_inj (b := 0) h)
    rw [UInt64.toNat_and, UInt64.toNat_shiftRight, hs _ (by (clear * - hln; omega)), Nat.shiftRight_eq_div_pow] at t3
    have t3' : (w.toNat / 2 ^ ln) % 2 = 0 := by simpa [Nat.and_one_is_mod] using t3
    have h2 : w.toNat / 2 ^ ln < 2 := by
      rw [Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _)]; (clear * - hlt; omega)
    have : w.toNat / 2 ^ ln = 0 := by
      generalize w.toNat / 2 ^ ln = d at t3' h2 ⊢; (clear * - t3' h2; omega)
    rw [Nat.div_eq_zero_iff] at this
    rcases this with h | h
    · exact absurd h (Nat.two_pow_pos _).ne'
    · (clear * - h; omega)
  · have t3 := congrArg UInt64.toNat (w64_inj (b := 0) h)
    rw [UInt64.toNat_shiftLeft, hs _ (by (clear * - hln; omega)), Nat.shiftLeft_eq, UInt64.toNat_zero] at t3
    have hd : 2 ^ ln * 2 ^ (64 - ln) ∣ w.toNat * 2 ^ (64 - ln) := by
      rw [← Nat.pow_add, show ln + (64 - ln) = 64 by (clear * - hln; omega)]
      exact Nat.dvd_of_mod_eq_zero (by simpa using t3)
    obtain ⟨c, hc⟩ := Nat.dvd_of_mul_dvd_mul_right (Nat.two_pow_pos _) hd
    have : c < 2 := by
      by_contra hc2
      have : 2 ^ ln * 2 ≤ 2 ^ ln * c := Nat.mul_le_mul_left _ (by (clear * - hc2; omega))
      (clear * - hlt hc this; omega)
    rcases (show c = 0 ∨ c = 1 by (clear * - this; omega)) with rfl | rfl <;> simp at hc <;> (clear * - hlt hc; omega)

/-- **The child's header checks** (A3). -/
theorem qsig_child {c : Ctx} {M : Mem} {p : Ptr} {I : SigIn} (hln : 1 ≤ I.ln ∧ I.ln ≤ 62) (h : Ok c M (qsig I) p)
    (hg : M.k I.flag = 1) (hks : SigKS I (qsig I p).1 M.k) (hbits : SigBits I (qsig I p).1 M.k) :
    ChildOk I M.k := by
  obtain ⟨⟨qP, hP, eP⟩, -, -, -, -, ⟨qH, hH⟩, -, ⟨qS, hS⟩, ⟨qM, hM, eM⟩⟩ := qsig_parts h
  have pre := gPre_spec hP.1
  rw [eP] at pre
  obtain ⟨tZ, tO, eZ, eO, -⟩ := pre
  obtain ⟨hvk, -, hbb, hb0, htop, hmul, hprod, hsel⟩ := header_spec tZ tO hH.1 hH.2 hg eZ eO
  have hsl := gSl_spec hS.1 hS.2 hg
  obtain ⟨-, -, -, -, -, -, ⟨qls, hls, els⟩, ⟨qns, hns, ens⟩⟩ := gMsg_parts hM
  rw [eM] at els ens
  set o := (qsig I p).1 with ho
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
  dsimp only [ChildOk]
  rcases bool_of_idem hbb with hb | hb
  · have hcl : digAt M.k I.cL = digAt M.k I.yls := digAt_congr fun l hl => by
      have := hsel l hl; rw [hb, zero_mul, zero_add] at this; exact this.symm
    rw [hb, z0, ite_eq_left rfl, hcl, hLS]
    refine ⟨Or.inl rfl, digAt_congr hvk, hn.1, hn.2, fun _ => ⟨digAt_zero (hb0 hb), fun k hk => ?_⟩,
      fun h => absurd h (by decide), rfl⟩
    have := hsl k hk; rwa [hb, zero_mul, zero_add] at this
  · have hcl : digAt M.k I.cL = digAt M.k I.yns := digAt_congr fun l hl => by
      have := hsel l hl
      rw [hb, one_mul, add_assoc, FK.add_self, add_zero] at this; exact this.symm
    rw [hb, z1, ite_eq_right (by decide), hcl, hNS, hLS]
    refine ⟨Or.inr rfl, digAt_congr hvk, hn.1, hn.2, fun h => absurd h (by decide),
      fun _ k hk => ?_, rfl⟩
    have := hsl k hk; rw [hb, one_mul] at this
    exact (FK.eq_neg_of_add this).symm

end Lvm.QSig
end
-- ===== end of `LvmQSigChild` =====

-- ===== merged from `LvmQSigSigAux` (GOLF module merge: `LvmQSigSigAux.lean` is now a stub importing `LvmQSigSound`) =====
section

/-!
# `Q_sig`'s signature: helpers (words, digests, one hash per kind, one chain)

New for lvm (WP-12). Helpers of `qsig_sigOk` (`LvmQSigSig`).
-/

set_option autoImplicit false

namespace Lvm.QSig.SigH

open Lvm.QSig RecursionFast RecursionFast.Keccak Lvm Lvm.Loop Lvm.Loop.Build Lvm.Bits Lvm.KSponge Lvm.Wots

/-! ## Words and bits -/

theorem sOut1_val {v : Nat → FK} {w : Nat} {b : BOut} {c : Nat} (h : Out1 v w b c) :
    (v c).val = b.word (v w).val := by rw [h]

theorem bit_word (w : UInt64) {z : Nat} (hz : z < 64) :
    (BOut.bit z).word w = if ubit w z then 1 else 0 := by
  apply u64_ext
  intro i hi
  simp only [BOut.word, ubit_and, ubit_shr _ hz, ubit_one]
  by_cases h : ubit w z <;> by_cases h0 : i = 0 <;> simp_all [ubit_one, ubit_zero]

theorem w64_bit (w : UInt64) {z : Nat} (hz : z < 64) :
    w64 ((BOut.bit z).word w) = if ubit w z then 1 else 0 := by
  rw [bit_word w hz]; split <;> rfl

theorem bit_bool (w : UInt64) {z : Nat} (hz : z < 64) :
    w64 ((BOut.bit z).word w) = 0 ∨ w64 ((BOut.bit z).word w) = 1 := by
  rw [w64_bit w hz]; split <;> simp

theorem bnat_bit (w : UInt64) {z : Nat} (hz : z < 64) :
    bnat (w64 ((BOut.bit z).word w)) = (ubit w z).toNat := by
  rw [w64_bit w hz]
  have h01 : ¬ ((0 : FK) = 1) := by decide
  split <;> simp_all [bnat]

theorem ubit_testBit (w : UInt64) (z : Nat) : ubit w z = w.toNat.testBit z := rfl

/-! ## Digests -/

theorem digOfW_congr {w w' : Nat → UInt64} (h : ∀ l < 4, w l = w' l) : digOfW w = digOfW w' := by
  apply Vector.ext
  intro k hk
  simp only [digOfW, Vector.getElem_ofFn]
  rw [h _ (by (clear * - hk; omega))]

theorem digOfW_ite {v : Nat → FK} {w : Nat → UInt64} {c : Prop} [Decidable c] {A B : Nat}
    (h : ∀ l < 4, w l = if c then (v (A + l)).val else (v (B + l)).val) :
    digOfW w = if c then digAt v A else digAt v B := by
  unfold digAt
  split_ifs with hc
  · exact digOfW_congr fun l hl => by simp only [h l hl, hc, ↓reduceIte]
  · exact digOfW_congr fun l hl => by simp only [h l hl, hc, ↓reduceIte]

/-! ## One hash per kind -/

/-- A chain step from its lanes (`steps_spec`'s form). -/
theorem step_of_lanes {lane X xw : Nat → UInt64} {jw T c : UInt64} {i s : Nat}
    (hj : jw.toNat < 2 ^ 16) (hi : i < 256) (hs : s < 256)
    (hTc : T ^^^ c = (i.toUInt64 <<< (8 : Nat).toUInt64) ^^^ (s.toUInt64 <<< (16 : Nat).toUInt64))
    (hX : ∀ l < 4, X (2 * l) = xw l <<< (24 : Nat).toUInt64 ∧ X (2 * l + 1) = xw l >>> (40 : Nat).toUInt64)
    (L0 : lane 0 = (jw <<< (8 : Nat).toUInt64) ^^^ 0x57) (L1 : lane 1 = (T ^^^ X 0) ^^^ c)
    (Lk : ∀ k, 1 ≤ k → k < 4 → lane (k + 1) = X (2 * k - 1) ^^^ X (2 * k))
    (L5 : lane 5 = X 7 ^^^ 0x1000000) (Lz : ∀ l, 6 ≤ l → l < 16 → lane l = 0)
    (L16 : lane 16 = 0x8000000000000000) {st : State}
    (hperm : BlockPerm (xorMsg zeroSt (laneByte lane)) st) :
    stDigest st = wotsStep jw.toNat i s (digOfW xw) := by
  have h1 : lane 1 = ((i.toUInt64 <<< (8 : ℕ).toUInt64) ^^^ (s.toUInt64 <<< (16 : ℕ).toUInt64)) ^^^
      (xw 0 <<< (24 : ℕ).toUInt64) := by
    rw [L1, UInt64.xor_assoc, UInt64.xor_comm (X 0), ← UInt64.xor_assoc, hTc, ← (hX 0 (by (clear * -; first | decide | (simp only [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]; done) | ring1 | omega))).1]
  have hx : ∀ k, 1 ≤ k → k < 4 →
      lane (k + 1) = (xw (k - 1) >>> (40 : ℕ).toUInt64) ^^^ (xw k <<< (24 : ℕ).toUInt64) := by
    intro k h1 h2
    rw [Lk k h1 h2, show 2 * k - 1 = 2 * (k - 1) + 1 by (clear * - h1 h2; omega), (hX (k - 1) (by (clear * - h1 h2; omega))).2,
      (hX k h2).1]
  have h5 : lane 5 = (xw 3 >>> (40 : ℕ).toUInt64) ^^^ 0x1000000 := by
    rw [L5, ← (hX 3 (by (clear * -; first | decide | (simp only [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]; done) | ring1 | omega))).2]
  obtain ⟨b0, b1, b2, b3, b4, b5⟩ := wotsStep_lanes jw hj i s hi hs xw lane L0 h1 hx h5 Lz L16
  exact wotsStep_block _ _ _ _ _ _ b0 b1 b2 b3 b4 b5 hperm

/-- A path node from its lanes (`two_spec`'s form, tag `0x4D`). -/
theorem node_of_lanes {lane A B a b : Nat → UInt64}
    (hA : ∀ l < 4, A (2 * l) = a l <<< (8 : Nat).toUInt64 ∧ A (2 * l + 1) = a l >>> (56 : Nat).toUInt64)
    (hB : ∀ l < 4, B (2 * l) = b l <<< (8 : Nat).toUInt64 ∧ B (2 * l + 1) = b l >>> (56 : Nat).toUInt64)
    (L0 : lane 0 = A 0 ^^^ 0x4D) (Lk : ∀ k, 1 ≤ k → k < 4 → lane k = A (2 * k - 1) ^^^ A (2 * k))
    (L4 : lane 4 = A 7 ^^^ B 0)
    (Lb : ∀ k, 1 ≤ k → k < 4 → lane (4 + k) = B (2 * k - 1) ^^^ B (2 * k))
    (L8 : lane 8 = B 7 ^^^ 0x100) (Lz : ∀ l, 9 ≤ l → l < 16 → lane l = 0)
    (L16 : lane 16 = 0x8000000000000000) {st : State}
    (hperm : BlockPerm (xorMsg zeroSt (laneByte lane)) st) :
    stDigest st = sigNode (digOfW a) (digOfW b) := by
  have h0 : lane 0 = (a 0 <<< (8 : ℕ).toUInt64) ^^^ tagSigNode.toUInt64 := by
    rw [L0, ← (hA 0 (by (clear * -; first | decide | (simp only [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]; done) | ring1 | omega))).1]; rfl
  have ha : ∀ k, 1 ≤ k → k < 4 →
      lane k = (a (k - 1) >>> (56 : ℕ).toUInt64) ^^^ (a k <<< (8 : ℕ).toUInt64) := by
    intro k h1 h2
    rw [Lk k h1 h2, show 2 * k - 1 = 2 * (k - 1) + 1 by (clear * - h1 h2; omega), (hA (k - 1) (by (clear * - h1 h2; omega))).2,
      (hA k h2).1]
  have h4 : lane 4 = (a 3 >>> (56 : ℕ).toUInt64) ^^^ (b 0 <<< (8 : ℕ).toUInt64) := by
    rw [L4, ← (hA 3 (by (clear * -; first | decide | (simp only [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]; done) | ring1 | omega))).2, ← (hB 0 (by (clear * -; first | decide | (simp only [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]; done) | ring1 | omega))).1]
  have hb : ∀ k, 1 ≤ k → k < 4 →
      lane (4 + k) = (b (k - 1) >>> (56 : ℕ).toUInt64) ^^^ (b k <<< (8 : ℕ).toUInt64) := by
    intro k h1 h2
    rw [Lb k h1 h2, show 2 * k - 1 = 2 * (k - 1) + 1 by (clear * - h1 h2; omega), (hB (k - 1) (by (clear * - h1 h2; omega))).2,
      (hB k h2).1]
  have h8 : lane 8 = (b 3 >>> (56 : ℕ).toUInt64) ^^^ 0x100 := by
    rw [L8, ← (hB 3 (by (clear * -; first | decide | (simp only [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]; done) | ring1 | omega))).2]
  obtain ⟨b0, b1, b2, b3⟩ := two_lanes tagSigNode a b lane h0 ha h4 hb h8 Lz L16
  exact sigNode_block _ _ _ _ b0 b1 b2 b3 hperm

/-- The WOTS key leaf from its 544 lanes (`lane`), read by blocks of 17. -/
theorem leaf_of_lanes {lane E : Nat → UInt64} {jw : UInt64} (hj : jw.toNat < 2 ^ 16)
    (h0 : lane 0 = (jw <<< (8 : ℕ).toUInt64) ^^^ 0x4B) (h1 : lane 1 = E 0 <<< (8 : ℕ).toUInt64)
    (hE : ∀ m, 2 ≤ m → m ≤ 532 →
      lane m = (E (m - 2) >>> (56 : ℕ).toUInt64) ^^^ (E (m - 1) <<< (8 : ℕ).toUInt64))
    (h533 : lane 533 = (E 531 >>> (56 : ℕ).toUInt64) ^^^ 0x100)
    (hz : ∀ l, 534 ≤ l → l < 543 → lane l = 0) (h543 : lane 543 = 0x8000000000000000)
    {ends : List Digest} (hlen : ends.length = wotsLen)
    (hends : ∀ i (hi : i < wotsLen), ∀ k (hk : k < 32),
      (ends[i]'(hlen ▸ hi))[k] = byteW (E (4 * i + k / 8)) (k % 8))
    {sIn sOut : Nat → State} (hstart : sIn 0 = zeroSt)
    (hperm : ∀ u < 32, BlockPerm (xorMsg (sIn u) (laneByte fun l => lane (17 * u + l))) (sOut u))
    (hlink : ∀ u, u + 1 < 32 → sIn (u + 1) = sOut u) :
    stDigest (sOut 31) = wotsLeaf jw.toNat ends := by
  have hrate : rate = 136 := rfl
  obtain ⟨b0, b1, b2, b3⟩ := wotsLeaf_lanes jw hj E lane h0 h1 hE h533 hz h543
  have hm : ∀ p, laneByte (fun l => lane (17 * (p / rate) + l)) (p % rate) = laneByte lane p := by
    intro p
    simp only [laneByte, hrate]
    rw [show 17 * (p / 136) + p % 136 / 8 = p / 8 by (clear * -; first | decide | (simp only [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]; done) | ring1 | (clear * - p; omega)), show p % 136 % 8 = p % 8 by (clear * -; first | decide | (simp only [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]; done) | ring1 | (clear * - p; omega))]
  have hb : ∀ p, laneByte lane (rate * (p / rate) + p % rate) = laneByte lane p := fun p => by
    rw [Nat.div_add_mod]
  beta_reduce at b0 b1 b2 b3
  refine wotsLeaf_stream jw.toNat ends _ sIn sOut hstart hperm hlink (fun p hp1 hp2 => ?_) ?_
  · rw [hm, ← hb]; exact b3 p hp1 hp2
  · apply wotsLeaf_bytes jw.toNat ends hlen
    · have := hm 0
      simp only [Nat.zero_div, Nat.zero_mod, Nat.mul_zero] at this b0
      rw [this]; exact b0
    · intro k hk; rw [hm, ← hb]; exact b1 k hk
    · intro i hi k hk; rw [hm, ← hb, hends i hi k hk]; exact b2 i hi k hk

/-! ## One chain -/

/-- **One chain's end** from its three steps and the selections (`chain_spec`'s form). -/
theorem chain_end {v : Nat → FK} {o : SigOut} {I : SigIn} {i d : Nat} {j : Nat} (hd : d ≤ 3)
    (hstep : ∀ s < 3, digAt v (I.ys + 4 * (3 * i + s)) = wotsStep j i s (digOfW (lanesW v (xin I o i s))))
    (hm : ∀ s, 1 ≤ s → s < 3 → ∀ l < 4, (v (xin I o i s l)).val =
      if d < s then (v (I.ys + 4 * (3 * i + (s - 1)) + l)).val else (v (I.sg + 1 + 4 * i + l)).val)
    (he : ∀ l < 4, (v (endc o i l)).val =
      if d < 3 then (v (I.ys + 4 * (3 * i + 2) + l)).val else (v (I.sg + 1 + 4 * i + l)).val) :
    digOfW (lanesW v (endc o i)) = wotsChain j i d (3 - d) (digAt v (I.sg + 1 + 4 * i)) := by
  refine wots_chain_sound hd (a := fun s => digOfW (lanesW v (xin I o i (s - 1))))
    (out := fun s => digAt v (I.ys + 4 * (3 * i + (s - 1)))) (fun s h1 h3 => hstep _ (by (clear * - h1 h3; omega)))
    (fun s h1 h3 => ?_) (digOfW_ite he)
  rcases (show s = 1 ∨ s = 2 ∨ s = 3 by (clear * - h1 h3; omega)) with rfl | rfl | rfl
  · simp only [show ¬ d + 1 < 1 by (clear * - hd; omega), ↓reduceIte]
    unfold digAt
    exact digOfW_congr fun l _ => by simp [lanesW, xin]
  · show digOfW (lanesW v (xin I o i 1)) = _
    rw [digOfW_ite (w := lanesW v (xin I o i 1)) (hm 1 le_rfl (by (clear * -; first | decide | (simp only [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]; done) | ring1 | omega))),
      show (2 : Nat) - 1 - 1 = 1 - 1 from rfl]
    split_ifs <;> first | (exfalso; omega) | rfl
  · show digOfW (lanesW v (xin I o i 2)) = _
    rw [digOfW_ite (w := lanesW v (xin I o i 2)) (hm 2 (by (clear * -; first | decide | (simp only [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]; done) | ring1 | omega)) (by (clear * -; first | decide | (simp only [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]; done) | ring1 | omega))),
      show (3 : Nat) - 1 - 1 = 2 - 1 from rfl]
    split_ifs <;> first | (exfalso; omega) | rfl


/-! ## The gadget's cells -/

theorem xcell_m {o : SigOut} {i s : Nat} (hi : i < 128) (hs : s < 3) (l : Nat) :
    xcell o (3 * i + s) l = (o.msg.xm.cell (17 * s + l) i).n := by
  simp only [xcell, show 3 * i + s < 384 by (clear * - i s hi hs; omega), ↓reduceIte, show (3 * i + s) % 3 = s by (clear * - hs; omega),
    show (3 * i + s) / 3 = i by (clear * - hs; omega)]

theorem xcell_c {o : SigOut} {u s : Nat} (hu : u < 5) (hs : s < 3) (l : Nat) :
    xcell o (3 * (128 + u) + s) l = ((o.msg.xc.getD u dLoop).cell (17 * s + l) 0).n := by
  simp only [xcell, show ¬ 3 * (128 + u) + s < 384 by (clear * - u s hu hs; omega), show 3 * (128 + u) + s < 399 by (clear * - u s hu hs; omega),
    ↓reduceIte, show (3 * (128 + u) + s - 384) % 3 = s by (clear * - u s hu hs; omega),
    show (3 * (128 + u) + s - 384) / 3 = u by (clear * - u s hu hs; omega)]

theorem xcell_leaf (v : Nat → FK) (o : SigOut) {u : Nat} (hu : u < 32) :
    lanesW v (xcell o (399 + u)) = fun l => (v (leafLane o (17 * u + l))).val := by
  funext l
  simp only [lanesW, xcell, show ¬ 399 + u < 384 by (clear * - u hu; omega), show ¬ 399 + u < 399 by (clear * - u hu; omega),
    show 399 + u < 431 by (clear * - u hu; omega), ↓reduceIte, show 399 + u - 399 = u by (clear * - u hu; omega)]

theorem xcell_path (v : Nat → FK) (o : SigOut) {t : Nat} (ht : t < 16) :
    lanesW v (xcell o (431 + t)) = fun l => (v (o.msg.xp.cell l t).n).val := by
  funext l
  simp only [lanesW, xcell, show ¬ 431 + t < 384 by (clear * - t ht; omega), show ¬ 431 + t < 399 by (clear * - t ht; omega),
    show ¬ 431 + t < 431 by (clear * - t ht; omega), show 431 + t < 447 by (clear * - t ht; omega), ↓reduceIte,
    show 431 + t - 431 = t by (clear * - t ht; omega)]

theorem ov_nil (M : Mem) (o : LoopOut) (hd : o.dims = []) (n s : Nat) :
    ov M o 0 (oS n s) = M.k n := by
  simp [ov, Opd.resolve, Addr.at, dot, hd, unflat]

theorem bnat_dec (b : FK) : bnat b = (decide (b = 1)).toNat := by
  unfold bnat; split <;> simp_all

/-! ## The path mux -/

theorem path_spec {c : Ctx} {M : Mem} {q : Ptr} {I : SigIn}
    (h : SegsHold c M q (loop [4] (pathTpl I) q).2) {t l : Nat} (ht : t < 16) (hl : l < 4)
    (hb : M.k (I.bi + 1 + t) = 0 ∨ M.k (I.bi + 1 + t) = 1) :
    M.k ((loop [4] (pathTpl I) q).1.cell (4 + l) t).n =
        (if M.k (I.bi + 1 + t) = 1 then M.k (I.sg + 533 + l + 4 * t) else M.k (I.yc + l + 4 * t)) ∧
      M.k ((loop [4] (pathTpl I) q).1.cell (8 + l) t).n =
        (if M.k (I.bi + 1 + t) = 1 then M.k (I.yc + l + 4 * t) else M.k (I.sg + 533 + l + 4 * t)) := by
  have hjf : t < 2 ^ ([4] : List Nat).sum := by simpa using ht
  have ht' : t < 2 ^ 4 := by simpa using ht
  have hd : (loop [4] (pathTpl I) q).1.dims = [4] := rfl
  have hlen : (pathTpl I).length = 12 := by simp [pathTpl]
  have g0 : (pathTpl I).getD l default = lr 1 0 (oS (I.yc + l) 4) (oS (I.sg + 533 + l) 4) := by
    interval_cases l <;> rfl
  have g4 : (pathTpl I).getD (4 + l) default = mr (oS (I.bi + 1) 1) (.cur l) (oS (I.yc + l) 4) := by
    interval_cases l <;> rfl
  have g8 : (pathTpl I).getD (8 + l) default =
      mr (oS (I.bi + 1) 1) (.cur l) (oS (I.sg + 533 + l) 4) := by
    interval_cases l <;> rfl
  have hK : ((loop [4] (pathTpl I) q).1.tpl.getD l default).ty = .K := by
    show ((pathTpl I).getD l default).ty = .K; rw [g0]
  have r0 := loopK_lin h hjf (by (clear * - hl hlen; omega)) g0 rfl rfl
  have r4 := loopK_mad h hjf (by (clear * - hl hlen; omega)) g4 rfl hK rfl
  have r8 := loopK_mad h hjf (by (clear * - hl hlen; omega)) g8 rfl hK rfl
  rw [ov_cur M _ hjf l hK, r0] at r4 r8
  simp only [ov_oS M _ hd ht', one_mul, add_zero] at r4 r8
  rw [r4, r8, add_comm (M.k (I.yc + l + 4 * t)) (M.k (I.sg + 533 + l + 4 * t)),
    mux_eq hb]
  rw [add_comm (M.k (I.sg + 533 + l + 4 * t)) (M.k (I.yc + l + 4 * t)), mux_eq hb]
  exact ⟨rfl, rfl⟩

/-! ## Chain steps -/

/-- **A message chain's step** `s` (row `3i + s`). -/
theorem step_m {c : Ctx} {M : Mem} {I : SigIn} {o : SigOut} {r : Ptr} {Zn Tb : Nat}
    (hks : SigKS I o M.k) (hbits : SigBits I o M.k) (hZ : M.k Zn = 0)
    (hT : ∀ i < 128, M.k (Tb + i) = w64 (i.toUInt64 <<< (8 : Nat).toUInt64))
    (hj : (M.k I.sg).val.toNat < 2 ^ 16)
    (h : SegsHold c M r (loop [7] (stepsTpl I Zn (oS Tb 1)
      (fun s => (s.toUInt64 <<< (16 : Nat).toUInt64)) I.bx 24) r).2)
    (e : (loop [7] (stepsTpl I Zn (oS Tb 1)
      (fun s => (s.toUInt64 <<< (16 : Nat).toUInt64)) I.bx 24) r).1 = o.msg.xm)
    {i s : Nat} (hi : i < 128) (hs : s < 3) :
    digAt M.k (I.ys + 4 * (3 * i + s)) =
      wotsStep (M.k I.sg).val.toNat i s (digOfW (lanesW M.k (xin I o i s))) := by
  obtain ⟨st, hp, hd⟩ := hks.step (3 * i + s) (by (clear * - hi hs; omega))
  rw [hd]
  have hjf : i < 2 ^ ([7] : List Nat).sum := by simpa using hi
  have hi7 : i < 2 ^ 7 := by simpa using hi
  have hd7 : (loop [7] (stepsTpl I Zn (oS Tb 1)
      (fun s => (s.toUInt64 <<< (16 : Nat).toUInt64)) I.bx 24) r).1.dims = [7] := rfl
  obtain ⟨L0, L1, Lk, L5, Lz, L16⟩ := steps_spec h hjf rfl hZ hs
  beta_reduce at L0 L1 Lk L5 Lz L16
  have hlane : ∀ l, lanesW M.k (xcell o (3 * i + s)) l = V M ((loop [7] (stepsTpl I Zn (oS Tb 1)
      (fun s => (s.toUInt64 <<< (16 : Nat).toUInt64)) I.bx 24) r).1.cell (17 * s + l) i).n := by
    intro l; rw [e]; simp only [lanesW, xcell_m hi hs]
  have hbi : V M I.bi = (M.k I.sg).val <<< (8 : Nat).toUInt64 := by
    show (M.k I.bi).val = _; rw [hbits.idx_lo]; rfl
  refine step_of_lanes (lane := lanesW M.k (xcell o (3 * i + s)))
    (X := fun k => OV M (loop [7] (stepsTpl I Zn (oS Tb 1)
      (fun s => (s.toUInt64 <<< (16 : Nat).toUInt64)) I.bx 24) r).1 i (oS (I.bx + 8 * s + k) 24)) hj (by (clear * - hi; omega)) (by (clear * - hs; omega))
    ?_ (fun l hl => ⟨?_, ?_⟩) (by rw [hlane, L0, hbi]) (by rw [hlane]; exact L1)
    (fun k h1 h2 => by rw [hlane]; exact Lk k h1 h2) (by rw [hlane]; exact L5)
    (fun l h1 h2 => by rw [hlane]; exact Lz l h1 h2) (by rw [hlane]; exact L16) hp
  · rw [ovS_V hd7 hi7 (show Tb + 1 * i = Tb + i by ring)]
    show (M.k (Tb + i)).val ^^^ _ = _
    rw [hT i hi]
  · rw [ovS_V hd7 hi7 (show I.bx + 8 * s + 2 * l + 24 * i = I.bx + 2 * (4 * (3 * i + s) + l) by ring)]
    dsimp only [V]; rw [sOut1_val (hbits.x i (by (clear * - hi; omega)) s hs l hl).1]; rfl
  · rw [ovS_V hd7 hi7
      (show I.bx + 8 * s + (2 * l + 1) + 24 * i = I.bx + 2 * (4 * (3 * i + s) + l) + 1 by ring)]
    dsimp only [V]; rw [sOut1_val (hbits.x i (by (clear * - hi; omega)) s hs l hl).2]; rfl

/-- **A checksum chain's step** `s` (chain `128 + u`, row `3(128 + u) + s`). -/
theorem step_c {c : Ctx} {M : Mem} {I : SigIn} {o : SigOut} {r : Ptr} {Zn u : Nat}
    (hks : SigKS I o M.k) (hbits : SigBits I o M.k) (hZ : M.k Zn = 0)
    (hj : (M.k I.sg).val.toNat < 2 ^ 16) (hu : u < 5)
    (h : SegsHold c M r (loop [] (stepsTpl I Zn (oA Zn)
      (fun s => ((128 + u).toUInt64 <<< (8 : Nat).toUInt64) ^^^ (s.toUInt64 <<< (16 : Nat).toUInt64))
      (I.bx + 24 * (128 + u)) 0) r).2)
    (e : (loop [] (stepsTpl I Zn (oA Zn)
      (fun s => ((128 + u).toUInt64 <<< (8 : Nat).toUInt64) ^^^ (s.toUInt64 <<< (16 : Nat).toUInt64))
      (I.bx + 24 * (128 + u)) 0) r).1 = o.msg.xc.getD u dLoop)
    {s : Nat} (hs : s < 3) :
    digAt M.k (I.ys + 4 * (3 * (128 + u) + s)) =
      wotsStep (M.k I.sg).val.toNat (128 + u) s (digOfW (lanesW M.k (xin I o (128 + u) s))) := by
  obtain ⟨st, hp, hd⟩ := hks.step (3 * (128 + u) + s) (by (clear * - hu hs; omega))
  rw [hd]
  have hjf : 0 < 2 ^ ([] : List Nat).sum := by simp
  have hd0 : (loop [] (stepsTpl I Zn (oA Zn)
      (fun s => ((128 + u).toUInt64 <<< (8 : Nat).toUInt64) ^^^ (s.toUInt64 <<< (16 : Nat).toUInt64))
      (I.bx + 24 * (128 + u)) 0) r).1.dims = [] := rfl
  obtain ⟨L0, L1, Lk, L5, Lz, L16⟩ := steps_spec h hjf rfl hZ hs
  beta_reduce at L0 L1 Lk L5 Lz L16
  have hlane : ∀ l, lanesW M.k (xcell o (3 * (128 + u) + s)) l = V M ((loop [] (stepsTpl I Zn (oA Zn)
      (fun s => ((128 + u).toUInt64 <<< (8 : Nat).toUInt64) ^^^ (s.toUInt64 <<< (16 : Nat).toUInt64))
      (I.bx + 24 * (128 + u)) 0) r).1.cell (17 * s + l) 0).n := by
    intro l; rw [e]; simp only [lanesW, xcell_c hu hs]
  have hbi : V M I.bi = (M.k I.sg).val <<< (8 : Nat).toUInt64 := by
    show (M.k I.bi).val = _; rw [hbits.idx_lo]; rfl
  refine step_of_lanes (lane := lanesW M.k (xcell o (3 * (128 + u) + s)))
    (X := fun k => OV M (loop [] (stepsTpl I Zn (oA Zn)
      (fun s => ((128 + u).toUInt64 <<< (8 : Nat).toUInt64) ^^^ (s.toUInt64 <<< (16 : Nat).toUInt64))
      (I.bx + 24 * (128 + u)) 0) r).1 0 (oS (I.bx + 24 * (128 + u) + 8 * s + k) 0)) hj (by (clear * - hu; omega)) (by (clear * - hs; omega))
    ?_ (fun l hl => ⟨?_, ?_⟩) (by rw [hlane, L0, hbi]) (by rw [hlane]; exact L1)
    (fun k h1 h2 => by rw [hlane]; exact Lk k h1 h2) (by rw [hlane]; exact L5)
    (fun l h1 h2 => by rw [hlane]; exact Lz l h1 h2) (by rw [hlane]; exact L16) hp
  · show (ov M _ 0 (oA Zn)).val ^^^ _ = _
    rw [ov_oA, hZ]; exact UInt64.zero_xor
  · show (ov M _ 0 (oS _ 0)).val = _
    rw [ov_nil M _ hd0, show I.bx + 24 * (128 + u) + 8 * s + 2 * l =
      I.bx + 2 * (4 * (3 * (128 + u) + s) + l) by ring]
    rw [sOut1_val (hbits.x (128 + u) (by (clear * - hu; omega)) s hs l hl).1]; rfl
  · show (ov M _ 0 (oS _ 0)).val = _
    rw [ov_nil M _ hd0, show I.bx + 24 * (128 + u) + 8 * s + (2 * l + 1) =
      I.bx + 2 * (4 * (3 * (128 + u) + s) + l) + 1 by ring]
    rw [sOut1_val (hbits.x (128 + u) (by (clear * - hu; omega)) s hs l hl).2]; rfl

/-! ## Chain selections -/

theorem loop_dims_eq (dims : List Nat) (tpl : List LRow) (q : Ptr) : (loop dims tpl q).1.dims = dims :=
  rfl

theorem kval_congr (M : Mem) {a b : Nat} (h : a = b) : (M.k a).val = (M.k b).val := by rw [h]

/-- **A message chain's selections** (iteration `i` of the `cm` loop). -/
theorem sel_m {c : Ctx} {M : Mem} {I : SigIn} {o : SigOut} {q : Ptr} {Zn On : Nat}
    (h : SegsHold c M q (loop [7] (chainM I Zn On) q).2)
    (e : (loop [7] (chainM I Zn On) q).1 = o.cm) (hZ : M.k Zn = 0) (hO : M.k On = 1)
    (hbd : ∀ q < 256, M.k (I.bd + q) = 0 ∨ M.k (I.bd + q) = 1) {i : Nat} (hi : i < 128) :
    (∀ s, 1 ≤ s → s < 3 → ∀ l < 4, (M.k (xin I o i s l)).val =
      if mdig M I i < s then (M.k (I.ys + 4 * (3 * i + (s - 1)) + l)).val
        else (M.k (I.sg + 1 + 4 * i + l)).val) ∧
    (∀ l < 4, (M.k (endc o i l)).val =
      if mdig M I i < 3 then (M.k (I.ys + 4 * (3 * i + 2) + l)).val
        else (M.k (I.sg + 1 + 4 * i + l)).val) := by
  unfold chainM at h e
  have hjf : i < 2 ^ ([7] : List Nat).sum := by simpa using hi
  have hi7 : i < 2 ^ 7 := by simpa using hi
  have hd7 := loop_dims_eq [7] (chainTpl (oS I.bd 2) (oS (I.bd + 1) 2) (oA Zn) (oA On)
    (fun l => oS (I.sg + 1 + l) 4) (fun l => oS (I.ys + l) 12) (fun l => oS (I.ys + 4 + l) 12)
    (fun l => oS (I.ys + 8 + l) 12)) q
  have C := fun l (hl : l < 4) => chain_spec (d0 := oS I.bd 2) (d1 := oS (I.bd + 1) 2)
    (Z := oA Zn) (O := oA On) (ots := fun l => oS (I.sg + 1 + l) 4)
    (o1 := fun l => oS (I.ys + l) 12) (o2 := fun l => oS (I.ys + 4 + l) 12)
    (o3 := fun l => oS (I.ys + 8 + l) 12) h hjf
    (fun x hx => by simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
                    rcases hx with rfl | rfl | rfl | rfl <;> rfl)
    (fun l _ x hx => by simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
                        rcases hx with rfl | rfl | rfl | rfl <;> rfl)
    (by rw [ov_oA, hZ]) (by rw [ov_oA, hO]) (b0 := M.k (I.bd + 2 * i))
    (b1 := M.k (I.bd + 2 * i + 1)) (by rw [ov_oS _ _ hd7 hi7])
    (by rw [ov_oS _ _ hd7 hi7, show I.bd + 1 + 2 * i = I.bd + 2 * i + 1 by ring])
    (hbd _ (by (clear * - hi; omega))) (by rw [Nat.add_assoc]; exact hbd _ (by (clear * - hi; omega))) hl
  unfold mdig
  refine ⟨fun s h1 h2 l hl => ?_, fun l hl => ?_⟩
  · obtain ⟨C1, C2, -⟩ := C l hl
    simp only [cv] at C1 C2
    rcases (show s = 1 ∨ s = 2 by (clear * - h1 h2; omega)) with rfl | rfl
    · simp only [← e, xin, chainCell, one_ne_zero, ↓reduceIte, hi, show 8 * 1 + l = 8 + l by ring, C1,
        ov_oS _ _ hd7 hi7]
      split_ifs <;> exact kval_congr M (by (clear * -; first | decide | (simp only [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]; done) | ring1 | omega))
    · simp only [← e, xin, chainCell, show (2 : Nat) ≠ 0 by (clear * -; first | decide | (simp only [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]; done) | ring1 | omega), ↓reduceIte, hi,
        show 8 * 2 + l = 16 + l by ring, C2, ov_oS _ _ hd7 hi7]
      split_ifs <;> exact kval_congr M (by (clear * -; first | decide | (simp only [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]; done) | ring1 | omega))
  · obtain ⟨-, -, C3⟩ := C l hl
    simp only [cv] at C3
    simp only [← e, endc, chainCell, hi, ↓reduceIte, C3, ov_oS _ _ hd7 hi7]
    split_ifs <;> exact kval_congr M (by (clear * -; first | decide | (simp only [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]; done) | ring1 | omega))

/-- The digit of checksum chain `128 + u` from its bit cells. -/
def cdig (M : Mem) (I : SigIn) (u : Nat) : Nat :=
  bnat (M.k (I.bc + 2 * u)) + 2 * bnat (M.k (I.bc + 2 * u + 1))

/-- **A checksum chain's selections** (chain `128 + u`). -/
theorem sel_c {c : Ctx} {M : Mem} {I : SigIn} {o : SigOut} {q : Ptr} {Zn On u : Nat}
    (h : SegsHold c M q (loop [] (chainC I Zn On u) q).2)
    (e : (loop [] (chainC I Zn On u) q).1 = o.cc.getD u dLoop) (hZ : M.k Zn = 0) (hO : M.k On = 1)
    (hbc : ∀ k < 10, M.k (I.bc + k) = 0 ∨ M.k (I.bc + k) = 1) (hu : u < 5) :
    (∀ s, 1 ≤ s → s < 3 → ∀ l < 4, (M.k (xin I o (128 + u) s l)).val =
      if cdig M I u < s then (M.k (I.ys + 4 * (3 * (128 + u) + (s - 1)) + l)).val
        else (M.k (I.sg + 1 + 4 * (128 + u) + l)).val) ∧
    (∀ l < 4, (M.k (endc o (128 + u) l)).val =
      if cdig M I u < 3 then (M.k (I.ys + 4 * (3 * (128 + u) + 2) + l)).val
        else (M.k (I.sg + 1 + 4 * (128 + u) + l)).val) := by
  unfold chainC at h e
  have hjf : 0 < 2 ^ ([] : List Nat).sum := by simp
  have C := fun l (hl : l < 4) => chain_spec (d0 := oA (I.bc + 2 * u)) (d1 := oA (I.bc + 2 * u + 1))
    (Z := oA Zn) (O := oA On) (ots := fun l => oA (I.sg + 1 + 4 * (128 + u) + l))
    (o1 := fun l => oA (I.ys + 4 * (3 * (128 + u)) + l))
    (o2 := fun l => oA (I.ys + 4 * (3 * (128 + u) + 1) + l))
    (o3 := fun l => oA (I.ys + 4 * (3 * (128 + u) + 2) + l)) h hjf
    (fun x hx => by simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
                    rcases hx with rfl | rfl | rfl | rfl <;> rfl)
    (fun l _ x hx => by simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
                        rcases hx with rfl | rfl | rfl | rfl <;> rfl)
    (by rw [ov_oA, hZ]) (by rw [ov_oA, hO]) (b0 := M.k (I.bc + 2 * u))
    (b1 := M.k (I.bc + 2 * u + 1)) (by rw [ov_oA]) (by rw [ov_oA])
    (hbc _ (by (clear * - hu; omega))) (by rw [Nat.add_assoc]; exact hbc _ (by (clear * - hu; omega))) hl
  unfold cdig
  have hn : ¬ 128 + u < 128 := by (clear * - hu; omega)
  have hs : 128 + u - 128 = u := by (clear * - hu; omega)
  refine ⟨fun s h1 h2 l hl => ?_, fun l hl => ?_⟩
  · obtain ⟨C1, C2, -⟩ := C l hl
    simp only [cv] at C1 C2
    rcases (show s = 1 ∨ s = 2 by (clear * - h1 h2; omega)) with rfl | rfl
    · simp only [← e, xin, chainCell, one_ne_zero, ↓reduceIte, hn, hs, show 8 * 1 + l = 8 + l by ring, C1,
        ov_oA]
      split_ifs <;> exact kval_congr M (by (clear * -; first | decide | (simp only [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]; done) | ring1 | omega))
    · simp only [← e, xin, chainCell, show (2 : Nat) ≠ 0 by (clear * -; first | decide | (simp only [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]; done) | ring1 | omega), ↓reduceIte, hn, hs,
        show 8 * 2 + l = 16 + l by ring, C2, ov_oA]
      split_ifs <;> exact kval_congr M (by (clear * -; first | decide | (simp only [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]; done) | ring1 | omega))
  · obtain ⟨-, -, C3⟩ := C l hl
    simp only [cv] at C3
    simp only [← e, endc, chainCell, hn, hs, ↓reduceIte, C3, ov_oA]
    split_ifs <;> rfl

/-! ## Digits -/

theorem mdig_eq {M : Mem} {I : SigIn} {o : SigOut} (hbits : SigBits I o M.k) {i : Nat} (hi : i < 128) :
    mdig M I i = (msgDigits (digAt M.k I.md))[i]'(by rw [msgDigits_length]; exact hi) := by
  rw [msgDigit_bits (digAt M.k I.md) (fun l => (M.k (I.md + l)).val) (fun k hk => digOfW_get _ hk) hi]
  unfold mdig
  have h0 := hbits.md (2 * i) (by (clear * - hi; omega))
  have h1 := hbits.md (2 * i + 1) (by (clear * - hi; omega))
  unfold Out1 at h0 h1
  rw [Nat.add_assoc, h0, h1, bnat_bit _ (Nat.mod_lt _ (by norm_num)),
    bnat_bit _ (Nat.mod_lt _ (by norm_num)), show 2 * i / 64 = i / 32 by (clear * -; first | decide | (simp only [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]; done) | ring1 | (clear * - i; omega)),
    show (2 * i + 1) / 64 = i / 32 by (clear * -; first | decide | (simp only [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]; done) | ring1 | (clear * - i; omega)), show (2 * i + 1) % 64 = 2 * i % 64 + 1 by (clear * -; first | decide | (simp only [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]; done) | ring1 | (clear * - i; omega))]

theorem wdig_lt (m : Digest) {i : Nat} (hi : i < 128) :
    (wotsDigits m)[i]'(by rw [wotsDigits_length]; simp [wotsLen]; omega) =
      (msgDigits m)[i]'(by rw [msgDigits_length]; exact hi) := by
  simp only [wotsDigits]
  rw [List.getElem_append_left]

theorem range_mdig {M : Mem} {I : SigIn} {o : SigOut} (hbits : SigBits I o M.k) :
    (List.range 128).map (fun i => 3 - mdig M I i) = (msgDigits (digAt M.k I.md)).map (3 - ·) := by
  apply List.ext_getElem (by simp [msgDigits_length])
  intro n h1 h2
  have hn : n < 128 := by simpa using h1
  simp only [List.getElem_map, List.getElem_range]
  rw [mdig_eq hbits hn]

theorem cdig_eq {M : Mem} {I : SigIn} (m : Digest)
    (hC : ((msgDigits m).map (3 - ·)).sum = bitsVal (cbit M I) 10) {u : Nat} (hu : u < 5) :
    cdig M I u = (wotsDigits m)[128 + u]'(by rw [wotsDigits_length]; simp [wotsLen]; omega) := by
  rw [checksum_digit m (cbit M I) hC hu, cdig, bnat_dec, bnat_dec]
  rfl

/-! ## The key leaf and the path nodes -/

/-- **The key leaf** of the chain ends. -/
theorem leaf_digest {c : Ctx} {M : Mem} {I : SigIn} {o : SigOut} {r3 r4 r5 : Ptr} {Zn : Nat}
    (hks : SigKS I o M.k) (hbits : SigBits I o M.k) (hZ : M.k Zn = 0)
    (hj : (M.k I.sg).val.toNat < 2 ^ 16)
    (hla : SegsHold c M r3 (loop [] (leafA I) r3).2) (ela : (loop [] (leafA I) r3).1 = o.msg.la)
    (hlb : SegsHold c M r4 (loop [9] (leafB I) r4).2) (elb : (loop [9] (leafB I) r4).1 = o.msg.lb)
    (hlc : SegsHold c M r5 (loop [] (leafC I Zn) r5).2) (elc : (loop [] (leafC I Zn) r5).1 = o.msg.lc) :
    digAt M.k I.yc = wotsLeaf (M.k I.sg).val.toNat
      ((List.range wotsLen).map fun i => digOfW (lanesW M.k (endc o i))) := by
  obtain ⟨sIn, sOut, hstart, hperm, hlink, hdig⟩ := hks.leaf
  rw [hdig]
  have hEk : ∀ k < 532, (M.k (I.be + 2 * k)).val = (M.k (endc o (k / 4) (k % 4))).val <<< (8 : Nat).toUInt64 ∧
      (M.k (I.be + 2 * k + 1)).val = (M.k (endc o (k / 4) (k % 4))).val >>> (56 : Nat).toUInt64 := by
    intro k hk
    have := hbits.e (k / 4) (by (clear * - hk; omega)) (k % 4) (by (clear * -; first | decide | (simp only [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]; done) | ring1 | (clear * - k; omega)))
    rw [show 2 * (4 * (k / 4) + k % 4) = 2 * k by (clear * -; first | decide | (simp only [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]; done) | ring1 | (clear * - k; omega))] at this
    exact ⟨sOut1_val this.1, sOut1_val this.2⟩
  have hbi : (M.k I.bi).val = (M.k I.sg).val <<< (8 : Nat).toUInt64 := by rw [hbits.idx_lo]; rfl
  obtain ⟨A0, A1⟩ := leafA_spec hla (jf := 0) (by simp)
  rw [ela] at A0 A1
  have hB : ∀ m < 512, V M (o.msg.lb.cell 0 m).n =
      V M (I.be + 2 * m + 1) ^^^ V M (I.be + 2 * (m + 1)) := fun m hm => by
    rw [← elb]; exact leafB_spec hlb (by simpa using hm)
  obtain ⟨C1, C2, C3, C4⟩ := leafC_spec hlc (jf := 0) (by simp) hZ
  beta_reduce at C1 C2 C3 C4
  rw [elc] at C1 C2 C3 C4
  dsimp only [V] at A0 A1 hB C1 C2 C3 C4
  refine leaf_of_lanes (lane := fun m => (M.k (leafLane o m)).val)
    (E := fun k => (M.k (endc o (k / 4) (k % 4))).val) hj ?_ ?_ (fun m h1 h2 => ?_) ?_
    (fun l h1 h2 => ?_) ?_ (by simp [wotsLen]) (fun i hi k hk => ?_) hstart
    (fun u hu => by have := hperm u hu; rwa [xcell_leaf _ _ hu] at this) hlink
  · show (M.k (leafLane o 0)).val = _
    simp only [leafLane, show (0 : Nat) < 2 by (clear * -; first | decide | (simp only [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]; done) | ring1 | omega), ↓reduceIte]
    rw [A0, hbi]
  · show (M.k (leafLane o 1)).val = _
    simp only [leafLane, show (1 : Nat) < 2 by (clear * -; first | decide | (simp only [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]; done) | ring1 | omega), ↓reduceIte]
    rw [A1]; exact (hEk 0 (by (clear * -; first | decide | (simp only [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]; done) | ring1 | omega))).1
  · show (M.k (leafLane o m)).val = _
    by_cases hm : m < 514
    · simp only [leafLane, show ¬ m < 2 by (clear * - h1 h2 hm; omega), hm, ↓reduceIte]
      rw [hB (m - 2) (by (clear * - h1 h2 hm; omega)), show m - 2 + 1 = m - 1 by (clear * - h1 h2 hm; omega)]
      exact congrArg₂ _ (hEk (m - 2) (by (clear * - h1 h2 hm; omega))).2 (hEk (m - 1) (by (clear * - h1 h2 hm; omega))).1
    · simp only [leafLane, show ¬ m < 2 by (clear * - h1 h2 hm; omega), hm, ↓reduceIte]
      rw [C1 (m - 514) (by (clear * - h1 h2 hm; omega)), show 512 + (m - 514) = m - 2 by (clear * - h1 h2 hm; omega),
        show 513 + (m - 514) = m - 1 by (clear * - h1 h2 hm; omega)]
      exact congrArg₂ _ (hEk (m - 2) (by (clear * - h1 h2 hm; omega))).2 (hEk (m - 1) (by (clear * - h1 h2 hm; omega))).1
  · show (M.k (leafLane o 533)).val = _
    simp only [leafLane, show ¬ (533 : Nat) < 2 by (clear * -; first | decide | (simp only [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]; done) | ring1 | omega), show ¬ (533 : Nat) < 514 by (clear * -; first | decide | (simp only [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]; done) | ring1 | omega),
      ↓reduceIte]
    rw [show (533 : Nat) - 514 = 19 from rfl, C2]
    exact congrArg (· ^^^ _) (hEk 531 (by (clear * -; first | decide | (simp only [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]; done) | ring1 | omega))).2
  · show (M.k (leafLane o l)).val = _
    simp only [leafLane, show ¬ l < 2 by (clear * - h1 h2; omega), show ¬ l < 514 by (clear * - h1 h2; omega), ↓reduceIte]
    exact C3 (l - 514) (by (clear * - h1 h2; omega)) (by (clear * - h1 h2; omega))
  · show (M.k (leafLane o 543)).val = _
    simp only [leafLane, show ¬ (543 : Nat) < 2 by (clear * -; first | decide | (simp only [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]; done) | ring1 | omega), show ¬ (543 : Nat) < 514 by (clear * -; first | decide | (simp only [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]; done) | ring1 | omega),
      ↓reduceIte]
    exact C4
  · simp only [List.getElem_map, List.getElem_range]
    rw [digOfW_get _ hk, show (4 * i + k / 8) / 4 = i by (clear * - hk; omega), show (4 * i + k / 8) % 4 = k / 8 by (clear * - hk; omega)]
    rfl

/-- **A path node** (level `t`) of the mux outputs. -/
theorem node_digest {c : Ctx} {M : Mem} {I : SigIn} {o : SigOut} {r : Ptr} {Zn : Nat}
    (hks : SigKS I o M.k) (hbits : SigBits I o M.k) (hZ : M.k Zn = 0)
    (h : SegsHold c M r (loop [4] (twoLanes Zn 0x4D I.bp (I.bp + 8) 16) r).2)
    (e : (loop [4] (twoLanes Zn 0x4D I.bp (I.bp + 8) 16) r).1 = o.msg.xp) {t : Nat} (ht : t < 16) :
    digAt M.k (I.yc + 4 * (t + 1)) = sigNode (digOfW fun l => (M.k (o.pa.cell (4 + l) t).n).val)
      (digOfW fun l => (M.k (o.pa.cell (8 + l) t).n).val) := by
  obtain ⟨st, hp, hd⟩ := hks.path t ht
  rw [hd]
  rw [xcell_path _ _ ht] at hp
  have hjf : t < 2 ^ ([4] : List Nat).sum := by simpa using ht
  have ht4 : t < 2 ^ 4 := by simpa using ht
  have hd4 := loop_dims_eq [4] (twoLanes Zn 0x4D I.bp (I.bp + 8) 16) r
  obtain ⟨L0, Lk, L4, Lb, L8, Lz, L16⟩ := two_spec h hjf hZ
  beta_reduce at L0 Lk L4 Lb L8 Lz L16
  have hlane : ∀ l, (M.k (o.msg.xp.cell l t).n).val =
      V M ((loop [4] (twoLanes Zn 0x4D I.bp (I.bp + 8) 16) r).1.cell l t).n := by
    intro l; rw [e]
  refine node_of_lanes (lane := fun l => (M.k (o.msg.xp.cell l t).n).val)
    (A := fun k => OV M (loop [4] (twoLanes Zn 0x4D I.bp (I.bp + 8) 16) r).1 t (oS (I.bp + k) 16))
    (B := fun k => OV M (loop [4] (twoLanes Zn 0x4D I.bp (I.bp + 8) 16) r).1 t (oS (I.bp + 8 + k) 16))
    (fun l hl => ⟨?_, ?_⟩) (fun l hl => ⟨?_, ?_⟩) (by rw [hlane]; exact L0)
    (fun k h1 h2 => by rw [hlane]; exact Lk k h1 h2) (by rw [hlane]; exact L4)
    (fun k h1 h2 => by rw [hlane]; exact Lb k h1 h2) (by rw [hlane]; exact L8)
    (fun l h1 h2 => by rw [hlane]; exact Lz l h1 h2) (by rw [hlane]; exact L16) hp
  · have := (hbits.p t ht 0 (by (clear * -; first | decide | (simp only [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]; done) | ring1 | omega)) l hl).1
    simp only [Nat.mul_zero, Nat.add_zero] at this
    rw [ovS_V hd4 ht4 (show I.bp + 2 * l + 16 * t = I.bp + 2 * (8 * t + l) by ring)]
    dsimp only [V]; rw [sOut1_val this]; rfl
  · have := (hbits.p t ht 0 (by (clear * -; first | decide | (simp only [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]; done) | ring1 | omega)) l hl).2
    simp only [Nat.mul_zero, Nat.add_zero] at this
    rw [ovS_V hd4 ht4 (show I.bp + (2 * l + 1) + 16 * t = I.bp + 2 * (8 * t + l) + 1 by ring)]
    dsimp only [V]; rw [sOut1_val this]; rfl
  · have := (hbits.p t ht 1 (by (clear * -; first | decide | (simp only [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]; done) | ring1 | omega)) l hl).1
    rw [show 4 + 4 * 1 + l = 8 + l by ring] at this
    rw [ovS_V hd4 ht4 (show I.bp + 8 + 2 * l + 16 * t = I.bp + 2 * (8 * t + 4 * 1 + l) by ring)]
    dsimp only [V]; rw [sOut1_val this]; rfl
  · have := (hbits.p t ht 1 (by (clear * -; first | decide | (simp only [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]; done) | ring1 | omega)) l hl).2
    rw [show 4 + 4 * 1 + l = 8 + l by ring] at this
    rw [ovS_V hd4 ht4
      (show I.bp + 8 + (2 * l + 1) + 16 * t = I.bp + 2 * (8 * t + 4 * 1 + l) + 1 by ring)]
    dsimp only [V]; rw [sOut1_val this]; rfl

/-! ## The index -/

theorem idx_lt {c : Ctx} {M : Mem} {I : SigIn} {o : SigOut} {q : Ptr}
    (has : Ok c M (assert0 (kc (I.bi + 17)) (kc I.flag)) q) (hg : M.k I.flag = 1)
    (hbits : SigBits I o M.k) : (M.k I.sg).val.toNat < 2 ^ 16 := by
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

end Lvm.QSig.SigH
end
-- ===== end of `LvmQSigSigAux` =====

-- ===== merged from `LvmQSigSig` (GOLF module merge: `LvmQSigSig.lean` is now a stub importing `LvmQSigSound`) =====
section

/-!
# `Q_sig`: the child's signature (`SigOk`)

New for lvm (WP-12). See `LvmQSigDefs` for the hypotheses. FR's `wots_sound` with the chains
(`chain_end` of `step_m`/`step_c` and `sel_m`/`sel_c`), the key leaf (`leaf_digest`), the path
(`node_digest`, `path_spec`) and the root check of `header_spec`; helpers in `LvmQSigSigAux`.
-/

set_option autoImplicit false

namespace Lvm.QSig

open RecursionFast RecursionFast.Keccak Lvm Lvm.Loop Lvm.Loop.Build Lvm.Bits Lvm.KSponge Lvm.Wots
open Lvm.QSig.SigH

/-- **The child's signature** (the one WOTS walk, A2). -/
theorem qsig_sigOk {c : Ctx} {M : Mem} {p : Ptr} {I : SigIn} (h : Ok c M (qsig I) p)
    (hg : M.k I.flag = 1) (hks : SigKS I (qsig I p).1 M.k) (hbits : SigBits I (qsig I p).1 M.k)
    (hinj : ∀ a b, a < 1024 → b < 1024 → FK.x ^ a = FK.x ^ b → a = b) :
    SigOk (digAt M.k I.vk) (digAt M.k I.md) (sigAt' M.k I.sg) = true := by
  obtain ⟨⟨q1, hpre, epre⟩, ⟨q2, hcm, ecm⟩, hcc, ⟨q4, hck⟩, ⟨q5, hpa, epa⟩, ⟨q6, hhd⟩, ⟨q7, has⟩, -,
    ⟨q9, hmsg, emsg⟩⟩ := qsig_parts h
  obtain ⟨⟨r1, hxm, exm⟩, hxc, ⟨r3, hla, ela⟩, ⟨r4, hlb, elb⟩, ⟨r5, hlc, elc⟩, ⟨r6, hxp, exp⟩, -, -⟩ :=
    gMsg_parts hmsg
  rw [emsg] at exm hxc ela elb elc exp
  have pre := gPre_spec hpre.1
  rw [epre] at pre
  obtain ⟨hZt, hOt, hZ, hO, hT⟩ := pre
  clear h hpre epre hmsg emsg
  generalize (qsig I p).1 = o at *
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

end Lvm.QSig
end
-- ===== end of `LvmQSigSig` =====

-- ===== merged from `LvmQSigXs` (GOLF module merge: `LvmQSigXs.lean` is now a stub importing `LvmQSigSound`) =====
section

/-!
# `Q_sig`: the `KS` message lanes are input cells (decision A19)

New for lvm (WP-12). The `KS` rows read their message lanes from the input array `I.xs` (row `r`'s
lane `l` at `I.xs + 17 r + l`); `Q_sig` computes the message lanes consecutively from `o.x0`
(`xcell_eq`) and asserts, gated by the node flag, that they equal the input array (`gXeq`,
`qsig_xeq`). **`qsig_sound_in`** is `qsig_sound` with the `KS` hypothesis on the input array
(`SigKSin`, which does not mention `Q_sig`'s output).
-/

set_option autoImplicit false

namespace Lvm.QSig

open RecursionFast RecursionFast.Keccak Lvm Lvm.Loop Lvm.Loop.Build Lvm.KSponge Lvm.Wots

/-! ## The layout of the message lanes -/

theorem out_bind {α β : Type} (m : BM α) (f : α → BM β) (p : Ptr) :
    ((m >>= f) p).1 = (f (m p).1 (p.adv (m p).2)).1 := rfl

theorem getPtr_apply (p : Ptr) : getPtr p = (p, []) := rfl

/-! The same equations as proof-producing `simp` rules (proofs that are not `rfl`): as `rfl` lemmas
`simp` applies them definitionally and the kernel re-derives each step by unfolding `>>=`, where it
compares the blocks' builders first (1 s each in `qsig_msg`, `qsig_gXeq`). -/

theorem out_bind_eq {α β : Type} (m : BM α) (f : α → BM β) (p : Ptr) :
    ((m >>= f) p).1 = (f (m p).1 (p.adv (m p).2)).1 := (out_bind m f p).trans rfl

theorem getPtr_apply_eq (p : Ptr) : getPtr p = (p, []) := (getPtr_apply p).trans rfl

theorem pure_apply_eq {α : Type} (x : α) (p : Ptr) : (pure x : BM α) p = (x, []) := (pure_apply x p).trans rfl

/-- Every template row writes one `K` cell. -/
def AllK (tpl : List LRow) : Prop := ∀ r ∈ tpl, r.op ≠ .assert0 ∧ r.ty = .K

theorem ltw_allK {tpl : List LRow} (hw : AllK tpl) : ltw .K tpl = tpl.length := by
  have hall : ∀ r ∈ tpl, LRow.w .K r = 1 := fun r hr => by
    obtain ⟨h1, h2⟩ := hw r hr
    obtain ⟨op, ty, args⟩ := r
    simp only at h1 h2; subst h2
    cases op <;> simp_all [LRow.w, Row.w, Row.writes]
  unfold ltw
  rw [List.map_congr_left (g := fun _ => 1) hall]
  simp

theorem loop_cellK {dims : List Nat} {tpl : List LRow} (q : Ptr) (hw : AllK tpl) {t : Nat}
    (jf : Nat) (ht : t < tpl.length) :
    ((loop dims tpl q).1.cell t jf).n = q.k + t + tpl.length * jf :=
  cell_lin1 _ t jf ht hw

theorem loop_advK {dims : List Nat} {tpl : List LRow} (q : Ptr) (hw : AllK tpl) :
    (q.adv (loop dims tpl q).2).k = q.k + tpl.length * 2 ^ dims.sum := by
  have hs : (mkLoop q dims tpl).size = 2 ^ dims.sum := rfl
  show q.k + segsW .K [.blk (mkLoop q dims tpl)] = _
  simp only [segsW, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Seg.w, mkLoop_tw,
    ltw_allK hw, hs, Nat.add_zero]

/-- A sequence of loops of the same size. -/
theorem seqAll_loops {d : List Nat} {tp : Nat → List LRow} {w : Nat} (hw : ∀ u, AllK (tp u))
    (hl : ∀ u, (tp u).length * 2 ^ d.sum = w) :
    ∀ (ls : List Nat) (q : Ptr),
      (q.adv (seqAll (ls.map fun u => loop d (tp u)) q).2).k = q.k + w * ls.length ∧
      ∀ i < ls.length, ∃ q' : Ptr, q'.k = q.k + w * i ∧
        (seqAll (ls.map fun u => loop d (tp u)) q).1.getD i dLoop = (loop d (tp (ls.getD i 0)) q').1
  | [], q => ⟨by simp [seqAll, pure_apply], fun i hi => absurd hi (by simp)⟩
  | u :: ls, q => by
    obtain ⟨ih1, ih2⟩ := seqAll_loops hw hl ls (q.adv (loop d (tp u) q).2)
    rw [List.map_cons, seqAll_cons_apply]
    refine ⟨?_, fun i hi => ?_⟩
    · rw [List.append_nil, Ptr.adv_append, ih1, loop_advK q (hw u), hl u, List.length_cons,
        Nat.mul_succ]
      (clear * -; first | decide | (simp only [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]; done) | ring1 | omega)
    · cases i with
      | zero => exact ⟨q, by simp, rfl⟩
      | succ i =>
        obtain ⟨q', e1, e2⟩ := ih2 i (by simpa using hi)
        refine ⟨q', ?_, by simpa using e2⟩
        rw [e1, loop_advK q (hw u), hl u, Nat.mul_succ]
        (clear * -; first | decide | (simp only [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]; done) | ring1 | omega)

theorem forN_loops {n : Nat} {d : List Nat} {tp : Nat → List LRow} {w : Nat} (hw : ∀ u, AllK (tp u))
    (hl : ∀ u, (tp u).length * 2 ^ d.sum = w) (q : Ptr) :
    (q.adv (forN n (fun u => loop d (tp u)) q).2).k = q.k + w * n ∧
      ∀ i < n, ∃ q' : Ptr, q'.k = q.k + w * i ∧
        (forN n (fun u => loop d (tp u)) q).1.getD i dLoop = (loop d (tp i) q').1 := by
  obtain ⟨h1, h2⟩ := seqAll_loops hw hl (List.range n) q
  refine ⟨by rw [List.length_range] at h1; exact h1, fun i hi => ?_⟩
  obtain ⟨q', e1, e2⟩ := h2 i (by simpa using hi)
  refine ⟨q', e1, ?_⟩
  rw [show (List.range n).getD i 0 = i by simp [hi]] at e2
  exact e2

theorem stepsTpl_allK (I : SigIn) (Zn : Nat) (T : Opd) (c1 : Nat → UInt64) (xb st : Nat) :
    AllK (stepsTpl I Zn T c1 xb st) := by
  simp only [AllK, stepsTpl, stepLanes, zeroLanes, padLane, List.forall_mem_append,
    List.forall_mem_cons, List.forall_mem_map]
  simp

theorem stepsTpl_len (I : SigIn) (Zn : Nat) (T : Opd) (c1 : Nat → UInt64) (xb st : Nat) :
    (stepsTpl I Zn T c1 xb st).length = 51 := by
  simp [stepsTpl, stepLanes, zeroLanes]

theorem leafA_allK (I : SigIn) : AllK (leafA I) := by
  simp only [AllK, leafA, List.forall_mem_cons]
  simp

theorem leafB_allK (I : SigIn) : AllK (leafB I) := by
  simp only [AllK, leafB, List.forall_mem_cons]
  simp

theorem leafC_allK (I : SigIn) (Zn : Nat) : AllK (leafC I Zn) := by
  simp only [AllK, leafC, zeroLanes, padLane, List.forall_mem_append, List.forall_mem_cons,
    List.forall_mem_map]
  simp

theorem leafC_len (I : SigIn) (Zn : Nat) : (leafC I Zn).length = 30 := by simp [leafC, zeroLanes]

theorem twoLanes_allK (Zn : Nat) (tag : UInt64) (aB bB st : Nat) :
    AllK (twoLanes Zn tag aB bB st) := by
  simp only [AllK, twoLanes, zeroLanes, padLane, List.forall_mem_append, List.forall_mem_cons,
    List.forall_mem_map]
  simp

theorem twoLanes_len (Zn : Nat) (tag : UInt64) (aB bB st : Nat) :
    (twoLanes Zn tag aB bB st).length = 17 := by simp [twoLanes, zeroLanes]

theorem leafStmt_allK (I : SigIn) (Zn : Nat) : AllK (leafStmtLanes I Zn) := by
  simp only [AllK, leafStmtLanes, zeroLanes, padLane, List.forall_mem_append, List.forall_mem_cons,
    List.forall_mem_map]
  simp

theorem leafStmt_len (I : SigIn) (Zn : Nat) : (leafStmtLanes I Zn).length = 17 := by
  simp [leafStmtLanes, zeroLanes]

/-- **The message lanes of `gMsg` at `q` are consecutive from `q.k`.** -/
theorem gMsg_xcell {I : SigIn} {Zn Tb : Nat} {q : Ptr} {o : SigOut} (hm : o.msg = (gMsg I Zn Tb q).1)
    {r l : Nat} (hr : r < 449) (hl : l < 17) : xcell o r l = q.k + 17 * r + l := by
  simp only [gMsg, out_bind, pure_apply] at hm
  obtain ⟨hF, hG⟩ := forN_loops (n := 5) (d := []) (w := 51)
    (tp := fun u => stepsTpl I Zn (oA Zn)
      (fun s => ((128 + u).toUInt64 <<< (8 : Nat).toUInt64) ^^^ (s.toUInt64 <<< (16 : Nat).toUInt64))
      (I.bx + 24 * (128 + u)) 0)
    (fun u => stepsTpl_allK _ _ _ _ _ _) (fun u => by simp [stepsTpl_len])
    (q.adv (loop [7] (stepsTpl I Zn (oS Tb 1) (fun s => (s.toUInt64 <<< (16 : Nat).toUInt64)) I.bx 24) q).2)
  unfold xcell leafLane
  by_cases h1 : r < 384
  on_goal 1 => rw [if_pos h1]
  on_goal 2 => rw [if_neg h1]; by_cases h2 : r < 399
  on_goal 2 => rw [if_pos h2]
  on_goal 3 => rw [if_neg h2]; by_cases h3 : r < 431
  on_goal 3 => rw [if_pos h3]; by_cases h4 : 17 * (r - 399) + l < 2
  on_goal 3 => rw [if_pos h4]
  on_goal 4 => rw [if_neg h4]; by_cases h5 : 17 * (r - 399) + l < 514
  on_goal 4 => rw [if_pos h5]
  on_goal 5 => rw [if_neg h5]
  on_goal 6 => rw [if_neg h3]; by_cases h6 : r < 447
  on_goal 6 => rw [if_pos h6]
  on_goal 7 => rw [if_neg h6]; by_cases h7 : r = 447
  on_goal 7 => rw [if_pos h7]
  on_goal 8 => rw [if_neg h7]
  all_goals (rw [hm]; dsimp only)
  · rw [loop_cellK _ (stepsTpl_allK _ _ _ _ _ _) _ (by rw [stepsTpl_len]; (clear * - hl; omega)), stepsTpl_len]
    (clear * -; first | decide | (simp only [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]; done) | ring1 | (clear * - q r l; omega))
  · obtain ⟨q', e1, e2⟩ := hG ((r - 384) / 3) (by (clear * - hr h1 h2; omega))
    rw [e2, loop_cellK _ (stepsTpl_allK _ _ _ _ _ _) _ (by rw [stepsTpl_len]; (clear * - hl; omega)), e1,
      loop_advK _ (stepsTpl_allK _ _ _ _ _ _), stepsTpl_len]
    simp only [List.sum_cons, List.sum_nil]
    (clear * - hr h1 h2; omega)
  · rw [loop_cellK _ (leafA_allK I) _ (by simp [leafA]; (clear * - h4; omega)), hF,
      loop_advK _ (stepsTpl_allK _ _ _ _ _ _), stepsTpl_len]
    simp only [List.sum_cons, List.sum_nil]
    (clear * - hr hl h1 h2 h3 h4; omega)
  · rw [loop_cellK _ (leafB_allK I) _ (by simp [leafB]), loop_advK _ (leafA_allK I), hF,
      loop_advK _ (stepsTpl_allK _ _ _ _ _ _), stepsTpl_len]
    simp only [List.sum_cons, List.sum_nil, leafA, leafB, List.length_cons, List.length_nil]
    (clear * - hr h1 h2 h3 h4 h5; omega)
  · rw [loop_cellK _ (leafC_allK I Zn) _ (by rw [leafC_len]; (clear * - hr hl h1 h2 h3 h5; omega)), loop_advK _ (leafB_allK I),
      loop_advK _ (leafA_allK I), hF, loop_advK _ (stepsTpl_allK _ _ _ _ _ _), stepsTpl_len]
    simp only [List.sum_cons, List.sum_nil, leafA, leafB, List.length_cons, List.length_nil]
    (clear * - hr h1 h2 h3 h5; omega)
  · rw [loop_cellK _ (twoLanes_allK _ _ _ _ _) _ (by rw [twoLanes_len]; (clear * - hl; omega)), twoLanes_len,
      loop_advK _ (leafC_allK I Zn), loop_advK _ (leafB_allK I),
      loop_advK _ (leafA_allK I), hF, loop_advK _ (stepsTpl_allK _ _ _ _ _ _), stepsTpl_len, leafC_len]
    simp only [List.sum_cons, List.sum_nil, leafA, leafB, List.length_cons, List.length_nil]
    (clear * - hr h1 h2 h3 h6; omega)
  · rw [loop_cellK _ (leafStmt_allK _ _) _ (by rw [leafStmt_len]; (clear * - hl; omega)), leafStmt_len,
      loop_advK _ (twoLanes_allK _ _ _ _ _), twoLanes_len, loop_advK _ (leafC_allK I Zn),
      loop_advK _ (leafB_allK I), loop_advK _ (leafA_allK I), hF, loop_advK _ (stepsTpl_allK _ _ _ _ _ _),
      stepsTpl_len, leafC_len]
    simp only [List.sum_cons, List.sum_nil, leafA, leafB, List.length_cons, List.length_nil]
    (clear * - h7; omega)
  · rw [loop_cellK _ (twoLanes_allK _ _ _ _ _) _ (by rw [twoLanes_len]; (clear * - hl; omega)), twoLanes_len,
      loop_advK _ (leafStmt_allK _ _), leafStmt_len,
      loop_advK _ (twoLanes_allK _ _ _ _ _), twoLanes_len, loop_advK _ (leafC_allK I Zn),
      loop_advK _ (leafB_allK I), loop_advK _ (leafA_allK I), hF, loop_advK _ (stepsTpl_allK _ _ _ _ _ _),
      stepsTpl_len, leafC_len]
    simp only [List.sum_cons, List.sum_nil, leafA, leafB, List.length_cons, List.length_nil]
    (clear * - hr h1 h2 h3 h6 h7; omega)

theorem qsig_msg (I : SigIn) (p : Ptr) : ∃ q : Ptr, (qsig I p).1.x0 = q.k ∧
    (qsig I p).1.msg = (gMsg I (qsig I p).1.pre.1.n (Tbase (qsig I p).1.pre) q).1 := by
  unfold qsig
  simp only [out_bind_eq, getPtr_apply_eq, pure_apply_eq, Ptr.adv_nil]
  exact ⟨_, rfl, rfl⟩

/-- **KS row `r`'s lane `l` is the cell `x0 + 17 r + l`.** -/
theorem xcell_eq {I : SigIn} {p : Ptr} {r l : Nat} (hr : r < 449) (hl : l < 17) :
    xcell (qsig I p).1 r l = (qsig I p).1.x0 + 17 * r + l := by
  obtain ⟨q, e1, e2⟩ := qsig_msg I p
  rw [e1]
  exact gMsg_xcell e2 hr hl

/-! ## The equality with the input array -/

/-- One `xeqTpl` loop: lane `off + j` of the message equals lane `off + j` of the input array when
the gate is on. -/
theorem xeq_loop {c : Ctx} {M : Mem} {p : Ptr} {I : SigIn} {x0 d off : Nat}
    (h : SegsHold c M p (loop [d] (xeqTpl I x0 off) p).2)
    (hA : SegsAssert M p (loop [d] (xeqTpl I x0 off) p).2) (hg : M.k I.flag = 1) :
    ∀ j < 2 ^ d, M.k (x0 + off + j) = M.k (I.xs + off + j) := by
  intro j hj
  have hjf : j < 2 ^ ([d] : List Nat).sum := by simpa using hj
  have hK : OpdK (loop [d] (xeqTpl I x0 off) p).1 (.cur 0) := rfl
  have r := loopK_lin h hjf (t := 0) (by simp [xeqTpl]) rfl rfl rfl
  have a := loopK_as0 hA hjf (t := 1) (by simp [xeqTpl]) rfl hK rfl
  rw [ov_cur M _ hjf 0 rfl, r, ov_oA, ov_oS M _ rfl hj, ov_oS M _ rfl hj, hg] at a
  simp only [one_mul, add_zero] at a
  have := congrArg (· + M.k (I.xs + off + j)) a
  simpa [add_assoc, FK.add_self] using this

/-- **`gXeq`**: the 7,633 message lanes equal the input array when the gate is on. -/
theorem gXeq_spec {c : Ctx} {M : Mem} {q : Ptr} {I : SigIn} {x0 : Nat} (h : Ok c M (gXeq I x0) q)
    (hg : M.k I.flag = 1) : ∀ j < 7633, M.k (x0 + j) = M.k (I.xs + j) := by
  obtain ⟨h, hA⟩ := h
  simp only [gXeq, hold_bind, assert_bind] at h hA
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, -⟩ := h
  obtain ⟨a0, a1, a2, a3, a4, a5, a6, a7, -⟩ := hA
  have e0 := xeq_loop h0 a0 hg
  have e1 := xeq_loop h1 a1 hg
  have e2 := xeq_loop h2 a2 hg
  have e3 := xeq_loop h3 a3 hg
  have e4 := xeq_loop h4 a4 hg
  have e5 := xeq_loop h5 a5 hg
  have e6 := xeq_loop h6 a6 hg
  have e7 := xeq_loop h7 a7 hg
  intro j hj
  have key : ∀ off d, (∀ i < 2 ^ d, M.k (x0 + off + i) = M.k (I.xs + off + i)) →
      off ≤ j → j < off + 2 ^ d → M.k (x0 + j) = M.k (I.xs + j) := fun off d e h1 h2 => by
    have := e (j - off) (by (clear * - h1 h2; omega))
    rwa [show x0 + off + (j - off) = x0 + j by (clear * - h1; omega),
      show I.xs + off + (j - off) = I.xs + j by (clear * - h1; omega)] at this
  by_cases k0 : j < 4096
  · exact key 0 12 e0 (by (clear * - hj k0; omega)) (by norm_num; omega)
  by_cases k1 : j < 6144
  · exact key 4096 11 e1 (by (clear * - hj k0 k1; omega)) (by norm_num; omega)
  by_cases k2 : j < 7168
  · exact key 6144 10 e2 (by (clear * - hj k0 k1 k2; omega)) (by norm_num; omega)
  by_cases k3 : j < 7424
  · exact key 7168 8 e3 (by (clear * - hj k0 k1 k2 k3; omega)) (by norm_num; omega)
  by_cases k4 : j < 7552
  · exact key 7424 7 e4 (by (clear * - hj k0 k1 k2 k3 k4; omega)) (by norm_num; omega)
  by_cases k5 : j < 7616
  · exact key 7552 6 e5 (by (clear * - hj k0 k1 k2 k3 k4 k5; omega)) (by norm_num; omega)
  by_cases k6 : j < 7632
  · exact key 7616 4 e6 (by (clear * - hj k0 k1 k2 k3 k4 k5 k6; omega)) (by norm_num; omega)
  · exact key 7632 0 e7 (by (clear * - hj k0 k1 k2 k3 k4 k5 k6; omega)) (by norm_num; omega)

set_option maxRecDepth 100000 in
theorem qsig_gXeq {c : Ctx} {M : Mem} {p : Ptr} {I : SigIn} (h : Ok c M (qsig I) p) :
    ∃ q, Ok c M (gXeq I (qsig I p).1.x0) q := by
  unfold qsig at h ⊢
  obtain ⟨-, h, -⟩ := ok_bind' h
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
theorem qsig_xeq {c : Ctx} {M : Mem} {p : Ptr} {I : SigIn} (h : Ok c M (qsig I) p)
    (hg : M.k I.flag = 1) : ∀ j < 7633, M.k ((qsig I p).1.x0 + j) = M.k (I.xs + j) := by
  obtain ⟨q, hq⟩ := qsig_gXeq h
  exact gXeq_spec hq hg

/-! ## `qsig_sound` on the input array -/

/-- **The `KS` rows of the signature schedule, on the input array** (`SigKS` with row `r`'s lanes
the cells `I.xs + 17 r + l`). -/
structure SigKSin (I : SigIn) (v : Nat → FK) : Prop where
  step : ∀ r < 399, OneHash v (fun l => I.xs + 17 * r + l) (I.ys + 4 * r)
  leaf : ∃ sIn sOut : Nat → State, sIn 0 = zeroSt ∧
    (∀ u < 32, BlockPerm (xorMsg (sIn u) (laneByte (lanesW v (fun l => I.xs + 17 * (399 + u) + l))))
      (sOut u)) ∧
    (∀ u, u + 1 < 32 → sIn (u + 1) = sOut u) ∧ digAt v I.yc = stDigest (sOut 31)
  path : ∀ t < 16, OneHash v (fun l => I.xs + 17 * (431 + t) + l) (I.yc + 4 * (t + 1))
  ls : OneHash v (fun l => I.xs + 17 * 447 + l) I.yls
  ns : OneHash v (fun l => I.xs + 17 * 448 + l) I.yns

/-- A block's absorption reads only lanes `0 … 16`. -/
theorem xorMsg_lanes {a : State} {v : Nat → FK} {f g : Nat → Nat} (h : ∀ l < 17, v (f l) = v (g l)) :
    xorMsg a (laneByte (lanesW v f)) = xorMsg a (laneByte (lanesW v g)) := by
  have e : rateArr (laneByte (lanesW v f)) = rateArr (laneByte (lanesW v g)) := by
    unfold rateArr
    congr 1
    funext j
    have hj : j.val < 136 := j.2
    simp only [laneByte, lanesW]
    rw [h _ (by (clear * - hj; omega))]
  simp only [xorMsg, e]

theorem oneHash_lanes {v : Nat → FK} {f g : Nat → Nat} {y : Nat} (h : ∀ l < 17, v (f l) = v (g l))
    (hg : OneHash v g y) : OneHash v f y := by
  obtain ⟨s, h1, h2⟩ := hg
  exact ⟨s, by rw [xorMsg_lanes h]; exact h1, h2⟩

/-- `SigKSin` gives `SigKS`. -/
theorem sigKS_of_in {c : Ctx} {M : Mem} {p : Ptr} {I : SigIn} (h : Ok c M (qsig I) p)
    (hg : M.k I.flag = 1) (hks : SigKSin I M.k) : SigKS I (qsig I p).1 M.k := by
  have hx : ∀ r < 449, ∀ l < 17, M.k (xcell (qsig I p).1 r l) = M.k (I.xs + 17 * r + l) :=
    fun r hr l hl => by
      rw [xcell_eq hr hl, Nat.add_assoc, qsig_xeq h hg _ (by (clear * - hr hl; omega)), Nat.add_assoc]
  obtain ⟨sIn, sOut, h0, h1, h2, h3⟩ := hks.leaf
  refine ⟨fun r hr => oneHash_lanes (hx r (by (clear * - hr; omega))) (hks.step r hr),
    ⟨sIn, sOut, h0, fun u hu => ?_, h2, h3⟩,
    fun t ht => oneHash_lanes (hx _ (by (clear * - ht; omega))) (hks.path t ht),
    oneHash_lanes (hx _ (by (clear * -; first | decide | (simp only [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]; done) | ring1 | omega))) hks.ls, oneHash_lanes (hx _ (by (clear * -; first | decide | (simp only [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]; done) | ring1 | omega))) hks.ns⟩
  rw [xorMsg_lanes (hx _ (by (clear * - hu; omega)))]
  exact h1 u hu

end Lvm.QSig
end
-- ===== end of `LvmQSigXs` =====

/-!
# `Q_sig` is sound (BLUEPRINT §4.6, §11 A2, A3)

New for lvm (WP-12). **`qsig_sound`** (the theorem WP-14 consumes): `LvmQSigDefs` states the
hypotheses (`SigKS`, `SigBits`) and the conclusions (`SigOk`, `ChildOk`). **`qsig_sound_in`**: the
same with the `KS` hypothesis on the message input array `I.xs` (`SigKSin`, decision A19), which
`Q_sig` asserts equal to its message lanes (`LvmQSigXs`).
-/

set_option autoImplicit false

namespace Lvm.QSig

open RecursionFast Lvm Lvm.Loop Lvm.Loop.Build

/-- **`Q_sig` is sound.** -/
theorem qsig_sound {c : Ctx} {M : Mem} {p : Ptr} {I : SigIn} (hln : 1 ≤ I.ln ∧ I.ln ≤ 62) (h : Ok c M (qsig I) p)
    (hg : M.k I.flag = 1) (hks : SigKS I (qsig I p).1 M.k) (hbits : SigBits I (qsig I p).1 M.k)
    (hinj : ∀ a b, a < 1024 → b < 1024 → FK.x ^ a = FK.x ^ b → a = b) :
    SigOk (digAt M.k I.vk) (digAt M.k I.md) (sigAt' M.k I.sg) = true ∧ ChildOk I M.k :=
  ⟨qsig_sigOk h hg hks hbits hinj, qsig_child hln h hg hks hbits⟩

/-- **`Q_sig` is sound, `KS` on the input array** (A19). -/
theorem qsig_sound_in {c : Ctx} {M : Mem} {p : Ptr} {I : SigIn} (hln : 1 ≤ I.ln ∧ I.ln ≤ 62) (h : Ok c M (qsig I) p)
    (hg : M.k I.flag = 1) (hks : SigKSin I M.k) (hbits : SigBits I (qsig I p).1 M.k)
    (hinj : ∀ a b, a < 1024 → b < 1024 → FK.x ^ a = FK.x ^ b → a = b) :
    SigOk (digAt M.k I.vk) (digAt M.k I.md) (sigAt' M.k I.sg) = true ∧ ChildOk I M.k :=
  qsig_sound hln h hg (sigKS_of_in h hg hks) hbits hinj

end Lvm.QSig
