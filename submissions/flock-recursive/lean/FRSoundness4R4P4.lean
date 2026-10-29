-- New for `flock-recursive` (BLUEPRINT revision 4.1, A.9 `finP 4`; track R4h). The 3.x templates are
-- `FRVIRFinalsSG.flag_finP4` (`run_encOps`, `run_positions`), `FRSoundnessAccEq.encVal_eq_encAt` and
-- the `pf0`/`enc` cases of `FRSoundnessAccLog.finLog_of_run`.
import FRSoundness4R4LinkP

/-!
# `FinRest4.pf0` and `FinRest4.enc`: `finP 4` (`gFinPTop`) on an accepted run

`gFinP P 4 = gFinPTop P` (field `10` of the rest) is 3.x's `finP 4` over `2^P.S.pf` final
elements. Its relocated run (`reloc P.S`: the final message's reads become absolute,
`fieldOffOf P.S fFinal + 32 c`) has the flag **`relP44`** (**`flag_gFinP4`**): every level-4
query's fold is `encVal4` (Horner over the final elements with the weights `tensorW p e_v`) at its
position, and Pf's first claim is P1.4's last.

* **`pf04_of_fields`**: `FinRest4.pf0` (`rSum pfStart es 0 = c1 c₀ 4 L es`, any `c₀`).
* **`encVal4_eq`** (spec side, 3.x's `encVal_eq_encAt` for any `n ≤ 7`): with `tensorW` at
  `tensorWS`, `encVal4` is `encF n m p` when the final elements agree with `m` below `2^n` and are
  zero from `2^n` to `2^7`.
* **`enc4_of_fields`**: `FinRest4.enc` for the folds `yv4`, given the final message's zero tail
  beyond `2^mLog` (the kind's exact tail check, at the end of `finPf`: `FRSoundness4R4PfRun`).
-/

namespace FR.Snd.R4
open RecursionFast Rev4 Finset

/-! ## The relocation leaves `gEncOps` unchanged -/

theorem layerOps_reloc (S : Seq) (w : Reg) (xs : List Reg) (n b : ℕ) :
    ∀ k, (layerOps w xs n b k).map (reloc S) = layerOps w xs n b k
  | 0 => rfl
  | k + 1 => by rw [layerOps, List.map_append, layerOps_reloc S w xs n b k]; rfl

theorem hornerKOps_reloc (S : Seq) (ws : List Reg) :
    ∀ v xs b, (hornerKOps ws v xs b).map (reloc S) = hornerKOps ws v xs b
  | 0, _, _ => rfl
  | v + 1, xs, b => by
    rw [hornerKOps, List.map_append, layerOps_reloc, hornerKOps_reloc S ws v]

theorem gEncOps_reloc (S : Seq) (pf : ℕ) (units fin : List Reg) (j y b : ℕ) :
    (gEncOps pf units fin j y b).map (reloc S) = gEncOps pf units fin j y b := by
  rw [gEncOps, List.map_append, List.map_append, hornerKOps_reloc, List.map_map]; rfl

theorem rest_gFinP4 (P : FinP) :
    (finalsOf P).rest[10]'(by rw [rest_finalsOf_length]; omega) = gFinPTop P := by
  have hl : 4 < ((List.range nLevels).map (gFinP P)).length := by simp [nLevels]
  simp only [Finals.rest, finalsOf, show 10 = 4 + 1 + 1 + 1 + 1 + 1 + 1 by omega,
    List.getElem_cons_succ, List.nil_append, List.cons_append]
  rw [List.getElem_append_left hl, List.getElem_map, List.getElem_range, gFinP, if_neg (by omega)]

/-! ## The flag of the relocated `finP 4` -/

/-- The final message's element `c` in `S`'s format. -/
def finV4 (S : Seq) (inp : Input) (c : ℕ) : K := K.ofBytes (bytesAt inp.π (fieldOffOf S fFinal + 32 * c) 32)

/-- `Enc(final)[p]` as `gEncOps` computes it (Horner over `2^S.pf` elements, `W_v = tensorW p e_v`). -/
def encVal4 (impl : OpImpl) (S : Seq) (inp : Input) (p : ℕ) : K :=
  hornerVal (fun v => impl.tensorW p (gUnitK S.pf v)) S.pf (finV4 S inp)

section Run
variable (impl : OpImpl) (κ : Kind) (inp : Input) (r : Array Val)

/-- **One position at level 4** over `2^pf` final elements `X` (3.x's `run_encOps`). -/
theorem run_gEncOps (pf : ℕ) (units fin : List Reg) (j y : Reg) (X : ℕ → K) (L : List Val)
    (hj : j < r.size) (hy : y < r.size)
    (hu : ∀ v < pf, units.getD v 0 < r.size + L.length ∧
      rd (r ++ L.toArray) (units.getD v 0) = .ak (gUnitK pf v))
    (hf : ∀ c < 2 ^ pf, fin.getD c 0 < r.size + L.length ∧
      rd (r ++ L.toArray) (fin.getD c 0) = .k (X c)) :
    ∃ M, pureRun impl κ inp (gEncOps pf units fin j y (r.size + L.length)) r L =
      some (L ++ M, (Val.k (hornerVal (fun v => impl.tensorW (rd r j).toN (gUnitK pf v)) pf X)).eqv
        (rd r y)) ∧ M.length = gEncW pf := by
  set tws : List Op := (List.range pf).map fun v => .tensorW j (units.getD v 0)
  have h1 := run_frozen impl κ inp r L (twVal impl r L) tws [] (fun op hop Y => by
    obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hop
    have hv' := (hu v (List.mem_range.mp hv)).1
    simp only [evalOp, twVal, rd_app_left _ _ hj, FR.rd_pre r hv'])
  simp only [List.append_nil] at h1
  set M₁ := tws.map (twVal impl r L)
  have hl1 : M₁.length = pf := by simp [M₁, tws]
  have hM₁ : ∀ v < pf, rd (r ++ (L ++ M₁).toArray) ((r.size + L.length) + v) =
      .k (impl.tensorW (rd r j).toN (gUnitK pf v)) := by
    intro v hv
    rw [show (r.size + L.length) + v = r.size + (L.length + v) by omega, rd_app,
      List.getD_append_right _ _ _ _ (by omega)]
    have hu2 := (hu v hv).2
    simp only [List.getD_eq_getElem?_getD] at hu2
    simp [M₁, tws, twVal, hv, hu2]; rfl
  obtain ⟨M₂, h2, hl2, hv2⟩ :=
    run_horner impl κ inp r ((List.range pf).map ((r.size + L.length) + ·))
    (fun v => impl.tensorW (rd r j).toN (gUnitK pf v)) pf fin X (L ++ M₁)
    (fun u hu' => by
      simp only [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hu',
        Option.map_some, Option.getD_some, List.length_append, hl1]
      exact ⟨by rw [← Nat.add_assoc]; exact Nat.add_lt_add_left hu' _, hM₁ u hu'⟩)
    (fun c hc => by
      obtain ⟨a, a'⟩ := hf c hc
      exact ⟨Nat.lt_of_lt_of_le a (by simp only [List.length_append]; omega),
        by rw [FR.rd_pre r a, a']⟩)
  have hb7 : r.size + (L ++ M₁).length = (r.size + L.length) + pf := by
    rw [List.length_append, hl1]; omega
  rw [hb7] at h2 hv2
  refine ⟨M₁ ++ M₂, ?_, by simp [hl1, hl2, gEncW]⟩
  simp only [gEncOps]
  rw [List.append_assoc, pureRun_append, h1, Option.bind_some, pureRun_append, h2,
    Option.bind_some]
  simp only [pureRun, evalOp, allK, Bool.not_true, Bool.false_or, ← List.append_assoc]
  rw [hv2, rd_app_left _ _ hy]
  simp

/-- The flag of position `q` at level 4 (`S`'s format). -/
def encFlag4 (S : Seq) (ys : List Reg) (q : ℕ) : Bool :=
  (Val.k (encVal4 impl S inp (rd r (ys.getD q 0 - 3)).toN)).eqv (rd r (ys.getD q 0))

/-- **The `T` first positions at level 4** (3.x's `run_positions`). -/
theorem run_gPositions (S : Seq) (units fin ys : List Reg) (L : List Val) (hys : ∀ y ∈ ys, y < r.size)
    (hu : ∀ v < S.pf, units.getD v 0 < r.size + L.length ∧
      rd (r ++ L.toArray) (units.getD v 0) = .ak (gUnitK S.pf v))
    (hf : ∀ c < 2 ^ S.pf, fin.getD c 0 < r.size + L.length ∧
      rd (r ++ L.toArray) (fin.getD c 0) = .k (finV4 S inp c)) :
    ∀ T ≤ ys.length, ∃ M, pureRun impl κ inp ((List.range T).flatMap fun q =>
        gEncOps S.pf units fin (ys.getD q 0 - 3) (ys.getD q 0) (r.size + L.length + gEncW S.pf * q)) r L =
      some (L ++ M, (List.range T).all (encFlag4 impl inp r S ys)) ∧ M.length = gEncW S.pf * T
  | 0, _ => ⟨[], by simp [pureRun], by simp⟩
  | T + 1, hT => by
    obtain ⟨M, hM, hl⟩ := run_gPositions S units fin ys L hys hu hf T (by omega)
    have hyT : ys.getD T 0 < r.size := by
      have := hys _ (List.getElem_mem (show T < ys.length by omega))
      simpa [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (show T < ys.length by omega)]
    obtain ⟨M', hM', hl'⟩ := run_gEncOps impl κ inp r S.pf units fin (ys.getD T 0 - 3) (ys.getD T 0)
      (finV4 S inp) (L ++ M) (Nat.lt_of_le_of_lt (Nat.sub_le _ _) hyT) hyT
      (fun v hv => by
        obtain ⟨a, a'⟩ := hu v hv
        exact ⟨Nat.lt_of_lt_of_le a (by simp), by rw [FR.rd_pre r a, a']⟩)
      (fun c hc => by
        obtain ⟨a, a'⟩ := hf c hc
        exact ⟨Nat.lt_of_lt_of_le a (by simp), by rw [FR.rd_pre r a, a']⟩)
    have hb : r.size + (L ++ M).length = r.size + L.length + gEncW S.pf * T := by
      rw [List.length_append, hl]; omega
    rw [hb] at hM'
    refine ⟨M ++ M', ?_, by simp [hl, hl']; ring⟩
    rw [List.range_succ, List.flatMap_append, pureRun_append, hM, Option.bind_some]
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, hM', Option.map_some,
      List.all_append, List.all_cons, List.all_nil, Bool.and_true, List.append_assoc]
    rfl

/-- **`finP 4`'s relation at `S`** (3.x's `relP4`): every `y_q = Enc(final)[p_q]`, and Pf's first
claim is P1.4's last. -/
def relP44 (S : Seq) (fi : FinIn) : Bool :=
  (List.range (ysOf fi 4).length).all (encFlag4 impl inp r S (ysOf fi 4)) &&
    (rd r (claim0 fi "Pf")).eqv (rd r (p1ClaimN fi 4))

/-- **`flag_gFinP4`** (3.x's `flag_finP4`): the relocated `gFinPTop` asks nothing; its flag is
`relP44`. -/
theorem flag_gFinP4 (P : FinP) (fi : FinIn)
    (hin : ∀ x ∈ ysOf fi 4 ++ [claim0 fi "Pf", p1ClaimN fi 4], x < r.size) :
    ∃ L, pureRun impl κ inp ((gFinPTop P fi r.size).1.map (reloc P.S)) r [] =
      some (L, relP44 impl inp r P.S fi) := by
  simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hin
  have hys : ∀ y ∈ ysOf fi 4, y < r.size := fun y hy => hin y (.inl hy)
  have hP := hin _ (.inr (.inl rfl)); have hN := hin _ (.inr (.inr rfl))
  set A : List Op := (List.range (2 ^ P.S.pf)).map fun c => .piElemK 0 (fieldOffOf P.S fFinal + 32 * c)
  set B : List Op := (List.range P.S.pf).map fun v => .const fun _ => .ak (gUnitK P.S.pf v)
  have hAB := run_indep impl κ inp r (p4Val κ inp) (A ++ B) [] (fun op hop regs => by
    rcases List.mem_append.mp hop with h | h
    · obtain ⟨c, -, rfl⟩ := List.mem_map.mp h; rfl
    · obtain ⟨v, -, rfl⟩ := List.mem_map.mp h; rfl)
  simp only [List.nil_append] at hAB
  set L₀ := (A ++ B).map (p4Val κ inp)
  have hl0 : L₀.length = 2 ^ P.S.pf + P.S.pf := by simp [L₀, A, B]
  obtain ⟨M, hM, -⟩ := run_gPositions impl κ inp r P.S ((List.range P.S.pf).map (r.size + 2 ^ P.S.pf + ·))
    ((List.range (2 ^ P.S.pf)).map (r.size + ·)) (ysOf fi 4) L₀ hys
    (fun v hv => by
      have hg : ((List.range P.S.pf).map (r.size + 2 ^ P.S.pf + ·)).getD v 0 = r.size + 2 ^ P.S.pf + v := by
        simp [hv]
      refine ⟨?_, ?_⟩
      · rw [hg, hl0, Nat.add_assoc]; exact Nat.add_lt_add_left (Nat.add_lt_add_left hv _) _
      rw [hg, Nat.add_assoc, rd_app]
      simp only [L₀, A, B, List.getD_eq_getElem?_getD, List.map_append, List.map_map]
      rw [List.getElem?_append_right (by simp)]
      simp [hv, p4Val])
    (fun c hc => by
      have hg : ((List.range (2 ^ P.S.pf)).map (r.size + ·)).getD c 0 = r.size + c := by simp [hc]
      refine ⟨?_, ?_⟩
      · rw [hg, hl0]; exact Nat.add_lt_add_left (Nat.lt_of_lt_of_le hc (Nat.le_add_right _ _)) _
      rw [hg, rd_app]
      simp only [L₀, A, B, List.getD_eq_getElem?_getD, List.map_append, List.map_map]
      rw [List.getElem?_append_left (by simp; omega)]
      simp [hc, p4Val, finV4, absOff_zero])
    (ysOf fi 4).length le_rfl
  rw [hl0] at hM
  have hfz : fFinal < 19 := by decide
  have eA : ((List.range (2 ^ P.S.pf)).map fun c => Op.piElemK fFinal (32 * c)).map (reloc P.S) = A := by
    simp only [A, List.map_map]
    exact List.map_congr_left fun c _ => by simp only [Function.comp_apply, reloc, if_pos hfz]
  have eB : ((List.range P.S.pf).map fun v => Op.const fun _ => Val.ak (gUnitK P.S.pf v)).map (reloc P.S) = B := by
    simp only [B, List.map_map]; rfl
  have eC : ((List.range (ysOf fi 4).length).flatMap fun q =>
      gEncOps P.S.pf ((List.range P.S.pf).map (r.size + 2 ^ P.S.pf + ·)) ((List.range (2 ^ P.S.pf)).map (r.size + ·))
        ((ysOf fi 4).getD q 0 - 3) ((ysOf fi 4).getD q 0) (r.size + (2 ^ P.S.pf + P.S.pf) + gEncW P.S.pf * q)).map
      (reloc P.S) = (List.range (ysOf fi 4).length).flatMap fun q =>
      gEncOps P.S.pf ((List.range P.S.pf).map (r.size + 2 ^ P.S.pf + ·)) ((List.range (2 ^ P.S.pf)).map (r.size + ·))
        ((ysOf fi 4).getD q 0 - 3) ((ysOf fi 4).getD q 0) (r.size + (2 ^ P.S.pf + P.S.pf) + gEncW P.S.pf * q) := by
    rw [List.map_flatMap]; exact List.flatMap_congr fun q _ => gEncOps_reloc _ _ _ _ _ _ _
  refine ⟨L₀ ++ M, ?_⟩
  simp only [gFinPTop, List.map_append, List.map_cons, List.map_nil]
  rw [eA, eB, eC, ← Nat.add_assoc] at *
  rw [pureRun_append, pureRun_append, hAB, Option.bind_some, hM]
  simp only [Option.map_some, Option.bind_some, pureRun, evalOp, allK, Bool.not_true, Bool.false_or,
    rd_app_left _ _ hP, rd_app_left _ _ hN, Bool.true_and, Bool.and_true, relP44, List.append_nil,
    reloc]

end Run

/-! ## Level 4's encoding at the spec -/

theorem gUnitK_seven (v : ℕ) : gUnitK 7 v = unitK v := rfl

/-- **`encVal4` is `Enc(m)[p]`** (3.x's `encVal_eq_encAt` for any `n ≤ 7`): with `tensorW` at
`tensorWS`, Horner over `seq4`'s `2^7` final elements is the encoding of a message `m` equal to
them below `2^n`, when they are zero from `2^n` on. -/
theorem encVal4_eq (impl : OpImpl) (ht : ∀ j r, impl.tensorW j r = Impl.tensorWS j r) (inp : Input)
    {n : ℕ} (hle : n ≤ 7) (m : ℕ → K) (p : ℕ) (hm : ∀ c < 2 ^ n, finV4 seq4 inp c = m c)
    (hz : ∀ c, 2 ^ n ≤ c → c < 2 ^ 7 → finV4 seq4 inp c = 0) :
    encVal4 impl seq4 inp p = encF n (fun x => m x) p := by
  rw [encVal4, seq4_pf, hornerVal_eq, encF]
  simp only [gUnitK_seven]
  set X := finV4 seq4 inp
  rw [← Fin.sum_univ_eq_sum_range (fun c => X c * ∏ u ∈ range 7,
    (if c.testBit u then impl.tensorW p (unitK u) else 1)) (2 ^ 7)]
  have hsplit : ∑ c : Fin (2 ^ 7), X c * ∏ u ∈ range 7,
      (if (c : ℕ).testBit u then impl.tensorW p (unitK u) else 1) =
      ∑ c ∈ range (2 ^ n), X c * ∏ u ∈ range 7,
        (if c.testBit u then impl.tensorW p (unitK u) else 1) := by
    rw [Fin.sum_univ_eq_sum_range (fun c => X c * ∏ u ∈ range 7,
      (if c.testBit u then impl.tensorW p (unitK u) else 1)) (2 ^ 7)]
    symm
    refine sum_subset (range_subset_range.2 (Nat.pow_le_pow_right (by norm_num) hle))
      fun c hc hnc => ?_
    rw [hz c (by simpa using hnc) (by simpa using hc), zero_mul]
  rw [hsplit, ← Fin.sum_univ_eq_sum_range (fun c => X c * ∏ u ∈ range 7,
    (if c.testBit u then impl.tensorW p (unitK u) else 1)) (2 ^ n)]
  refine Fintype.sum_congr _ _ fun x => ?_
  rw [hm x x.2, bitProd, bitSel]
  congr 1
  rw [← prod_range_mul_prod_Ico _ hle]
  have hhi : ∏ u ∈ Ico n 7, (if (x : ℕ).testBit u then impl.tensorW p (unitK u) else 1) = 1 :=
    prod_eq_one fun u hu => by
      rw [Nat.testBit_lt_two_pow (lt_of_lt_of_le x.2
        (Nat.pow_le_pow_right (by norm_num) (mem_Ico.1 hu).1))]; rfl
  rw [hhi, mul_one]
  refine prod_congr rfl fun u hu => ?_
  have hu7 : u < 7 := by have := mem_range.1 hu; omega
  split_ifs <;> simp [ht, tensorWS_unit p hu7]

theorem toN_n4 (x : ℕ) : (Val.n x).toN = x := rfl

theorem mLog4_eq (κ : CKind) : T4.mLog κ 4 = κ.m - 25 := by
  cases κ <;> rename_i k <;> cases k <;> decide

/-! ## On an accepted run -/

/-- The final message's absorb (a table certificate): at `phStart4 47`, π's `fFinal` field. -/
theorem finalMsg4 : (fsMsgs4 seq4).getD (phStart4 47) none = some (fieldOffOf seq4 fFinal, 4096) := by
  rw [phStart4, fsStarts4_eq, fsMsgs4, fieldOffOf, seq4_eq]; decide +kernel

section Acc
variable {impl : OpImpl} {p : KindP} {inp : Input} {tr : Trace} {y : List Val × List Bool × Trace}

/-- **The final message on the log is π's** (`finV4` at `seq4`). -/
theorem finalAt_eq4 (h : SkRun4 impl p inp tr y) {e : ℕ} (he : e < 128) :
    T4.finalAt (fsOf tr (itemsOf seq4)) e = finV4 seq4 inp e := by
  have hp : phStart4 47 < 482 ∧ phStart4 47 ≠ 0 := by
    rw [phStart4, fsStarts4_eq]; decide
  have e1 := h.hq _ hp.1
  rw [finalMsg4] at e1
  simp only [qOf, hp.2, if_false] at e1
  rw [T4.finalAt, msgAt_of_q e1, readK, bytesAt_extract_of_le inp.π (by omega), finV4]

/-- **Query `q`'s position register** (`yReg4 p i q − 3`) holds its position `qPos`. -/
theorem posReg4 (h : SkRun4 impl p inp tr y) {L : Log} (hL : (L.map Prod.fst).Nodup)
    (hin : ∀ e ∈ tr, e ∈ L) (hm : p.d.m = (kindOfC (fsOf tr (itemsOf seq4))).m) {i : ℕ} (hi : i < 5)
    {q : ℕ} (hq : q < (CKind.lv (kindOfC (fsOf tr (itemsOf seq4))) i).t) :
    rd (#[] ++ y.1.toArray) (yReg4 p i q - 3) =
      .n (T4.qPos (kindOfC (fsOf tr (itemsOf seq4))) (fsOf tr (itemsOf seq4)) i q) := by
  set es := fsOf tr (itemsOf seq4)
  set κ := kindOfC es
  set R := #[] ++ y.1.toArray with hRd
  have hLk : CKind.lv κ i = lvOf κ.m i := rfl
  obtain ⟨hT, hsib, -, -, hper, hper0, -, -, hsq0, -⟩ := lv_facts4 (CKind.m_mem κ) hi
  rw [← hLk] at hT hsib hper hper0
  have hK : seq4.lvK p.d.m i = CKind.lv κ i := by rw [hm, lvK_eq4]; rfl
  obtain ⟨-, hP2, hQ⟩ := phases4_lvl hi
  obtain ⟨hnP, eP⟩ := ph4 hP2
  obtain ⟨hnQ, eQ⟩ := ph4 hQ
  have hcQ : cAt4 seq4 p (29 + 5 * i) =
      (genPhase4 seq4 p (28 + 5 * i) ("P2", .squeezes (seq4.lv i).sq (.pos i)) (cAt4 seq4 p (28 + 5 * i))).2 := by
    rw [show 29 + 5 * i = 28 + 5 * i + 1 by ring, cAt4_succ seq4 p hnP, eP]
  have hpA : (cAt4 seq4 p (29 + 5 * i)).posAns = (List.range (seq4.lv i).sq).map ((cAt4 seq4 p (28 + 5 * i)).next + ·) := by
    rw [hcQ, (genPhase4_pos_ctx ..).2.1]
  obtain ⟨-, -, hans⟩ := pos_view4 h hnP (by rw [eP]) hsq0
  obtain ⟨bQ, houtQ, -, hQv⟩ := queries_view4 h hL hin hnQ (by rw [eQ]) (by rw [hK]; exact hsib)
  have hq' : q < (seq4.lv i).t := hT ▸ hq
  obtain ⟨hidx, -⟩ := hQv q hq'
  have hgy : yReg4 p i q - 3 = bQ + 2 + posW4 seq4 i * q := by
    rw [yReg4, houtQ, List.getD_eq_getElem _ _ (by simpa using hq'), List.getElem_map, List.getElem_range]
    exact Nat.add_sub_cancel _ _
  have hqp : q / (CKind.lv κ i).per < (seq4.lv i).sq :=
    lt_of_le_of_lt (Nat.div_le_div_right (by omega)) hper
  have hj : idxOf (CKind.lv κ i).logN ((rd R ((cAt4 seq4 p (29 + 5 * i)).posAns.getD
      (q / (CKind.lv κ i).per) 0)).toD) (q % (CKind.lv κ i).per) = T4.qPos κ es i q := by
    rw [hpA, List.getD_eq_getElem _ _ (by simpa using hqp), List.getElem_map, List.getElem_range,
      hans _ hqp, T4.qPos, posAt, phStart4_P2 hi]
    rfl
  simp only [hK, ← hRd] at hidx
  rw [hgy, hidx, hj]

variable {P : FinP} {zh : List Reg} {Rs : ℕ → Array Val} {Ex : ℕ → Array (List Reg)}

/-- `finP 4`'s relation on an accepted run's fields (field 10). -/
theorem relP44_of_fields (hF : Fields4 impl p inp tr P y zh Rs Ex) :
    relP44 impl inp (Rs 10) P.S ⟨(skeleton4 seq4 p).2.outs, zh, Ex 10⟩ = true := by
  set fi : FinIn := ⟨(skeleton4 seq4 p).2.outs, zh, Ex 10⟩
  have hfi : fi.outs = (skeleton4 seq4 p).2.outs := rfl
  have hE := hF.ext 10 (by omega)
  have hpos0 := skel_pos4 hF.sk
  obtain ⟨-, Lk, hLk, -, -⟩ := hF.fld 10 (by omega)
  rw [rest_gFinP4 P] at hLk
  obtain ⟨b0, -, -, -, -, hlt0, -⟩ := p1_view4 hF.sk hfi (i := 4) (by omega)
  have hpo := (pf_view4 hF.sk hfi).2.2.2.2.1
  have hys : ysOf fi 4 = (skeleton4 seq4 p).2.outs.getD 49 [] := by
    rw [ysOf, lvOuts, hfi, phaseIx_P1]
  obtain ⟨L', hL'⟩ := flag_gFinP4 impl p.tix inp (Rs 10) P fi (by
    intro x hx
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hx
    refine lt_of_lt_of_le ?_ hE.1
    rcases hx with hx | hx | hx
    · exact skeleton4_out_lt p hF.sk.ref _ x (by rw [← hys]; exact hx)
    · rw [hx]; exact headD_lt hpo hpos0
    · rw [hx]; exact getLastD_lt hlt0 hpos0)
  exact pureRun_det hLk hL'

/-- **`FinRest4.pf0`** on the fields (any `c₀`: P1.4's last claim is `c1 c₀ 4`). -/
theorem pf04_of_fields (hF : Fields4 impl p inp tr P y zh Rs Ex) (c₀ : Log → Log → K) (L : Log) :
    rSum T4.pfStart (fsOf tr (itemsOf seq4)) 0 = T4.c1 c₀ 4 L (fsOf tr (itemsOf seq4)) := by
  set fi : FinIn := ⟨(skeleton4 seq4 p).2.outs, zh, Ex 10⟩
  have hfi : fi.outs = (skeleton4 seq4 p).2.outs := rfl
  have hE := hF.ext 10 (by omega)
  have hpos0 := skel_pos4 hF.sk
  have hrel := relP44_of_fields hF
  obtain ⟨b0, -, -, -, hN0, hlt0, -⟩ := p1_view4 hF.sk hfi (i := 4) (by omega)
  obtain ⟨-, -, h0, -, hpo, -⟩ := pf_view4 hF.sk hfi
  simp only [relP44, Bool.and_eq_true] at hrel
  have hc := hrel.2
  rw [hE.rd (x := claim0 fi "Pf") (headD_lt hpo hpos0), hE.rd (x := p1ClaimN fi 4) (getLastD_lt hlt0 hpos0),
    h0, hN0, eqv_k] at hc
  rw [hc, c1_eq4 c₀ (by omega)]

/-- **`FinRest4.enc`** on the fields, for the folds `yv4`: with `tensorW` at the spec and the final
message zero beyond `2^mLog` (π's elements; the kind's tail check in `finPf`). -/
theorem enc4_of_fields (hF : Fields4 impl p inp tr P y zh Rs Ex) (hPS : P.S = seq4)
    (ht : ∀ j r, impl.tensorW j r = Impl.tensorWS j r) {L : Log} (hb : ¬ Bad L)
    (hin : ∀ e ∈ tr, e ∈ L) (hm : p.d.m = (kindOfC (fsOf tr (itemsOf seq4))).m)
    (hz : ∀ c, 2 ^ T4.mLog (kindOfC (fsOf tr (itemsOf seq4))) 4 ≤ c → c < 2 ^ 7 → finV4 seq4 inp c = 0) :
    ∀ q < (CKind.lv (kindOfC (fsOf tr (itemsOf seq4))) 4).t,
      yv4 p (#[] ++ y.1.toArray) 4 q = T4.encAt (kindOfC (fsOf tr (itemsOf seq4))) 4
        (T4.finalAt (fsOf tr (itemsOf seq4))) (T4.qPos (kindOfC (fsOf tr (itemsOf seq4))) (fsOf tr (itemsOf seq4)) 4 q) := by
  have hL : (L.map Prod.fst).Nodup := by by_contra hr; exact hb (.inr (.inr (.inr hr)))
  set fi : FinIn := ⟨(skeleton4 seq4 p).2.outs, zh, Ex 10⟩
  have hfi : fi.outs = (skeleton4 seq4 p).2.outs := rfl
  have hE := hF.ext 10 (by omega)
  intro q hq
  have hrel := relP44_of_fields hF
  simp only [relP44, Bool.and_eq_true, List.all_eq_true] at hrel
  have hT : (CKind.lv (kindOfC (fsOf tr (itemsOf seq4))) 4).t = (seq4.lv 4).t := (lv_facts4 (CKind.m_mem (kindOfC (fsOf tr (itemsOf seq4)))) (i := 4) (by omega)).1
  obtain ⟨hnQ, eQ⟩ := ph4 (phases4_lvl (i := 4) (by omega)).2.2
  have hys : ysOf fi 4 = (skeleton4 seq4 p).2.outs.getD (29 + 5 * 4) [] := by
    rw [ysOf, lvOuts, hfi, phaseIx_P1]
  have hysE : (ysOf fi 4).length = (seq4.lv 4).t := by
    rw [hys, skeleton4_outs seq4 p hnQ, eQ, genPhase4_queries_outs, List.length_map, List.length_range]
  have hf := hrel.1 q (List.mem_range.2 (by rw [hysE, ← hT]; exact hq))
  have hyq : (ysOf fi 4).getD q 0 = yReg4 p 4 q := by rw [yReg4, ← hys]
  have hmem : yReg4 p 4 q ∈ ysOf fi 4 := by
    rw [← hyq, List.getD_eq_getElem _ _ (by rw [hysE, ← hT]; exact hq)]; exact List.getElem_mem _
  have hylt : yReg4 p 4 q < (#[] ++ y.1.toArray).size :=
    skeleton4_out_lt p hF.sk.ref _ _ (by rw [← hys]; exact hmem)
  unfold encFlag4 at hf
  rw [hyq, hE.rd (lt_of_le_of_lt (Nat.sub_le _ _) hylt), posReg4 hF.sk hL hin hm (by omega) hq,
    hE.rd hylt, hPS, toN_n4] at hf
  have hle : T4.mLog (kindOfC (fsOf tr (itemsOf seq4))) 4 ≤ 7 := by rw [mLog4_eq]; have := CKind.m_mem (kindOfC (fsOf tr (itemsOf seq4))); omega
  rw [encVal4_eq impl ht inp hle (T4.finalAt (fsOf tr (itemsOf seq4))) _ (fun c hc => (finalAt_eq4 hF.sk
    (lt_of_lt_of_le hc (le_trans (Nat.pow_le_pow_right (by norm_num) hle) (by norm_num)))).symm) hz] at hf
  have hv := val_eqv_k hf
  rw [yv4, hv, toK_k, T4.encAt]

end Acc

end FR.Snd.R4
