-- New for `flock-recursive` (BLUEPRINT revision 4.1, A.4, A.9, §5.1; track R4g). The 3.x templates are
-- `FRVIRSpec`'s `stepT`/`stepsT`/`posT`/`posAllT` with `exec_merkleOps`/`exec_posOps`/`exec_posAll`,
-- and `FRSoundnessAccQry`'s `stepsT_path`/`posT_path`/`posAllT_path`.
import FRSoundness4R4Start

/-!
# `posOps4` on a trace, and its Merkle paths on the log

`genPhase4`'s `.queries i` runs `posOps4` per position (the kind's level `K = S.lvK m i` for the
index, its depth `Lk.sib` and its cap; `sL = (S.lv i).sib` Merkle slots; absolute π offsets). This
module is 3.x's reference of a position at those parameters:

* **`stepT4`/`stepsT4`/`posT4`/`posAllT4`**: the registers, flag and remaining trace of the Merkle
  steps, one position, `t` positions;
* **`exec_merkleOps4`**, **`exec_posOps4`**, **`exec_posAll4`**: `exec` of the ops is the
  reference (the 3.x proofs at the 4.1 ops);
* **`posAllT4_path`**: on a log that contains the trace and repeats no query, every position's
  column has a path to its **committed digest** `D_r`, π's 32 bytes at `dO + 32·p` (revision 4.4.1,
  (β′): V asserts the root equal to the static read of field `fD`; `stepsT4_path`, `posT4_path`), and
  the position's cap index `j >>> Lk.sib` and `D_r` are its registers `4 + 6·sL`, `4 + 6·sL + 1`.
-/

namespace FR.Snd.R4
open RecursionFast Rev4 FR.Merkle

/-! ## The reference -/

section Ref
variable (inp : Input)

/-- **One Merkle step** at depth `h` of position `j` (`sib`: the kind's depth). -/
def stepT4 (sib i h j so : ℕ) (cur : Digest) : Trace → Option (List Val × Bool × Digest × Trace)
  | (q, a) :: tr =>
    let act := decide (h < sib)
    let s := bytesAt inp.π (absOff 0 so) 32
    let b := j.testBit h
    let l := if b then s else cur
    let r := if b then cur else s
    if q = (if act then nodeQ i l r else nodeQ i zeroD zeroD) then
      some ([.d s, .bit b, .d l, .d r, .d a, .d (if act then a else cur)],
        act || decide (s = zeroD), if act then a else cur, tr)
    else none
  | [] => none

/-- `n` Merkle steps from depth `h`. -/
def stepsT4 (sib i j : ℕ) : ℕ → ℕ → ℕ → Digest → Trace → Option (List Val × Bool × Digest × Trace)
  | 0, _, _, cur, tr => some ([], true, cur, tr)
  | n + 1, h, so, cur, tr =>
    (stepT4 inp sib i h j so cur tr).bind fun x =>
      (stepsT4 sib i j n (h + 1) (so + 32) x.2.2.1 x.2.2.2).map fun y =>
        (x.1 ++ y.1, x.2.1 && y.2.1, y.2.2)

/-- **Position `p` of level `i`** (`Lk`: the kind's level; `sL` Merkle slots; `ad`, `w`: the answer
and weight values; `dO`: the level's first committed digest, absolute). Revision 4.4.1 (β′): after
the cap index, the static read of `D_r` (π at `dO + 32·p`) and the check `cur = D_r`. -/
def posT4 (Lk : Level) (sL i co so dO : ℕ) (ad : ℕ → Digest) (w : Array K) (p : ℕ) :
    Trace → Option (List Val × Bool × Trace)
  | (q, a) :: tr =>
    let j := idxOf Lk.logN (ad (p / Lk.per)) (p % Lk.per)
    let col := inp.π.extract (absOff 0 (co + p * colBytes i)) (absOff 0 (co + p * colBytes i) + colBytes i)
    if q = colQ i col then
      (stepsT4 inp Lk.sib i j sL 0 (so + p * sL * 32) a tr).map fun x =>
        let capIx := j >>> Lk.sib
        let dr := bytesAt inp.π (absOff 0 (dO + 32 * p)) 32
        ([.n j, .b col, .d a, .k (dotKF w col)] ++ x.1 ++ [.n capIx, .d dr],
          x.2.1 && decide (x.2.2.1 = dr), x.2.2.2)
    else none
  | [] => none

/-- All positions from `p`. -/
def posAllT4 (Lk : Level) (sL i co so dO : ℕ) (ad : ℕ → Digest) (w : Array K) :
    ℕ → ℕ → Trace → Option (List Val × Bool × Trace)
  | 0, _, tr => some ([], true, tr)
  | t + 1, p, tr =>
    (posT4 inp Lk sL i co so dO ad w p tr).bind fun x =>
      (posAllT4 Lk sL i co so dO ad w t (p + 1) x.2.2).map fun y => (x.1 ++ y.1, x.2.1 && y.2.1, y.2.2)

theorem stepT4_spec {sib i h j so : ℕ} {cur : Digest} {tr : Trace} {y : List Val × Bool × Digest × Trace}
    (hy : stepT4 inp sib i h j so cur tr = some y) : y.1.length = 6 ∧ y.1.getD 5 default = .d y.2.2.1 := by
  rcases tr with _ | ⟨⟨q, a⟩, tr⟩
  · cases hy
  · simp only [stepT4] at hy
    split_ifs at hy <;> cases hy <;> simp

theorem stepsT4_spec {sib i j n h so : ℕ} {cur : Digest} {tr : Trace}
    {x : List Val × Bool × Digest × Trace} (hx : stepsT4 inp sib i j n h so cur tr = some x) :
    x.1.length = 6 * n ∧ (n = 0 → x.2.2.1 = cur) ∧ (0 < n → x.1.getD (6 * n - 1) default = .d x.2.2.1) := by
  induction n generalizing h so cur tr x with
  | zero => simp [stepsT4] at hx; subst hx; simp
  | succ n ih =>
    simp only [stepsT4, Option.bind_eq_some_iff, Option.map_eq_some_iff] at hx
    obtain ⟨y, hy, z, hz, rfl⟩ := hx
    obtain ⟨hl, h5⟩ := stepT4_spec inp hy
    obtain ⟨h1, h2, h3⟩ := ih hz
    refine ⟨by simp [hl, h1]; ring, by omega, fun _ => ?_⟩
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · have hz0 : z.1 = [] := List.length_eq_zero_iff.1 (by simpa using h1)
      rw [hz0, h2 rfl]; simpa using h5
    · rw [List.getD_append_right _ _ _ _ (by omega), hl,
        show 6 * (n + 1) - 1 - 6 = 6 * n - 1 by omega, h3 hn]

/-- The steps consume `n` entries. -/
theorem stepsT4_len {sib i j n h so : ℕ} {cur : Digest} {tr : Trace}
    {x : List Val × Bool × Digest × Trace} (hx : stepsT4 inp sib i j n h so cur tr = some x) :
    ∃ seg, tr = seg ++ x.2.2.2 ∧ seg.length = n := by
  induction n generalizing h so cur tr x with
  | zero => simp [stepsT4] at hx; subst hx; exact ⟨[], by simp, rfl⟩
  | succ n ih =>
    simp only [stepsT4, Option.bind_eq_some_iff, Option.map_eq_some_iff] at hx
    obtain ⟨y, hy, z, hz, rfl⟩ := hx
    rcases tr with _ | ⟨e, tr⟩
    · cases hy
    have hy2 : y.2.2.2 = tr := by
      simp only [stepT4] at hy; split_ifs at hy <;> cases hy <;> rfl
    obtain ⟨seg, h1, h2⟩ := ih hz
    exact ⟨e :: seg, by simp [← hy2, h1], by simp [h2]⟩

theorem posT4_length {Lk : Level} {sL i co so dO p : ℕ} {ad : ℕ → Digest} {w : Array K} {tr : Trace}
    {x : List Val × Bool × Trace} (hx : posT4 inp Lk sL i co so dO ad w p tr = some x) :
    x.1.length = 4 + 6 * sL + 2 := by
  rcases tr with _ | ⟨⟨q, a⟩, tr⟩
  · cases hx
  simp only [posT4] at hx
  split_ifs at hx
  obtain ⟨y, hy, rfl⟩ := Option.map_eq_some_iff.1 hx
  simp [(stepsT4_spec inp hy).1]; omega

theorem posAllT4_length {Lk : Level} {sL i co so dO t p : ℕ} {ad : ℕ → Digest} {w : Array K}
    {tr : Trace} {x : List Val × Bool × Trace} (hx : posAllT4 inp Lk sL i co so dO ad w t p tr = some x) :
    x.1.length = (4 + 6 * sL + 2) * t := by
  induction t generalizing p tr x with
  | zero => simp [posAllT4] at hx; subst hx; simp
  | succ t ih =>
    simp only [posAllT4, Option.bind_eq_some_iff, Option.map_eq_some_iff] at hx
    obtain ⟨y, hy, z, hz, rfl⟩ := hx
    simp only [List.length_append, posT4_length inp hy, ih hz, Nat.mul_succ]; omega

end Ref

/-! ## `exec` of the ops is the reference -/

section Exec
variable (impl : OpImpl) (κ : Kind) (inp : Input)

theorem exec_merkleOps4 (sib i j jr n h curR so : ℕ) (r : Array Val) (ok : Bool) (ops : List Op)
    (cur : Digest) (hj : jr < r.size) (hjv : (rd r jr).toN = j) (hc : curR < r.size)
    (hcv : rd r curR = .d cur) (tr : Trace) :
    exec impl κ inp (merkleOps4 sib i jr n h curR so r.size ++ ops) ⟨r, ok⟩ tr =
      (stepsT4 inp sib i j n h so cur tr).bind fun x =>
        exec impl κ inp ops ⟨r ++ x.1.toArray, ok && x.2.1⟩ x.2.2.2 := by
  induction n generalizing h curR so r ok cur tr with
  | zero => simp [merkleOps4, stepsT4]
  | succ n ih =>
    rw [show (⟨r, ok⟩ : St) = ⟨r ++ ([] : List Val).toArray, ok⟩ by simp]
    simp only [merkleOps4, stepsT4, List.cons_append, List.nil_append]
    rcases tr with _ | ⟨⟨q, a⟩, tr⟩
    · simp only [exec_app, evalOp, List.nil_append, stepT4, Option.bind_none]
    have hsel : ∀ (c : Bool) (x y : Digest), (if c then Val.d x else Val.d y) = Val.d (if c then x else y) :=
      fun c x y => by cases c <;> rfl
    simp only [exec_app, evalOp, rd_app, rd_app0, rd_app_left _ _ hj, rd_app_left _ _ hc, hjv, hcv,
      List.getD_cons_succ, List.getD_cons_zero, List.nil_append, List.cons_append, Val.toBit, toD_d,
      hsel, stepT4, nodeQF_eq, digestAt_eq]
    generalize bytesAt inp.π (absOff 0 so) 32 = sb
    generalize hQ : (if decide (h < sib) = true then
      nodeQ i (if j.testBit h = true then sb else cur) (if j.testBit h = true then cur else sb)
      else nodeQ i zeroD zeroD) = Q
    by_cases hq : q = Q
    · simp only [hq, ite_true, Option.bind_some, Option.bind_map]
      rw [show r.size + 6 = (r ++ [Val.d sb, Val.bit (j.testBit h),
          Val.d (if j.testBit h = true then sb else cur), Val.d (if j.testBit h = true then cur else sb),
          Val.d a, Val.d (if decide (h < sib) = true then a else cur)].toArray).size by simp,
        ih _ _ _ _ _ _ (by simp; omega) (by rw [rd_app_left _ _ hj, hjv]) (by simp) (by rw [rd_app]; rfl)]
      refine Option.bind_congr fun y _ => ?_
      simp [Array.append_assoc, Bool.and_assoc, Val.isZero]
    · simp [hq]

theorem exec_merkleOps4' (sib i j jr n h curR so b : ℕ) (r : Array Val) (ok : Bool) (ops : List Op)
    (cur : Digest) (hb : b = r.size) (hj : jr < r.size) (hjv : (rd r jr).toN = j) (hc : curR < r.size)
    (hcv : rd r curR = .d cur) (tr : Trace) :
    exec impl κ inp (merkleOps4 sib i jr n h curR so b ++ ops) ⟨r, ok⟩ tr =
      (stepsT4 inp sib i j n h so cur tr).bind fun x =>
        exec impl κ inp ops ⟨r ++ x.1.toArray, ok && x.2.1⟩ x.2.2.2 := by
  subst hb; exact exec_merkleOps4 impl κ inp sib i j jr n h curR so r ok ops cur hj hjv hc hcv tr

/-- A position's first four registers. -/
theorem exec_posHead4 (Lk : Level) (i co : ℕ) (ans : List Reg) (w p : ℕ) (r : Array Val) (ok : Bool)
    (rest : List Op) (ad : ℕ → Digest) (wv : Array K) (hA : ∀ k, ans.getD k 0 < r.size)
    (had : ∀ k, (rd r (ans.getD k 0)).toD = ad k) (hw : w < r.size) (hwv : (rd r w).toAK = wv)
    (q : ByteArray) (a : Digest) (tr : Trace) :
    exec impl κ inp ([.idx (fun _ => ans.getD (p / Lk.per) 0) (fun _ => Lk.logN) (fun _ => p % Lk.per),
      .piField 0 (co + p * colBytes i) (colBytes i), .askCol i (r.size + 1), .dotKF w (r.size + 1)] ++ rest)
      ⟨r, ok⟩ ((q, a) :: tr) =
      let j := idxOf Lk.logN (ad (p / Lk.per)) (p % Lk.per)
      let col := inp.π.extract (absOff 0 (co + p * colBytes i)) (absOff 0 (co + p * colBytes i) + colBytes i)
      if q = colQ i col then
        exec impl κ inp rest ⟨r ++ (posHeadVals j col a wv).toArray, ok⟩ tr
      else none := by
  rw [show (⟨r, ok⟩ : St) = ⟨r ++ ([] : List Val).toArray, ok⟩ by simp]
  simp only [List.cons_append, List.nil_append, exec_app, evalOp, rd_app_left _ _ (hA _), had,
    rd_app_left _ _ hw, hwv, rd_app, List.getD_cons_succ, List.getD_cons_zero, Val.toB,
    Bool.and_true, posHeadVals, dotKFF_eq, idxOfF_eq]

/-- A position's last three ops (revision 4.4.1: the static read of `D_r` at `o`). -/
theorem exec_posTail4 (Lk : Level) (o jr curR e : ℕ) (R : Array Val) (ok : Bool) (ops : List Op) (j : ℕ)
    (cur : Digest) (he : e = R.size) (hjr : jr < R.size) (hj : rd R jr = .n j) (hcr : curR < R.size)
    (hc : rd R curR = .d cur) (tr : Trace) :
    exec impl κ inp ([.shrN jr (fun _ => Lk.sib), .piDigest 0 o, .assertEq curR (e + 1) allK] ++ ops)
      ⟨R, ok⟩ tr =
      exec impl κ inp ops ⟨R ++ [Val.n (j >>> Lk.sib), .d (bytesAt inp.π (absOff 0 o) 32)].toArray,
        ok && decide (cur = bytesAt inp.π (absOff 0 o) 32)⟩ tr := by
  subst he
  rw [show (⟨R, ok⟩ : St) = ⟨R ++ ([] : List Val).toArray, ok⟩ by simp]
  simp only [List.cons_append, List.nil_append, exec_app, evalOp, rd_app_left _ _ hjr, hj,
    rd_app_left _ _ hcr, hc, rd_app, rd_app0, List.getD_cons_succ, List.getD_cons_zero, Val.toN,
    Val.eqv, allK, Bool.not_true, Bool.false_or, Bool.and_true, digestAt_eq]

/-- A position's Merkle steps after its first four registers. -/
theorem exec_posMid4 (sib i j n so : ℕ) (r : Array Val) (col : ByteArray) (a : Digest) (wv : Array K)
    (ok : Bool) (ops : List Op) (tr : Trace) :
    exec impl κ inp (merkleOps4 sib i r.size n 0 (r.size + 2) so (r.size + 4) ++ ops)
      ⟨r ++ (posHeadVals j col a wv).toArray, ok⟩ tr =
      (stepsT4 inp sib i j n 0 so a tr).bind fun x =>
        exec impl κ inp ops ⟨r ++ (posHeadVals j col a wv).toArray ++ x.1.toArray, ok && x.2.1⟩ x.2.2.2 :=
  exec_merkleOps4' impl κ inp sib i j r.size n 0 (r.size + 2) so (r.size + 4) _ ok ops a
    (posHead_size r j col a wv).symm (by rw [posHead_size]; omega) (by rw [posHead_rd0]; rfl)
    (by rw [posHead_size]; omega) (posHead_rd2 r j col a wv) tr

/-- **One position** against `posT4`. -/
theorem exec_posOps4 (S : Seq) (k : KindP) (i co so dO : ℕ) (ans : List Reg) (w p : ℕ) (r : Array Val)
    (ok : Bool) (ops : List Op) (ad : ℕ → Digest) (wv : Array K) (hA : ∀ k, ans.getD k 0 < r.size)
    (had : ∀ k, (rd r (ans.getD k 0)).toD = ad k) (hw : w < r.size) (hwv : (rd r w).toAK = wv)
    (tr : Trace) :
    exec impl κ inp (posOps4 S k i co so dO ans w p r.size ++ ops) ⟨r, ok⟩ tr =
      (posT4 inp (S.lvK k.d.m i) (S.lv i).sib i co so dO ad wv p tr).bind fun x =>
        exec impl κ inp ops ⟨r ++ x.1.toArray, ok && x.2.1⟩ x.2.2 := by
  simp only [posOps4, List.append_assoc]
  rcases tr with _ | ⟨⟨q, a⟩, tr⟩
  · rw [show (⟨r, ok⟩ : St) = ⟨r ++ ([] : List Val).toArray, ok⟩ by simp]
    simp only [List.cons_append, List.nil_append, exec_app, evalOp, posT4, Option.bind_none]
  rw [exec_posHead4 impl κ inp (S.lvK k.d.m i) i co ans w p r ok _ ad wv hA had hw hwv]
  simp only [posT4]
  generalize idxOf (S.lvK k.d.m i).logN (ad (p / (S.lvK k.d.m i).per)) (p % (S.lvK k.d.m i).per) = j
  generalize inp.π.extract (absOff 0 (co + p * colBytes i)) (absOff 0 (co + p * colBytes i) + colBytes i) = col
  by_cases hq : q = colQ i col
  swap; · simp [hq]
  simp only [hq, ite_true]
  have hs4 : (r ++ (posHeadVals j col a wv).toArray).size = r.size + 4 := posHead_size r j col a wv
  rw [exec_posMid4, Option.bind_map]
  · refine Option.bind_congr fun x hx => ?_
    obtain ⟨hl, h0, hlast⟩ := stepsT4_spec inp hx
    generalize hsb : (S.lv i).sib = sb at *
    rw [exec_posTail4 impl κ inp (S.lvK k.d.m i) (dO + 32 * p) (jr := r.size)
      (curR := curOfY sb (r.size + 3)) (e := r.size + 4 + 6 * sb)
      (j := j) (cur := x.2.2.1) (he := by simp [hl]; omega)
      (hjr := by simp)
      (hj := by rw [rd_append_left (by rw [posHead_size]; omega), posHead_rd0])
      (hcr := by unfold curOfY; split_ifs <;> simp [hl] <;> omega) (hc := ?_)]
    · simp [Array.append_assoc, Bool.and_assoc, posHeadVals]
    · by_cases hs : sb = 0
      · rw [curOfY, if_pos hs, show r.size + 3 - 1 = r.size + 2 by omega,
          rd_append_left (by rw [posHead_size]; omega), posHead_rd2, h0 hs]
      · have hsb0 : 0 < sb := Nat.pos_of_ne_zero hs
        have e : curOfY sb (r.size + 3) = (r ++ (posHeadVals j col a wv).toArray).size + (6 * sb - 1) := by
          rw [curOfY, if_neg hs, hs4]; exact (by omega : r.size + 3 + 6 * sb = r.size + 4 + (6 * sb - 1))
        rw [e, rd_app, hlast hsb0]

/-- **The positions of a level** from `p` on, against `posAllT4`. -/
theorem exec_posAll4 (S : Seq) (k : KindP) (i co so dO : ℕ) (ans : List Reg) (w b : ℕ) (ad : ℕ → Digest)
    (wv : Array K) (t : ℕ) : ∀ (p : ℕ) (r : Array Val) (ok : Bool) (ops : List Op) (tr : Trace),
    r.size = b + 2 + posW4 S i * p → (∀ k, ans.getD k 0 < r.size) →
    (∀ k, (rd r (ans.getD k 0)).toD = ad k) → w < r.size → (rd r w).toAK = wv →
    exec impl κ inp (((List.range' p t).flatMap fun q =>
        posOps4 S k i co so dO ans w q (b + 2 + posW4 S i * q)) ++ ops) ⟨r, ok⟩ tr =
      (posAllT4 inp (S.lvK k.d.m i) (S.lv i).sib i co so dO ad wv t p tr).bind fun x =>
        exec impl κ inp ops ⟨r ++ x.1.toArray, ok && x.2.1⟩ x.2.2 := by
  induction t with
  | zero => intro p r ok ops tr _ _ _ _ _; simp [posAllT4]
  | succ t ih =>
    intro p r ok ops tr hs hA had hw hwv
    have h := exec_posOps4 impl κ inp S k i co so dO ans w p r ok
      (((List.range' (p + 1) t).flatMap fun q => posOps4 S k i co so dO ans w q (b + 2 + posW4 S i * q)) ++ ops)
      ad wv hA had hw hwv tr
    rw [hs] at h
    rw [List.range'_succ, List.flatMap_cons, List.append_assoc, h]
    simp only [posAllT4, Option.bind_assoc, Option.bind_map]
    refine Option.bind_congr fun x hx => ?_
    have hl := posT4_length inp hx
    rw [ih (p + 1) (r ++ x.1.toArray) _ ops x.2.2 (by simp [hl, hs, posW4, Nat.mul_succ]; omega)
      (fun k => by simp; exact Nat.lt_add_right _ (hA k))
      (fun k => by rw [rd_append_left (hA k), had]) (by simp; exact Nat.lt_add_right _ hw)
      (by rw [rd_append_left hw, hwv])]
    simp [Array.append_assoc, Bool.and_assoc]

end Exec

/-! ## The Merkle paths on the log -/

section Path
variable (inp : Input)

/-- **The Merkle steps are a climb on the log** (3.x's `stepsT_path`). -/
theorem stepsT4_path {L : Log} (hL : (L.map Prod.fst).Nodup) {sib i j : ℕ} :
    ∀ (n h so : ℕ) (cur : Digest) (tr : Trace) (x : List Val × Bool × Digest × Trace),
      stepsT4 inp sib i j n h so cur tr = some x → (∀ e ∈ tr, e ∈ L) → sib ≤ h + n →
      ∃ ss : List Digest, ss.length = sib - h ∧ (climb (frEnc i) j h cur ss).runLog L = some x.2.2.1
  | 0, h, _, cur, tr, x, hx, _, hs => by
    simp only [stepsT4, Option.some.injEq] at hx; subst hx
    exact ⟨[], by simp; omega, rfl⟩
  | n + 1, h, so, cur, (q, a) :: tr, x, hx, hin, hs => by
    simp only [stepsT4, Option.bind_eq_some_iff, Option.map_eq_some_iff] at hx
    obtain ⟨z, hz, y, hy, rfl⟩ := hx
    simp only [stepT4, Option.ite_none_right_eq_some] at hz
    obtain ⟨hq, hz⟩ := hz
    simp only [Option.some.injEq] at hz; subst hz
    have hin' : ∀ e ∈ tr, e ∈ L := fun e he => hin e (List.mem_cons_of_mem _ he)
    have hmem : (q, a) ∈ L := hin _ (List.mem_cons_self ..)
    by_cases hact : h < sib
    · simp only [hact, decide_true, ite_true] at hq hy ⊢
      obtain ⟨ss, hl, hr⟩ := stepsT4_path hL n (h + 1) _ a tr y hy hin' (by omega)
      refine ⟨bytesAt inp.π (absOff 0 so) 32 :: ss, by simp [hl]; omega, ?_⟩
      have hm' : (stepQ (frEnc i) j h cur (bytesAt inp.π (absOff 0 so) 32), a) ∈ L := by
        convert hmem using 2; rw [hq]; simp only [stepQ, frEnc]; split_ifs <;> rfl
      rw [climb, runLog_query_mem hL hm']
      exact hr
    · simp only [hact, decide_false, Bool.false_eq_true, ite_false] at hy ⊢
      obtain ⟨ss, hl, hr⟩ := stepsT4_path hL n (h + 1) _ cur tr y hy hin' (by omega)
      have hss : ss = [] := List.eq_nil_of_length_eq_zero (by omega)
      subst hss
      exact ⟨[], by simp; omega, by simpa [climb] using hr⟩
  | _ + 1, _, _, _, [], x, hx, _, _ => by simp [stepsT4, stepT4] at hx

/-- **One position on the log** (3.x's `posT_path`; revision 4.4.1: the path to the committed
digest `D_r`, the cap index and `D_r` in registers `4 + 6·sL`, `4 + 6·sL + 1`). -/
theorem posT4_path {L : Log} (hL : (L.map Prod.fst).Nodup) {Lk : Level} {sL i co so dO p : ℕ}
    {ad : ℕ → Digest} {w : Array K} {tr : Trace} {x : List Val × Bool × Trace}
    (hx : posT4 inp Lk sL i co so dO ad w p tr = some x) (hin : ∀ e ∈ tr, e ∈ L)
    (hsib : Lk.sib ≤ sL) (hok : x.2.1 = true) :
    let j := idxOf Lk.logN (ad (p / Lk.per)) (p % Lk.per)
    let col := inp.π.extract (absOff 0 (co + p * colBytes i)) (absOff 0 (co + p * colBytes i) + colBytes i)
    x.1.getD 0 default = .n j ∧ x.1.getD 3 default = .k (dotKF w col) ∧
      x.1.getD (4 + 6 * sL) default = .n (j >>> Lk.sib) ∧
      x.1.getD (4 + 6 * sL + 1) default = .d (bytesAt inp.π (absOff 0 (dO + 32 * p)) 32) ∧
      (∃ ss : List Digest, ss.length = Lk.sib ∧ (openPath (frEnc i) col j ss).runLog L =
        some (bytesAt inp.π (absOff 0 (dO + 32 * p)) 32)) ∧
      ∃ seg, tr = seg ++ x.2.2 := by
  intro j col
  rcases tr with _ | ⟨⟨q, a⟩, tr⟩
  · cases hx
  simp only [posT4] at hx
  split_ifs at hx with hq
  obtain ⟨y, hy, rfl⟩ := Option.map_eq_some_iff.1 hx
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hok
  obtain ⟨ss, hl, hr⟩ := stepsT4_path inp hL _ 0 _ a tr y hy
    (fun e he => hin e (List.mem_cons_of_mem _ he)) (by omega)
  obtain ⟨seg, hseg, -⟩ := stepsT4_len inp hy
  have hl6 := (stepsT4_spec inp hy).1
  have hpre : ([Val.n j, .b col, .d a, .k (dotKF w col)] ++ y.1).length = 4 + 6 * sL := by
    simp only [List.length_append, List.length_cons, List.length_nil, hl6]
  refine ⟨rfl, rfl, ?_, ?_, ⟨ss, by simpa using hl, ?_⟩, ⟨(q, a) :: seg, by simp [hseg]⟩⟩
  · rw [List.getD_append_right _ _ _ _ (by rw [hpre]), hpre, Nat.sub_self]; rfl
  · rw [List.getD_append_right _ _ _ _ (by rw [hpre]; omega), hpre,
      show 4 + 6 * sL + 1 - (4 + 6 * sL) = 1 by omega]; rfl
  · have hmem : (q, a) ∈ L := hin _ (List.mem_cons_self ..)
    rw [openPath, runLog_query_mem hL (show ((frEnc i).colQ col, a) ∈ L by rw [hq] at hmem; exact hmem),
      hr, hok.2]

/-- **All positions on the log** (3.x's `posAllT_path`; revision 4.4.1: as `posT4_path`). -/
theorem posAllT4_path {L : Log} (hL : (L.map Prod.fst).Nodup) {Lk : Level} {sL i co so dO : ℕ}
    {ad : ℕ → Digest} {w : Array K} (hsib : Lk.sib ≤ sL) :
    ∀ (t p : ℕ) (tr : Trace) (x : List Val × Bool × Trace),
      posAllT4 inp Lk sL i co so dO ad w t p tr = some x → (∀ e ∈ tr, e ∈ L) → x.2.1 = true →
      ∀ q < t,
        x.1.getD ((4 + 6 * sL + 2) * q) default = .n (idxOf Lk.logN (ad ((p + q) / Lk.per)) ((p + q) % Lk.per)) ∧
        x.1.getD ((4 + 6 * sL + 2) * q + 3) default = .k (dotKF w (inp.π.extract
          (absOff 0 (co + (p + q) * colBytes i)) (absOff 0 (co + (p + q) * colBytes i) + colBytes i))) ∧
        x.1.getD ((4 + 6 * sL + 2) * q + (4 + 6 * sL)) default =
          .n (idxOf Lk.logN (ad ((p + q) / Lk.per)) ((p + q) % Lk.per) >>> Lk.sib) ∧
        x.1.getD ((4 + 6 * sL + 2) * q + (4 + 6 * sL + 1)) default =
          .d (bytesAt inp.π (absOff 0 (dO + 32 * (p + q))) 32) ∧
        ∃ ss : List Digest, ss.length = Lk.sib ∧
          (openPath (frEnc i) (inp.π.extract (absOff 0 (co + (p + q) * colBytes i))
            (absOff 0 (co + (p + q) * colBytes i) + colBytes i))
            (idxOf Lk.logN (ad ((p + q) / Lk.per)) ((p + q) % Lk.per)) ss).runLog L =
          some (bytesAt inp.π (absOff 0 (dO + 32 * (p + q))) 32)
  | 0, _, _, _, _, _, _, q, hq => absurd hq (by omega)
  | t + 1, p, tr, x, hx, hin, hok, q, hq => by
    simp only [posAllT4, Option.bind_eq_some_iff, Option.map_eq_some_iff] at hx
    obtain ⟨z, hz, y, hy, rfl⟩ := hx
    simp only [Bool.and_eq_true] at hok
    obtain ⟨h0, h3, hk, hd, hpath, seg, hseg⟩ := posT4_path inp hL hz hin hsib hok.1
    have hzl := posT4_length inp hz
    rcases q with _ | q
    · refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · rw [Nat.mul_zero, List.getD_append _ _ _ _ (by rw [hzl]; omega)]; simpa using h0
      · rw [Nat.mul_zero, Nat.zero_add, List.getD_append _ _ _ _ (by rw [hzl]; omega)]
        simpa using h3
      · rw [Nat.mul_zero, Nat.zero_add, List.getD_append _ _ _ _ (by rw [hzl]; omega)]
        simpa using hk
      · rw [Nat.mul_zero, Nat.zero_add, List.getD_append _ _ _ _ (by rw [hzl]; omega)]
        simpa using hd
      · simpa using hpath
    · obtain ⟨i0, i3, ik, id, ip⟩ := posAllT4_path hL hsib t (p + 1) _ y hy
        (fun e he => hin e (by rw [hseg]; exact List.mem_append_right _ he)) hok.2 q (by omega)
      rw [show p + (q + 1) = p + 1 + q by omega]
      refine ⟨?_, ?_, ?_, ?_, ip⟩
      · rw [show (4 + 6 * sL + 2) * (q + 1) = z.1.length + (4 + 6 * sL + 2) * q by rw [hzl]; ring,
          List.getD_append_right _ _ _ _ (by omega), Nat.add_sub_cancel_left, i0]
      · rw [show (4 + 6 * sL + 2) * (q + 1) + 3 = z.1.length + ((4 + 6 * sL + 2) * q + 3) by rw [hzl]; ring,
          List.getD_append_right _ _ _ _ (by omega), Nat.add_sub_cancel_left, i3]
      · rw [show (4 + 6 * sL + 2) * (q + 1) + (4 + 6 * sL) =
            z.1.length + ((4 + 6 * sL + 2) * q + (4 + 6 * sL)) by rw [hzl]; ring,
          List.getD_append_right _ _ _ _ (by omega), Nat.add_sub_cancel_left, ik]
      · rw [show (4 + 6 * sL + 2) * (q + 1) + (4 + 6 * sL + 1) =
            z.1.length + ((4 + 6 * sL + 2) * q + (4 + 6 * sL + 1)) by rw [hzl]; ring,
          List.getD_append_right _ _ _ _ (by omega), Nat.add_sub_cancel_left, id]

end Path

end FR.Snd.R4
