-- New for `flock-recursive` (`flock-128`, design D128 §2.1, §5.5; stage I3): the proof of work's
-- semantics in the verifier IR, and its controls.
import FRVIR4
import FRVIRFinalsCore

/-!
# The proof of work in the IR: `powOps` rejects exactly a nonzero byte 31

D128 §2.1: for every grinded phase, the verifier requires byte 31 of the phase's last squeeze answer
to be zero. `FRVIR4.powOps a b` emits `idx a 8 31`, eight `bitOf`, eight ungated `assertZero` (A.8's
ops; no new op, so `FRVIRCompile`'s `compile_sound` covers them as they are).

* **`pureRun_powOps`**, **`exec_powOps`**: on a register holding the digest `d`, the ops append
  `powVals d` (the byte and its eight bits) and the flag `powOk d = decide (d[31] = 0)`.
* **`roundsT4`**, **`exec_roundsT4`**: the sumcheck rounds of `roundsOps4` against a reference, as
  3.x's `exec_roundsT`: each F round's flag is the proof of work on its answer, a degree-2 round's
  `c₂` is `claim + c₁` (no check), a dummy round asserts zero **all but the nonce** (`[o, o + 48)` /
  `[o, o + 32)`, the ruling on the D128 review, finding 1).
* **Controls** (concrete digests and messages, `decide`): a grinded single-squeeze phase as `gen4`
  emits it (`L1`) accepts an answer whose byte 31 is zero (the honest, grinded trace) and rejects one
  whose byte 31 is `1` (`l1_pow_accepts`, `l1_pow_rejects`); a dummy degree-2 and degree-3 round
  accepts a nonzero nonce and rejects a nonzero coefficient byte (`dummy2_*`, `dummy3_*`); a real
  degree-2 round's next claim is `c₀ + r c₁ + r² (claim + c₁)` and its check `g(0) + g(1) = claim`
  holds by construction (`round2d_claim`, `FRSoundness128Rd.chk2d`); the segment-only zero check of
  `Lrend`/`Eend` leaves their nonce out (`end_nonce_ctl`).
-/

namespace FR
namespace Rev4
open RecursionFast

variable (impl : OpImpl) (κ : Kind) (inp : Input)

/-! ## The byte and its bits -/

/-- **The proof of work's predicate** (D128 §2.1): byte 31 of the answer is zero. -/
def powOk (d : Digest) : Bool := decide (d[31] = 0)

/-- The registers `powOps` appends on the answer `d`: byte 31 (`idx d 8 31`), its copy (`shrN … 0`),
then its eight bits. -/
def powVals (d : Digest) : List Val :=
  .n (idxOfF 8 d 31) :: .n (idxOfF 8 d 31 >>> 0) ::
    (List.range 8).map fun h => .bit ((idxOfF 8 d 31 >>> 0).testBit h)

theorem idxOfF_8_31 (d : Digest) : idxOfF 8 d 31 = d[31].toNat := by
  have hw : dWin d 31 = d[31].toNat := by simp [dWin, dByte]
  show (if 8 ≤ 24 then dWin d (31 * 8 / 8) >>> (31 * 8 % 8) % (1 <<< 8) else idxOf 8 d 31) = _
  simp only [show (8 : ℕ) ≤ 24 from by norm_num, ↓reduceIte]
  rw [show 31 * 8 / 8 = 31 from rfl, show 31 * 8 % 8 = 0 from rfl, hw,
    Nat.shiftRight_zero, show (1 <<< 8 : ℕ) = 256 from rfl, Nat.mod_eq_of_lt (UInt8.toNat_lt _)]

/-- A byte is zero iff its eight bits are. -/
theorem bits_zero (x : UInt8) : ((List.range 8).all fun h => !x.toNat.testBit h) = decide (x = 0) := by
  have h : ∀ n, n < 256 → ((List.range 8).all fun h => !n.testBit h) = decide (n = 0) := by decide +kernel
  rw [h _ (UInt8.toNat_lt x)]
  simp [← UInt8.toNat_inj]

theorem powVals_length (d : Digest) : (powVals d).length = powW := by simp [powVals, powW]

/-- The eight `bitOf` from register `b` (holding `n`), then `rest`. -/
theorem pureRun_bits (b n : ℕ) (r : Array Val) (rest : List Op) :
    ∀ (hs : List ℕ) (L : List Val), rd (r ++ L.toArray) b = .n n → b < (r ++ L.toArray).size →
      pureRun impl κ inp (hs.map (fun h => Op.bitOf b h) ++ rest) r L =
        (pureRun impl κ inp rest r (L ++ hs.map fun h => .bit (n.testBit h))).map fun p => (p.1, true && p.2)
  | [], L, _, _ => by simp
  | h :: hs, L, hb, hlt => by
    have hb' : rd (r ++ (L ++ [Val.bit (n.testBit h)]).toArray) b = .n n := by
      rw [← app_app, rd_append_left hlt, hb]
    rw [List.map_cons, List.cons_append, pureRun]
    simp only [evalOp, hb, Val.toN]
    rw [pureRun_bits b n r rest hs _ hb' (by simp at hlt ⊢; omega)]
    simp

/-- Eight `assertZero` on registers `c + h` (holding the bits of `n`). -/
theorem pureRun_asserts (c n : ℕ) (r : Array Val) (L : List Val) :
    ∀ hs : List ℕ, (∀ h ∈ hs, rd (r ++ L.toArray) (c + h) = .bit (n.testBit h)) →
      pureRun impl κ inp (hs.map fun h => Op.assertZero (c + h) allK) r L =
        some (L, hs.all fun h => !n.testBit h)
  | [], _ => rfl
  | h :: hs, hv => by
    rw [List.map_cons, pureRun]
    simp only [evalOp, hv h (List.mem_cons_self ..), allK, Bool.not_true, Bool.false_or, Val.isZero,
      List.append_nil]
    rw [pureRun_asserts c n r L hs fun h' h'm => hv h' (List.mem_cons_of_mem _ h'm)]
    simp

/-- **`powOps a b` on the digest `d`** (register `a`; `b` the next register): it appends `powVals d`
and its flag is `powOk d`. -/
theorem pureRun_powOps (a : ℕ) (r : Array Val) (L : List Val) (d : Digest)
    (ha : (rd (r ++ L.toArray) a).toD = d) :
    pureRun impl κ inp (powOps a (r ++ L.toArray).size) r L = some (L ++ powVals d, powOk d) := by
  set b := (r ++ L.toArray).size with hb
  have h0 : rd (r ++ (L ++ [Val.n (idxOfF 8 d 31)]).toArray) b = .n (idxOfF 8 d 31) := by
    rw [hb, ← app_app]; simp [rd]
  have h1 : rd (r ++ (L ++ [Val.n (idxOfF 8 d 31)] ++ [Val.n (idxOfF 8 d 31 >>> 0)]).toArray) (b + 1) = .n (idxOfF 8 d 31 >>> 0) := by
    rw [show b + 1 = r.size + (L ++ [Val.n (idxOfF 8 d 31)]).length by simp [hb]; omega, rd_app]; simp
  rw [powOps, pureRun]
  simp only [evalOp, ha]
  rw [pureRun]
  simp only [evalOp, h0, Val.toN, Option.map_map]
  rw [pureRun_bits impl κ inp (b + 1) (idxOfF 8 d 31 >>> 0) r _ (List.range 8) _ h1 (by simp [hb]; omega)]
  rw [pureRun_asserts impl κ inp (b + 2) (idxOfF 8 d 31 >>> 0) r _ (List.range 8) fun h hh => by
    have hh8 : h < 8 := List.mem_range.mp hh
    rw [show b + 2 + h = r.size + ((L ++ [Val.n (idxOfF 8 d 31)] ++ [Val.n (idxOfF 8 d 31 >>> 0)]).length + h) by simp [hb]; omega,
      rd_app]
    simp only [List.getD_eq_getElem?_getD]
    rw [List.getElem?_append_right (by omega), Nat.add_sub_cancel_left]
    simp [hh8]]
  simp only [Option.map_some, Option.map_map, Function.comp_def, Bool.true_and, Bool.and_true, powOk,
    powVals, Nat.shiftRight_zero, ← bits_zero, idxOfF_8_31, List.append_assoc, List.singleton_append,
    List.cons_append, List.nil_append]

/-- **`powOps` in a run**: the registers gain `powVals d`, the flag `powOk d` (`d` the digest register
`a` holds; `idx` reads any register as a digest, `Val.toD`). -/
theorem exec_powOps (a : ℕ) (r : Array Val) (L : List Val) (d : Digest) (ha : (rd (r ++ L.toArray) a).toD = d)
    (ops : List Op) (ok : Bool) (tr : Trace) :
    exec impl κ inp (powOps a (r ++ L.toArray).size ++ ops) ⟨r ++ L.toArray, ok⟩ tr =
      exec impl κ inp ops ⟨r ++ (L ++ powVals d).toArray, ok && powOk d⟩ tr :=
  exec_pureRun impl κ inp _ ops r L _ _ ok tr (pureRun_powOps impl κ inp a r L d ha)

/-! ## The univariate round and the sumcheck rounds (the references of `FRSoundness4R4Ref`) -/

/-- The registers of `uniOps4` (3.x's `uniVals` without the pad's register, then `powVals`). -/
def uniVals4 (f o : ℕ) (pe : Array F) (a₁ a₂ : Digest) : List Val :=
  (uniVals impl inp f o pe a₁ a₂).dropLast ++ powVals a₂

theorem uniVals4_eq (f o : ℕ) (pe : Array F) (a₁ a₂ : Digest) :
    uniVals4 impl inp f o pe a₁ a₂ =
      ([.b (msgAt inp f o uniBytes), .d a₁, .d a₂, .f (chF a₂ 0)] ++ (uniEs inp f o).map .f) ++
        ([.af (uniEs inp f o).toArray, .af pe,
          .f (impl.lagrangeS (uniEs inp f o).toArray (chF a₂ 0) pe).1,
          .f (impl.lagrangeS (uniEs inp f o).toArray (chF a₂ 0) pe).2] ++ powVals a₂) := by
  rw [uniVals4, uniVals, List.dropLast_append_of_ne_nil (by simp), List.append_assoc]
  rfl

theorem uniVals4_length (f o : ℕ) (pe : Array F) (a₁ a₂ : Digest) :
    (uniVals4 impl inp f o pe a₁ a₂).length = 135 + powW := by
  simp [uniVals4, uniVals_length, powVals_length]

/-- **Z2's round** (`uniOps4`): no pad check; the flag is the proof of work on its answer. -/
theorem exec_uni4 (f o st pt : ℕ) (r : Array Val) (ok : Bool) (ops : List Op) (d : Digest)
    (hst : st < r.size) (hpt : pt < r.size) (hd : (rd r st).toD = d) (q₁ q₂ : ByteArray)
    (a₁ a₂ : Digest) (tr : Trace) :
    exec impl κ inp (uniOps4 f o st pt r.size ++ ops) ⟨r, ok⟩ ((q₁, a₁) :: (q₂, a₂) :: tr) =
      if q₁ = absorbQ d (msgAt inp f o uniBytes) ∧ q₂ = squeezeQ a₁ then
        exec impl κ inp ops ⟨r ++ (uniVals4 impl inp f o (impl.targetS κ (rd r pt).toAF) a₁ a₂).toArray,
          ok && powOk a₂⟩ tr
      else none := by
  rw [show (⟨r, ok⟩ : St) = ⟨r ++ ([] : List Val).toArray, ok⟩ by simp, uniOps4, List.append_assoc,
    List.append_assoc, List.append_assoc]
  simp only [uniHead, List.cons_append, List.nil_append]
  generalize hM : uniElems f o ++ Op.packF ((List.range 127).map (r.size + 4 + ·)) :: Op.targetS pt ::
    Op.lagrangeS (r.size + 131) (r.size + 3) (r.size + 132) :: (powOps (r.size + 2) (r.size + 135) ++ ops) = M
  simp only [exec_app, evalOp, rd_app_left _ _ hst, hd, toD_d, Val.toB, rd_app,
    rd_app0, List.nil_append, List.cons_append, List.getD_eq_getElem?_getD, List.getElem?_cons_succ,
    List.getElem?_cons_zero, Option.getD_some]
  simp only [msgAt]
  by_cases h₁ : q₁ = absorbQ d (inp.π.extract (absOff f o) (absOff f o + uniBytes)) <;>
    by_cases h₂ : q₂ = squeezeQ a₁ <;>
    simp only [h₁, h₂, ite_true, ite_false, and_self, and_false, false_and,
      Bool.and_true] <;> try rfl
  subst hM
  rw [uniElems, exec_map_pure impl κ inp _ _ (fun i => .f (elemAt inp f (o + 16 * i))) (fun _ _ => rfl)]
  obtain ⟨L, hL⟩ : ∃ L : List Val, L = [Val.b (inp.π.extract (absOff f o) (absOff f o + uniBytes)),
    Val.d a₁, Val.d a₂, Val.f (chF a₂ 0)] ++ (uniEs inp f o).map .f := ⟨_, rfl⟩
  have hLen : L.length = 131 := by simp [hL, uniEs]
  rw [exec_regs impl κ inp (R' := r ++ L.toArray) (by apply Array.ext'; simp [hL, uniEs])]
  have hpack : ((List.range 127).map (r.size + 4 + ·)).map (fun x => (rd (r ++ L.toArray) x).toF) =
      uniEs inp f o := by
    rw [List.map_map]
    refine List.ext_getElem (by simp [uniEs]) fun i h₁ h₂ => ?_
    have hi : i < 127 := by simpa using h₁
    simp only [uniEs, List.getElem_map, List.getElem_range, Function.comp_apply]
    rw [show r.size + 4 + i = r.size + (4 + i) by omega, rd_app, hL,
      List.getD_append_right _ _ _ _ (by simp), List.getD_eq_getElem _ _ (by simp; omega)]
    simp [Val.toF, uniEs]
  have h3 : ∀ X : List Val, rd (r ++ (L ++ X).toArray) (r.size + 3) = .f (chF a₂ 0) := by
    intro X; rw [rd_app, hL]; rfl
  have h131 : ∀ X : List Val, rd (r ++ (L ++ X).toArray) (r.size + 131) = X.getD 0 default := by
    intro X; rw [rd_app, List.getD_append_right _ _ _ _ (by omega), hLen]
  have h132 : ∀ X : List Val, rd (r ++ (L ++ X).toArray) (r.size + 132) = X.getD 1 default := by
    intro X; rw [rd_app, List.getD_append_right _ _ _ _ (by omega), hLen]
  simp only [exec_app, evalOp, hpack, rd_app_left _ _ hpt, List.append_assoc,
    List.cons_append, List.nil_append, h3, h131, h132, List.getD_cons_succ, List.getD_cons_zero, Bool.and_true,
    show ∀ y, (Val.af y).toAF = y from fun _ => rfl, show ∀ y, (Val.f y).toF = y from fun _ => rfl]
  set x := impl.lagrangeS (uniEs inp f o).toArray (chF a₂ 0) (impl.targetS κ (rd r pt).toAF)
  have hsz : (r ++ (L ++ [Val.af (uniEs inp f o).toArray, Val.af (impl.targetS κ (rd r pt).toAF),
      Val.f x.1, Val.f x.2]).toArray).size = r.size + 135 := by simp [hLen]
  have ha : rd (r ++ (L ++ [Val.af (uniEs inp f o).toArray, Val.af (impl.targetS κ (rd r pt).toAF),
      Val.f x.1, Val.f x.2]).toArray) (r.size + 2) = .d a₂ := by rw [rd_app, hL]; rfl
  rw [← hsz, exec_powOps impl κ inp _ r _ a₂ (by rw [ha]; rfl), uniVals4_eq, hL]
  simp only [msgAt, List.append_assoc, List.cons_append, List.nil_append, x]

/-- **One F round of `roundOpsF4`**: its registers with the claim `c` (degree 3: `c₃ := c + c₁ + c₂`;
degree 2: `c₂ := c + c₁`), the proof of work, then the dummy check's body (all but the nonce). -/
def roundF4V (f o deg : ℕ) (re : Bool) (a₁ a₂ : Digest) (c : Val) : List Val :=
  let r := chF a₂ 0
  let c₀ := elemAt inp f o; let c₁ := elemAt inp f (o + 16)
  ([.b (msgAt inp f o (roundBytesD deg false)), .d a₁, .d a₂, .f r] : List Val) ++ powVals a₂ ++
  (if deg = 3 then
    let c₂ := elemAt inp f (o + 32)
    let s := c₁ + c₂; let c₃ := c.toF + s
    let t₁ := r * c₃; let t₂ := c₂ + t₁; let t₃ := r * t₂; let t₄ := c₁ + t₃; let t₅ := r * t₄
    let g := c₀ + t₅
    [.f c₀, .f c₁, .f c₂, .f s, .f c₃, .f t₁, .f t₂, .f t₃, .f t₄, .f t₅, .f g, .b (msgAt inp f o 48),
      if re then .f g else c]
  else
    let c₂ := c.toF + c₁
    let t₁ := r * c₂; let t₂ := c₁ + t₁; let t₃ := r * t₂; let g := c₀ + t₃
    [.f c₀, .f c₁, .f c₂, .f t₁, .f t₂, .f t₃, .f g, .b (msgAt inp f o 32), if re then .f g else c])

/-- The dummy round's body: all of the message but the nonce (degree 3: 48 bytes; degree 2: 32). -/
def bodyLen (deg : ℕ) : ℕ := if deg = 3 then 48 else 32

/-- **One F round** (`roundOpsF4`) against its reference: the flag is the proof of work on its answer
and, for a dummy round, the zero body. -/
theorem exec_roundF4 (f o deg : ℕ) (real : KC Bool) (st cl : ℕ) (r : Array Val) (ok : Bool)
    (ops : List Op) (d : Digest) (c : Val) (hst : st < r.size) (hcl : cl < r.size)
    (hd : (rd r st).toD = d) (hc : rd r cl = c) (q₁ q₂ : ByteArray) (a₁ a₂ : Digest) (tr : Trace) :
    exec impl κ inp (roundOpsF4 f o deg real st cl r.size ++ ops) ⟨r, ok⟩ ((q₁, a₁) :: (q₂, a₂) :: tr) =
      if q₁ = absorbQ d (msgAt inp f o (roundBytesD deg false)) ∧ q₂ = squeezeQ a₁ then
        exec impl κ inp ops ⟨r ++ (roundF4V inp f o deg (real κ) a₁ a₂ c).toArray,
          ok && (powOk a₂ && (real κ || (Val.b (msgAt inp f o (bodyLen deg))).isZero))⟩ tr
      else none := by
  rw [show (⟨r, ok⟩ : St) = ⟨r ++ ([] : List Val).toArray, ok⟩ by simp, roundOpsF4, List.append_assoc,
    List.append_assoc]
  simp only [List.cons_append, List.nil_append, exec_app, evalOp, rd_app_left _ _ hst, hd, toD_d, Val.toB,
    rd_app0, List.getD_cons_zero]
  by_cases h₁ : q₁ = absorbQ d (msgAt inp f o (roundBytesD deg false)) <;>
    by_cases h₂ : q₂ = squeezeQ a₁ <;>
    simp only [msgAt] at h₁ ⊢ <;>
    simp only [h₁, h₂, ite_true, ite_false, and_self, and_false, false_and] <;>
    (try rfl) <;> (try (simp only [rd_app, List.getD_cons_succ, List.getD_cons_zero, toD_d, h₂, ite_false]; done))
  simp only [rd_app, List.getD_cons_succ, List.getD_cons_zero, Val.toD, Bool.and_true]
  have ha : rd (r ++ [Val.b (inp.π.extract (absOff f o) (absOff f o + roundBytesD deg false)), .d a₁, .d a₂,
      .f (chF a₂ 0)].toArray) (r.size + 2) = .d a₂ := by rw [rd_app]; rfl
  rw [show r.size + 4 = (r ++ [Val.b (inp.π.extract (absOff f o) (absOff f o + roundBytesD deg false)), .d a₁,
      .d a₂, .f (chF a₂ 0)].toArray).size by simp, exec_powOps impl κ inp _ r _ a₂ (by rw [ha]; rfl)]
  have hP := powVals_length a₂
  simp only [powW] at hP
  obtain ⟨L, hL⟩ : ∃ L : List Val, L = [Val.b (inp.π.extract (absOff f o) (absOff f o + roundBytesD deg false)),
    .d a₁, .d a₂, .f (chF a₂ 0)] ++ powVals a₂ := ⟨_, rfl⟩
  have hLen : L.length = 14 := by simp [hL, hP]
  rw [← hL]
  have hr3 : ∀ X : List Val, rd (r ++ (L ++ X).toArray) (r.size + 3) = .f (chF a₂ 0) := by
    intro X; rw [rd_app, hL]; rfl
  have hX : ∀ (X : List Val) n, rd (r ++ (L ++ X).toArray) (r.size + n) =
      if n < 14 then L.getD n default else X.getD (n - 14) default := by
    intro X n; rw [rd_app]; split_ifs with hn
    · rw [List.getD_append _ _ _ _ (by omega)]
    · rw [List.getD_append_right _ _ _ _ (by omega), hLen]
  have hcl' : ∀ X : List Val, rd (r ++ (L ++ X).toArray) cl = c := fun X => by rw [rd_app_left _ _ hcl, hc]
  have hL3 : L.getD 3 default = .f (chF a₂ 0) := by rw [hL]; rfl
  have key : ∀ (A A' : Array Val) (B B' : Bool), A = A' → B = B' →
      exec impl κ inp ops ⟨A, B⟩ tr = exec impl κ inp ops ⟨A', B'⟩ tr := by rintro _ _ _ _ rfl rfl; rfl
  by_cases h3 : deg = 3
  · subst h3
    simp only [ite_true, List.cons_append, List.nil_append, exec_app, evalOp, hX, hcl', hL3, List.append_assoc]
    simp only [Nat.reduceLT, ite_false, ite_true, Nat.reduceSub, List.getD_cons_succ, List.getD_cons_zero,
      Val.toF, Val.toB, List.nil_append, List.cons_append]
    refine key _ _ _ _ ?_ ?_
    · apply Array.ext'; simp [roundF4V, hL, msgAt, elemAt, bodyLen, Val.toF]
    · cases real κ <;> simp [bodyLen, msgAt, Bool.and_assoc]
  · simp only [h3, ite_false, List.cons_append, List.nil_append, exec_app, evalOp, hX, hcl', hL3,
      List.append_assoc]
    simp only [Nat.reduceLT, ite_false, ite_true, Nat.reduceSub, List.getD_cons_succ, List.getD_cons_zero,
      Val.toF, Val.toB, List.nil_append, List.cons_append]
    refine key _ _ _ _ ?_ ?_
    · apply Array.ext'; simp [roundF4V, h3, hL, msgAt, elemAt, bodyLen, Val.toF]
    · cases real κ <;> simp [bodyLen, h3, msgAt, Bool.and_assoc]

/-- The registers of one round of `roundsOps4` (K: 3.x's `roundKVals`). -/
def roundV4 (f o deg : ℕ) (inK re : Bool) (a₁ a₂ : Digest) (c : Val) : List Val :=
  if inK then roundKVals inp f o re a₁ a₂ c else roundF4V inp f o deg re a₁ a₂ c

/-- One round's flag (K: 3.x's check `c₁ + c₂ = claim` and zero dummy; F: the proof of work and the
zero body of a dummy). -/
def roundChk4 (f o deg : ℕ) (inK re : Bool) (a₂ : Digest) (c : Val) : Bool :=
  if inK then (!re || (Val.k (elemKAt inp f (o + 32) + elemKAt inp f (o + 64))).eqv c) &&
      (re || (Val.b (msgAt inp f o (roundBytesD deg inK))).isZero)
  else powOk a₂ && (re || (Val.b (msgAt inp f o (bodyLen deg))).isZero)

/-- **Reference: `n` sumcheck rounds of `roundsOps4`** from round `j`, state `d` and claim `c`. -/
def roundsT4 (f o deg : ℕ) (inK : Bool) (real : ℕ) :
    ℕ → ℕ → Digest → Val → Trace → Option (List Val × Bool × Trace)
  | 0, _, _, _, tr => some ([], true, tr)
  | n + 1, j, d, c, (q₁, a₁) :: (q₂, a₂) :: tr =>
    let rb := roundBytesD deg inK
    let o' := o + j * rb
    if q₁ = absorbQ d (msgAt inp f o' rb) ∧ q₂ = squeezeQ a₁ then
      let vs := roundV4 inp f o' deg inK (decide (j < real)) a₁ a₂ c
      (roundsT4 f o deg inK real n (j + 1) a₂ (vs.getLastD default) tr).map fun x =>
        (vs ++ x.1, roundChk4 inp f o' deg inK (decide (j < real)) a₂ c && x.2.1, x.2.2)
    else none
  | _ + 1, _, _, _, _ => none

theorem roundBytesD_K (deg : ℕ) : roundBytesD deg true = roundBytes true := rfl

/-- **One round of any kind** (`roundsOps4`'s step) against `roundV4`, `roundChk4`. -/
theorem exec_round4 (f o deg : ℕ) (inK : Bool) (real : KC Bool) (st cl : ℕ) (r : Array Val) (ok : Bool)
    (ops : List Op) (d : Digest) (c : Val) (hst : st < r.size) (hcl : cl < r.size)
    (hd : (rd r st).toD = d) (hc : rd r cl = c) (q₁ q₂ : ByteArray) (a₁ a₂ : Digest) (tr : Trace) :
    exec impl κ inp ((if inK then roundOpsK f o real st cl r.size else roundOpsF4 f o deg real st cl r.size)
        ++ ops) ⟨r, ok⟩ ((q₁, a₁) :: (q₂, a₂) :: tr) =
      if q₁ = absorbQ d (msgAt inp f o (roundBytesD deg inK)) ∧ q₂ = squeezeQ a₁ then
        exec impl κ inp ops ⟨r ++ (roundV4 inp f o deg inK (real κ) a₁ a₂ c).toArray,
          ok && roundChk4 inp f o deg inK (real κ) a₂ c⟩ tr
      else none := by
  cases inK
  · simp only [Bool.false_eq_true, ite_false, roundV4, roundChk4]
    exact exec_roundF4 impl κ inp f o deg real st cl r ok ops d c hst hcl hd hc q₁ q₂ a₁ a₂ tr
  · have := exec_round impl κ inp f o deg true real st cl r ok ops d c hst hcl hd hc q₁ q₂ a₁ a₂ tr
    simp only [ite_true] at this ⊢
    rw [this, roundBytesD_K]
    simp [roundV4, roundChk4, roundBytesD_K, Bool.and_assoc]

theorem roundV4_spec (f o deg : ℕ) (inK re : Bool) (a₁ a₂ : Digest) (c : Val) :
    (roundV4 inp f o deg inK re a₁ a₂ c).length = roundW4 deg inK ∧
    (roundV4 inp f o deg inK re a₁ a₂ c).getD 2 default = .d a₂ ∧
    (roundV4 inp f o deg inK re a₁ a₂ c).getD (roundW4 deg inK - 1) default =
      (roundV4 inp f o deg inK re a₁ a₂ c).getLastD default := by
  have hP := powVals_length a₂
  simp only [powW] at hP
  have hl : (roundV4 inp f o deg inK re a₁ a₂ c).length = roundW4 deg inK := by
    by_cases h3 : deg = 3 <;> cases inK <;> simp [roundV4, h3, roundW4, roundF4V, roundKVals, hP]
  refine ⟨hl, ?_, ?_⟩
  · by_cases h3 : deg = 3 <;> cases inK <;> simp [roundV4, h3, roundF4V, roundKVals]
  · rw [List.getLastD_eq_getLast?, List.getLast?_eq_getElem?, List.getD_eq_getElem?_getD, hl]

/-- **`n` rounds of any kind** (`roundsOps4`) against `roundsT4`. -/
theorem exec_roundsT4 (f o deg : ℕ) (inK : Bool) (real : KC ℕ) (n j st cl : ℕ) (r : Array Val)
    (ok : Bool) (ops : List Op) (d : Digest) (c : Val) (hst : st < r.size) (hcl : cl < r.size)
    (hd : (rd r st).toD = d) (hc : rd r cl = c) (tr : Trace) :
    exec impl κ inp (roundsOps4 f o deg inK real n j st cl r.size ++ ops) ⟨r, ok⟩ tr =
      (roundsT4 inp f o deg inK (real κ) n j d c tr).bind fun x =>
        exec impl κ inp ops ⟨r ++ x.1.toArray, ok && x.2.1⟩ x.2.2 := by
  induction n generalizing j st cl r ok d c tr with
  | zero => simp [roundsOps4, roundsT4]
  | succ n ih =>
    rcases tr with _ | ⟨⟨q₁, a₁⟩, _ | ⟨⟨q₂, a₂⟩, tr⟩⟩
    · cases inK <;> simp [roundsOps4, roundOpsF4, roundOpsK, exec, evalOp, roundsT4]
    · cases inK <;> simp [roundsOps4, roundOpsF4, roundOpsK, exec, evalOp, roundsT4] <;> split <;> simp
    simp only [roundsOps4, List.append_assoc]
    rw [exec_round4 impl κ inp f _ deg inK _ st cl r ok _ d c hst hcl hd hc]
    simp only [roundsT4]
    have hv := roundV4_spec inp f (o + j * roundBytesD deg inK) deg inK (decide (j < real κ)) a₁ a₂ c
    by_cases h : q₁ = absorbQ d (msgAt inp f (o + j * roundBytesD deg inK) (roundBytesD deg inK)) ∧
      q₂ = squeezeQ a₁
    · simp only [h, and_self, ite_true]
      obtain ⟨hl, h2, hL⟩ := hv
      set vs := roundV4 inp f (o + j * roundBytesD deg inK) deg inK (decide (j < real κ)) a₁ a₂ c with hvs
      set w := roundW4 deg inK with hw
      have hw3 : 3 ≤ w := by simp only [hw, roundW4]; split_ifs <;> omega
      have hs : (r ++ vs.toArray).size = r.size + w := by simp [hl]
      rw [show r.size + w = (r ++ vs.toArray).size from hs.symm,
        ih (j + 1) (r.size + 2) ((r ++ vs.toArray).size - 1) _ _ a₂ (vs.getLastD default) (by omega)
          (by omega) (by rw [rd_app, h2]; rfl)
          (by rw [hs, show r.size + w - 1 = r.size + (w - 1) by omega, rd_app, hL]),
        Option.bind_map]
      simp [Array.append_assoc, Bool.and_assoc]
    · simp only [h, ite_false, Option.bind_none]

theorem roundsT4_length {f o deg real n j : ℕ} {inK : Bool} {d : Digest} {c : Val} {tr : Trace}
    {x : List Val × Bool × Trace} (hx : roundsT4 inp f o deg inK real n j d c tr = some x) :
    x.1.length = roundW4 deg inK * n := by
  induction n generalizing j d c tr x with
  | zero => simp [roundsT4] at hx; subst hx; simp
  | succ n ih =>
    rcases tr with _ | ⟨⟨q₁, a₁⟩, _ | ⟨⟨q₂, a₂⟩, tr⟩⟩
    · cases hx
    · cases hx
    simp only [roundsT4] at hx
    split_ifs at hx
    obtain ⟨y, hy, rfl⟩ := Option.map_eq_some_iff.1 hx
    rw [List.length_append, ih hy, (roundV4_spec inp _ _ _ _ _ _ _ _).1, Nat.mul_succ]
    omega

/-- **`roundsT4`'s Fiat–Shamir entries** are the chain of its round messages (`roundMsgs`, `S`'s
round bytes `roundBytesD`), and the last answer is the last round's squeeze register (3.x's
`roundsT_chain`). -/
theorem roundsT4_chain {f o deg real k j : ℕ} {inK : Bool} {d : Digest} {cl : Val} {tr : Trace}
    {x : List Val × Bool × Trace} (hx : roundsT4 inp f o deg inK real k j d cl tr = some x)
    {p : ℕ} (hp : p ≠ 0) :
    ∃ seg, tr = seg ++ x.2.2 ∧ seg.length = 2 * k ∧
      ChainOK inp seg (roundMsgs (fieldOffA.getD f 0) o (roundBytesD deg inK) j k) p d ∧
      lastAns seg d = if k = 0 then d else
        (x.1.getD (roundW4 deg inK * k - roundW4 deg inK + 2) default).toD := by
  induction k generalizing j d cl tr x p with
  | zero =>
    simp [roundsT4] at hx; subst hx
    exact ⟨[], by simp, rfl, by simp [ChainOK, roundMsgs], by simp [lastAns]⟩
  | succ k ih =>
    rcases tr with _ | ⟨⟨q₁, a₁⟩, _ | ⟨⟨q₂, a₂⟩, tr⟩⟩
    · cases hx
    · cases hx
    simp only [roundsT4] at hx
    by_cases hq : q₁ = absorbQ d (msgAt inp f (o + j * roundBytesD deg inK) (roundBytesD deg inK)) ∧
      q₂ = squeezeQ a₁
    swap; · rw [if_neg hq] at hx; cases hx
    rw [if_pos hq] at hx
    obtain ⟨y, hy, rfl⟩ := Option.map_eq_some_iff.1 hx
    obtain ⟨seg, h1, h2, h3, h4⟩ := ih hy (p := p + 2) (by omega)
    have hv := roundV4_spec inp f (o + j * roundBytesD deg inK) deg inK (decide (j < real)) a₁ a₂ cl
    have hW3 : 3 ≤ roundW4 deg inK := by unfold roundW4; split_ifs <;> omega
    generalize roundW4 deg inK = W at hv h4 hW3 ⊢
    generalize roundV4 inp f (o + j * roundBytesD deg inK) deg inK (decide (j < real)) a₁ a₂ cl = V at hv ⊢
    obtain ⟨hvl, hv2, -⟩ := hv
    refine ⟨(q₁, a₁) :: (q₂, a₂) :: seg, by simp [h1], by simp [h2]; omega, ?_, ?_⟩
    · simp only [roundMsgs, List.range'_succ, List.flatMap_cons, List.cons_append, List.nil_append,
        ChainOK, qOf, if_neg hp]
      refine ⟨?_, hq.2, ?_⟩
      · rw [hq.1, msgAt]; simp [absOff, Nat.add_assoc]
      · simpa [roundMsgs, show p + 1 + 1 = p + 2 by omega] using h3
    · rw [lastAns_cons, lastAns_cons, h4, if_neg (Nat.succ_ne_zero k)]
      rcases Nat.eq_zero_or_pos k with rfl | hk
      · rw [if_pos rfl, show W * (0 + 1) - W + 2 = 2 by omega, List.getD_eq_getElem?_getD,
          List.getElem?_append_left (by omega), ← List.getD_eq_getElem?_getD, hv2]; rfl
      · have hW1 : W ≤ W * k := Nat.le_mul_of_pos_right _ hk
        dsimp only
        rw [if_neg (by omega),
          show W * (k + 1) - W + 2 = V.length + (W * k - W + 2) by rw [hvl, Nat.mul_succ]; omega, getD_app]

/-! ## Controls: a grinded phase as `gen4` emits it -/

/-- `L1`'s ops (`.squeezes 1 .one`, a grinded single squeeze) of any kind at any context. -/
theorem l1_ops (S : Seq) (p : KindP) (n : ℕ) (c : GCtx) :
    (genPhase4 S p n ("L1", .squeezes 1 .one) c).1 =
      [.askSqueeze c.st, .chF c.next 0] ++ powOps c.next (c.next + 2) := by
  simp [genPhase4, sqzOps, kSqueeze]

/-- An answer whose byte 31 is `byte` (every other byte `7`). -/
def ansB (byte : UInt8) : Digest := Vector.ofFn fun i => if i.val = 31 then byte else 7

/-- `L1` run from the state `s` (register 0) on the one-entry trace `(squeezeQ s, a)`: its flag. -/
theorem l1_run (S : Seq) (p : KindP) (n : ℕ) (s a : Digest) :
    (exec impl κ inp (genPhase4 S p n ("L1", .squeezes 1 .one) ⟨1, 0, 0, [], [], 0, #[]⟩).1
      ⟨#[.d s], true⟩ [(squeezeQ s, a)]).map (·.1.ok) = some (powOk a) := by
  rw [l1_ops, show (⟨#[.d s], true⟩ : St) = ⟨#[.d s] ++ ([] : List Val).toArray, true⟩ by simp]
  rw [List.cons_append, exec_app]
  simp only [evalOp, show rd (#[Val.d s] ++ ([] : List Val).toArray) 0 = .d s from rfl, Val.toD, ite_true,
    List.nil_append]
  rw [List.cons_append, exec_app]
  simp only [evalOp, show rd (#[Val.d s] ++ [Val.d a].toArray) 1 = .d a from rfl, Val.toD,
    List.cons_append, List.nil_append]
  have h3 : (1 : ℕ) + 2 = (#[Val.d s] ++ [Val.d a, Val.f (chF a 0)].toArray).size := rfl
  rw [h3, ← List.append_nil (powOps _ _), exec_powOps impl κ inp 1 _ _ a rfl]
  simp [exec]

/-- (+) **The honest, grinded answer is accepted**: byte 31 zero. -/
theorem l1_pow_accepts (S : Seq) (p : KindP) (n : ℕ) (s : Digest) :
    (exec impl κ inp (genPhase4 S p n ("L1", .squeezes 1 .one) ⟨1, 0, 0, [], [], 0, #[]⟩).1
      ⟨#[.d s], true⟩ [(squeezeQ s, ansB 0)]).map (·.1.ok) = some true := by
  rw [l1_run]; decide

/-- (−) **A wrong proof-of-work byte is rejected**: byte 31 is `1` (byte 30 and the challenge's
bytes `0 … 15` unconstrained). -/
theorem l1_pow_rejects (S : Seq) (p : KindP) (n : ℕ) (s : Digest) :
    (exec impl κ inp (genPhase4 S p n ("L1", .squeezes 1 .one) ⟨1, 0, 0, [], [], 0, #[]⟩).1
      ⟨#[.d s], true⟩ [(squeezeQ s, ansB 1)]).map (·.1.ok) = some false := by
  rw [l1_run]; decide

/-- (−) Every nonzero byte 31 is rejected, every zero one accepted: the check is exactly the byte. -/
theorem powOk_iff (d : Digest) : powOk d = true ↔ d[31] = 0 := by simp [powOk]

/-- (−) **The K challenges are not grinded**: the cap check's `ζ` phase emits no proof of work. -/
theorem capZeta_no_pow (S : Seq) (p : KindP) (n : ℕ) (c : GCtx) :
    (genPhase4 S p n ("CapZeta", .squeezes 1 .one) c).1 = [.askSqueeze c.st, .chF c.next 0] := by
  simp [genPhase4, sqzOps, kSqueeze]

/-! ## Controls: every kind grinds every round (the orchestrator's ruling on the D128 review, finding 1)

A dummy round's zero check covers `c₀ ‖ c₁` (degree 2) or `c₀ ‖ c₁ ‖ c₂` (degree 3), not the nonce, so
a small kind's dummy round can carry a nonzero nonce and grind; a nonzero coefficient byte is still
rejected. Messages at absolute offset `0` (`gen4` reads field `0`). -/

theorem absOff0 (x : ℕ) : absOff 0 x = x := by
  rw [absOff, fieldOffA_getD (by decide)]; simp [fieldOff]

/-- A 64-byte proof, zero but byte `i`, which is `v`. -/
def piAt (i : ℕ) (v : UInt8) : ByteArray := ⟨Array.ofFn (n := 64) fun j => if j.val = i then v else 0⟩

/-- Its input. -/
def inpAt (i : ℕ) (v : UInt8) : Input := ⟨zeroD, zeroD, piAt i v⟩

/-- The dummy check of a round at offset `0` of `inpAt i v`. -/
def dummyBody (deg i : ℕ) (v : UInt8) : Bool := (Val.b (msgAt (inpAt i v) 0 0 (bodyLen deg))).isZero

/-- (+) **A dummy round's nonce is free**: degree 2, byte 40 (the third slot `[32, 48)`), degree 3,
byte 56 (the appended `[48, 64)`); (−) **its coefficients are not**: degree 2, byte 20 (`c₁`),
degree 3, byte 40 (`c₂`). -/
theorem dummy_body_ctl : dummyBody 2 40 0xAB = true ∧ dummyBody 3 56 0xAB = true ∧
    dummyBody 2 20 1 = false ∧ dummyBody 3 40 1 = false := by
  simp only [dummyBody, msgAt, absOff0]; decide +kernel

/-- (−) **3.x's whole-message check would have rejected the nonce** (degree 2: 48 bytes; degree 3:
the 64-byte message): the exclusion is needed. -/
theorem dummy_whole_rejects : (Val.b (msgAt (inpAt 40 0xAB) 0 0 48)).isZero = false ∧
    (Val.b (msgAt (inpAt 56 0xAB) 0 0 64)).isZero = false := by
  simp only [msgAt, absOff0]; decide +kernel

/-- **A dummy round's flag** (`exec_roundF4` at `real = false`): the proof of work and the body. So
with the controls above, a dummy degree-2 round of `inpAt 40 0xAB` (nonzero nonce) is accepted
exactly when its answer passes the proof of work, and one of `inpAt 20 1` is rejected. -/
theorem dummy_round_flag (deg : ℕ) (i : ℕ) (v : UInt8) (st cl : ℕ) (r : Array Val) (ok : Bool)
    (ops : List Op) (d : Digest) (c : Val) (hst : st < r.size) (hcl : cl < r.size)
    (hd : (rd r st).toD = d) (hc : rd r cl = c) (a₁ a₂ : Digest) (tr : Trace) :
    exec impl κ (inpAt i v) (roundOpsF4 0 0 deg (fun _ => false) st cl r.size ++ ops) ⟨r, ok⟩
        ((absorbQ d (msgAt (inpAt i v) 0 0 (roundBytesD deg false)), a₁) :: (squeezeQ a₁, a₂) :: tr) =
      exec impl κ (inpAt i v) ops ⟨r ++ (roundF4V (inpAt i v) 0 0 deg false a₁ a₂ c).toArray,
        ok && (powOk a₂ && dummyBody deg i v)⟩ tr := by
  rw [exec_roundF4 impl κ (inpAt i v) 0 0 deg _ st cl r ok ops d c hst hcl hd hc]
  simp [dummyBody]

/-- (+) **The segment-only zero check of `Lrend`/`Eend` leaves the appended nonce out**: the last 16
bytes of a 64-byte message are not read (`absTail4`'s `piField … (len − S.nb)`, `seq4.nb = 16`); (−) a nonzero
byte before them is. -/
theorem end_nonce_ctl : seq4.nb = 16 ∧ (Val.b (msgAt (inpAt 56 0xAB) 0 0 (64 - seq4.nb))).isZero = true ∧
    (Val.b (msgAt (inpAt 40 1) 0 0 (64 - seq4.nb))).isZero = false := by
  have h : seq4.nb = 16 := by rw [Seq.nb, seq4_eq]; rfl
  refine ⟨h, ?_⟩
  simp only [h, msgAt, absOff0]; decide +kernel

/-! ## Controls: a real degree-2 round derives `c₂` -/

/-- **A real degree-2 round's next claim** (`roundF4V`'s last register) is `c₀ + r(c₁ + r(c + c₁))`,
the evaluation at `r` of `g = (c₀, c₁, c + c₁)` (Horner), whose `g(0) + g(1) = c` holds by
construction in characteristic two (`FRSoundness128Rd.chk2d`). -/
theorem round2d_claim (f o : ℕ) (a₁ a₂ : Digest) (c : F) :
    (roundF4V inp f o 2 true a₁ a₂ (.f c)).getLastD default =
      .f (elemAt inp f o + chF a₂ 0 * (elemAt inp f (o + 16) + chF a₂ 0 * (c + elemAt inp f (o + 16)))) := by
  have hP := powVals_length a₂
  simp only [powW] at hP
  have h := (roundV4_spec inp f o 2 false true a₁ a₂ (.f c)).2.2
  simp only [roundV4, roundW4, Bool.false_eq_true, ite_false, show (2 : ℕ) ≠ 3 by decide] at h
  rw [← h]
  simp [roundF4V, Val.toF, List.getD_eq_getElem?_getD, List.getElem?_append_right, hP]

/-! Finding 5 of the D128 review (P2's byte 31 free of position bits for every kind) is I1's
`FRSoundness4Pos.p2_pow_room` (the table's `Seq.sqP`). -/

end Rev4
end FR
