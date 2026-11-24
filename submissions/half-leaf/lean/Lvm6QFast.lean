-- New for lvm6 (KDQ, kernel diet): kernel-friendly copies of `Q_link`'s static checks (`opensOK`, `streamOkL6`,
-- `qOkS6`), each proved equal to the original for every plan.
import Lvm6P18MemoS
import Lvm6QLink
import Lvm6QFormat

/-!
# Fast copies of `Q_link`'s static checks (KDQ)

The kernel decides `opensOKP18`, `streamOkP18` and `qOkSP18` by evaluating the checks over `P18`'s plan (4349
entries). Their copies here compute the same Booleans with fewer kernel steps:

* comparisons are `Nat.ble`/`Nat.blt`/`Nat.beq` instead of `decide` (`Memo.decide_le`, …);
* `opensOKF` compares an opening's entries with its plan by `PE6.beqF` (field by field, `Nat.beq`) instead of the
  derived `DecidableEq` (`Memo.beqBy_eq_decide`, `PE6.beqF_iff`);
* `qOkS6F` reads an entry's lane by one pass over the plan (`eLane6F`, `bOffGo`) instead of
  `slenS ((lens6 P).take i)` (three list passes).

**`opensOK_eq_F`**, **`streamOkL6_eq_F`**, **`qOkS6_eq_F`**: each copy is the original, for every plan.

**`opens6_P18`** (in `Lvm6P18Memo` since INT11): `P18`'s openings (`Q.opensP18`) as the literal `opensTabP18`, checked once.
-/

set_option autoImplicit false

namespace Lvm6.Q

open RecursionFast Lvm Lvm.Replay Lvm.QLink Lvm.Loop Lvm.Loop.Build

/-! ## Entries compared field by field -/

/-- Equality of entry kinds, field by field. -/
def EK6.beqF : EK6 → EK6 → Bool
  | .q0, .q0 => true
  | .seed, .seed => true
  | .fs a b, .fs c d => Nat.beq a c && Nat.beq b d
  | .leaf, .leaf => true
  | .node a b c d none, .node a' b' c' d' none => Nat.beq a a' && Nat.beq b b' && Nat.beq c c' && Nat.beq d d'
  | .node a b c d (some (x, y, z)), .node a' b' c' d' (some (x', y', z')) =>
    Nat.beq a a' && Nat.beq b b' && Nat.beq c c' && Nat.beq d d' && Nat.beq x x' && Nat.beq y y' && Nat.beq z z'
  | _, _ => false

theorem EK6.beqF_iff (a b : EK6) : EK6.beqF a b = true ↔ a = b := by
  rcases a with _ | _ | ⟨_, _⟩ | _ | ⟨_, _, _, _, _ | ⟨_, _, _⟩⟩ <;>
    rcases b with _ | _ | ⟨_, _⟩ | _ | ⟨_, _, _, _, _ | ⟨_, _, _⟩⟩ <;>
    simp [EK6.beqF, Nat.beq_eq, and_assoc]

/-- Equality of entries, field by field. -/
def PE6.beqF (a b : PE6) : Bool := EK6.beqF a.k b.k && Nat.beq a.len b.len

theorem PE6.beqF_iff (a b : PE6) : PE6.beqF a b = true ↔ a = b := by
  rcases a with ⟨k, l⟩
  rcases b with ⟨k', l'⟩
  simp [PE6.beqF, EK6.beqF_iff, Nat.beq_eq]

/-! ## `opensOK` -/

/-- `opensOK` with `Nat.ble`/`Nat.blt` and `PE6.beqF`. -/
def opensOKF (P : List PE6) (os : List Open6Q) : Bool :=
  (os.all fun o => Nat.ble 2 o.i0 && Nat.ble (o.i0 + o.t * (1 + o.path)) P.length &&
    Memo.beqBy PE6.beqF ((P.drop o.i0).take (o.t * (1 + o.path))) o.plan) &&
  P.zipIdx.all fun x => !x.1.k.isOpen ||
    os.any fun o => Nat.ble o.i0 x.2 && Nat.blt x.2 (o.i0 + o.t * (1 + o.path))

/-- **`opensOKF` is `opensOK`.** -/
theorem opensOK_eq_F (P : List PE6) (os : List Open6Q) : opensOK P os = opensOKF P os := by
  simp only [opensOK, opensOKF, Memo.beqBy_eq_decide PE6.beqF_iff, Memo.decide_le, Memo.decide_lt]

/-! ## `streamOkL6` -/

/-- `entryOk6` with `Nat.ble`/`Nat.blt`/`Nat.beq`. -/
def entryOk6F (P : List PE6) (e : PE6) (i : ℕ) : Bool :=
  match e.k with
  | .q0 => Nat.beq i 0 && Nat.beq e.len 7
  | .seed => Nat.beq i 1 && Nat.ble 64 e.len
  | .fs st _ => Nat.ble 32 e.len && Nat.blt st i && Nat.ble 1 i
  | .leaf => Nat.ble 1 i
  | .node pd sh h lvl cap =>
    Nat.beq e.len 64 && Nat.ble 2 i && Nat.blt lvl h && Nat.ble (sh + h) 128 && Nat.blt pd i && Nat.ble 1 pd &&
      (match cap with
       | none => true
       | some (ce, co, path) => Nat.beq (co % 8) 0 && Nat.ble path h && Nat.ble 32 co &&
           Nat.ble (co + 32 * 2 ^ (h - path)) (P.getD ce default).len && Nat.ble 1 ce && Nat.blt ce i)

theorem entryOk6_eq_F (P : List PE6) (e : PE6) (i : ℕ) : entryOk6 P e i = entryOk6F P e i := by
  rcases e with ⟨k, len⟩
  rcases k with _ | _ | ⟨_, _⟩ | _ | ⟨_, _, _, _, _ | ⟨_, _, _⟩⟩ <;>
    simp only [entryOk6, entryOk6F, Memo.decide_le, Memo.decide_lt, Memo.beq_nat]

/-- `streamOkL6` with `entryOk6F` and `Nat.beq`. -/
def streamOkL6F (P : List PE6) : Bool :=
  (P.tail.all fun e => Nat.beq (e.len % 8) 0) && P.zipIdx.all fun x => entryOk6F P x.1 x.2

/-- **`streamOkL6F` is `streamOkL6`.** -/
theorem streamOkL6_eq_F (P : List PE6) : streamOkL6 P = streamOkL6F P := by
  simp only [streamOkL6, streamOkL6F, entryOk6_eq_F, Memo.beq_nat]

/-! ## `qOkS6` -/

/-- `acc` plus the stream bytes of the first `i` entries (`40 + len` each), in one pass. -/
def bOffGo : List PE6 → ℕ → ℕ → ℕ
  | [], _, acc => acc
  | _ :: _, 0, acc => acc
  | e :: P, i + 1, acc => bOffGo P i (acc + (40 + e.len))

theorem bOffGo_eq : ∀ (P : List PE6) (i acc : ℕ), bOffGo P i acc = acc + slenS ((lens6 P).take i)
  | [], _, acc => by simp [bOffGo, lens6, slenS]
  | _ :: _, 0, acc => by simp [bOffGo, slenS]
  | e :: P, i + 1, acc => by
    rw [bOffGo, bOffGo_eq P i]
    simp only [lens6, slenS, List.map_cons, List.take_succ_cons, List.sum_cons] at *
    omega

/-- `eLane6` by one pass over the plan. -/
def eLane6F (P : List PE6) (i : ℕ) : ℕ := (1 + bOffGo P i 0) / 8

theorem eLane6_eq_F (P : List PE6) (i : ℕ) : eLane6 P i = eLane6F P i := by
  rw [eLane6, eLane6F, bOff6, bOffGo_eq, Nat.zero_add]

/-- `qOkS6` with `eLane6F` and `Nat.ble`/`Nat.blt`. -/
def qOkS6F (P : List PE6) (os : List Open6Q) (m K aQ : ℕ) : Bool :=
  Nat.ble (qltEntries6 P default).length (2 ^ aQ) &&
    Nat.ble (hashedLen6 P / 8 + 17) (2 ^ m) && Nat.ble (17 * nBlk (hashedLen6 P) + 4) (2 ^ m) &&
    P.all (fun e => Nat.blt e.len (2 ^ 64)) &&
    (List.range (17 * nBlk (hashedLen6 P) - hashedLen6 P / 8)).all
      (fun k => Nat.blt (padLane (hashedLen6 P) (hashedLen6 P / 8 + k)) (2 ^ 64)) &&
    os.all (fun o => Nat.ble 1 o.path && Nat.blt o.path o.h && (pchunks o.t).all (fun c => Nat.ble c.2 K) &&
      Nat.ble (eLane6F P o.ce + 1 + o.co / 8 + 4 * 2 ^ (o.h - o.path)) (2 ^ m) && Nat.blt o.row (2 ^ 64))

/-- **`qOkS6F` is `qOkS6`.** -/
theorem qOkS6_eq_F (P : List PE6) (os : List Open6Q) (m K aQ : ℕ) : qOkS6 P os m K aQ = qOkS6F P os m K aQ := by
  simp only [qOkS6, qOkS6F, eLane6_eq_F, Memo.decide_le, Memo.decide_lt]

end Lvm6.Q

namespace Lvm6

open Q

/-! ## The openings of `P18` -/

end Lvm6
