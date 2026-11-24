-- New for lvm6 (VS1): the driver's draws without the 192-bit answer number where the schedule ignores it, the proof
-- of work on the answer's lane 2, and the cap index by shifts (`VS6H = VS6`).
import Lvm6VDrive

/-!
# VS1: the driver's draws and cap comparisons

`PN`'s `draw chk upd` builds `N = answerBits a` (two GMP products and sums) for every draw and tests `chk N`. For the
schedule's `D` and `B` draws `chk = tt` and `upd = keepPs` ignore `N` (`drawTT`); for its ground groups `G g` the
check `pw g N` (`N < 2 ^ (192 - g)`, a GMP power) is the answer's lane 2 shifted right by `64 - g` (`pwA`, for
`g ≤ 64`). `capHit` computes `2 ^ ht`, `2 ^ (ht - lv)` and `2 ^ lv` per opened position; `capHitH` and `openNH` shift.

* `drawTT` (`drawTT_eq`), `pwA` (`pwA_eq`), `drawG` (`drawG_eq`);
* `capHitH` (`capHitH_eq`), `openNH` (`openNH_eq`), `PNH` (`PNH_eq : PNH π L = PN π L`);
* `itemH`, `walkH` (`walkH_eq`: the schedule's walk at `PN`); **`VS6H`**, **`VS6H_eq : VS6H = VS6`**.
-/

set_option autoImplicit false

namespace Lvm6.V

open RecursionFast

/-! ## Draws -/

/-- `PN`'s draw at `tt` and `keepPs`: the answer is the new state, nothing else is read off it. -/
def drawTT : NStep := fun ns k =>
  if 32 + ns.buf.size ≤ queryCap then
    .query (Lvm.digestBytes ns.st ++ ns.buf) fun a =>
      k { ns with st := a, buf := ByteArray.empty, acc := .draw a :: ns.acc }
  else .ret false

theorem drawTT_eq (π : ByteArray) (L : List Lev) : (PN π L).draw tt keepPs = drawTT := by
  funext ns k
  simp only [PN, tt, keepPs, drawTT, ite_true]

/-- **The proof of work on lane 2**: for `g ≤ 64`, `answerBits a < 2 ^ (192 - g)` iff lane 2 is below `2 ^ (64 - g)`. -/
def pwA (g : Nat) (a : Digest) : Bool :=
  if g ≤ 64 then Lvm.u64At (Lvm.digestBytes a) 16 >>> (64 - g) == 0 else pw g (Lvm.answerBits a)

theorem u64At_lt' (b : ByteArray) (o : Nat) : Lvm.u64At b o < 2 ^ 64 := by
  unfold Lvm.u64At; exact UInt64.toNat_lt _

theorem pwA_eq (g : Nat) (a : Digest) : pwA g a = pw g (Lvm.answerBits a) := by
  unfold pwA
  split
  · rename_i hg
    have h0 := u64At_lt' (Lvm.digestBytes a) 0
    have h8 := u64At_lt' (Lvm.digestBytes a) 8
    have hp : (2 : Nat) ^ (192 - g) = 2 ^ 128 * 2 ^ (64 - g) := by rw [← Nat.pow_add]; congr 1; omega
    have hK : 0 < (2 : Nat) ^ (64 - g) := Nat.two_pow_pos _
    simp only [pw, Lvm.answerBits, hp, Nat.shiftRight_eq_div_pow]
    generalize (2 : Nat) ^ (64 - g) = K at hK ⊢
    generalize Lvm.u64At (Lvm.digestBytes a) 0 = x0 at h0 ⊢
    generalize Lvm.u64At (Lvm.digestBytes a) 8 = x8 at h8 ⊢
    generalize Lvm.u64At (Lvm.digestBytes a) 16 = x16
    rw [Bool.eq_iff_iff, beq_iff_eq, decide_eq_true_eq, Nat.div_eq_zero_iff]
    omega
  · rfl

/-- `PN`'s draw at `pw g` and `keepPs` by `pwA`. -/
def drawG (g : Nat) : NStep := fun ns k =>
  if 32 + ns.buf.size ≤ queryCap then
    .query (Lvm.digestBytes ns.st ++ ns.buf) fun a =>
      if pwA g a then k { ns with st := a, buf := ByteArray.empty, acc := .draw a :: ns.acc }
      else .ret false
  else .ret false

theorem drawG_eq (π : ByteArray) (L : List Lev) (g : Nat) : (PN π L).draw (pw g) keepPs = drawG g := by
  funext ns k
  simp only [PN, keepPs, drawG, pwA_eq]

/-! ## Cap comparisons -/

/-- `capHit` by shifts. -/
def capHitH (π : ByteArray) (co ht lv p : Nat) (top : Digest) : Bool :=
  let idx := (p % (1 <<< ht)) >>> (ht - lv)
  decide (idx < 1 <<< lv) && decide (Lvm.digestAt π (co + 32 * idx) = top)

theorem capHitH_eq : capHitH = capHit := by
  funext π co ht lv p top
  simp only [capHitH, capHit, Nat.one_shiftLeft, Nat.shiftRight_eq_div_pow]

/-- `openN` over `capHitH`. -/
def openNH (π : ByteArray) (co ht lv lb : Nat) : List Nat → Nat → (Nat → List Nat → OProg Bool) → OProg Bool
  | [], off, k => k off []
  | p :: ps, off, k =>
    if π.size - off < lb then .ret false else
    .query (π.extract off (off + lb)) fun d₀ =>
      climbN π (ht - lv) d₀ (p % (1 <<< ht)) (off + lb) fun top off' =>
        if capHitH π co ht lv p top then openNH π co ht lv lb ps off' fun off'' os => k off'' (off :: os)
        else .ret false

theorem openNH_eq : openNH = openN := by
  funext π co ht lv lb ps
  induction ps with
  | nil => rfl
  | cons p ps ih =>
    funext off k
    simp only [openNH, openN, ih, capHitH_eq, Nat.one_shiftLeft]

/-- `PN` with `openNH`. -/
def PNH (π : ByteArray) (L : List Lev) : Prims NStep :=
  { PN π L with
    opn := fun i ns k =>
      match ns.caps[i]? with
      | none => .ret false
      | some (co, ht, w) =>
        openNH π co ht (capOfL L ht w) (8 * min (occL L ht w) w) ns.ps ns.off fun off' os =>
          k { ns with off := off', acc := .rows i ns.ps w (occL L ht w) (8 * min (occL L ht w) w) os :: ns.acc } }

theorem PNH_eq (π : ByteArray) (L : List Lev) : PNH π L = PN π L := by
  simp only [PNH, PN, openNH_eq]
  rfl

/-! ## The walk -/

/-- One item at `PNH`, with `drawTT` and `drawG`. -/
def itemH (π : ByteArray) (L : List Lev) : Item → NStep
  | .G g => (PNH π L).seq ((PNH π L).rd 8) (drawG g)
  | .D k => (PNH π L).rep drawTT k
  | .B => drawTT
  | it => (PNH π L).item L it

theorem itemH_eq (π : ByteArray) (L : List Lev) (it : Item) : itemH π L it = (PN π L).item L it := by
  cases it <;> simp only [itemH, Prims.item, PNH_eq, drawTT_eq, drawG_eq]

/-- The walk of a schedule at `itemH`. -/
def walkH (π : ByteArray) (L : List Lev) : List Item → NStep
  | [] => (PNH π L).skip
  | it :: r => (PNH π L).seq (itemH π L it) (walkH π L r)

theorem walkH_eq (π : ByteArray) (L : List Lev) : ∀ s, walkH π L s = (PN π L).walk L s
  | [] => by simp only [walkH, Prims.walk, PNH_eq]
  | it :: r => by simp only [walkH, Prims.walk, PNH_eq, itemH_eq, walkH_eq π L r]

/-- **`VS6` over `walkH`.** -/
def VS6H (sh : VShape) (F : ByteArray → List NV → Bool) (vk c : Digest) (π : Proof) : OProg Bool :=
  if hdrLen sh ≤ π.size then
    if hdrOkWith leafStmtF nodeStmtF sh.nStar vk c (π.extract 0 (hdrLen sh)) &&
        decide (32 + hdrLen sh ≤ queryCap) then
      .query q0Q fun a₀ =>
        .query (Lvm.digestBytes a₀ ++ π.extract 0 (hdrLen sh))
          fun st => walkH π sh.levs sh.sched ⟨hdrLen sh, ByteArray.empty, st, [], [], [], 0⟩ fun ns =>
            .ret (F π ns.acc && decide (π.size ≤ ns.off))
    else .ret false
  else .ret false

theorem VS6H_eq : VS6H = VS6 := by
  funext sh F vk c π
  simp only [VS6H, VS6, driveN, walkH_eq]

end Lvm6.V
