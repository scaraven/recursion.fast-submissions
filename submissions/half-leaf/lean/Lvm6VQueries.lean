-- New for lvm6 (WP-V1, part 2): `VS_queries`: the executable `V_S` front asks at most `2 + qOf` queries on
-- every proof and every oracle, `qOf` the schedule's query count by a static walk; `P18`'s fixed part with
-- §6.3's core is 4,166 (+ `q₀` and the seed), kernel-checked.
import Lvm6VDrive

/-!
# The query bound of `V_S`

**`PQ L`**: the schedule read as a static count. The state is the shapes of the caps read so far and the
number of positions; a draw costs 1 (its position update is applied to a dummy list: only the count
matters), an opening of commitment `i` costs `positions · (1 + ht − lv)` with the shape of the `i`-th cap.
`qOf L s` is the count of the schedule `s` from no caps and no positions.

**`VS6_queries`**: `((VS6 sh F vk c π).queries H).length ≤ 2 + qOf sh.levs sh.sched`, for every decision,
proof and oracle (the run may stop early; it never asks more). By a simulation over the shared expansion
(`QSim`), as in `Lvm6VEq`; the draws' position updates are length-uniform (`LenU`).
-/

set_option autoImplicit false

namespace Lvm6.V

open RecursionFast

/-- The static state: cap shapes and the number of positions. -/
abbrev QA : Type := List (Nat × Nat) × Nat

/-- **The schedule as a static query count.** -/
def PQ (L : List Lev) : Prims (QA → Nat × QA) where
  skip := fun a => (0, a)
  seq := fun f g a => ((f a).1 + (g (f a).2).1, (g (f a).2).2)
  rd := fun _ a => (0, a)
  draw := fun _ upd a => (1, (a.1, (upd (List.replicate a.2 0) 0).length))
  cap := fun ht w a => (0, (a.1 ++ [(ht, w)], a.2))
  reset := fun a => (0, (a.1, 0))
  opn := fun i a => (match a.1[i]? with
    | some (ht, w) => a.2 * (1 + (ht - capOfL L ht w))
    | none => 0, a)

/-- The query count of a schedule. -/
def qOf (L : List Lev) (s : List Item) : Nat := ((PQ L).walk L s ([], 0)).1

/-- The static state of a driver state. -/
def absOf (ns : NS) : QA := (ns.caps.map fun c => (c.2.1, c.2.2), ns.ps.length)

/-- A position update whose result's length depends on the input's length only. -/
def LenU (upd : List Nat → Nat → List Nat) : Prop :=
  ∀ ps ps' N N', ps.length = ps'.length → (upd ps N).length = (upd ps' N').length

theorem lenU_keep : LenU keepPs := fun _ _ _ _ h => h

theorem lenU_add (ht cnt : Nat) : LenU (addPs ht cnt) := fun _ _ _ _ h => by
  simp [addPs, posList, h]

section Q

variable (π : ByteArray) (L : List Lev) (H : ByteArray → Digest)

/-- **Query simulation**: from every state of static state `a`, the driver step asks at most the static
cost plus what its continuation asks from the static state after it. -/
def QSim (nf : NStep) (f : QA → Nat × QA) : Prop :=
  ∀ a kN B, (∀ ns, absOf ns = (f a).2 → ((kN ns).queries H).length ≤ B) →
    ∀ ns, absOf ns = a → ((nf ns kN).queries H).length ≤ (f a).1 + B

theorem qsim_skip : QSim H (PN π L).skip (PQ L).skip := fun _ _ _ hk ns ha => by
  simpa [PN, PQ] using hk ns ha

theorem qsim_seq {nf ng : NStep} {f g : QA → Nat × QA} (hf : QSim H nf f) (hg : QSim H ng g) :
    QSim H ((PN π L).seq nf ng) ((PQ L).seq f g) := fun a kN B hk ns ha => by
  have := hf a (fun ns' => ng ns' kN) ((g (f a).2).1 + B) (fun ns' ha' => hg _ kN B hk ns' ha') ns ha
  simp only [PN, PQ]
  omega

theorem qsim_rd (w : Nat) : QSim H ((PN π L).rd w) ((PQ L).rd w) := fun a kN B hk ns ha => by
  simp only [PN, PQ]
  split
  · simp [OProg.queries]
  · simpa using hk _ (by subst ha; rfl)

theorem qsim_draw (chk : Nat → Bool) (upd : List Nat → Nat → List Nat) (hu : LenU upd) :
    QSim H ((PN π L).draw chk upd) ((PQ L).draw chk upd) := fun a kN B hk ns ha => by
  simp only [PN, PQ]
  split
  · simp only [OProg.queries, List.length_cons]
    split
    · rw [Nat.add_comm]
      refine Nat.add_le_add_left (hk _ ?_) 1
      subst ha
      exact Prod.ext rfl (hu _ _ _ _ (by simp [absOf]))
    · simp [OProg.queries]
  · simp [OProg.queries]

theorem qsim_cap (ht w : Nat) : QSim H ((PN π L).cap ht w) ((PQ L).cap ht w) := fun a kN B hk ns ha => by
  simp only [PN, PQ]
  split
  · simp [OProg.queries]
  · simpa using hk _ (by subst ha; simp [absOf, PQ])

theorem qsim_reset : QSim H (PN π L).reset (PQ L).reset := fun a kN B hk ns ha => by
  simpa [PN, PQ] using hk _ (by subst ha; simp [absOf, PQ])

theorem climbN_q : ∀ (m : Nat) (d : Digest) (q off : Nat) (k : Digest → Nat → OProg Bool) (B : Nat),
    (∀ top off', ((k top off').queries H).length ≤ B) → ((climbN π m d q off k).queries H).length ≤ m + B := by
  intro m
  induction m with
  | zero => intro d q off k B hk; simpa [climbN] using hk d off
  | succ m ih =>
    intro d q off k B hk
    simp only [climbN]
    split
    · simp [OProg.queries]
    · simp only [OProg.queries, List.length_cons]
      exact le_trans (Nat.succ_le_succ (ih _ _ _ k B hk)) (by omega)

theorem openN_q (co ht lv lb : Nat) : ∀ (ps : List Nat) (off : Nat) (k : Nat → List Nat → OProg Bool) (B : Nat),
    (∀ off' os, ((k off' os).queries H).length ≤ B) →
    ((openN π co ht lv lb ps off k).queries H).length ≤ ps.length * (1 + (ht - lv)) + B := by
  intro ps
  induction ps with
  | nil => intro off k B hk; simpa [openN] using hk off []
  | cons p ps ih =>
    intro off k B hk
    simp only [openN]
    split
    · simp [OProg.queries]
    · simp only [OProg.queries, List.length_cons, List.length_cons]
      have := climbN_q π H (ht - lv) (H (π.extract off (off + lb))) (p % 2 ^ ht) (off + lb)
        (fun top off' => if capHit π co ht lv p top then
          openN π co ht lv lb ps off' (fun off'' os => k off'' (off :: os)) else .ret false)
        (ps.length * (1 + (ht - lv)) + B) (fun top off' => by
          split
          · exact ih _ _ B (fun _ _ => hk _ _)
          · simp [OProg.queries])
      rw [Nat.succ_mul]
      omega

theorem qsim_open (i : Nat) : QSim H ((PN π L).opn i) ((PQ L).opn i) := fun a kN B hk ns ha => by
  subst ha
  simp only [PN, PQ, absOf, List.getElem?_map]
  rcases hc : ns.caps[i]? with _ | ⟨co, ht, w⟩
  · simp [OProg.queries]
  · simp only [Option.map_some]
    exact openN_q π H co ht _ _ ns.ps ns.off _ B fun off' os => hk _ rfl

theorem qsim_rep {nf : NStep} {f : QA → Nat × QA} (hf : QSim H nf f) :
    ∀ m, QSim H ((PN π L).rep nf m) ((PQ L).rep f m)
  | 0 => qsim_skip π L H
  | m + 1 => qsim_seq π L H hf (qsim_rep hf m)

theorem qsim_posRest (ht : Nat) : ∀ cs, QSim H ((PN π L).posRest ht cs) ((PQ L).posRest ht cs)
  | [] => qsim_skip π L H
  | _ :: cs => qsim_seq π L H (qsim_draw π L H _ _ (lenU_add _ _)) (qsim_posRest ht cs)

theorem qsim_item (it : Item) : QSim H ((PN π L).item L it) ((PQ L).item L it) := by
  cases it with
  | E k => exact qsim_rep π L H (qsim_rd π L H 16) _
  | K k => exact qsim_rep π L H (qsim_rd π L H 8) _
  | cap i => exact qsim_cap π L H _ _
  | G g => exact qsim_seq π L H (qsim_rd π L H 8) (qsim_draw π L H _ _ lenU_keep)
  | D k => exact qsim_rep π L H (qsim_draw π L H _ _ lenU_keep) k
  | B => exact qsim_draw π L H _ _ lenU_keep
  | pos i g =>
    exact qsim_seq π L H (qsim_reset π L H) (qsim_seq π L H (qsim_rd π L H 8)
      (qsim_seq π L H (qsim_draw π L H _ _ (lenU_add _ _)) (qsim_posRest π L H _ _)))
  | «open» i => exact qsim_open π L H i

theorem qsim_walk : ∀ s, QSim H (driveN π L s) ((PQ L).walk L s)
  | [] => qsim_skip π L H
  | it :: s => qsim_seq π L H (qsim_item π L H it) (qsim_walk s)

end Q

/-- **`VS_queries`**: the executable `V_S` front asks at most `2 + qOf` queries, for every decision,
proof and oracle. -/
theorem VS6_queries (sh : VShape) (F : ByteArray → List NV → Bool) (vk c : Digest) (π : Proof)
    (H : ByteArray → Digest) : ((VS6 sh F vk c π).queries H).length ≤ 2 + qOf sh.levs sh.sched := by
  unfold VS6
  split
  · split
    · simp only [OProg.queries, List.length_cons]
      have := qsim_walk π sh.levs H sh.sched ([], 0) (fun ns => OProg.ret (F π ns.acc && decide (π.size ≤ ns.off))) 0
        (fun _ _ => by simp [OProg.queries])
        ⟨hdrLen sh, ByteArray.empty, H (Lvm.digestBytes (H q0Q) ++ π.extract 0 (hdrLen sh)),
          [], [], [], 0⟩ rfl
      unfold qOf
      omega
    · simp [OProg.queries]
  · simp [OProg.queries]

end Lvm6.V
