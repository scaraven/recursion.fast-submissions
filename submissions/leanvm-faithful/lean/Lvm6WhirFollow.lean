-- New for lvm6 (WP W1). The deployed opening follows its part of the schedule (ASM's `Follows`,
-- `PhasesFollow.whir`): `whirP18 cl` performs exactly the operations of `opsOf P18.levs
-- P18.openPart` (FORMAT6 v2.2.1 §6.6) in order, or rejects; hence no proof of work in the language.
import Lvm6WhirProg
import Lvm6AsmProg

/-!
# The opening follows §6.6 (W1)

* `follows_readF`, `follows_readFs`, `follows_roundP`, `follows_roundsP`, `follows_tailP`,
  `follows_sumP`, `follows_finP`: each piece of the program, over `chalE2`.
* `ladOps lad`: the operations of a ladder; `follows_ladP`.
* **`whirP18_follows`**: `Follows (whirP18 cl) (opsOf P18.levs P18.openPart)`.
-/

namespace Lvm6.Whir

open LeanVM.Parameters LeanVM.Protocol.Compile LeanVM.Protocol.Whir.Sound Lvm.E2V

theorem follows_readF : Follows (readF chalE2) [.rd] := ⟨rfl, fun _ ↦ rfl⟩

theorem follows_readFs : ∀ n, Follows (readFs chalE2 n) (List.replicate n .rd)
  | 0 => rfl
  | n + 1 => by
    rw [List.replicate_succ, show Op.rd :: List.replicate n Op.rd =
      [Op.rd] ++ (List.replicate n Op.rd ++ []) by simp]
    exact Follows.bind' follows_readF fun _ ↦ Follows.bind' (follows_readFs n) fun _ ↦ rfl

theorem follows_grp (g k : ℕ) : Follows (chalE2.grp g k) (.rd :: List.replicate (k + 1) .smp) :=
  follows_grp6 g k

/-- A fold round's operations: `E(4)`, `G(g)`, `D(1)`. -/
def roundOps : List Op := List.replicate 4 .rd ++ (.rd :: List.replicate 2 .smp)

theorem follows_roundP (g : ℕ) : Follows (roundP chalE2 g) roundOps := by
  unfold roundP roundOps
  rw [show List.replicate 4 Op.rd ++ (Op.rd :: List.replicate 2 Op.smp) =
    [Op.rd] ++ ([Op.rd] ++ ([Op.rd] ++ ([Op.rd] ++ ((Op.rd :: List.replicate (1 + 1) Op.smp) ++
      [])))) by rfl]
  exact Follows.bind' follows_readF fun _ ↦ Follows.bind' follows_readF fun _ ↦
    Follows.bind' follows_readF fun _ ↦ Follows.bind' follows_readF fun _ ↦
      Follows.bind' (follows_grp g 1) fun _ ↦ rfl

theorem follows_roundsP (g : ℕ) : ∀ j, Follows (roundsP chalE2 g j) ((List.replicate j roundOps).flatten)
  | 0 => rfl
  | j + 1 => by
    rw [List.replicate_succ, List.flatten_cons, ← List.append_nil (List.flatten _)]
    exact Follows.bind' (follows_roundP g) fun _ ↦ Follows.bind' (follows_roundsP g j) fun _ ↦ rfl

/-- The operations of a level's interface. -/
def tailOps (nh ht wd ko kq i : ℕ) : List Op :=
  List.replicate nh .rd ++ ([.cap ht wd] ++ ([.smp] ++ ((.rd :: List.replicate (ko + 1) .smp) ++
    ([.rd] ++ ((.rd :: List.replicate (kq + 1 + 1) .smp) ++ ([.opn i] ++ []))))))

theorem follows_tailP {n n' m' : ℕ} (L : TailIface E2 n n' m') (ht wd i gO gQ : ℕ) (vals) :
    Follows (tailP L chalE2 ht wd i gO gQ vals) (tailOps L.nh ht wd L.ko L.kq i) := by
  unfold tailP tailOps
  exact Follows.bind' (follows_readFs _) fun _ ↦ Follows.bind' ⟨rfl, rfl⟩ fun _ ↦
    Follows.bind' ⟨rfl, fun _ ↦ rfl⟩ fun _ ↦ Follows.bind' (follows_grp _ _) fun _ ↦
      Follows.bind' follows_readF fun _ ↦ Follows.bind' (follows_grp _ _) fun _ ↦
        Follows.bind' ⟨rfl, fun _ ↦ rfl⟩ fun _ ↦ rfl

/-- The tail sumcheck's operations: `n` rounds `E(2)`, `G(g)`. -/
def sumOps (n : ℕ) : List Op := (List.replicate n [.rd, .rd, .rd, .smp]).flatten

theorem follows_sumP (g : ℕ) (Φ M : List E2 → E2) :
    ∀ n τ c, Follows (sumP chalE2 g Φ M n τ c) (sumOps n)
  | 0, _, _ => rfl
  | n + 1, τ, c => by
    rw [sumOps, List.replicate_succ, List.flatten_cons,
      show [Op.rd, Op.rd, Op.rd, Op.smp] ++ (List.replicate n [Op.rd, Op.rd, Op.rd, Op.smp]).flatten =
        [Op.rd] ++ ([Op.rd] ++ ((Op.rd :: List.replicate (0 + 1) Op.smp) ++ sumOps n)) by rfl]
    exact Follows.bind' follows_readF fun _ ↦ Follows.bind' follows_readF fun _ ↦
      Follows.bind' (follows_grp g 0) fun _ ↦ follows_sumP g Φ M n _ _

theorem follows_ite {α : Type} {c : Prop} [Decidable c] {p q : VerifierProgram α} {os : List Op}
    (hp : c → Follows p os) (hq : ¬ c → Follows q os) : Follows (if c then p else q) os := by
  split
  · exact hp ‹_›
  · exact hq ‹_›

/-- **A level with a next one** follows its rounds, its interface and the rest. -/
theorem follows_ladP_mid {n ℓ n' ℓ' : ℕ} (M : MidLv E2 WtE n ℓ n' ℓ') (rest : Lad E2 WtE n' ℓ')
    (os : List Op) (hrest : ∀ w σ, Follows (ladP chalE2 rest w σ) os) (w : WtE.Wt (0 + ℓ))
    (σ : E2) : Follows (ladP chalE2 (.mid M rest) w σ) ((List.replicate ℓ roundOps).flatten ++
      (tailOps M.L.nh M.ht M.wd M.L.ko M.L.kq M.i ++ os)) :=
  Follows.bind' (follows_roundsP M.g ℓ) fun _ ↦ Follows.bind' (follows_tailP _ _ _ _ _ _ _)
    fun _ ↦ hrest _ _

/-- **The final level** follows its rounds, the final polynomial, the positions, the openings and
the tail sumcheck. -/
theorem follows_ladP_fin (w : WtE.Wt (0 + 4)) (σ : E2) :
    Follows (ladP chalE2 (.fin fin18) w σ) ((List.replicate 4 roundOps).flatten ++
      (List.replicate 12 .rd ++ ((.rd :: List.replicate (2 + 1) .smp) ++ ([.opn 4] ++ sumOps 3)))) :=
  Follows.bind' (follows_roundsP 10 4) fun _ ↦ Follows.bind' (follows_readFs 12) fun _ ↦
    Follows.bind' (follows_grp 13 2) fun _ ↦ Follows.bind' (o₁ := [Op.opn 4])
      (show Follows (VerifierProgram.queryOpenings 4 _) [Op.opn 4] from ⟨rfl, fun _ ↦ rfl⟩)
      fun _ ↦ follows_ite (fun _ ↦ follows_sumP 2 _ _ 3 [] _)
        (fun _ ↦ (trivial : Follows (VerifierProgram.fail : VerifierProgram Bool) _))

/-- The opening's operations, level by level. -/
def ops18 : List Op :=
  (List.replicate 6 roundOps).flatten ++ (tailOps 6 20 32 18 18 0 ++
  ((List.replicate 4 roundOps).flatten ++ (tailOps 4 19 32 14 7 1 ++
  ((List.replicate 4 roundOps).flatten ++ (tailOps 4 18 32 10 4 2 ++
  ((List.replicate 4 roundOps).flatten ++ (tailOps 4 17 32 6 2 3 ++
  ((List.replicate 4 roundOps).flatten ++ (List.replicate 12 .rd ++
    ((.rd :: List.replicate (2 + 1) .smp) ++ ([.opn 4] ++ sumOps 3)))))))))))

theorem whirP18_follows_ops18 (cl : (List E2 → E2) × E2) : Follows (whirP18 cl) ops18 :=
  follows_ladP_mid mid0 _ _ (fun _ _ ↦ follows_ladP_mid mid1 _ _ (fun _ _ ↦
    follows_ladP_mid mid2 _ _ (fun _ _ ↦ follows_ladP_mid mid3 _ _ (fun _ _ ↦
      follows_ladP_fin _ _) _ _) _ _) _ _) _ _

theorem ops18_eq : opsOf P18.levs P18.openPart = ops18 := by decide +kernel

/-- **The deployed opening follows §6.6 of the schedule** (ASM's `PhasesFollow.whir` at `P18`). -/
theorem whirP18_follows (cl : (List E2 → E2) × E2) :
    Follows (whirP18 cl) (opsOf P18.levs P18.openPart) := by
  rw [ops18_eq]
  exact whirP18_follows_ops18 cl

end Lvm6.Whir
