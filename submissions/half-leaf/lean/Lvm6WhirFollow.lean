-- New for lvm6 (WP W1). The deployed opening follows its part of the schedule (ASM's `Follows`,
-- `PhasesFollow.whir`): `whirP cl` performs exactly the operations of `opsOf P17.levs
-- P17.openPart` (FORMAT6 v2.6 §6.6) in order, or rejects; hence no proof of work in the language.
import Lvm6WhirProg
import Lvm6AsmProg

/-!
# The opening follows §6.6 (W1)

* `follows_readF`, `follows_readFs`, `follows_roundP`, `follows_roundsP`, `follows_tailP`,
  `follows_sumP`, `follows_finP`: each piece of the program, over `chalE2`.
* `ladOps lad`: the operations of a ladder; `follows_ladP`.
* `follows_ladP_finE`: a final level (`finEOf`), for any row.
* **`whirP_follows`**: `Follows (whirP cl) (opsOf P17.levs P17.openPart)`.
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

/-- **A final level** (`finEOf`) follows its rounds, the final polynomial's `2^κ + ℓ` scalars, the
positions, the openings and the tail sumcheck's `κ` rounds. -/
theorem follows_ladP_finE (pl : PLv) (κ ℓ h kq t c gq : ℕ) (hκ : κ < 64) (hℓ : 1 ≤ ℓ) (hℓ' : ℓ ≤ 64)
    (hh : h ≤ 64) (hc : 0 < c) (hch : c * h ≤ 128) (ht : t ≤ (kq + 1) * c) (w : WtE.Wt (0 + ℓ))
    (σ : E2) :
    Follows (ladP chalE2 (.fin (finEOf pl κ ℓ h kq t c gq hκ hℓ hℓ' hh hc hch ht)) w σ)
      ((List.replicate ℓ roundOps).flatten ++ (List.replicate (2 ^ κ + ℓ) .rd ++
        ((.rd :: List.replicate (kq + 1) .smp) ++ ([.opn 4] ++ sumOps κ)))) :=
  Follows.bind' (follows_roundsP 10 ℓ) fun _ ↦ Follows.bind' (follows_readFs (2 ^ κ + ℓ)) fun _ ↦
    Follows.bind' (follows_grp gq kq) fun _ ↦ Follows.bind' (o₁ := [Op.opn 4])
      (show Follows (VerifierProgram.queryOpenings 4 _) [Op.opn 4] from ⟨rfl, fun _ ↦ rfl⟩)
      fun _ ↦ follows_ite (fun _ ↦ follows_sumP 2 _ _ κ [] _)
        (fun _ ↦ (trivial : Follows (VerifierProgram.fail : VerifierProgram Bool) _))

/-- **The deployed final level** follows its rounds, the final polynomial (8 scalars), the positions
(3 draws), the openings and the tail sumcheck (2 rounds). -/
theorem follows_ladP_fin (w : WtE.Wt (0 + 4)) (σ : E2) :
    Follows (ladP chalE2 (.fin finD) w σ) ((List.replicate 4 roundOps).flatten ++
      (List.replicate 8 .rd ++ ((.rd :: List.replicate (2 + 1) .smp) ++ ([.opn 4] ++ sumOps 2)))) :=
  follows_ladP_finE _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ w σ

/-- The opening's operations, level by level (`P17`). -/
def opsD : List Op :=
  (List.replicate 6 roundOps).flatten ++ (tailOps 6 19 32 17 18 0 ++
  ((List.replicate 4 roundOps).flatten ++ (tailOps 4 18 32 13 7 1 ++
  ((List.replicate 4 roundOps).flatten ++ (tailOps 4 17 32 9 3 2 ++
  ((List.replicate 4 roundOps).flatten ++ (tailOps 4 16 32 5 2 3 ++
  ((List.replicate 4 roundOps).flatten ++ (List.replicate 8 .rd ++
    ((.rd :: List.replicate (2 + 1) .smp) ++ ([.opn 4] ++ sumOps 2)))))))))))

theorem whirP_follows_opsD (cl : (List E2 → E2) × E2) : Follows (whirP cl) opsD :=
  follows_ladP_mid mid0 _ _ (fun _ _ ↦ follows_ladP_mid mid1 _ _ (fun _ _ ↦
    follows_ladP_mid mid2 _ _ (fun _ _ ↦ follows_ladP_mid mid3 _ _ (fun _ _ ↦
      follows_ladP_fin _ _) _ _) _ _) _ _) _ _

theorem opsD_eq : opsOf P17.levs P17.openPart = opsD := by decide +kernel

/-- **The deployed opening follows §6.6 of the schedule** (ASM's `PhasesFollow.whir` at `P17`). -/
theorem whirP_follows (cl : (List E2 → E2) × E2) :
    Follows (whirP cl) (opsOf P17.levs P17.openPart) := by
  rw [opsD_eq]
  exact whirP_follows_opsD cl

end Lvm6.Whir
