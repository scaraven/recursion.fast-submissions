-- New for lvm6 (WP LEN, F-X8b-1): the counts at `P18` (`opB` of the schedule is `bodyLen`; no part
-- before §6.6 opens a commitment) and the deployed opening's queries open `t_i` positions.
import Lvm6LenRun
import Lvm6WhirFollow
import Lvm6P18Memo

/-!
# `QLen` and the byte count at `P18` (LEN)

* `tP18 i`: the openings of level `i` (`P18.levs`).
* **`opB_P18`** (kernel): `opB` of `sched6 P18`'s operations with the scheme's read widths, cap
  levels and occupied words is `bodyLen P18`.
* **`noOpn_parts18`** (kernel): §6.1–§6.5's operations at `P18` have no opening.
* **`lad18_t`** (kernel): each level of `lad18` opens `tP18` of its commitment index positions.
* **`qlen_whirP18`**: the deployed opening's queries open `tP18 i` positions (W1's `List.ofFn` over
  `Fin L.t`).
-/

set_option autoImplicit false

namespace Lvm6

open LeanVM.Parameters LeanVM.Protocol.Compile LeanVM.Protocol.Whir.Sound Lvm.E2V

/-- The openings of level `i` at `P18`. -/
def tP18 (i : ℕ) : ℕ := (P18.levs.getD i default).t

/-- **The byte count of the `P18` schedule** is `bodyLen P18`. -/
theorem opB_P18 : opB (V.capOfL P18.levs) (V.occL P18.levs) tP18 [] (V.widths (sched6 P18))
    (opsOf P18.levs (sched6 P18)) = bodyLen P18 := by
  rw [opsOf_P18, bodyLen, sched6_P18_eq]
  decide +kernel

/-- The parts before §6.6 open no commitment. -/
theorem noOpn_parts18 : noOpnB (opsOf P18.levs P18.commitPart) = true ∧
    noOpnB (opsOf P18.levs P18.treePart) = true ∧ noOpnB (opsOf P18.levs P18.spongePart) = true ∧
    noOpnB (opsOf P18.levs (P18.subT.typed ++ P18.subT.bus)) = true ∧
    noOpnB (opsOf P18.levs P18.ringPart) = true := by
  decide +kernel

namespace Whir

theorem noOpn_rep (n : ℕ) (o : Op) (h : ∀ i, o ≠ .opn i) : NoOpn (List.replicate n o) := by
  intro i hi
  exact h i (List.eq_of_mem_replicate hi).symm

theorem noOpn_append {a b : List Op} (ha : NoOpn a) (hb : NoOpn b) : NoOpn (a ++ b) := by
  intro i hi
  rcases List.mem_append.1 hi with h | h
  · exact ha i h
  · exact hb i h

theorem noOpn_grp (k : ℕ) : NoOpn (.rd :: List.replicate k .smp) := by
  intro i hi
  rcases List.mem_cons.1 hi with h | h
  · cases h
  · cases List.eq_of_mem_replicate h

theorem noOpn_rounds (j : ℕ) : NoOpn (List.replicate j roundOps).flatten := by
  intro i hi
  obtain ⟨l, hl, hm⟩ := List.mem_flatten.1 hi
  rw [List.eq_of_mem_replicate hl] at hm
  exact noOpn_of roundOps rfl i hm

theorem noOpn_sum (n : ℕ) : NoOpn (sumOps n) := by
  intro i hi
  obtain ⟨l, hl, hm⟩ := List.mem_flatten.1 hi
  rw [List.eq_of_mem_replicate hl] at hm
  simp at hm

theorem qlen_tailP {t : ℕ → ℕ} {n n' m' : ℕ} (L : TailIface E2 n n' m') (ht wd i gO gQ : ℕ) (vals)
    (hL : L.t = t i) : QLen t (tailP L chalE2 ht wd i gO gQ vals) := by
  unfold tailP
  exact QLen.bind' (qlen_of_follows (follows_readFs _) (noOpn_rep _ _ fun _ h ↦ by cases h))
    fun _ ↦ QLen.bind' (qlen_of_follows (os := [.cap ht wd]) ⟨rfl, rfl⟩ (noOpn_of _ rfl))
    fun _ ↦ QLen.bind' (qlen_of_follows (os := [.smp]) ⟨rfl, fun _ ↦ rfl⟩ (noOpn_of _ rfl))
    fun _ ↦ QLen.bind' (qlen_of_follows (follows_grp _ _) (noOpn_grp _))
    fun _ ↦ QLen.bind' (qlen_of_follows follows_readF (noOpn_of _ rfl))
    fun _ ↦ QLen.bind' (qlen_of_follows (follows_grp _ _) (noOpn_grp _))
    fun _ ↦ QLen.bind' (show QLen t (VerifierProgram.queryOpenings i _) from
      ⟨List.length_ofFn.trans hL, fun _ ↦ trivial⟩)
    fun _ ↦ trivial

theorem qlen_ladP_mid {t : ℕ → ℕ} {n ℓ n' ℓ' : ℕ} (M : MidLv E2 WtE n ℓ n' ℓ')
    (rest : Lad E2 WtE n' ℓ') (hM : M.L.t = t M.i) (hrest : ∀ w σ, QLen t (ladP chalE2 rest w σ))
    (w : WtE.Wt (0 + ℓ)) (σ : E2) : QLen t (ladP chalE2 (.mid M rest) w σ) :=
  QLen.bind' (qlen_of_follows (follows_roundsP M.g ℓ) (noOpn_rounds ℓ)) fun _ ↦
    QLen.bind' (qlen_tailP _ _ _ _ _ _ _ hM) fun _ ↦ hrest _ _

theorem qlen_ladP_fin {t : ℕ → ℕ} (h4 : fin18.Fv.t = t 4) (w : WtE.Wt (0 + 4)) (σ : E2) :
    QLen t (ladP chalE2 (.fin fin18) w σ) :=
  QLen.bind' (qlen_of_follows (follows_roundsP 10 4) (noOpn_rounds 4)) fun _ ↦
    QLen.bind' (qlen_of_follows (follows_readFs 12) (noOpn_rep _ _ fun _ h ↦ by cases h)) fun _ ↦
    QLen.bind' (qlen_of_follows (follows_grp 13 2) (noOpn_grp _)) fun _ ↦
    QLen.bind' (show QLen t (VerifierProgram.queryOpenings 4 _) from
      ⟨List.length_ofFn.trans h4, fun _ ↦ trivial⟩) fun _ ↦
    qlen_ite (fun _ ↦ qlen_of_follows (follows_sumP 2 _ _ 3 [] _) (noOpn_sum 3)) fun _ ↦ trivial

/-- **Each level of `lad18` opens `tP18` positions of its commitment** (kernel). -/
theorem lad18_t : mid0.L.t = tP18 mid0.i ∧ mid1.L.t = tP18 mid1.i ∧ mid2.L.t = tP18 mid2.i ∧
    mid3.L.t = tP18 mid3.i ∧ fin18.Fv.t = tP18 4 := by
  decide +kernel

/-- **The deployed opening's queries open `tP18 i` positions.** -/
theorem qlen_whirP18 (cl : (List E2 → E2) × E2) : QLen tP18 (whirP18 cl) :=
  qlen_ladP_mid mid0 _ lad18_t.1 (fun _ _ ↦ qlen_ladP_mid mid1 _ lad18_t.2.1 (fun _ _ ↦
    qlen_ladP_mid mid2 _ lad18_t.2.2.1 (fun _ _ ↦ qlen_ladP_mid mid3 _ lad18_t.2.2.2.1 (fun _ _ ↦
      qlen_ladP_fin lad18_t.2.2.2.2 _ _) _ _) _ _) _ _) _ _

end Whir

end Lvm6
