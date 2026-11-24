-- New for lvm6 (WP LEN, F-X8b-1): the counts at the deployed shape (`opB` of the schedule is `bodyLen`; no part
-- before §6.6 opens a commitment) and the deployed opening's queries open `t_i` positions.
-- PORT17 W1: the deployed shape is `P17` (the names are `P18`'s until the port's rename); the final level's
-- step is generic (`qlen_ladP_finE`).
import Lvm6LenRun
import Lvm6WhirFollow
import Lvm6P17Memo

/-!
# `QLen` and the byte count at `P17` (LEN)

* `tPD i`: the openings of level `i` (`P17.levs`).
* **`opB_P`** (kernel): `opB` of `sched6 P17`'s operations with the scheme's read widths, cap
  levels and occupied words is `bodyLen P17`.
* **`noOpn_parts`** (kernel): §6.1–§6.5's operations at `P17` have no opening.
* **`ladD_t`** (kernel): each level of `ladD` opens `tPD` of its commitment index positions.
* **`qlen_whirP`**: the deployed opening's queries open `tPD i` positions (W1's `List.ofFn` over
  `Fin L.t`).
-/

set_option autoImplicit false

namespace Lvm6

open LeanVM.Parameters LeanVM.Protocol.Compile LeanVM.Protocol.Whir.Sound Lvm.E2V

/-- The openings of level `i` at `P17`. -/
def tPD (i : ℕ) : ℕ := (P17.levs.getD i default).t

/-- **The byte count of the `P17` schedule** is `bodyLen P17`. -/
theorem opB_P : opB (V.capOfL P17.levs) (V.occL P17.levs) tPD [] (V.widths (sched6 P17))
    (opsOf P17.levs (sched6 P17)) = bodyLen P17 := by
  rw [opsOf_P17, bodyLen, sched6_P17_eq]
  decide +kernel

/-- The parts before §6.6 open no commitment. -/
theorem noOpn_parts : noOpnB (opsOf P17.levs P17.commitPart) = true ∧
    noOpnB (opsOf P17.levs P17.treePart) = true ∧ noOpnB (opsOf P17.levs P17.spongePart) = true ∧
    noOpnB (opsOf P17.levs (P17.subT.typed ++ P17.subT.bus)) = true ∧
    noOpnB (opsOf P17.levs P17.ringPart) = true := by
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

/-- **A final level** (`finEOf`) opens `t 4` positions of its commitment. -/
theorem qlen_ladP_finE {t : ℕ → ℕ} (pl : PLv) (κ ℓ h kq t' c gq : ℕ) (hκ : κ < 64) (hℓ : 1 ≤ ℓ)
    (hℓ' : ℓ ≤ 64) (hh : h ≤ 64) (hc : 0 < c) (hch : c * h ≤ 128) (ht : t' ≤ (kq + 1) * c)
    (h4 : (finEOf pl κ ℓ h kq t' c gq hκ hℓ hℓ' hh hc hch ht).Fv.t = t 4) (w : WtE.Wt (0 + ℓ)) (σ : E2) :
    QLen t (ladP chalE2 (.fin (finEOf pl κ ℓ h kq t' c gq hκ hℓ hℓ' hh hc hch ht)) w σ) :=
  QLen.bind' (qlen_of_follows (follows_roundsP 10 ℓ) (noOpn_rounds ℓ)) fun _ ↦
    QLen.bind' (qlen_of_follows (follows_readFs (2 ^ κ + ℓ)) (noOpn_rep _ _ fun _ h ↦ by cases h))
    fun _ ↦ QLen.bind' (qlen_of_follows (follows_grp gq kq) (noOpn_grp _)) fun _ ↦
    QLen.bind' (show QLen t (VerifierProgram.queryOpenings 4 _) from
      ⟨List.length_ofFn.trans h4, fun _ ↦ trivial⟩) fun _ ↦
    qlen_ite (fun _ ↦ qlen_of_follows (follows_sumP 2 _ _ κ [] _) (noOpn_sum κ)) fun _ ↦ trivial

theorem qlen_ladP_fin {t : ℕ → ℕ} (h4 : finD.Fv.t = t 4) (w : WtE.Wt (0 + 4)) (σ : E2) :
    QLen t (ladP chalE2 (.fin finD) w σ) :=
  qlen_ladP_finE _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ h4 w σ

/-- **Each level of `ladD` opens `tPD` positions of its commitment** (kernel). -/
theorem ladD_t : mid0.L.t = tPD mid0.i ∧ mid1.L.t = tPD mid1.i ∧ mid2.L.t = tPD mid2.i ∧
    mid3.L.t = tPD mid3.i ∧ finD.Fv.t = tPD 4 := by
  decide +kernel

/-- **The deployed opening's queries open `tPD i` positions.** -/
theorem qlen_whirP (cl : (List E2 → E2) × E2) : QLen tPD (whirP cl) :=
  qlen_ladP_mid mid0 _ ladD_t.1 (fun _ _ ↦ qlen_ladP_mid mid1 _ ladD_t.2.1 (fun _ _ ↦
    qlen_ladP_mid mid2 _ ladD_t.2.2.1 (fun _ _ ↦ qlen_ladP_mid mid3 _ ladD_t.2.2.2.1 (fun _ _ ↦
      qlen_ladP_fin ladD_t.2.2.2.2 _ _) _ _) _ _) _ _) _ _

end Whir

end Lvm6
