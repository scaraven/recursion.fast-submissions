-- New for `flock-recursive` (BLUEPRINT A.10 cap₀, §5.1 `hExt`; stage S-G6).
import FRSoundnessFrE
import FRSoundnessShift
import FRSoundnessLigFinal

/-!
# The extractor's interface: `DF 2 := far₀ ∨ ¬ Stmt` and `ExtIface`

Orchestrator's ruling (S-G6, on S-G5's question 2): phase 2's doom (`cap₀`) is
`far₀ ∨ ¬ Stmt`, where **`Stmt`** is every statement part on the decoded `f⁽⁰⁾`. The front's
later dooms serve only the counts; `finalLaw_of`'s `hExt` needs only the prefix of length 3.

* **`StmtN fin`** (a node): `truthZN` (Z), `truthS1N` (S), `truthLr`, `truthE fin` and `PubOK`.
  A leaf's statement is a parameter `SL` (its chain truths are not yet stated on the log; see
  the RESULT). **`Stmt fin SL`** picks by the kind.
* **`ExtIface S vk W₀ c₀ St`** (the named target of S-E's node assembly and S-H2l's extractor):
  on an accepted run whose chain has passed Pf, if the level-0 word is close, the statement holds
  on `f⁽⁰⁾` and Ligerito's output facts hold, the extractor returns a witness.
* **`hExt_of_iface`**: `ExtIface` gives `finalLaw_of`'s `hExt` for every front whose `DF 2` is
  `far₀ ∨ ¬ St` with `St` reading before 3.
-/

namespace FR.Snd
open RecursionFast FR.Merkle Finset

set_option linter.constructorNameAsVariable false

/-! ## The statement on `f⁽⁰⁾` -/

/-- **A node's statement on the decoded `f⁽⁰⁾`**: Z, S, Lr, E and the public cells. -/
def StmtN (fin : Finals) (κ : Kind) (L es : Log) : Prop :=
  truthZN κ L es ∧ truthS1N κ L es ∧ truthLr κ L es ∧ truthE fin κ L es ∧ PubOK κ L es

/-- **The statement** by kind: a node's `StmtN`, a leaf's `SL`. -/
def Stmt (fin : Finals) (SL : Kind → Log → Log → Prop) (L es : Log) : Prop :=
  if (kindOf es).isNode then StmtN fin (kindOf es) L es else SL (kindOf es) L es

section Reads
variable {L es L' es' : Log} {p : ℕ}

theorem zW_same (h : Same L es L' es' p) (hp : 3 ≤ p) (κ : Kind) : zW κ L es = zW κ L' es' := by
  funext b; simp only [zW, fF_same h hp κ]

theorem stmtN_same (h : Same L es L' es' p) (hp : 3 ≤ p) (fin : Finals) (κ : Kind) :
    StmtN fin κ L es ↔ StmtN fin κ L' es' := by
  have hz : zBlk κ L es = zBlk κ L' es' := by funext blk k; simp only [zBlk, zW_same h hp κ]
  have hn : zNode κ L es = zNode κ L' es' := by funext blk q; simp only [zNode, zW_same h hp κ]
  simp only [StmtN, truthZN, truthS1N, truthLr, truthE, hz, hn, fF_same h hp κ,
    pubOK_same h hp κ]

theorem stmt_reads (fin : Finals) {SL : Kind → Log → Log → Prop}
    (hSL : ∀ κ, Reads 3 (SL κ)) : Reads 3 (Stmt fin SL) := fun L es L' es' h1 h2 h => by
  have hk := h.kind (by omega)
  unfold Stmt
  rw [hk]
  split_ifs
  · exact stmtN_same h le_rfl fin _
  · exact hSL _ L es L' es' h1 h2 h

end Reads

/-! ## The interface -/

/-- **The extractor's interface** (`ExtIface`): on an accepted run (`runLog`), whose chain `j`
has passed Pf's last round, a close level-0 word, the statement `St` on `f⁽⁰⁾` and Ligerito's
output facts give a witness. -/
def ExtIface (S : Submission) (vk : Digest) (W₀ : Log → Log → ℕ → K) (c₀ : Log → Log → K)
    (St : Log → Log → Prop) : Prop :=
  ∀ L c π j, L.length ≤ logCap → ¬ Bad L → (S.V vk c π).runLog L = some true →
    IsChain L j → pfStart + 14 ≤ (entriesOf L (pathOf L j)).length →
    ¬ farL (kindOf (entriesOf L (pathOf L j))) L (entriesOf L (pathOf L j)) 0 →
    St L (entriesOf L (pathOf L j)) → LigeritoOut W₀ c₀ L (entriesOf L (pathOf L j)) →
    ∃ w, S.E c π L = some w ∧ Rel (S.acc vk) c w

theorem phOf_two : phOf 2 = 2 := by
  have hph : ∀ q, phOf q = (fsStarts.filter (· ≤ q)).length - 1 := fun _ => rfl
  rw [hph, fsStarts_eq]; rfl

/-- **`hExt` from the interface**: with `DF 2 = far₀ ∨ ¬ St` and `St` reading before 3, the
prefix of length 3 of an undoomed accepted chain carries `St` to the whole chain. -/
theorem hExt_of_iface {S : Submission} {vk : Digest} {W₀ : Log → Log → ℕ → K}
    {c₀ : Log → Log → K} {St : Log → Log → Prop} {RejF : Log → Log → Prop}
    {DF : ℕ → Log → Log → Prop} (hI : ExtIface S vk W₀ c₀ St) (hSt : Reads 3 St)
    (hD2 : DF 2 = fun L es => farL (kindOf es) L es 0 ∨ ¬ St L es) :
    ∀ L c π j, L.length ≤ logCap → ¬ Bad L → (S.V vk c π).runLog L = some true →
      AcceptTail RejF W₀ c₀ L j →
      (∀ p < (entriesOf L (pathOf L j)).length,
        ¬ DC (RejC RejF c₀) (Dp (DkC DF W₀ c₀)) L ((entriesOf L (pathOf L j)).take (p + 1))) →
      LigeritoOut W₀ c₀ L (entriesOf L (pathOf L j)) →
      ∃ w, S.E c π L = some w ∧ Rel (S.acc vk) c w := by
  intro L c π j hl hb hrun hT hnd hLig
  have hlen := hT.len
  have hpf : 3 ≤ pfStart := by rw [pfStart_eq]; norm_num
  generalize hes : entriesOf L (pathOf L j) = es at hlen hnd hLig ⊢
  have h3 : (es.take 3).length = 3 := by simp; omega
  have hn := hnd 2 (by omega)
  simp only [DC, DPos, Dp, not_or, h3, show 3 - 1 = 2 from rfl, phOf_two,
    DkC_lt (show 2 < 26 by norm_num), hD2, not_not] at hn
  have hS : Same L es L (es.take 3) 3 := by
    have := same_append L (es.take 3) (es.drop 3)
    rwa [List.take_append_drop, h3] at this
  have hst : St L es := (hSt L es L (es.take 3) (by omega) (by omega) hS).mpr hn.2.2
  subst hes
  exact hI L c π j hl hb hrun hT.chain hlen (hLig.close 0 (by norm_num)) hst hLig

/-! ## Controls -/

/-- Control (positive): the interface with a false statement holds vacuously in `St`, i.e. it
only asks for a witness where `St` holds. -/
theorem extIface_false (S : Submission) (vk : Digest) (W₀ : Log → Log → ℕ → K)
    (c₀ : Log → Log → K) : ExtIface S vk W₀ c₀ fun _ _ => False :=
  fun _ _ _ _ _ _ _ _ _ _ h _ => h.elim

/-- Control (negative, non-vacuous): `Stmt` on a leaf is the leaf part, so a false leaf part
makes a leaf's statement false whatever the node part. -/
theorem not_stmt_leaf (fin : Finals) {L es : Log} (hk : kindOf es = .P30) :
    ¬ Stmt fin (fun _ _ _ => False) L es := by
  unfold Stmt; rw [hk]; simp [Kind.isNode]

/-- Control: on a node, `Stmt` is `StmtN` (the leaf part is ignored). -/
theorem stmt_node (fin : Finals) (SL : Kind → Log → Log → Prop) {L es : Log}
    (hk : (kindOf es).isNode = true) : Stmt fin SL L es ↔ StmtN fin (kindOf es) L es := by
  unfold Stmt; rw [if_pos hk]

end FR.Snd
