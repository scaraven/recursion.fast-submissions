-- Follows `submissions/spartan-srom/lean/SpartanSromMerkle.lean` (this repository,
-- `v4/flock-recursive` at `783328c`: `pre`, `colL`, `Collision`, `Hit`, `pre_of_mem`,
-- `open_binding_aux`, `colL_append`, `pre_none_append`, `colL_prefix`), re-stated for full 32-byte
-- digests, caps, and query encodings taken as a parameter (S-0 fixes them).
import RecursionFast.Contract.Oracle

/-!
# Merkle trees with caps, read off a query log (BLUEPRINT §5.4 step 1, Appendix A.2)

A level's commitment is a binary tree over its `2^depth` positions: the leaf of position `j` is
the answer to the **column query** of its column, a node is the answer to the **node query** of
its two children; the **cap** is the `2^cap` digests at height `h = depth − cap`, absorbed into the
transcript. The query byte layouts (tags `"FRMNOD" ‖ i ‖ 0`, `"FRMCOL" ‖ i ‖ 0`) are S-0's
(`FRTranscriptDefs`); this module takes them as a parameter `MerkleEnc` with the parsing laws it
needs, so it does not depend on S-0.

* The verifier's path (`climb`, `openPath`): the column query, then `h` node queries, the child
  order chosen by bit `t` of the position at height `t`; the result is compared with the cap
  entry `cap[j / 2^h]`. That `gen`'s `askCol`/`askNode`/`selectHalf` ops (A.5) run this program
  is `FRVIR`'s obligation (`runSeq_eq_runIR`), not proved here. `pre L d` searches the whole log:
  a first preimage of another level or kind parses to `none` (an erasure), never to a wrong
  column, since S-0's `parseNode i`/`parseCol i` check the level byte.
* The log side: `pre L d` (the first entry answering `d`), `colL L d h j` (the column of
  position `j` under `d` at height `h`, read top-down from first preimages), `Collision`
  (two different queries with one answer) and `Hit` (an answer carried in an earlier input).
* **`cap_binding`**: on a log without collisions, a column whose path verifies to `d` is the
  column read off the log under `d` (`colL`). **`colL_prefix`**: under no hit, a column read
  under a digest carried in an input of a prefix (the cap's absorb) is read off that prefix; with
  `colL_append`, the committed columns are fixed when the cap is absorbed.
-/

namespace FR.Merkle

open RecursionFast

/-- The query encodings of one Merkle tree and the laws this module uses (S-0 instantiates it
from Appendix A.2). `carried q` lists the digests that the input `q` carries (the in-play
windows of BLUEPRINT §5.1 contain them). -/
structure MerkleEnc where
  /-- The node query of two child digests. -/
  nodeQ : Digest → Digest → ByteArray
  /-- The column (leaf) query of a column's bytes. -/
  colQ : ByteArray → ByteArray
  /-- Parse a node query. -/
  parseNode : ByteArray → Option (Digest × Digest)
  /-- Parse a column query (and check its width). -/
  parseCol : ByteArray → Option ByteArray
  /-- The digests an input carries. -/
  carried : ByteArray → List Digest
  parseNode_nodeQ : ∀ a b, parseNode (nodeQ a b) = some (a, b)
  nodeQ_of_parseNode : ∀ q a b, parseNode q = some (a, b) → q = nodeQ a b
  parseCol_colQ : ∀ c, parseCol (colQ c) = some c
  carried_nodeQ : ∀ a b, a ∈ carried (nodeQ a b) ∧ b ∈ carried (nodeQ a b)

variable (E : MerkleEnc)

/-! ## The verifier's path -/

/-- The node query at height `t` of position `j`: the running digest is the right child iff
bit `t` of `j` is set. -/
def stepQ (j t : ℕ) (cur sib : Digest) : ByteArray :=
  if j.testBit t then E.nodeQ sib cur else E.nodeQ cur sib

/-- Climb from `cur` at height `t` with the siblings `ss` (bottom-up). -/
def climb (j : ℕ) : ℕ → Digest → List Digest → OProg Digest
  | _, cur, [] => .ret cur
  | t, cur, s :: ss => .query (stepQ E j t cur s) fun d => climb j (t + 1) d ss

/-- **The path of position `j`**: the column query, then one node query per sibling; the result
is to be compared with the cap entry `cap[j / 2^(ss.length)]`. -/
def openPath (col : ByteArray) (j : ℕ) (ss : List Digest) : OProg Digest :=
  .query (E.colQ col) fun d => climb E j 0 d ss

/-! ## The log side -/

/-- `pre L d`: the first entry of `L` whose answer is `d`. -/
def pre (L : Log) (d : Digest) : Option (ByteArray × Digest) := L.find? fun e => e.2 = d

/-- **`colL`**: the column of position `j` in the subtree of height `h` under `d`, read off `L`
top-down by first preimages (at height `t + 1` bit `t` of `j` picks the child); `none` if a query
on the way is missing or of the wrong shape. -/
def colL (L : Log) : Digest → ℕ → ℕ → Option ByteArray
  | d, 0, _ => (pre L d).bind fun e => E.parseCol e.1
  | d, h + 1, j => (pre L d).bind fun e => (E.parseNode e.1).bind fun ab =>
      colL L (if j.testBit h then ab.2 else ab.1) h j

/-- *Collision*: two entries with different queries and the same answer. -/
def Collision (L : Log) : Prop := ∃ e₁ ∈ L, ∃ e₂ ∈ L, e₁.1 ≠ e₂.1 ∧ e₁.2 = e₂.2

/-- *Hit*: an entry whose answer is carried in the input of an earlier entry. -/
def Hit (L : Log) : Prop :=
  ∃ i j : ℕ, ∃ (hij : i < j) (hj : j < L.length), L[j].2 ∈ E.carried (L[i]'(Nat.lt_trans hij hj)).1

variable {E}

/-- Under no collision, the first entry answering the answer of `e ∈ L` has `e`'s query. -/
theorem pre_of_mem {L : Log} (hc : ¬ Collision L) {e : ByteArray × Digest} (he : e ∈ L) :
    ∃ e', pre L e.2 = some e' ∧ e' ∈ L ∧ e'.1 = e.1 := by
  obtain ⟨e', he'⟩ := Option.isSome_iff_exists.mp
    (List.find?_isSome.mpr ⟨e, he, by simp⟩ : (pre L e.2).isSome)
  have hm := List.mem_of_find?_eq_some he'
  have ht : e'.2 = e.2 := by simpa using List.find?_some he'
  refine ⟨e', he', hm, ?_⟩
  by_contra hne
  exact hc ⟨e', hm, e, he, hne, ht⟩

/-- `runLog` of a query: the first entry for the query exists and the continuation runs on its
answer. -/
theorem runLog_query {α : Type} {L : Log} {q : ByteArray} {k : Digest → OProg α} {a : α}
    (h : (OProg.query q k).runLog L = some a) :
    ∃ e ∈ L, e.1 = q ∧ (k e.2).runLog L = some a := by
  simp only [OProg.runLog, Option.bind_eq_some_iff] at h
  obtain ⟨e, he, hk⟩ := h
  exact ⟨e, List.mem_of_find?_eq_some he, by simpa using List.find?_some he, hk⟩

theorem cap_binding_aux {L : Log} (hc : ¬ Collision L) {col : ByteArray} {j : ℕ} :
    ∀ (ss : List Digest) (t : ℕ) (cur d : Digest), colL E L cur t j = some col →
      (climb E j t cur ss).runLog L = some d → colL E L d (t + ss.length) j = some col := by
  intro ss
  induction ss with
  | nil =>
    intro t cur d hcol h
    simp only [climb, OProg.runLog, Option.some.injEq] at h
    subst h; simpa using hcol
  | cons s ss ih =>
    intro t cur d hcol h
    obtain ⟨e, he, hq, hk⟩ := runLog_query h
    rw [List.length_cons, show t + (ss.length + 1) = t + 1 + ss.length by omega]
    refine ih (t + 1) e.2 d ?_ hk
    obtain ⟨e', hpre, -, he'⟩ := pre_of_mem hc he
    simp only [colL, hpre, Option.bind_some, he', hq, stepQ]
    by_cases hb : j.testBit t = true <;> simp [E.parseNode_nodeQ, hb, hcol]

/-- **`cap_binding`** (BLUEPRINT §5.4 step 1): on a log without collisions, if the path of
position `j` from column `col` with siblings `ss` evaluates to `d` on the log, then `col` is the
column of position `j` read off the log under `d` at height `|ss|`. -/
theorem cap_binding {L : Log} (hc : ¬ Collision L) {col : ByteArray} {j : ℕ} {ss : List Digest}
    {d : Digest} (h : (openPath E col j ss).runLog L = some d) :
    colL E L d ss.length j = some col := by
  obtain ⟨e, he, hq, hk⟩ := runLog_query h
  have h0 : colL E L e.2 0 j = some col := by
    obtain ⟨e', hpre, -, he'⟩ := pre_of_mem hc he
    simp [colL, hpre, he', hq, E.parseCol_colQ]
  simpa using cap_binding_aux hc ss 0 e.2 d h0 hk

/-! ## Reading on a prefix: the columns are fixed when the cap is absorbed -/

theorem pre_append {L : Log} {d : Digest} {e : ByteArray × Digest} (L' : Log)
    (h : pre L d = some e) : pre (L ++ L') d = some e := by
  simp only [pre, List.find?_append] at h ⊢; rw [h]; rfl

/-- **`colL_append`**: a column read off a log is read off every extension of it. -/
theorem colL_append {L : Log} (L' : Log) :
    ∀ {d : Digest} {h j : ℕ} {col : ByteArray},
      colL E L d h j = some col → colL E (L ++ L') d h j = some col := by
  intro d h
  induction h generalizing d with
  | zero =>
    intro j col hc
    simp only [colL, Option.bind_eq_some_iff] at hc ⊢
    exact hc.imp fun e h => ⟨pre_append L' h.1, h.2⟩
  | succ h ih =>
    intro j col hc
    simp only [colL, Option.bind_eq_some_iff] at hc ⊢
    exact hc.imp fun e h => ⟨pre_append L' h.1, h.2.imp fun ab h' => ⟨h'.1, ih h'.2⟩⟩

/-- A digest carried in an input of `L` and answered by no entry of `L` is answered by no entry of
an extension without a hit. -/
theorem pre_none_append {L L' : Log} (hb : ¬ Hit E (L ++ L')) {d : Digest}
    (hin : ∃ e ∈ L, d ∈ E.carried e.1) (h : pre L d = none) : pre (L ++ L') d = none := by
  simp only [pre, List.find?_append] at h ⊢
  rw [h, Option.none_or, List.find?_eq_none]
  intro e he hd
  obtain ⟨e₀, he₀, hl⟩ := hin
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem he₀
  obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem he
  apply hb
  refine ⟨i, L.length + j, by omega, by rw [List.length_append]; omega, ?_⟩
  rw [List.getElem_append_right (Nat.le_add_right _ _), List.getElem_append_left hi]
  simp only [Nat.add_sub_cancel_left]
  rw [of_decide_eq_true hd]
  exact hl

/-- Under no hit, `L ++ L'` and `L` have the same first entry answering a digest carried in an input
of `L`. -/
private theorem pre_append_eq {L L' : Log} (hb : ¬ Hit E (L ++ L')) {d : Digest}
    (hin : ∃ e ∈ L, d ∈ E.carried e.1) : pre (L ++ L') d = pre L d := by
  cases hp : pre L d with
  | none => exact pre_none_append hb hin hp
  | some e => exact pre_append L' hp

/-- **`colL_prefix`**: under no hit, a column read off `L ++ L'` under a digest carried in an
input of `L` (the cap entry, carried by the cap's absorb) is already read off `L`. -/
theorem colL_prefix {L L' : Log} (hb : ¬ Hit E (L ++ L')) :
    ∀ {h : ℕ} {d : Digest} {j : ℕ} {col : ByteArray}, (∃ e ∈ L, d ∈ E.carried e.1) →
      colL E (L ++ L') d h j = some col → colL E L d h j = some col := by
  intro h
  induction h with
  | zero =>
    intro d j col hin hc
    simpa only [colL, pre_append_eq hb hin] using hc
  | succ h ih =>
    intro d j col hin hc
    simp only [colL, pre_append_eq hb hin, Option.bind_eq_some_iff] at hc ⊢
    obtain ⟨e, hp, ab, hn, hc⟩ := hc
    refine ⟨e, hp, ab, hn, ih ⟨e, List.mem_of_find?_eq_some hp, ?_⟩ hc⟩
    have hl : ab.1 ∈ E.carried e.1 ∧ ab.2 ∈ E.carried e.1 := by
      rw [E.nodeQ_of_parseNode e.1 ab.1 ab.2 hn]
      exact E.carried_nodeQ _ _
    by_cases hb : j.testBit h = true <;> simp [hb, hl]

/-- Collisions are kept by appending. -/
theorem collision_append {L : Log} (L' : Log) (h : Collision L) : Collision (L ++ L') := by
  obtain ⟨e₁, h₁, e₂, h₂, hne, ht⟩ := h
  exact ⟨e₁, by simp [h₁], e₂, by simp [h₂], hne, ht⟩

/-- Hits are kept by appending. -/
theorem hit_append {L : Log} (L' : Log) (h : Hit E L) : Hit E (L ++ L') := by
  obtain ⟨i, j, hij, hj, hm⟩ := h
  refine ⟨i, j, hij, by simp; omega, ?_⟩
  rwa [List.getElem_append_left hj, List.getElem_append_left (Nat.lt_trans hij hj)]

/-! ## Controls: a toy encoding (the laws are satisfiable) and the collision hypothesis -/

section Controls

/-- Toy node query `0x01 ‖ a ‖ b` (not the protocol's; S-0 fixes that one). -/
def toyNodeQ (a b : Digest) : ByteArray := ⟨#[1] ++ a.toArray ++ b.toArray⟩

/-- Toy column query `0x00 ‖ col`. -/
def toyColQ (c : ByteArray) : ByteArray := ⟨#[0] ++ c.data⟩

theorem toyNodeQ_data (a b : Digest) :
    (toyNodeQ a b).data.toList = 1 :: (a.toList ++ b.toList) := by
  simp [toyNodeQ, Vector.toList]

theorem toyColQ_data (c : ByteArray) : (toyColQ c).data.toList = 0 :: c.data.toList := by
  simp [toyColQ]

/-- Parse a toy node query. -/
def toyParseNode (q : ByteArray) : Option (Digest × Digest) :=
  match q.data.toList with
  | 1 :: rest =>
    if h : rest.length = 64 then
      some (⟨(rest.take 32).toArray, by simp [h]⟩, ⟨(rest.drop 32).toArray, by simp [h]⟩)
    else none
  | _ => none

/-- Parse a toy column query. -/
def toyParseCol (q : ByteArray) : Option ByteArray :=
  match q.data.toList with
  | 0 :: rest => some ⟨rest.toArray⟩
  | _ => none

private theorem toyParseNode_nodeQ (a b : Digest) : toyParseNode (toyNodeQ a b) = some (a, b) := by
  have ha : a.toList.length = 32 := by simp
  simp only [toyParseNode, toyNodeQ_data, List.length_append, ha, Vector.length_toList,
    dite_true, List.take_left' ha, List.drop_left' ha, Option.some.injEq, Prod.mk.injEq]
  exact ⟨Vector.ext fun i hi => by simp [Vector.toList], Vector.ext fun i hi => by
    simp [Vector.toList]⟩

theorem byteArray_ext_toList {a b : ByteArray} (h : a.data.toList = b.data.toList) : a = b :=
  ByteArray.ext (Array.ext' h)

/-- The toy encoding: a `MerkleEnc` exists (its laws are not contradictory). -/
def toyEnc : MerkleEnc where
  nodeQ := toyNodeQ
  colQ := toyColQ
  parseNode := toyParseNode
  parseCol := toyParseCol
  carried q := match toyParseNode q with
    | some (a, b) => [a, b]
    | none => []
  parseNode_nodeQ := toyParseNode_nodeQ
  nodeQ_of_parseNode q a b h := by
    unfold toyParseNode at h
    split at h
    · rename_i rest hq
      split at h
      · obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
        apply byteArray_ext_toList
        rw [hq, toyNodeQ_data]
        simp [Vector.toList]
      · cases h
    · cases h
  parseCol_colQ c := by
    simp only [toyParseCol, toyColQ_data]
  carried_nodeQ a b := by simp [toyParseNode_nodeQ]

/-- A constant digest. -/
def dg (b : UInt8) : Digest := Vector.replicate 32 b

/-- Two toy columns. -/
def toyCol : ByteArray := ⟨#[7, 7]⟩
def toyCol' : ByteArray := ⟨#[8]⟩

/-- A consistent log of one path of height 1: the column query of `toyCol` answered `dg 0`, the
node query `(dg 0, dg 2)` answered `dg 1`. -/
def toyLog : Log := [(toyColQ toyCol, dg 0), (toyNodeQ (dg 0) (dg 2), dg 1)]

theorem toy_path : (openPath toyEnc toyCol 0 [dg 2]).runLog toyLog = some (dg 1) := by
  decide +kernel

theorem toy_noCollision : ¬ Collision toyLog := by
  unfold Collision; decide +kernel

/-- **Positive control of `cap_binding`**: its hypotheses hold on a toy log, and it reads the
column under the path's top digest. -/
theorem cap_binding_toy : colL toyEnc toyLog (dg 1) 1 0 = some toyCol :=
  cap_binding (ss := [dg 2]) toy_noCollision toy_path

/-- A log with a collision: two column queries with the answer `dg 0`. -/
def collLog : Log := [(toyColQ toyCol, dg 0), (toyColQ toyCol', dg 0)]

/-- **Negative control of `cap_binding`** (the collision hypothesis is needed): on `collLog` the
path of `toyCol'` evaluates to `dg 0`, but the column read under `dg 0` is `toyCol`. -/
theorem cap_binding_needs_noCollision :
    (openPath toyEnc toyCol' 0 []).runLog collLog = some (dg 0) ∧
      colL toyEnc collLog (dg 0) 0 0 = some toyCol ∧ toyCol ≠ toyCol' := by
  decide +kernel

end Controls

end FR.Merkle
