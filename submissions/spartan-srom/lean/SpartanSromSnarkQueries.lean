/-
# The leaf SNARK's query bound along every answer path (new in v4)

v3's L-Q1 (`Leaf.queries_le`, `Leaf.len_snarkProg`) bounds the SNARK verifier's queries under an
oracle function. Here the same bound, `qBound (kap n)`, is proved along every path of answers
(`OProg.AtMost`, `SpartanSromQueries`), component by component as v3's `len_*` lemmas count them:
the transcript operations, the Merkle path check, Ligero's two phases and the algebraic layer.
`atMost_snarkProg` is what the v4 verifier's query bound and the trace-length bound of an accepted
child rest on.
-/
import SpartanSromVerifier
import SpartanSromQueries

namespace SpartanSrom
open RecursionFast Transcript PCS OProg

/-! ## The transcript -/

theorem atMost_seed (s : Digest) (n : ℕ) (h : Digest) : AtMost 1 (seed s n h) := atMost_ask _

theorem atMost_absorb (st : Digest) (k : UInt8) (m : ByteArray) : AtMost 1 (absorb st k m) :=
  atMost_ask _

theorem atMost_squeeze (st : Digest) : AtMost 1 (squeeze st) := atMost_ask _

theorem atMost_squeezeN : ∀ (st : Digest) (k : ℕ), AtMost k (squeezeN st k)
  | _, 0 => atMost_pure _ _
  | st, k + 1 => by
    rw [squeezeN]
    exact ((atMost_squeeze st).bind fun a => (atMost_squeezeN a k).bind (n := 0) fun _ =>
      atMost_pure 0 _).mono (by omega)

theorem atMost_squeezeE (st : Digest) (k : ℕ) : AtMost k (squeezeE st k) :=
  ((atMost_squeezeN st k).bind (n := 0) fun _ => atMost_pure 0 _).mono (by omega)

theorem atMost_squeezeIdx (st : Digest) (ℓ t : ℕ) : AtMost (nAns ℓ t) (squeezeIdx st ℓ t) :=
  ((atMost_squeezeN st _).bind (n := 0) fun _ => atMost_pure 0 _).mono (by omega)

/-! ## The Merkle path check -/

theorem atMost_hashL (q : ByteArray) : AtMost 1 (Merkle.hashL q) := (atMost_ask q).map _

theorem atMost_climb : ∀ (cur : Label) (c : ℕ) (ss : List Label),
    AtMost ss.length (Merkle.climb cur c ss)
  | _, _, [] => atMost_pure _ _
  | cur, c, s :: ss => by
    rw [Merkle.climb]
    exact ((atMost_hashL _).bind fun nxt => atMost_climb nxt (c / 2) ss).mono
      (by simp; omega)

theorem atMost_mverify (root : Label) (c : ℕ) (col : ByteArray) (ss : List Label) :
    AtMost (1 + ss.length) (Merkle.verify root c col ss) := by
  rw [Merkle.verify]
  exact ((atMost_hashL _).bind fun lf => (atMost_climb lf c ss).bind (n := 0) fun _ =>
    atMost_pure 0 _).mono (by omega)

/-! ## Ligero -/

theorem atMost_verify1 (κ : ℕ) (st : Digest) (a b : ByteArray) :
    AtMost (2 + rows κ) (Ligero.verify1 κ st a b) := by
  simp only [Ligero.verify1, Ligero.rootAndCoeffs, LawfulMonad.bind_assoc]
  exact ((atMost_absorb _ _ _).bind fun st => (atMost_squeezeE st (rows κ)).bind fun p =>
    (atMost_absorb _ _ _).bind (n := 0) fun _ => atMost_pure 0 _).mono (by omega)

theorem atMost_openOne (κ : ℕ) (ks : Array F) (root : Label) (r a ubar v : Array EF)
    (b : ByteArray) (o c : ℕ) : AtMost (1 + lN κ) (Ligero.openOne κ ks root r a ubar v b o c) := by
  rw [Ligero.openOne]
  have hl : (Ligero.readPath κ b o).length = lN κ := by simp [Ligero.readPath]
  exact ((atMost_mverify _ _ _ _).bind (n := 0) fun _ => atMost_pure 0 _).mono (by omega)

theorem atMost_verify2 (κ : ℕ) (st : Digest) (root : Label) (r a ubar : Array EF)
    (vB opens : ByteArray) :
    AtMost (1 + nAns (lN κ) tQ + tQ * (1 + lN κ)) (Ligero.verify2 κ st root r a ubar vB opens) := by
  rw [Ligero.verify2]
  refine ((atMost_absorb _ _ _).bind fun st => (atMost_squeezeIdx st _ _).bind fun p =>
    (atMost_mapM _ _ fun j _ => atMost_openOne κ _ root r a ubar _ opens _ _).bind (n := 0)
      fun _ => atMost_pure 0 _).mono ?_
  simp only [List.length_range]; omega

/-! ## The algebraic layer -/

theorem atMost_absorbRounds (kind : UInt8) :
    ∀ (st : Digest) (gs : List (Array EF)),
      AtMost (2 * gs.length) (Spartan.absorbRounds kind st gs)
  | _, [] => atMost_pure _ _
  | st, g :: gs => by
    rw [Spartan.absorbRounds]
    exact ((atMost_absorb _ _ _).bind fun st => (atMost_squeeze st).bind fun a =>
      (atMost_absorbRounds kind a gs).bind (n := 0) fun _ => atMost_pure 0 _).mono
        (by simp; omega)

theorem atMost_spartan (κ : ℕ) (ev : Spartan.Evals) (m : Spartan.Msgs) (st : Digest) :
    AtMost (Spartan.ly κ + 2 * m.outer.length + 2 + 2 * m.inner.length + 7 + 2 * m.ring.length)
      (Spartan.verify κ ev m st) := by
  rw [Spartan.verify]
  refine ((atMost_squeezeE _ _).bind fun p₁ => (atMost_absorbRounds _ _ _).bind fun p₂ =>
    (atMost_absorb _ _ _).bind fun st₃ => (atMost_squeeze _).bind fun a =>
    (atMost_absorbRounds _ _ _).bind fun p₄ => (atMost_absorb _ _ _).bind fun st₅ =>
    (atMost_squeezeE _ 6).bind fun p₆ => (atMost_absorbRounds _ _ _).bind (n := 0) fun _ =>
    atMost_pure 0 _).mono ?_
  omega

theorem atMost_spartan_parse (κ : ℕ) (ev : Spartan.Evals) (π : ByteArray) (o : ℕ)
    (st : Digest) :
    AtMost (5 * Spartan.ly κ + 9 + 2 * Spartan.lq κ)
      (Spartan.verify κ ev (Spartan.parseMsgs κ π o) st) := by
  refine (atMost_spartan κ ev _ st).mono ?_
  simp only [Spartan.parseMsgs, Spartan.split, Leaf.chunks_length]
  omega

/-! ## The SNARK verifier -/

/-- **L-Q1 along every path**: the SNARK verifier of a leaf with `n` steps asks at most
`qBound (kap n)` queries, whatever the answers and the proof. -/
theorem atMost_snarkProg (ev : Leaf.EvalsFor) (s : Digest) (n : ℕ) (h : Digest) (π : ByteArray) :
    AtMost (Leaf.qBound (Leaf.kap n)) (Leaf.snarkProg ev s n h π) := by
  rw [Leaf.snarkProg]
  refine ((atMost_seed s n h).bind fun st => (atMost_verify1 _ st _ _).bind fun p =>
    (atMost_spartan_parse _ _ π _ _).bind
      (n := 1 + nAns (lN (Leaf.kap n)) tQ + tQ * (1 + lN (Leaf.kap n))) fun res => ?_).mono ?_
  · rcases res with _ | ⟨st', pc⟩
    · exact atMost_pure _ _
    · simp only [Leaf.tail]
      exact AtMost.ite (atMost_verify2 _ _ _ _ _ _ _ _) (atMost_pure _ _)
  · simp only [Leaf.qBound]; omega

end SpartanSrom
