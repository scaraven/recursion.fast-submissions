/-
# Query bounds along every answer path (new in v4)

v3 bounded the verifier's queries under an oracle **function** (`(p.queries H).length`, the form
the contract's `KS` asks for). v4 runs a verifier on a signed **trace** (`OProg.runSeq`), whose
answers need not come from a function: a trace may answer one query twice, differently. The bound
that covers traces is `AtMost n p`: along every path of answers, `p` asks at most `n` queries.

* `AtMost.runSeq_length`: a trace on which `p` returns has at most `n` entries (exact
  consumption, V4-A3). This is how the entry shows that every child a node witness carries has a
  trace shorter than `2^64` entries, so that the witness fits the output format and its honest
  encoding decodes back (completeness of the node branch).
* `AtMost.queries_length`: the oracle-function bound of `KS` follows.
* The algebra: `ret`, `ask`, `bind`, `map`, `ite`, `mapM` over lists, `mono`.
-/
import SpartanSromOracle

namespace SpartanSrom
open RecursionFast

namespace OProg
variable {α β : Type}

/-- **`p` asks at most `n` queries along every path of answers.** -/
def AtMost : ℕ → OProg α → Prop
  | _, .ret _ => True
  | 0, .query _ _ => False
  | n + 1, .query _ k => ∀ a, AtMost n (k a)

@[simp] theorem atMost_ret (n : ℕ) (a : α) : AtMost n (OProg.ret a) := by
  cases n <;> trivial

@[simp] theorem atMost_pure (n : ℕ) (a : α) : AtMost n (pure a : OProg α) := atMost_ret n a

theorem atMost_query {n : ℕ} {q : ByteArray} {k : Digest → OProg α}
    (h : ∀ a, AtMost n (k a)) : AtMost (n + 1) (OProg.query q k) := h

theorem AtMost.mono : ∀ {m n : ℕ} {p : OProg α}, m ≤ n → AtMost m p → AtMost n p
  | _, _, .ret _, _, _ => atMost_ret _ _
  | 0, _, .query _ _, _, h => h.elim
  | _ + 1, 0, .query _ _, hmn, _ => absurd hmn (by omega)
  | m + 1, n + 1, .query _ k, hmn, h => fun a => AtMost.mono (by omega) (h a)

theorem atMost_ask (q : ByteArray) : AtMost 1 (ask q) := fun _ => trivial

theorem AtMost.bind : ∀ {m n : ℕ} {p : OProg α} {f : α → OProg β}, AtMost m p →
    (∀ x, AtMost n (f x)) → AtMost (m + n) (p >>= f)
  | m, n, .ret a, f, _, hf => (hf a).mono (by omega)
  | 0, _, .query _ _, _, h, _ => h.elim
  | m + 1, n, .query q k, f, h, hf => by
    rw [query_bind, show m + 1 + n = (m + n) + 1 by omega]
    exact fun a => AtMost.bind (h a) hf

theorem AtMost.map {n : ℕ} {p : OProg α} (h : AtMost n p) (f : α → β) : AtMost n (f <$> p) := by
  rw [← bind_pure_comp]
  exact (h.bind (n := 0) fun _ => atMost_pure 0 _).mono (by omega)

theorem AtMost.ite {n : ℕ} {c : Prop} [Decidable c] {p q : OProg α} (hp : AtMost n p)
    (hq : AtMost n q) : AtMost n (if c then p else q) := by
  split_ifs <;> assumption

theorem atMost_mapM {n : ℕ} (f : α → OProg β) :
    ∀ (xs : List α), (∀ x ∈ xs, AtMost n (f x)) → AtMost (xs.length * n) (xs.mapM f)
  | [], _ => atMost_pure _ _
  | x :: xs, h => by
    rw [List.mapM_cons, List.length_cons, show (xs.length + 1) * n = n + (xs.length * n + 0) by
      ring]
    exact (h x (List.mem_cons_self ..)).bind fun y =>
      (atMost_mapM f xs (fun z hz => h z (List.mem_cons_of_mem _ hz))).bind fun _ =>
        atMost_pure 0 _

/-- **A trace on which a program returns has at most `n` entries**, if the program asks at most
`n` queries along every path (the trace is used up exactly, V4-A3). -/
theorem AtMost.runSeq_length : ∀ {n : ℕ} {p : OProg α} {tr : Trace} {b : α},
    AtMost n p → p.runSeq tr = some b → tr.length ≤ n
  | _, .ret _, [], _, _, _ => Nat.zero_le _
  | _, .ret _, _ :: _, _, _, h => nomatch h
  | _, .query _ _, [], _, _, h => nomatch h
  | 0, .query _ _, _ :: _, _, h, _ => h.elim
  | n + 1, .query q k, (q', a) :: tr, b, h, hr => by
    simp only [RecursionFast.OProg.runSeq] at hr
    split at hr
    · exact Nat.succ_le_succ (AtMost.runSeq_length (h a) hr)
    · cases hr

/-- **The oracle-function bound follows**: under every oracle, at most `n` queries. -/
theorem AtMost.queries_length : ∀ {n : ℕ} {p : OProg α} (H : ByteArray → Digest),
    AtMost n p → (p.queries H).length ≤ n
  | _, .ret _, _, _ => Nat.zero_le _
  | 0, .query _ _, _, h => h.elim
  | n + 1, .query q k, H, h => by
    simp only [RecursionFast.OProg.queries, List.length_cons]
    exact Nat.succ_le_succ (AtMost.queries_length H (h (H q)))

end OProg

end SpartanSrom
