-- New for lvm2 MP-B cap pruning (CAP-VS, 2026-11-17): an S2GB opening (`openLoopB`: paths to `D`, layer, heap, cap
-- check) on the trace and the compiled verifier's `openAll` on the expanded body (`fillPaths`) on the log. Proof help
-- for `refinesB_of`.
import LvmS2GBFill
import LvmVEqSim
import LvmTypedVEqTop

/-!
# An S2GB opening and the compiled opening on the expanded body

The driver asks its queries on the trace `tr` (`runSeq`), the compiled verifier on the log `L` (`runLog`); every
entry of `tr` is `L`'s answer (`LogCons`). Per position `q` the compiled verifier climbs `D` levels with π's
siblings (the driver's path, `pathsB_simL`), then `m − c` levels with the siblings `wsibs` of the heap (the driver's
heap queries, `heapB_run`): at level `ℓ` the node of `x` is `2^ℓ + x` (`nodeB`, layer nodes `2^m + x`), its query
`node (2k) ‖ node (2k+1)` with `k = 2^(ℓ−1) + x/2`. `openLoopB_sim` puts them together.
-/

set_option autoImplicit false

namespace Lvm.VEq

open RecursionFast Lvm Lvm.FS LeanVM.Parameters LeanVM.Protocol.Compile

/-! ## Logs -/

/-- `L` answers `q` with `a` (its first entry for `q`). -/
def Ans (L : Log) (q : ByteArray) (a : Digest) : Prop :=
  ∃ e, L.find? (fun x ↦ decide (x.1 = q)) = some e ∧ e.2 = a

theorem ans_of_drop {L : Log} {tr : Trace} (hc : LogCons L tr) {i : ℕ} {q : ByteArray} {a : Digest}
    {rest : Trace} (h : tr.drop i = (q, a) :: rest) : Ans L q a :=
  hc (q, a) (List.mem_of_mem_drop (by rw [h]; exact List.mem_cons_self))

theorem runLog_query_ans {α : Type} {L : Log} {q : ByteArray} {a : Digest} (h : Ans L q a)
    (k : Digest → OProg α) : (OProg.query q k).runLog L = (k a).runLog L := by
  obtain ⟨e, he, rfl⟩ := h
  simp only [OProg.runLog, he, Option.bind_some]

theorem runLog_bind {α β : Type} (L : Log) (f : α → OProg β) : ∀ p : OProg α,
    (p.bind f).runLog L = (p.runLog L).bind fun a ↦ (f a).runLog L
  | .ret _ => rfl
  | .query q k => by
    simp only [OProg.bind, OProg.runLog, Option.bind_assoc]
    congr 1; funext e; exact runLog_bind L f (k e.2)

theorem toQ_dd (a b : Digest) : toQ (a.toList ++ b.toList) = digestBytes a ++ digestBytes b :=
  toQ_eq (by rw [blb_append, blb_digestBytes, blb_digestBytes])

/-! ## A climb on the log -/

/-- **A Merkle climb**: the driver's on the trace, the compiled verifier's on the log, the siblings π's. -/
theorem climb_simL (π : ByteArray) (L : Log) (tr : Trace) (hc : LogCons L tr) (q : ℕ) :
    ∀ (j lvl : ℕ) (cur : Digest) (s : DSt) (i : ℕ) (kc : DSt → Digest → OProg Bool),
    (∀ s' d n, (kc s' d).runSeq (tr.drop n) = some true → s'.off ≤ π.size) →
    (climb π q j lvl cur s kc).runSeq (tr.drop i) = some true →
    ∃ s' top n, (kc s' top).runSeq (tr.drop (i + n)) = some true ∧ s'.off = s.off + 32 * j ∧
      s'.st = s.st ∧ s'.pend = s.pend ∧ s'.caps = s.caps ∧ s'.pos = s.pos ∧
      entOff tr (i + n) = entOff tr i + 104 * j ∧
      ∀ body : List UInt8, (Scheme.climb j cur (q >>> lvl) (((blb π).drop s.off).take (32 * j) ++ body)).runLog L =
        some (some (top, body))
  | 0, lvl, cur, s, i, kc, _, h => ⟨s, cur, 0, h, by simp, rfl, rfl, rfl, rfl, by simp, fun body ↦ by
      simp [Scheme.climb, OProg.runLog]⟩
  | j + 1, lvl, cur, s, i, kc, hb, h => by
    rw [climb] at h
    obtain ⟨a, rest, hdrop, h'⟩ := ask_run h
    obtain ⟨s₂, d₂, n₂, h₂, -, ho₂, -⟩ := climb_run π q j (lvl + 1) a _ kc rest h'
    have hle : s.off + 32 * (j + 1) ≤ π.size := by
      have := hb s₂ d₂ (i + 1 + n₂) (by rw [← List.drop_drop, ← List.drop_drop, hdrop]; exact h₂)
      rw [ho₂] at this; simp only [nodeBytes] at this; (clear * - this; omega)
    have h32 : s.off + 32 ≤ π.size := by (clear * - hle; omega)
    have hrest : tr.drop (i + 1) = rest := by rw [← List.drop_drop, hdrop]; rfl
    obtain ⟨s', top, n, h1, h2, h3, h4, h5, h6, h7, h8⟩ := climb_simL π L tr hc q j (lvl + 1) a _ (i + 1) kc
      hb (by rw [hrest]; exact h')
    have e1 : i + (n + 1) = i + 1 + n := by (clear * -; omega)
    refine ⟨s', top, n + 1, by rw [e1]; exact h1, ?_, h3, h4, h5, h6, ?_, ?_⟩
    · rw [h2]; simp only; (clear * -; ring)
    · have hsz : (if (q >>> lvl) % 2 = 0 then digestBytes cur ++ π.extract s.off (s.off + 32)
          else π.extract s.off (s.off + 32) ++ digestBytes cur).size = 64 := by
        split <;> rw [ByteArray.size_append, size_extract_of h32, size_digestBytes]
      have he := (stream_entry hdrop).2.2
      rw [e1, h7, he, hsz]; (clear * -; ring)
    · intro body
      have hT : (((blb π).drop s.off).take 32).length = 32 := take_drop_blb h32
      have hX : ((blb π).drop s.off).take (32 * (j + 1)) ++ body =
          ((blb π).drop s.off).take 32 ++ (((blb π).drop (s.off + 32)).take (32 * j) ++ body) := by
        rw [show 32 * (j + 1) = 32 + 32 * j by ring, List.take_add, List.drop_drop, List.append_assoc]
      have hlen : ¬ (((blb π).drop s.off).take 32 ++ (((blb π).drop (s.off + 32)).take (32 * j) ++ body)).length
          < 32 := by rw [List.length_append, hT]; (clear * -; omega)
      have hq : toQ (if (q >>> lvl) % 2 = 0 then cur.toList ++ ((blb π).drop s.off).take 32
          else ((blb π).drop s.off).take 32 ++ cur.toList) =
          (if (q >>> lvl) % 2 = 0 then digestBytes cur ++ π.extract s.off (s.off + 32)
            else π.extract s.off (s.off + 32) ++ digestBytes cur) := by
        apply toQ_eq
        split <;> simp [blb_append, blb_extract, blb_digestBytes]
      rw [hX, Scheme.climb, if_neg hlen, List.take_left' hT, List.drop_left' hT, hq,
        runLog_query_ans (ans_of_drop hc hdrop)]
      rw [show (q >>> lvl) / 2 = q >>> (lvl + 1) by rw [Nat.shiftRight_succ]]
      exact h8 body

/-! ## The paths -/

/-- **One opened path on the log**: at body offset `o`, the leaf (`lb` bytes, its row `row`) is answered by
`d₀`, and the compiled climb of `D` levels with π's siblings from `d₀` tops at `top`. -/
def PathOK (L : Log) (π : ByteArray) (dec : List UInt8 → K) (lb D wd oc o q : ℕ) (top : Digest)
    (row : List K) : Prop :=
  o + lb + 32 * D ≤ π.size ∧ padRowOf dec wd oc (((blb π).drop o).take lb) = row ∧
    ∃ d₀, Ans L (π.extract o (o + lb)) d₀ ∧ ∀ body : List UInt8,
      (Scheme.climb D d₀ q (((blb π).drop (o + lb)).take (32 * D) ++ body)).runLog L = some (some (top, body))

/-- The opened paths on the log, from body offset `o`. -/
def PathsOK (L : Log) (π : ByteArray) (dec : List UInt8 → K) (lb D wd oc : ℕ) :
    List ℕ → ℕ → List Digest → List (List K) → Prop
  | [], _, [], [] => True
  | q :: qs, o, top :: tops, row :: rows =>
    PathOK L π dec lb D wd oc o q top row ∧ PathsOK L π dec lb D wd oc qs (o + (lb + 32 * D)) tops rows
  | _, _, _, _ => False

/-- **The paths of an opening**: the driver's on the trace; the tops, the stream's rows, the paths on the log. -/
theorem pathsB_simL (π : ByteArray) (L : Log) (tr : Trace) (hc : LogCons L tr) (dec : List UInt8 → K)
    (hdec : dec = kOfBytes) (Lv : Level) (wd oc : ℕ) (hrow : Lv.row = 8 * min oc wd) :
    ∀ (ps : List ℕ) (s : DSt) (acc : List Digest) (i : ℕ) (kp : DSt → List Digest → OProg Bool),
    (∀ s' tops n, (kp s' tops).runSeq (tr.drop n) = some true → s'.off ≤ π.size) →
    (pathsB π Lv ps s acc kp).runSeq (tr.drop i) = some true →
    ∃ s' tops n, (kp s' (acc.reverse ++ tops)).runSeq (tr.drop (i + n)) = some true ∧
      s'.off = s.off + ps.length * (Lv.row + 32 * Lv.path) ∧ s'.st = s.st ∧ s'.pend = s.pend ∧
      s'.caps = s.caps ∧ s'.pos = s.pos ∧ tops.length = ps.length ∧
      (opRows (traceBytesB tr) wd oc Lv.path ps.length (entOff tr i)).2 = entOff tr (i + n) ∧
      PathsOK L π dec Lv.row Lv.path wd oc ps s.off tops
        (opRows (traceBytesB tr) wd oc Lv.path ps.length (entOff tr i)).1 := by
  intro ps
  induction ps with
  | nil =>
    intro s acc i kp _ h
    refine ⟨s, [], 0, by simpa [pathsB] using h, by simp, rfl, rfl, rfl, rfl, rfl, by simp [opRows], ?_⟩
    simp [PathsOK, opRows]
  | cons q qs ih =>
    intro s acc i kp hk h
    obtain ⟨d₀, rest, hdrop, h'⟩ := ask_run h
    have hrest : tr.drop (i + 1) = rest := by rw [← List.drop_drop, hdrop]; rfl
    have hkc : ∀ s' d n, ((fun s top ↦ pathsB π Lv qs s (top :: acc) kp) s' d).runSeq (tr.drop n) = some true →
        s'.off ≤ π.size := by
      intro s' d n hh
      obtain ⟨s'', _, n', h1, h2, _⟩ := ih s' (d :: acc) n kp hk hh
      have := hk s'' _ (n + n') h1
      rw [h2] at this; (clear * - this; omega)
    obtain ⟨s₁, top, n₁, h1, ho1, hst1, hpe1, hca1, hpo1, he1, hcl⟩ :=
      climb_simL π L tr hc q Lv.path 0 d₀ _ (i + 1) _ hkc (by rw [hrest]; exact h')
    have hb1 := hkc _ _ _ h1
    simp only at ho1
    have hoff : s.off + Lv.row ≤ π.size := by rw [ho1] at hb1; (clear * - hb1; omega)
    obtain ⟨s', tops, n, h2, ho2, hst2, hpe2, hca2, hpo2, hl2, he2, hP2⟩ := ih s₁ (top :: acc) (i + 1 + n₁) kp hk h1
    have e1 : i + (n₁ + 1 + n) = i + 1 + n₁ + n := by (clear * -; omega)
    have hsz : (π.extract s.off (s.off + Lv.row)).size = Lv.row := size_extract_of hoff
    have hent : entOff tr (i + 1 + n₁) = entOff tr i + 40 + 8 * min oc wd + 104 * Lv.path := by
      rw [he1, (stream_entry hdrop).2.2, hsz, hrow]; (clear * -; ring)
    refine ⟨s', top :: tops, n₁ + 1 + n, ?_, ?_, by rw [hst2, hst1], by rw [hpe2, hpe1], by rw [hca2, hca1],
      by rw [hpo2, hpo1], by simp [hl2], ?_, ?_⟩
    · rw [e1]; simpa using h2
    · rw [ho2, ho1]; simp only [List.length_cons]; (clear * -; ring)
    · rw [List.length_cons, opRows_succ, e1, ← he2, hent]
    · rw [List.length_cons, opRows_succ]
      refine ⟨⟨by rw [ho1] at hb1; (clear * - hb1; omega), ?_, d₀, ans_of_drop hc hdrop, hcl⟩, ?_⟩
      · have := (stream_entry hdrop).1 0 (8 * min oc wd) (by rw [hsz, hrow]; (clear * -; omega))
        simp only [Nat.add_zero, List.drop_zero] at this
        rw [padAt, ← hdec, this, blb_extract, hrow,
          show s.off + 8 * min oc wd - s.off = 8 * min oc wd by (clear * -; omega), List.take_take, min_self]
      · rw [← hent, show s.off + (Lv.row + 32 * Lv.path) = s₁.off by rw [ho1]; (clear * -; omega)]
        exact hP2

/-! ## The heap -/

theorem nodeB_lt {lay A : Array Digest} {m k : ℕ} (h : k < 2 ^ m) : nodeB lay A m k = A.getD k zeroDigest := by
  rw [nodeB, if_neg (Nat.not_le.mpr h)]

theorem nodeB_lay {lay A : Array Digest} {m x : ℕ} : nodeB lay A m (2 ^ m + x) = lay.getD x zeroDigest := by
  rw [nodeB, if_pos (Nat.le_add_right _ _), Nat.add_sub_cancel_left]

/-- The heap's node query at `k`: `node (2k) ‖ node (2k+1)`. -/
def hqry (lay A : Array Digest) (m k : ℕ) : ByteArray :=
  digestBytes (nodeB lay A m (2 * k)) ++ digestBytes (nodeB lay A m (2 * k + 1))

/-- **The driver's heap on the trace**: `n` node queries from `kk` down; every answer is the log's, and the final
array's entries above `kk` are the initial ones. -/
theorem heapB_run (L : Log) (tr : Trace) (hc : LogCons L tr) (lay : Array Digest) (m : ℕ) :
    ∀ (n kk : ℕ) (A : Array Digest) (s : DSt) (i : ℕ) (kh : DSt → Array Digest → OProg Bool),
    n ≤ kk → kk < A.size →
    (heapB lay m n kk A s kh).runSeq (tr.drop i) = some true →
    ∃ s' A', (kh s' A').runSeq (tr.drop (i + n)) = some true ∧ s'.off = s.off ∧ s'.st = s.st ∧
      s'.pend = s.pend ∧ s'.caps = s.caps ∧ s'.pos = s.pos ∧ entOff tr (i + n) = entOff tr i + 104 * n ∧
      A'.size = A.size ∧ (∀ j, kk < j → A'.getD j zeroDigest = A.getD j zeroDigest) ∧
      ∀ k, kk < k + n → k ≤ kk → Ans L (hqry lay A' m k) (A'.getD k zeroDigest)
  | 0, kk, A, s, i, kh, _, _, h => ⟨s, A, h, rfl, rfl, rfl, rfl, rfl, by simp, rfl, fun _ _ ↦ rfl,
      fun k h1 h2 ↦ absurd h1 (by (clear * - h2; omega))⟩
  | n + 1, kk, A, s, i, kh, hn, hA, h => by
    rw [heapB] at h
    obtain ⟨a, rest, hdrop, h'⟩ := ask_run h
    have hrest : tr.drop (i + 1) = rest := by rw [← List.drop_drop, hdrop]; rfl
    obtain ⟨s', A', h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩ :=
      heapB_run L tr hc lay m n (kk - 1) (A.set! kk a) _ (i + 1) kh (by (clear * - hn; omega))
        (by simp only [Array.set!_eq_setIfInBounds, Array.size_setIfInBounds]; (clear * - hA; omega))
        (by rw [hrest]; exact h')
    have hA1 : ∀ j, kk ≤ j → A'.getD j zeroDigest = (A.set! kk a).getD j zeroDigest :=
      fun j hj ↦ h9 j (by (clear * - hj hn; omega))
    have hset : (A.set! kk a).getD kk zeroDigest = a := by
      simp [Array.getElem?_setIfInBounds_self_of_lt hA]
    have hne : ∀ j, j ≠ kk → (A.set! kk a).getD j zeroDigest = A.getD j zeroDigest := by
      intro j hj; simp [Array.getElem?_setIfInBounds_ne (Ne.symm hj)]
    have hnode : ∀ j, kk < j → nodeB lay A' m j = nodeB lay A m j := by
      intro j hj; unfold nodeB; split
      · rfl
      · rw [hA1 j hj.le, hne j (by (clear * - hj; omega))]
    have e1 : i + (n + 1) = i + 1 + n := by (clear * -; omega)
    refine ⟨s', A', by rw [e1]; exact h1, h2, h3, h4, h5, h6, ?_, ?_, ?_, ?_⟩
    · have hsz : (hqry lay A m kk).size = 64 := by
        simp only [hqry, ByteArray.size_append, size_digestBytes]
      rw [e1, h7, (stream_entry hdrop).2.2]
      rw [show (digestBytes (nodeB lay A m (2 * kk)) ++ digestBytes (nodeB lay A m (2 * kk + 1))).size = 64
        from hsz]
      (clear * -; ring)
    · rw [h8]; simp only [Array.set!_eq_setIfInBounds, Array.size_setIfInBounds]
    · intro j hj; rw [h9 j (by (clear * - hj; omega)), hne j (by (clear * - hj; omega))]
    · intro k hk1 hk2
      rcases Nat.lt_or_ge k kk with hlt | hge
      · exact h10 k (by (clear * - hk1 hlt; omega)) (by (clear * - hlt; omega))
      · have hk : k = kk := by (clear * - hk2 hge; omega)
        subst hk
        have hq : hqry lay A' m k = hqry lay A m k := by
          unfold hqry; rw [hnode (2 * k) (by (clear * - hn; omega)), hnode (2 * k + 1) (by (clear * - hn; omega))]
        rw [hq, hA1 k le_rfl, hset]
        exact ans_of_drop hc hdrop

/-- The siblings of a heap climb of `E` levels from the node `2^ℓ + x`. -/
def wsibs (lay A : Array Digest) (m : ℕ) : ℕ → ℕ → ℕ → List UInt8
  | 0, _, _ => []
  | E + 1, ℓ, x => (nodeB lay A m (2 ^ ℓ + (if x % 2 = 0 then x + 1 else x - 1))).toList ++
      wsibs lay A m E (ℓ - 1) (x / 2)

theorem length_wsibs (lay A : Array Digest) (m : ℕ) : ∀ E ℓ x, (wsibs lay A m E ℓ x).length = 32 * E
  | 0, _, _ => rfl
  | E + 1, ℓ, x => by
    rw [wsibs, List.length_append, length_wsibs lay A m E, Vector.length_toList]; (clear * -; ring)

/-- **The heap's answers on the log**: every heap node query `k ∈ [2^c, 2^m)` is answered by `node k`. -/
def HeapOK (L : Log) (lay A : Array Digest) (m c : ℕ) : Prop :=
  ∀ k, 2 ^ c ≤ k → k < 2 ^ m → Ans L (hqry lay A m k) (nodeB lay A m k)

/-- **A heap climb on the log**: `E` levels from the node `2^ℓ + x` with the siblings `wsibs`. -/
theorem heapClimb (L : Log) (lay A : Array Digest) (m c : ℕ) (hH : HeapOK L lay A m c) :
    ∀ (E ℓ x : ℕ) (R : List UInt8), E + c ≤ ℓ → ℓ ≤ m → x < 2 ^ ℓ →
    (Scheme.climb E (nodeB lay A m (2 ^ ℓ + x)) x (wsibs lay A m E ℓ x ++ R)).runLog L =
      some (some (nodeB lay A m (2 ^ (ℓ - E) + (x >>> E)), R))
  | 0, ℓ, x, R, _, _, _ => by simp [Scheme.climb, wsibs, OProg.runLog]
  | E + 1, ℓ, x, R, h1, h2, h3 => by
    obtain ⟨l, rfl⟩ : ∃ l, ℓ = l + 1 := ⟨ℓ - 1, by (clear * - h1; omega)⟩
    have hP : 2 ^ (l + 1) = 2 * 2 ^ l := by ring
    have hx2 : x / 2 < 2 ^ l := by (clear * - hP h3; omega)
    have hk1 : 2 ^ c ≤ 2 ^ l + x / 2 :=
      le_trans (Nat.pow_le_pow_right (by norm_num) (by (clear * - h1; omega))) (Nat.le_add_right _ _)
    have hk2 : 2 ^ l + x / 2 < 2 ^ m :=
      lt_of_lt_of_le (by (clear * - hP hx2; omega)) (Nat.pow_le_pow_right (by norm_num) h2)
    have hA := hH _ hk1 hk2
    have ih := heapClimb L lay A m c hH E l (x / 2) R (by (clear * - h1; omega)) (by (clear * - h2; omega)) hx2
    have hsh : x >>> (E + 1) = (x / 2) >>> E := by
      rw [Nat.shiftRight_eq_div_pow, Nat.shiftRight_eq_div_pow, Nat.div_div_eq_div_mul, ← pow_succ']
    rw [show l + 1 - (E + 1) = l - E by (clear * -; omega), hsh]
    unfold hqry at hA
    have hT : ∀ d : Digest, d.toList.length = 32 := fun d ↦ Vector.length_toList
    rw [wsibs, Nat.add_sub_cancel, List.append_assoc, Scheme.climb,
      if_neg (by rw [List.length_append, hT]; (clear * -; omega)), List.take_left' (hT _), List.drop_left' (hT _)]
    by_cases hx : x % 2 = 0
    · rw [if_pos hx, if_pos hx, toQ_dd]
      rw [show 2 * (2 ^ l + x / 2) + 1 = 2 ^ (l + 1) + (x + 1) by (clear * - hP hx; omega),
        show 2 * (2 ^ l + x / 2) = 2 ^ (l + 1) + x by (clear * - hP hx; omega)] at hA
      rw [runLog_query_ans hA]
      exact ih
    · rw [if_neg hx, if_neg hx, toQ_dd]
      rw [show 2 * (2 ^ l + x / 2) + 1 = 2 ^ (l + 1) + x by (clear * - hP hx; omega),
        show 2 * (2 ^ l + x / 2) = 2 ^ (l + 1) + (x - 1) by (clear * - hP hx; omega)] at hA
      rw [runLog_query_ans hA]
      exact ih

/-- **Climbs compose** on the log. -/
theorem climb_add (L : Log) : ∀ (a b : ℕ) (d : Digest) (q : ℕ) (body : List UInt8) (d' : Digest)
    (body' : List UInt8), (Scheme.climb a d q body).runLog L = some (some (d', body')) →
    (Scheme.climb (a + b) d q body).runLog L = (Scheme.climb b d' (q / 2 ^ a) body').runLog L
  | 0, b, d, q, body, d', body', h => by
    simp only [Scheme.climb, OProg.runLog, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    simp
  | a + 1, b, d, q, body, d', body', h => by
    rw [show a + 1 + b = (a + b) + 1 by (clear * -; omega)]
    simp only [Scheme.climb] at h ⊢
    split at h
    · simp [OProg.runLog] at h
    · rename_i hl
      rw [if_neg hl]
      simp only [OProg.runLog] at h ⊢
      obtain ⟨e, he, h2⟩ := Option.bind_eq_some_iff.mp h
      rw [he, Option.bind_some, climb_add L a b e.2 (q / 2) _ d' body' h2, Nat.div_div_eq_div_mul, ← pow_succ']

/-! ## The compiled opening on the expanded body -/

/-- The upper siblings of the positions `ps`: each `m − c` heap levels from its layer node `2^m + (q >> D)`. -/
def wOf (lay A : Array Digest) (m c D : ℕ) (ps : List ℕ) : List UInt8 :=
  ps.flatMap fun q ↦ wsibs lay A m (m - c) m (q >>> D)

theorem length_wOf (lay A : Array Digest) (m c D : ℕ) : ∀ ps : List ℕ,
    (wOf lay A m c D ps).length = ps.length * (32 * (m - c))
  | [] => by simp [wOf]
  | q :: qs => by
    rw [wOf, List.flatMap_cons, List.length_append, ← wOf, length_wOf lay A m c D qs, length_wsibs,
      List.length_cons]; (clear * -; ring)

/-- **The compiled opening on the log**: at the expanded body (each path's leaf and `D` siblings from π, then its
`m − c` upper siblings `wOf`), the rows of the paths, the rest of the body after them. -/
theorem openAll_specB (S : Scheme) (L : Log) (π : ByteArray) (ci : CapI) (lay A : Array Digest) (m c D : ℕ)
    (hH : HeapOK L lay A m c) (hcm : c ≤ m) (hht : ci.ht = D + m) (hlv : ci.lv = c)
    (hcap : ∀ j < 2 ^ c, ci.cap[j]? = some (nodeB lay A m (2 ^ c + j))) (lb : ℕ) (hlb : S.lb ci = lb) :
    ∀ (ps : List ℕ) (o : ℕ) (rows : List (List K)) (R : List UInt8), (∀ q ∈ ps, q < 2 ^ ci.ht) →
      PathsOK L π S.decK lb D ci.wd (S.occ ci.ht ci.wd) ps o (ps.map fun q ↦ nodeB lay A m (2 ^ m + (q >>> D)))
        rows →
      (S.openAll ci ps (fillPaths (blb π) (lb + 32 * D) (32 * (m - c)) ps.length o (wOf lay A m c D ps) ++ R)).runLog
        L = some (some (rows, R))
  | [], o, rows, R, _, hP => by
    cases rows with
    | nil => simp [fillPaths, Scheme.openAll, OProg.runLog]
    | cons _ _ => exact hP.elim
  | q :: qs, o, rows, R, hq, hP => by
    cases rows with
    | nil => exact hP.elim
    | cons row rows =>
    obtain ⟨⟨hb, hrow, d₀, hd₀, hcl⟩, hP'⟩ := hP
    have ih := openAll_specB S L π ci lay A m c D hH hcm hht hlv hcap lb hlb qs (o + (lb + 32 * D)) rows R
      (fun q' h' ↦ hq q' (List.mem_cons_of_mem _ h')) hP'
    have hq0 : q < 2 ^ ci.ht := hq q List.mem_cons_self
    have hW : wOf lay A m c D (q :: qs) = wsibs lay A m (m - c) m (q >>> D) ++ wOf lay A m c D qs := by
      rw [wOf, List.flatMap_cons, ← wOf]
    have hWl := length_wsibs lay A m (m - c) m (q >>> D)
    have hX : (((blb π).drop o).take (lb + 32 * D)).length = lb + 32 * D :=
      take_drop_blb (by (clear * - hb; omega))
    set FP := fillPaths (blb π) (lb + 32 * D) (32 * (m - c)) qs.length (o + (lb + 32 * D)) (wOf lay A m c D qs)
    have hbody : fillPaths (blb π) (lb + 32 * D) (32 * (m - c)) (q :: qs).length o (wOf lay A m c D (q :: qs)) ++ R =
        ((blb π).drop o).take (lb + 32 * D) ++ (wsibs lay A m (m - c) m (q >>> D) ++ (FP ++ R)) := by
      rw [List.length_cons, fillPaths, hW, List.take_left' hWl, List.drop_left' hWl]
      simp only [FP, List.append_assoc]
    -- the leaf
    have hlen : ¬ (((blb π).drop o).take (lb + 32 * D) ++ (wsibs lay A m (m - c) m (q >>> D) ++ (FP ++ R))).length <
        S.lb ci := by rw [List.length_append, hX, hlb]; (clear * -; omega)
    have htk : (((blb π).drop o).take (lb + 32 * D) ++ (wsibs lay A m (m - c) m (q >>> D) ++ (FP ++ R))).take lb =
        ((blb π).drop o).take lb := by
      rw [List.take_append_of_le_length (by rw [hX]; (clear * -; omega)), List.take_take, Nat.min_eq_left
        (by (clear * -; omega))]
    have hdr : (((blb π).drop o).take (lb + 32 * D) ++ (wsibs lay A m (m - c) m (q >>> D) ++ (FP ++ R))).drop lb =
        ((blb π).drop (o + lb)).take (32 * D) ++ (wsibs lay A m (m - c) m (q >>> D) ++ (FP ++ R)) := by
      rw [List.drop_append_of_le_length (by rw [hX]; (clear * -; omega)), List.drop_take, List.drop_drop,
        Nat.add_sub_cancel_left]
    have hqb : toQ (((blb π).drop o).take lb) = π.extract o (o + lb) := by
      apply toQ_eq; rw [blb_extract, Nat.add_sub_cancel_left]
    -- the climb: `D` levels with π's siblings, then `m − c` heap levels
    have hmod : q % 2 ^ ci.ht = q := Nat.mod_eq_of_lt hq0
    have hxl : q >>> D < 2 ^ m := by
      rw [Nat.shiftRight_eq_div_pow, Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _), ← pow_add, Nat.add_comm, ← hht]
      exact hq0
    have hcl2 := climb_add L D (m - c) d₀ q _ _ _ (hcl (wsibs lay A m (m - c) m (q >>> D) ++ (FP ++ R)))
    rw [← Nat.shiftRight_eq_div_pow, heapClimb L lay A m c hH (m - c) m (q >>> D) (FP ++ R)
      (by (clear * - hcm; omega)) le_rfl hxl, Nat.sub_sub_self hcm, ← Nat.shiftRight_add] at hcl2
    have hj : q >>> (D + (m - c)) < 2 ^ c := by
      rw [Nat.shiftRight_eq_div_pow, Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _), ← pow_add,
        show c + (D + (m - c)) = ci.ht by rw [hht]; (clear * - hcm; omega)]
      exact hq0
    have hidx : q % 2 ^ ci.ht / 2 ^ (ci.ht - ci.lv) = q >>> (D + (m - c)) := by
      rw [hmod, hht, hlv, Nat.shiftRight_eq_div_pow]; congr 2; (clear * - hcm; omega)
    have hone : (S.openOne ci q (((blb π).drop o).take (lb + 32 * D) ++ (wsibs lay A m (m - c) m (q >>> D) ++
        (FP ++ R)))).runLog L = some (some (row, FP ++ R)) := by
      rw [Scheme.openOne, if_neg hlen, hlb, htk, hqb, runLog_query_ans hd₀, hdr, runLog_bind, hmod,
        show ci.ht - ci.lv = D + (m - c) by rw [hht, hlv]; (clear * - hcm; omega), hcl2]
      have hidx' : q / 2 ^ (D + (m - c)) = q >>> (D + (m - c)) := (Nat.shiftRight_eq_div_pow _ _).symm
      simp only [Option.bind_some, OProg.runLog, hidx', hcap _ hj, ↓reduceIte, Scheme.padRow, htk, hlb, hrow]
    rw [hbody, Scheme.openAll, runLog_bind, hone, Option.bind_some]
    simp only
    rw [runLog_bind, ih]
    rfl

end Lvm.VEq
