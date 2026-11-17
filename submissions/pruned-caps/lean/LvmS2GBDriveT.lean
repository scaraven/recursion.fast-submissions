-- New for lvm2 MP-B cap pruning (CAP-L3, 2026-11-17): S2GB's driver facts (moved verbatim from LvmS2GBCert, placement
-- only). DAY-0 STATEMENTS: every `sorry` is tagged `-- CAP-FRZ L`. A proof never changes its statement.
import LvmS2GBV

/-!
# S2GB's driver facts

* **`driveItemsB_tail`**: an accepting `driveItemsB` run moves the tail cursor by whole nodes, at most
  `capLayerAll` of them.
* **`parseOkB_size`**, **`piSizeB`**: an accepted proof is its static part and whole tail nodes.
* **`hq_VSSB`**: O1 for S2GB's `V_S`.
-/

set_option autoImplicit false

namespace Lvm

open RecursionFast

/-- The cap-layer nodes of the openings of `items`, `Σ 2^cap` (the tail nodes the driver can read). -/
def capLayerAll (p : Params) (items : List Item) : Nat :=
  items.foldl (fun a it => match it with | .opening r => a + 2 ^ (p.level r).cap | _ => a) 0

/-! ### Proof help: accepting runs of the driver's loops reach their continuations -/

theorem rlB_query {L : Log} {q : ByteArray} {f : Digest → OProg Bool}
    (h : (OProg.query q f).runLog L = some true) : ∃ d, (f d).runLog L = some true := by
  simp only [OProg.runLog] at h
  revert h
  cases L.find? (fun e => decide (e.1 = q)) with
  | none => simp
  | some e => exact fun h => ⟨e.2, by simpa using h⟩

theorem rlB_ret {L : Log} (h : (OProg.ret false : OProg Bool).runLog L = some true) : False := by
  simp [OProg.runLog] at h

theorem rlB_climb (π : ByteArray) (L : Log) (q : Nat) : ∀ (j lvl : Nat) (cur : Digest) (s : DSt)
    (k : DSt → Digest → OProg Bool), (climb π q j lvl cur s k).runLog L = some true →
      ∃ s' d, (k s' d).runLog L = some true
  | 0, _, cur, s, k, h => ⟨s, cur, by simpa only [climb] using h⟩
  | j + 1, lvl, cur, s, k, h => by
    simp only [climb, ask] at h
    obtain ⟨d, hd⟩ := rlB_query h
    exact rlB_climb π L q j (lvl + 1) _ _ k hd

theorem rlB_posLoop (π : ByteArray) (L : Log) (h : Nat) : ∀ (n rem : Nat) (s : DSt) (k : DSt → OProg Bool),
    (posLoop π h n rem s k).runLog L = some true → ∃ s', (k s').runLog L = some true
  | 0, _, s, k, hr => ⟨s, by simpa only [posLoop] using hr⟩
  | n + 1, rem, s, k, hr => by
    simp only [posLoop, fsQuery, ask] at hr
    obtain ⟨d, hd⟩ := rlB_query hr
    exact rlB_posLoop π L h n _ _ k hd

theorem rlB_pathsB (π : ByteArray) (L : Log) (Lv : Level) : ∀ (qs : List Nat) (s : DSt) (acc : List Digest)
    (k : DSt → List Digest → OProg Bool), (pathsB π Lv qs s acc k).runLog L = some true →
      ∃ s' tops, (k s' tops).runLog L = some true
  | [], s, acc, k, h => ⟨s, acc.reverse, by simpa only [pathsB] using h⟩
  | q :: qs, s, acc, k, h => by
    simp only [pathsB, ask] at h
    obtain ⟨d, hd⟩ := rlB_query h
    obtain ⟨s1, d1, h1⟩ := rlB_climb π L q _ _ _ _ _ hd
    exact rlB_pathsB π L Lv qs s1 _ k h1

theorem rlB_heapB (L : Log) (lay : Array Digest) (m : Nat) : ∀ (n kk : Nat) (A : Array Digest) (s : DSt)
    (k : DSt → Array Digest → OProg Bool), (heapB lay m n kk A s k).runLog L = some true →
      ∃ s' A', (k s' A').runLog L = some true
  | 0, _, A, s, k, h => ⟨s, A, by simpa only [heapB] using h⟩
  | n + 1, kk, A, s, k, h => by
    simp only [heapB, ask] at h
    obtain ⟨d, hd⟩ := rlB_query h
    exact rlB_heapB L lay m n _ _ _ k hd

/-- A fold whose step keeps the cursor or moves it by one node moves it by at most `|xs|` nodes. -/
theorem foldB_snd {α β : Type} (f : α × Nat → β → α × Nat)
    (hf : ∀ a x, (f a x).2 = a.2 ∨ (f a x).2 = a.2 + nodeBytes) :
    ∀ (xs : List β) (a : α × Nat), ∃ u, u ≤ xs.length ∧ (xs.foldl f a).2 = a.2 + nodeBytes * u
  | [], a => ⟨0, Nat.zero_le _, by simp⟩
  | x :: xs, a => by
    obtain ⟨u, hu, he⟩ := foldB_snd f hf xs (f a x)
    rw [List.foldl_cons, he]
    rcases hf a x with h | h
    · exact ⟨u, by simp only [List.length_cons]; omega, by rw [h]⟩
    · exact ⟨u + 1, by simp only [List.length_cons]; omega, by rw [h, Nat.mul_add]; omega⟩

theorem layerB_snd (π : ByteArray) (m D : Nat) (qt : List (Nat × Digest)) (tail : Nat) :
    ∃ u, u ≤ 2 ^ m ∧ (layerB π m D qt tail).2 = tail + nodeBytes * u := by
  unfold layerB
  refine (foldB_snd _ ?_ (List.range (2 ^ m)) (#[], tail)).imp fun u h => ⟨by simpa using h.1, h.2⟩
  intro a x
  split <;> simp

theorem rlB_openLoopB (π : ByteArray) (L : Log) (Lv : Level) (c capOff : Nat) (s : DSt) (tail : Nat)
    (k : DSt → Nat → OProg Bool) (h : (openLoopB π Lv c capOff s tail k).runLog L = some true) :
    ∃ s' u, u ≤ 2 ^ Lv.cap ∧ (k s' (tail + nodeBytes * u)).runLog L = some true := by
  unfold openLoopB at h
  obtain ⟨s1, tops, h1⟩ := rlB_pathsB π L Lv _ s [] _ h
  try dsimp only at h1
  split at h1
  · obtain ⟨s2, A, h2⟩ := rlB_heapB L _ _ _ _ _ _ _ h1
    try dsimp only at h2
    split at h2
    · obtain ⟨u, hu, he⟩ := layerB_snd π Lv.cap Lv.path (s.pos.zip tops) tail
      exact ⟨s2, u, hu, he ▸ h2⟩
    · exact (rlB_ret h2).elim
  · exact (rlB_ret h1).elim

theorem foldB_shift {β : Type} (g : Nat → β → Nat) (hg : ∀ a x, g a x = a + g 0 x) :
    ∀ (xs : List β) (a : Nat), xs.foldl g a = a + xs.foldl g 0
  | [], a => by simp
  | x :: xs, a => by
    rw [List.foldl_cons, List.foldl_cons, foldB_shift g hg xs (g a x), foldB_shift g hg xs (g 0 x), hg a x]
    omega

theorem capLayerAll_cons (p : Params) (it : Item) (rest : List Item) :
    capLayerAll p (it :: rest) = capLayerAll p [it] + capLayerAll p rest := by
  unfold capLayerAll
  rw [List.foldl_cons, foldB_shift _ (fun a x => by cases x <;> simp) rest]
  simp

/-- **CAP-FRZ L**: **the driver's tail invariant**: an accepting run of `driveItemsB` reaches its continuation with
the tail cursor moved by whole nodes, at most `capLayerAll` of them. -/
theorem driveItemsB_tail (p : Params) (π : ByteArray) (L : Log) :
    ∀ (items : List Item) (s : DSt) (t : Nat) (k : DSt → Nat → OProg Bool),
      (driveItemsB p π items s t k).runLog L = some true →
      ∃ s' u, u ≤ capLayerAll p items ∧ (k s' (t + nodeBytes * u)).runLog L = some true := by
  intro items
  induction items with
  | nil =>
    intro s t k h
    exact ⟨s, 0, Nat.zero_le _, by simpa only [driveItemsB, Nat.mul_zero, Nat.add_zero] using h⟩
  | cons it rest ih =>
    intro s t k h
    rw [capLayerAll_cons]
    cases it with
    | read m =>
      obtain ⟨s', u, hu, hk⟩ := ih _ t k (by simpa only [driveItemsB] using h)
      exact ⟨s', u, hu.trans (Nat.le_add_left _ _), hk⟩
    | readW m w =>
      obtain ⟨s', u, hu, hk⟩ := ih _ t k (by simpa only [driveItemsB] using h)
      exact ⟨s', u, hu.trans (Nat.le_add_left _ _), hk⟩
    | cap c r =>
      obtain ⟨s', u, hu, hk⟩ := ih _ t k (by simpa only [driveItemsB] using h)
      exact ⟨s', u, hu.trans (Nat.le_add_left _ _), hk⟩
    | sample =>
      simp only [driveItemsB, fsQuery, ask] at h
      obtain ⟨d, hd⟩ := rlB_query h
      obtain ⟨s', u, hu, hk⟩ := ih _ t k hd
      exact ⟨s', u, hu.trans (Nat.le_add_left _ _), hk⟩
    | positions r =>
      simp only [driveItemsB] at h
      obtain ⟨s1, h1⟩ := rlB_posLoop π L _ _ _ _ _ h
      obtain ⟨s', u, hu, hk⟩ := ih _ t k h1
      exact ⟨s', u, hu.trans (Nat.le_add_left _ _), hk⟩
    | opening r =>
      simp only [driveItemsB] at h
      split at h
      · exact (rlB_ret h).elim
      · split at h
        · obtain ⟨s1, u1, hu1, h1⟩ := rlB_openLoopB π L _ _ _ s t _ h
          obtain ⟨s', u2, hu2, h2⟩ := ih _ _ k h1
          have hc : capLayerAll p [.opening r] = 2 ^ (p.level r).cap := by simp [capLayerAll]
          refine ⟨s', u1 + u2, by rw [hc]; omega, ?_⟩
          rw [Nat.mul_add, ← Nat.add_assoc]
          exact h2
        · exact (rlB_ret h).elim

end Lvm

namespace Lvm.CT

open RecursionFast Lvm Lvm.T Lvm.ASM Lvm.FS Lvm.E2S
open Lvm.E2T (TNatT)

/-- `parseOkB`'s size range (proof help). -/
theorem parseOkB_size {p : Params} {vk c : RecursionFast.Digest} {π : RecursionFast.Proof}
    (h : parseOkB p vk c π = true) : piStatic p ≤ π.size ∧ π.size ≤ piStatic p + tailMax p := by
  unfold parseOkB at h
  have h4 := ((Bool.and_eq_true _ _).mp h).1
  have h3 := ((Bool.and_eq_true _ _).mp h4).1
  have h2 := ((Bool.and_eq_true _ _).mp h3).1
  have h1 := (Bool.and_eq_true _ _).mp h2
  exact ⟨of_decide_eq_true h1.1, of_decide_eq_true h1.2⟩

/-! ### Proof help: the query counts of the S2GB driver (`q_driveItems`'s twins over `qcItemsB`) -/

section QB

variable (H : ByteArray → Digest) (π : ByteArray)

theorem qB_pathsB (Lv : Level) : ∀ (qs : List Nat) (s : DSt) (acc : List Digest)
    (k : DSt → List Digest → OProg Bool) (K : Nat),
    (∀ s' tops, s'.pos = s.pos → ((k s' tops).queries H).length ≤ K) →
      ((pathsB π Lv qs s acc k).queries H).length ≤ qs.length * (1 + Lv.path) + K
  | [], s, acc, k, K, hk => by simp only [pathsB]; exact (hk s _ rfl).trans (by simp)
  | q :: qs, s, acc, k, K, hk => by
    simp only [pathsB, ask, OProg.queries, List.length_cons]
    refine (Nat.add_le_add_right (q_climb H π q Lv.path 0 _ _ _ (qs.length * (1 + Lv.path) + K) ?_) 1).trans ?_
    · intro s' d h
      exact qB_pathsB Lv qs s' _ k K fun s'' tops h' => hk s'' tops (h'.trans h)
    · rw [Nat.add_mul, Nat.one_mul]
      omega

theorem qB_heapB (lay : Array Digest) (m : Nat) : ∀ (n kk : Nat) (A : Array Digest) (s : DSt)
    (k : DSt → Array Digest → OProg Bool) (K : Nat),
    (∀ s' A', s'.pos = s.pos → ((k s' A').queries H).length ≤ K) →
      ((heapB lay m n kk A s k).queries H).length ≤ n + K
  | 0, _, A, s, k, K, hk => by simp only [heapB]; exact (hk s A rfl).trans (by omega)
  | n + 1, kk, A, s, k, K, hk => by
    simp only [heapB, ask, OProg.queries, List.length_cons]
    refine (Nat.add_le_add_right (qB_heapB lay m n (kk - 1) _ _ k K ?_) 1).trans ?_
    · exact fun s' A' h => hk s' A' h
    · omega

theorem qB_openLoopB (Lv : Level) (c capOff : Nat) (s : DSt) (tail : Nat) (k : DSt → Nat → OProg Bool) (K : Nat)
    (hk : ∀ s' t, s'.pos = s.pos → ((k s' t).queries H).length ≤ K) :
    ((openLoopB π Lv c capOff s tail k).queries H).length ≤
      s.pos.length * (1 + Lv.path) + ((2 ^ Lv.cap - 2 ^ c) + K) := by
  unfold openLoopB
  refine qB_pathsB H π Lv s.pos s [] _ _ fun s1 tops h1 => ?_
  dsimp only
  split
  · refine qB_heapB H _ _ _ _ _ s1 _ K fun s2 A h2 => ?_
    split
    · exact hk s2 _ (h2.trans h1)
    · simp [OProg.queries]
  · simp [OProg.queries]

theorem qB_driveItemsB (p : Params) (k : DSt → Nat → OProg Bool) (K : Nat)
    (hk : ∀ s t, ((k s t).queries H).length ≤ K) :
    ∀ (items : List Item) (b : Nat) (s : DSt) (t : Nat), s.pos.length ≤ b →
      ((driveItemsB p π items s t k).queries H).length ≤ qcItemsB p items b + K
  | [], b, s, t, _ => by simp only [driveItemsB, qcItemsB]; exact (hk s t).trans (by omega)
  | .read m :: rest, b, s, t, hs => by
    simp only [driveItemsB, qcItemsB]; exact qB_driveItemsB p k K hk rest b _ t hs
  | .readW m w :: rest, b, s, t, hs => by
    simp only [driveItemsB, qcItemsB]; exact qB_driveItemsB p k K hk rest b _ t hs
  | .cap c r :: rest, b, s, t, hs => by
    simp only [driveItemsB, qcItemsB]; exact qB_driveItemsB p k K hk rest b _ t hs
  | .sample :: rest, b, s, t, hs => by
    simp only [driveItemsB, qcItemsB, fsQuery, ask, OProg.queries, List.length_cons]
    refine (Nat.add_le_add_right (qB_driveItemsB p k K hk rest b _ t ?_) 1).trans ?_
    · exact hs
    · omega
  | .positions r :: rest, b, s, t, _ => by
    simp only [driveItemsB, qcItemsB]
    refine (q_posLoop H π (p.level r).height (p.level r).nPosQ (p.level r).t { s with pos := [] }
      _ (qcItemsB p rest (p.level r).t + K) fun s' hs' ↦
        qB_driveItemsB p k K hk rest (p.level r).t s' t (by simpa using hs')).trans ?_
    omega
  | .opening r :: rest, b, s, t, hs => by
    simp only [driveItemsB, qcItemsB]
    split
    · simp [OProg.queries]
    · rename_i capOff _
      split
      · refine (qB_openLoopB H π (p.level r) _ capOff s t _ (qcItemsB p rest b + K)
          fun s' t' hs' ↦ qB_driveItemsB p k K hk rest b _ t' (by simpa [hs'] using hs)).trans ?_
        have hm := Nat.mul_le_mul_right (1 + (p.level r).path) hs
        have hq : p.heapQ r.lv (p.level r).cap =
            2 ^ (p.level r).cap - 2 ^ p.capSendBits r.lv (p.level r).cap := by
          by_cases hc : p.capPrune = true <;> simp [Params.heapQ, Params.capSendBits, hc]
        omega
      · simp [OProg.queries]

end QB

/-- **CAP-FRZ L**: **`piSizeB`**: an `S` proof `V_S` accepts at S2GB is its static part and whole tail nodes, at most
`tailMax P20B` bytes of them. -/
theorem piSizeB (N : TNatT) (vk c : RecursionFast.Digest) (π : RecursionFast.Proof) (L : Log)
    (h : (VSSB N vk c π).runLog L = some true) :
    ∃ u, π.size = piStatic P20B + nodeBytes * u ∧ nodeBytes * u ≤ tailMax P20B := by
  have h' : (if parseOkB P20B vk c π then driveB P20B π (decideFBX N vk c) else .ret false : OProg Bool).runLog L =
      some true := h
  split at h'
  · rename_i hp
    have hs := parseOkB_size hp
    simp only [driveB] at h'
    obtain ⟨a0, h1⟩ := rlB_query h'
    obtain ⟨st0, h2⟩ := rlB_query h1
    obtain ⟨s', u, -, h3⟩ := driveItemsB_tail P20B π L _ _ _ _ h2
    simp only [OProg.runLog, Option.some.injEq, Bool.and_eq_true, beq_iff_eq] at h3
    refine ⟨u, h3.1.2.symm, ?_⟩
    omega
  · exact (rlB_ret h').elim

/-- **CAP-FRZ L**: **O1 for S2GB's `V_S`** (`hq_VSSX`'s with the heap queries, `qcItemsB_P20B`). -/
theorem hq_VSSB (N : TNatT) (H : ByteArray → RecursionFast.Digest) (vk c : RecursionFast.Digest)
    (π : RecursionFast.Proof) : ((VSSB N vk c π).queries H).length ≤ qVlvm := by
  show ((if parseOkB P20B vk c π then driveB P20B π (decideFBX N vk c) else .ret false : OProg Bool).queries H).length ≤
    qVlvm
  split
  · simp only [driveB, OProg.queries, List.length_cons]
    refine (Nat.add_le_add_right (Nat.add_le_add_right (qB_driveItemsB H π P20B _ 0
      (fun s t ↦ by simp [OProg.queries]) (schedule P20B) 0 _ _ (by simp)) 1) 1).trans ?_
    have := qcItemsB_P20B
    show _ ≤ 16384
    omega
  · simp [OProg.queries]

end Lvm.CT
