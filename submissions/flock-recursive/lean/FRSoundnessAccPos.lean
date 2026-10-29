-- New for `flock-recursive` (BLUEPRINT §5.4, A.4, A.9; stage S-G3 pass 2, `hFin` steps 3–4).
-- RET-2: the declarations revision 4.1 reads moved to `FRSoundnessCoreAcc`.
import FRSoundnessAccFin
import FRSoundnessCoreAcc

/-!
# `hFin`, steps 3–4: the Fiat–Shamir positions and the K rounds' arithmetic

* **Step 3, positions** (from `fsMsgs_eq`, no new `decide`): `phStart n` is the number of
  Fiat–Shamir items before phase `n` (`phStart_eq_sum`), a phase has one message per Fiat–Shamir
  item (`phaseMsgs_length`), so `fsMsgs` at `phStart n + k` is phase `n`'s message `k`
  (**`fsMsgs_phase`**). For a `.rounds` phase, round `l`'s absorb is at `phStart n + 2l` with π
  range `fieldOff f + phaseOff n f + l·rb` (**`fsMsgs_round`**), its squeeze at `+ 1`.
* **Step 4, arithmetic**: `rSum = c₁ + c₂` and `rVal = c₀ + r(c₁ + r c₂)` of the log's message
  (`rSum_eq`, `rVal_eq`); on the run's entries they are the verifier's `elemKAt` sums and `gK`
  (**`rSum_fsQ`**, **`rVal_fsQ`**); `Val.eqv` on K values is equality (`eqv_k`).
* **The K rounds' flags** (**`roundsT_chk`**): an accepted run of `roundsT` over K with every
  round real checks `c₁ + c₂` of round `l + 1` against `gK` of round `l`.
-/

namespace FR.Snd
open RecursionFast Finset

/-! ## Step 3: positions -/

theorem fsStarts_foldl (ps : List Phase) (a : ℕ) (acc : List ℕ) :
    (ps.foldl (fun (acc : ℕ × List ℕ) p =>
      (acc.1 + (p.shape.items.filter Item.isFS).length, acc.2 ++ [acc.1])) (a, acc)).2 =
      acc ++ (List.range ps.length).map fun n =>
        a + ((ps.take n).map fun p => (p.shape.items.filter Item.isFS).length).sum := by
  induction ps generalizing a acc with
  | nil => simp
  | cons p ps ih =>
    rw [List.foldl_cons, ih, List.length_cons, List.range_succ_eq_map, List.map_cons,
      List.map_map]
    simp only [List.take_zero, List.map_nil, List.sum_nil, Nat.add_zero, List.append_assoc,
      List.singleton_append, Function.comp_def, List.take_succ_cons, List.map_cons, List.sum_cons,
      Nat.add_assoc]

/-- **`phStart n`** is the number of Fiat–Shamir items before phase `n`. -/
theorem phStart_eq_sum {n : ℕ} (hn : n < phases.length) :
    phStart n = ((phases.take n).map fun p => (p.shape.items.filter Item.isFS).length).sum := by
  rw [phStart, fsStarts, fsStarts_foldl, List.nil_append, List.getD_eq_getElem _ _ (by simpa)]
  simp

theorem filter_isFS_replicate_pos (i : ℕ) (n : ℕ) :
    ((List.replicate n (posItems i)).flatten.filter Item.isFS) = [] := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [List.replicate_succ, List.flatten_cons, List.filter_append, ih, List.append_nil,
      posItems, List.filter_cons]
    simp [Item.isFS]

/-- A phase has one message per Fiat–Shamir item. -/
theorem phaseMsgs_length (n : ℕ) (sh : Shape) :
    (X.phaseMsgs n sh).length = (sh.items.filter Item.isFS).length := by
  cases sh with
  | seed => rfl
  | absorb f len => rfl
  | squeezes k ch => simp [X.phaseMsgs, Shape.items, List.filter_replicate, Item.isFS]
  | uni f => rfl
  | rounds f k deg inK real =>
    simp only [X.phaseMsgs, Shape.items, List.length_flatMap, List.length_cons, List.length_nil]
    induction k with
    | zero => rfl
    | succ k ih =>
      rw [List.range_succ, List.map_append, List.sum_append, ih, List.replicate_succ',
        List.flatten_append, List.filter_append, List.length_append]
      simp [List.filter_cons, Item.isFS]
  | queries i => simp only [X.phaseMsgs, Shape.items, filter_isFS_replicate_pos]; rfl

theorem msgsFrom_getD : ∀ (ps : List Phase) (m n k : ℕ) (hn : n < ps.length),
    k < (X.phaseMsgs (m + n) (ps[n]'hn).shape).length →
    (msgsFrom ps m).getD
        (((ps.take n).map fun p => (p.shape.items.filter Item.isFS).length).sum + k) none =
      (X.phaseMsgs (m + n) (ps[n]'hn).shape).getD k none
  | [], _, _, _, hn, _ => absurd hn (by simp)
  | p :: ps, m, 0, k, _, hk => by
    simp only [List.take_zero, List.map_nil, List.sum_nil, Nat.zero_add, msgsFrom,
      List.getElem_cons_zero, Nat.add_zero] at hk ⊢
    rw [List.getD_append _ _ _ _ hk]
  | p :: ps, m, n + 1, k, hn, hk => by
    have hl := phaseMsgs_length m p.shape
    simp only [List.take_succ_cons, List.map_cons, List.sum_cons, msgsFrom,
      List.getElem_cons_succ] at hk ⊢
    rw [Nat.add_assoc, List.getD_append_right _ _ _ _ (by omega), hl, Nat.add_sub_cancel_left,
      show m + (n + 1) = m + 1 + n by omega]
    exact msgsFrom_getD ps (m + 1) n k (by simpa using hn) (by rwa [show m + (n + 1) = m + 1 + n
      by omega] at hk)

/-- **`fsMsgs` at `phStart n + k` is phase `n`'s message `k`.** -/
theorem fsMsgs_phase {n k : ℕ} (hn : n < phases.length)
    (hk : k < (X.phaseMsgs n (phases[n]'hn).shape).length) :
    X.fsMsgs.getD (phStart n + k) none = (X.phaseMsgs n (phases[n]'hn).shape).getD k none := by
  rw [fsMsgs_eq, phStart_eq_sum hn]
  have := msgsFrom_getD phases 0 n k hn (by rwa [Nat.zero_add])
  rwa [Nat.zero_add] at this

theorem rounds_msgs_getD (n f K deg : ℕ) (inK : Bool) (real : KC ℕ) {l : ℕ} (hl : l < K) :
    (X.phaseMsgs n (.rounds f K deg inK real)).getD (2 * l) none =
        some (fieldOff f + phaseOff n f + l * roundBytes inK, roundBytes inK) ∧
      (X.phaseMsgs n (.rounds f K deg inK real)).getD (2 * l + 1) none = none ∧
      2 * l + 1 < (X.phaseMsgs n (.rounds f K deg inK real)).length := by
  simp only [X.phaseMsgs]
  induction K with
  | zero => omega
  | succ K ih =>
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton]
    have hlen : ((List.range K).flatMap fun j =>
        [some (fieldOff f + phaseOff n f + j * roundBytes inK, roundBytes inK), none]).length =
          2 * K := by
      rw [List.length_flatMap]; simp [List.sum_replicate]; ring
    rcases Nat.lt_succ_iff_lt_or_eq.mp hl with h | rfl
    · obtain ⟨h1, h2, h3⟩ := ih h
      refine ⟨?_, ?_, ?_⟩
      · rw [List.getD_append _ _ _ _ (by omega), h1]
      · rw [List.getD_append _ _ _ _ (by omega), h2]
      · simp only [List.length_append]; omega
    · refine ⟨?_, ?_, ?_⟩
      · rw [List.getD_append_right _ _ _ _ (by omega), hlen, Nat.sub_self]; rfl
      · rw [List.getD_append_right _ _ _ _ (by omega), hlen, show 2 * l + 1 - 2 * l = 1 by omega]
        rfl
      · simp only [List.length_append, hlen, List.length_cons, List.length_nil]; omega

/-- **Round `l` of a `.rounds` phase**: its absorb's π range, and its squeeze. -/
theorem fsMsgs_round {n f K deg : ℕ} {inK : Bool} {real : KC ℕ} (hn : n < phases.length)
    (hsh : (phases[n]'hn).shape = .rounds f K deg inK real) {l : ℕ} (hl : l < K) :
    X.fsMsgs.getD (phStart n + 2 * l) none =
        some (fieldOff f + phaseOff n f + l * roundBytes inK, roundBytes inK) ∧
      X.fsMsgs.getD (phStart n + 2 * l + 1) none = none := by
  obtain ⟨h1, h2, h3⟩ := rounds_msgs_getD n f K deg inK real hl
  rw [← hsh] at h1 h2 h3
  exact ⟨by rw [fsMsgs_phase hn (by omega), h1], by
    rw [Nat.add_assoc, fsMsgs_phase hn h3, h2]⟩

/-! ## Step 4: the rounds' arithmetic -/

/-- `rVal` is `c₀ + r·(c₁ + r·c₂)`. -/
theorem rVal_eq (b : ℕ) (es : Log) (l : ℕ) :
    rVal b es l = readK (msgAt es (b + 2 * l)) 0 + chK (ansAt es (b + 2 * l + 1)) *
      (readK (msgAt es (b + 2 * l)) 32 + chK (ansAt es (b + 2 * l + 1)) *
        readK (msgAt es (b + 2 * l)) 64) := by
  rw [rVal, g2At, rch2, peval_three]; ring

theorem absOff_eq {f : ℕ} (hf : f ≤ nFields) (o : ℕ) : absOff f o = fieldOff f + o := by
  rw [absOff, fieldOffA_getD hf]

/-- **`rSum` on the run's entries is the verifier's `c₁ + c₂`** (round `l` of the K phase `n`,
field `f`, from `fsQ_gen`'s chain). -/
theorem rSum_fsQ {vk c : Digest} {π : Proof} {es : Log}
    (hq : ∀ p < 468, (es.getD p default).1 = X.fsQ vk c π p (es.getD (p - 1) default).2)
    {n f K deg : ℕ} {real : KC ℕ} (hn : n < phases.length)
    (hsh : (phases[n]'hn).shape = .rounds f K deg true real) (hf : f ≤ nFields) {l : ℕ}
    (hl : l < K) (hp : phStart n + 2 * l < 468) (hp0 : 0 < phStart n + 2 * l) :
    rSum (phStart n) es l = elemKAt ⟨vk, c, π⟩ f (phaseOff n f + l * 96 + 32) +
      elemKAt ⟨vk, c, π⟩ f (phaseOff n f + l * 96 + 64) := by
  have hm := (fsMsgs_round hn hsh hl).1
  simp only [roundBytes, ite_true] at hm
  rw [rSum_eq, readK_fsQ hq hp hp0 hm (by norm_num), readK_fsQ hq hp hp0 hm (by norm_num)]
  simp only [elemKAt, absOff_eq hf, Nat.add_assoc]

/-- **`rVal` on the run's entries is the verifier's `gK`** (`a₂` the squeeze's answer). -/
theorem rVal_fsQ {vk c : Digest} {π : Proof} {es : Log}
    (hq : ∀ p < 468, (es.getD p default).1 = X.fsQ vk c π p (es.getD (p - 1) default).2)
    {n f K deg : ℕ} {real : KC ℕ} (hn : n < phases.length)
    (hsh : (phases[n]'hn).shape = .rounds f K deg true real) (hf : f ≤ nFields) {l : ℕ}
    (hl : l < K) (hp : phStart n + 2 * l < 468) (hp0 : 0 < phStart n + 2 * l) :
    rVal (phStart n) es l =
      gK ⟨vk, c, π⟩ f (phaseOff n f + l * 96) (ansAt es (phStart n + 2 * l + 1)) := by
  have hm := (fsMsgs_round hn hsh hl).1
  simp only [roundBytes, ite_true] at hm
  rw [rVal_eq, readK_fsQ hq hp hp0 hm (by norm_num), readK_fsQ hq hp hp0 hm (by norm_num),
    readK_fsQ hq hp hp0 hm (by norm_num)]
  simp only [gK, elemKAt, absOff_eq hf, Nat.add_assoc, Nat.add_zero]

/-! ## The K rounds' flags -/

/-- **An accepted run of real K rounds checks each round against the previous one**: round
`l + 1`'s `c₁ + c₂` is round `l`'s `gK` at its squeeze's answer, and round `0`'s is the claim. -/
theorem roundsT_chk (inp : Input) (f o real : ℕ) :
    ∀ (n j : ℕ) (d : Digest) (cv : Val) (tr : Trace) (x : List Val × Bool × Trace),
      roundsT inp f o 2 true real n j d cv tr = some x → x.2.1 = true → j + n ≤ real →
      (0 < n → (Val.k (elemKAt inp f (o + j * 96 + 32) + elemKAt inp f (o + j * 96 + 64))).eqv cv
        = true) ∧
      ∀ l, l + 1 < n → elemKAt inp f (o + (j + l + 1) * 96 + 32) +
          elemKAt inp f (o + (j + l + 1) * 96 + 64) = gK inp f (o + (j + l) * 96) (sqAns tr l)
  | 0, _, _, _, _, _, _, _, _ => ⟨fun h => absurd h (by omega), fun l hl => by omega⟩
  | n + 1, j, d, cv, (q₁, a₁) :: (q₂, a₂) :: tr, x, h, hx, hr => by
    simp only [roundsT, ite_true] at h
    split_ifs at h with hq
    obtain ⟨x', hx', rfl⟩ := Option.map_eq_some_iff.mp h
    simp only [show decide (j < real) = true from decide_eq_true (by omega), Bool.not_true,
      Bool.false_or, Bool.true_or, Bool.and_true, Bool.and_eq_true] at hx
    have ih := roundsT_chk inp f o real n (j + 1) a₂ _ tr x' hx' hx.2 (by omega)
    refine ⟨fun _ => hx.1, fun l hl => ?_⟩
    rcases l with _ | l
    · have h0 := ih.1 (by omega)
      simp only [roundKVals, List.getLastD_eq_getLast?, List.getLast?_cons_cons,
        List.getLast?_singleton, Option.getD_some] at h0
      rw [ite_pos' (decide_eq_true (by omega)), eqv_k] at h0
      simpa [sqAns, roundBytes, Nat.add_assoc] using h0
    · have := ih.2 l (by omega)
      simpa [sqAns, Nat.add_assoc, Nat.add_comm 1, Nat.mul_add, Nat.add_mul] using this
  | _ + 1, _, _, _, [], _, h, _, _ => by simp [roundsT] at h
  | _ + 1, _, _, _, [_], _, h, _, _ => by simp [roundsT] at h

end FR.Snd
