-- New for `flock-recursive` (BLUEPRINT revision 4.1, A.9; stage R4d).
import FRSoundness4R4Acc

/-!
# The finals' exports on an accepted run (`exAt`'s bookkeeping)

`Finals.ops` passes field `k` the exports `exAt … k` of the fields before it, computed at the
fold's own bases `baseAt … k`. **`exAt_succ`**: field `k`'s exports are pushed at base
`baseAt … k`. **`fields_ex4`**: on an accepted run of `gen4 seq4 p (finOps4 P)` the register file
`Rs k` that field `k` runs from has size `baseAt … k`, so `Ex (k + 1)` is `Ex k` with field `k`'s
exports at `(Rs k).size` pushed: `lrEx` of `finE` names `finLr`'s exports (`lrEx_eq4`).
-/

namespace FR.Snd.R4
open RecursionFast Rev4

section ExAt
variable (outs : Array (List Reg)) (zh : List Reg)

/-- **The base the fold gives field `k`** (as `exAt`, the exports). -/
def baseAt : List FinField → ℕ → Array (List Reg) → ℕ → ℕ
  | [], b, _, _ => b
  | _ :: _, b, _, 0 => b
  | f :: fs, b, ex, k + 1 =>
    baseAt fs (b + opsOut (f ⟨outs, zh, ex⟩ b).1) (ex.push (f ⟨outs, zh, ex⟩ b).2) k

theorem exAt_zero (fs : List FinField) (b : ℕ) (ex : Array (List Reg)) :
    exAt outs zh fs b ex 0 = ex ∧ baseAt outs zh fs b ex 0 = b := by
  cases fs <;> exact ⟨rfl, rfl⟩

/-- **One step of the fold**: field `k`'s exports, at base `baseAt … k`, are pushed. -/
theorem exAt_succ : ∀ (fs : List FinField) (b : ℕ) (ex : Array (List Reg)) (k : ℕ) (hk : k < fs.length),
    exAt outs zh fs b ex (k + 1) = (exAt outs zh fs b ex k).push
        ((fs[k]'hk) ⟨outs, zh, exAt outs zh fs b ex k⟩ (baseAt outs zh fs b ex k)).2 ∧
      baseAt outs zh fs b ex (k + 1) = baseAt outs zh fs b ex k +
        opsOut ((fs[k]'hk) ⟨outs, zh, exAt outs zh fs b ex k⟩ (baseAt outs zh fs b ex k)).1
  | [], _, _, _, hk => absurd hk (by simp)
  | f :: fs, b, ex, 0, _ => by cases fs <;> exact ⟨rfl, rfl⟩
  | f :: fs, b, ex, k + 1, hk => by
    simp only [exAt, baseAt, List.getElem_cons_succ]
    exact exAt_succ fs _ _ k (by simpa using hk)

end ExAt

/-! ## `finRS`'s exports are its registers (revision 4.1's `gFinRS`) -/

/-- `gFinRS` appends `7 + 4·(1 + 128·8) + 10` registers. -/
theorem opsOut_gFinRS (P : FinP) (fi : FinIn) (b : ℕ) : opsOut (gFinRS P fi b).1 = 4117 := by
  simp only [gFinRS, opsOut_append]
  rw [opsOut_claimOps, opsOut_claimOps, opsOut_claimOps, opsOut_claimOps]
  · simp [opsOut, gRsTail, Op.outs, elemW]
  all_goals intro; rfl

/-- **`gFinRS`'s exports are among its registers.** -/
theorem gFinRS_ex_lt (P : FinP) (fi : FinIn) (b : ℕ) :
    ∀ x ∈ (gFinRS P fi b).2, x < b + opsOut (gFinRS P fi b).1 := by
  rw [opsOut_gFinRS]
  simp only [Reg]
  intro x hx
  simp only [gFinRS, elemW, List.mem_append, List.mem_map, List.mem_range, List.mem_cons,
    List.not_mem_nil, or_false, Nat.reduceMul, Nat.reduceAdd] at hx
  rcases hx with ⟨j, hj, rfl⟩ | rfl
  · have : j * 1025 ≤ 3 * 1025 := Nat.mul_le_mul_right _ (by omega)
    omega
  · omega

variable {impl : OpImpl} {p : KindP} {inp : Input}

/-- **The fields of an accepted run, with their exports**: field `k` of `finalsOf P` runs
(relocated) from `Rs k` with exports `Ex k` (`k + 1` of them) at base `(Rs k).size`, flag `true`;
`Rs (k + 1)` appends its output and `Ex (k + 1)` pushes its exports. -/
theorem fields_ex4 (P : FinP) {tr : Trace}
    (h : semIR impl (gen4 seq4 p (finOps4 P)) inp tr = some true) :
    ∃ y, SkRun4 impl p inp tr y ∧ ∃ (zh : List Reg) (Rs : ℕ → Array Val) (Ex : ℕ → Array (List Reg)),
      (∀ k ≤ 12, ExtA (#[] ++ y.1.toArray) (Rs k)) ∧ (∀ x ∈ zh, x < (Rs 0).size) ∧
      ∀ k (hk : k < 12), (Ex k).size = k + 1 ∧ ∃ L : List Val,
        pureRun impl p.tix inp ((((finalsOf P).rest[k]'(by rw [rest_finalsOf_length]; exact hk))
          ⟨(skeleton4 seq4 p).2.outs, zh, Ex k⟩ (Rs k).size).1.map (reloc P.S)) (Rs k) [] = some (L, true) ∧
        Rs (k + 1) = Rs k ++ L.toArray ∧
        Ex (k + 1) = (Ex k).push (((finalsOf P).rest[k]'(by rw [rest_finalsOf_length]; exact hk))
          ⟨(skeleton4 seq4 p).2.outs, zh, Ex k⟩ (Rs k).size).2 := by
  rw [finOps4_eq] at h
  have hna := noAsk_relocFin P.S (noAsk_finalsOf P)
  obtain ⟨y, hy, hf, hnx, L₀, h0L, Rs, h0, hrest⟩ := accept_chain4 impl seq4 p inp _ hna h
  obtain ⟨hl, hq⟩ := fsQ_gen4 impl inp seq4 p shOK_seq4 _ h
  rw [fsMsgs4_len] at hl hq
  have hlen : (relocFin P.S (finalsOf P)).rest.length = 12 := by
    rw [relocFin_rest, List.length_map, rest_finalsOf_length]
  have hget : ∀ k (hk : k < 12), (relocFin P.S (finalsOf P)).rest[k]'(by rw [hlen]; exact hk) =
      relocF P.S ((finalsOf P).rest[k]'(by rw [rest_finalsOf_length]; exact hk)) := by
    intro k hk; simp only [relocFin_rest, List.getElem_map]
  set fin := relocFin P.S (finalsOf P)
  set outs := (skeleton4 seq4 p).2.outs
  set zh := (fin.finRS ⟨outs, [], #[]⟩ (skeleton4 seq4 p).2.next).2
  set B0 := (skeleton4 seq4 p).2.next + opsOut (fin.finRS ⟨outs, [], #[]⟩ (skeleton4 seq4 p).2.next).1
  -- the files' sizes are the fold's bases
  have hsz : ∀ k ≤ 12, (Rs k).size = baseAt outs zh fin.rest B0 #[zh] k := by
    intro k hk
    induction k with
    | zero =>
      rw [(exAt_zero outs zh _ _ _).2, h0]
      have := pureRun_len impl p.tix inp _ _ [] L₀ true h0L
      simp only [Array.size_append, List.size_toArray, this, List.length_nil, Nat.zero_add, B0, hnx]
    | succ k ih =>
      obtain ⟨L, hL, he⟩ := hrest k (by rw [hlen]; omega)
      have hl' := pureRun_len impl p.tix inp _ _ [] L true hL
      have e1 : (Rs (k + 1)).size = (Rs k).size + L.length := by rw [he]; simp
      rw [e1, hl', List.length_nil, Nat.zero_add,
        (exAt_succ outs zh fin.rest B0 #[zh] k (by rw [hlen]; omega)).2, ← ih (by omega)]
  have hzh : ∀ x ∈ zh, x < (Rs 0).size := by
    rw [hsz 0 (by omega), (exAt_zero outs zh _ _ _).2]
    intro x hx
    have := gFinRS_ex_lt P ⟨outs, [], #[]⟩ (skeleton4 seq4 p).2.next x hx
    simpa only [B0, fin, relocFin, relocF, opsOut_reloc, finalsOf] using this
  have hexs : ∀ k ≤ 12, (exAt outs zh fin.rest B0 #[zh] k).size = k + 1 := by
    intro k hk
    induction k with
    | zero => rw [(exAt_zero outs zh _ _ _).1]; rfl
    | succ k ih =>
      rw [(exAt_succ outs zh fin.rest B0 #[zh] k (by rw [hlen]; omega)).1, Array.size_push, ih (by omega)]
  refine ⟨y, ⟨hy, hf, hl, hq⟩, zh, Rs, fun k => exAt outs zh fin.rest B0 #[zh] k, ?_, hzh,
    fun k hk => ⟨hexs k (by omega), ?_⟩⟩
  · intro k hk
    induction k with
    | zero => rw [h0]; exact ExtA.app _ _
    | succ k ih =>
      obtain ⟨L, -, he⟩ := hrest k (by rw [hlen]; omega)
      rw [he]; exact (ih (by omega)).trans (ExtA.app _ _)
  · obtain ⟨L, hL, he⟩ := hrest k (by rw [hlen]; exact hk)
    have e := hget k hk
    have hs := exAt_succ outs zh fin.rest B0 #[zh] k (by rw [hlen]; exact hk)
    rw [e] at hL hs
    rw [← hsz k (by omega)] at hs
    exact ⟨L, hL, he, hs.1⟩

/-- **`finE`'s `lrEx` are `finLr`'s exports**: with the fold's exports `Ex 3` before `finLr`
(four of them), `Ex 4`'s entry `exLr` is `finLr`'s output list. -/
theorem lrEx_eq4 {Ex3 : Array (List Reg)} (hs : Ex3.size = 4) (e : List Reg) (fi : FinIn)
    (hfi : fi.ex = Ex3.push e) (j : ℕ) : lrEx fi j = e.getD j 0 := by
  rw [lrEx, hfi, exLr, Array.getD_eq_getD_getElem?, Array.getElem?_push, hs, if_pos rfl, Option.getD_some]

end FR.Snd.R4
