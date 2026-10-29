-- New for `flock-recursive` (BLUEPRINT revision 4.1, A.9 the finals; stage R4e).
import FRSoundness4R4Ex

/-!
# One accepted run, every field: `Fields4`

`fields_ex4` gives each field's run, but its `zhat` registers and register files are existential:
two calls cannot be joined. **`Fields4`** packages one choice of them, together with `finRS`'s run
(its exports are the `zhat` registers, its file `Rs 0`'s prefix), so the checks of several fields
(`finRS`'s `α_j` with `finZ`'s, `finLc`'s, `finSh`'s, `finE`'s bindings) can be read on the same
registers. **`fields4_of_accept`**: an accepted run has one. **`field_run4`**: field `k`'s
relocated run from `Rs k`, flag `true`. Revision 4.4.1: `cap`, the batched cap check's run from
`Rs 12` (after every field), flag `true`.
-/

namespace FR.Snd.R4
open RecursionFast Rev4

/-- **An accepted run's fields**: the skeleton's run `y`, `finRS`'s run from the skeleton's file
(exports `zh`, file `Rs 0`), and field `k` of the rest from `Rs k` with exports `Ex k`. -/
structure Fields4 (impl : OpImpl) (p : KindP) (inp : Input) (tr : Trace) (P : FinP)
    (y : List Val × List Bool × Trace) (zh : List Reg) (Rs : ℕ → Array Val)
    (Ex : ℕ → Array (List Reg)) : Prop where
  sk : SkRun4 impl p inp tr y
  ext : ∀ k ≤ 12, ExtA (#[] ++ y.1.toArray) (Rs k)
  zlt : ∀ x ∈ zh, x < (Rs 0).size
  zh_eq : zh = ((finalsOf P).finRS ⟨(skeleton4 seq4 p).2.outs, [], #[]⟩ (#[] ++ y.1.toArray).size).2
  rs : ∃ L₀ : List Val, pureRun impl p.tix inp
      (((finalsOf P).finRS ⟨(skeleton4 seq4 p).2.outs, [], #[]⟩ (#[] ++ y.1.toArray).size).1.map
        (reloc P.S)) (#[] ++ y.1.toArray) [] = some (L₀, true) ∧
    Rs 0 = (#[] ++ y.1.toArray) ++ L₀.toArray
  fld : ∀ k (hk : k < 12), (Ex k).size = k + 1 ∧ ∃ L : List Val,
    pureRun impl p.tix inp ((((finalsOf P).rest[k]'(by rw [rest_finalsOf_length]; exact hk))
      ⟨(skeleton4 seq4 p).2.outs, zh, Ex k⟩ (Rs k).size).1.map (reloc P.S)) (Rs k) [] = some (L, true) ∧
    Rs (k + 1) = Rs k ++ L.toArray ∧
    Ex (k + 1) = (Ex k).push (((finalsOf P).rest[k]'(by rw [rest_finalsOf_length]; exact hk))
      ⟨(skeleton4 seq4 p).2.outs, zh, Ex k⟩ (Rs k).size).2
  /-- The batched cap check (revision 4.4.1) runs from `Rs 12`, flag `true`. -/
  cap : ∃ L : List Val, pureRun impl p.tix inp
    ((capChkOps P.S (skeleton4 seq4 p).2.outs (Rs 12).size).map (reloc P.S)) (Rs 12) [] = some (L, true)

variable {impl : OpImpl} {p : KindP} {inp : Input}

/-- **An accepted run has its fields** (`fields_ex4` with `finRS`'s run kept). -/
theorem fields4_of_accept (P : FinP) {tr : Trace}
    (h : semIR impl (gen4 seq4 p (finOps4 P)) inp tr = some true) :
    ∃ y zh Rs Ex, Fields4 impl p inp tr P y zh Rs Ex := by
  rw [finOps4_eq] at h
  obtain ⟨y, hy, hf, hnx, L₀, h0L, Rs, h0, hrest⟩ := accept_chain4 impl seq4 p inp _ _ (noAsk_finOps4 P) h
  obtain ⟨hl, hq⟩ := fsQ_gen4 impl inp seq4 p shOK_seq4 _ h
  rw [fsMsgs4_len] at hl hq
  set fs := (relocFin P.S (finalsOf P)).rest ++ [capF P.S] with hfs
  have hlen : fs.length = 13 := by
    rw [hfs, List.length_append, relocFin_rest, List.length_map, rest_finalsOf_length]; rfl
  have hget : ∀ k (hk : k < 12), fs[k]'(by rw [hlen]; omega) =
      relocF P.S ((finalsOf P).rest[k]'(by rw [rest_finalsOf_length]; exact hk)) := by
    intro k hk
    simp only [hfs]
    rw [List.getElem_append_left (by rw [relocFin_rest, List.length_map, rest_finalsOf_length]; exact hk)]
    simp only [relocFin_rest, List.getElem_map]
  have hcap : fs[12]'(by rw [hlen]; omega) = capF P.S := by
    simp only [hfs]
    rw [List.getElem_append_right (by rw [relocFin_rest, List.length_map, rest_finalsOf_length])]
    simp [relocFin_rest, rest_finalsOf_length]
  set fin := relocFin P.S (finalsOf P)
  set outs := (skeleton4 seq4 p).2.outs
  set zh := (fin.finRS ⟨outs, [], #[]⟩ (skeleton4 seq4 p).2.next).2
  set B0 := (skeleton4 seq4 p).2.next + opsOut (fin.finRS ⟨outs, [], #[]⟩ (skeleton4 seq4 p).2.next).1
  have hsz : ∀ k ≤ 12, (Rs k).size = baseAt outs zh fs B0 #[zh] k := by
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
        (exAt_succ outs zh fs B0 #[zh] k (by rw [hlen]; omega)).2, ← ih (by omega)]
  have hzh : ∀ x ∈ zh, x < (Rs 0).size := by
    rw [hsz 0 (by omega), (exAt_zero outs zh _ _ _).2]
    intro x hx
    have := gFinRS_ex_lt P ⟨outs, [], #[]⟩ (skeleton4 seq4 p).2.next x hx
    simpa only [B0, fin, relocFin, relocF, opsOut_reloc, finalsOf] using this
  have hexs : ∀ k ≤ 12, (exAt outs zh fs B0 #[zh] k).size = k + 1 := by
    intro k hk
    induction k with
    | zero => rw [(exAt_zero outs zh _ _ _).1]; rfl
    | succ k ih =>
      rw [(exAt_succ outs zh fs B0 #[zh] k (by rw [hlen]; omega)).1, Array.size_push, ih (by omega)]
  refine ⟨y, zh, Rs, fun k => exAt outs zh fs B0 #[zh] k, ⟨⟨hy, hf, hl, hq⟩, ?_, hzh,
    by rw [← hnx]; rfl, ⟨L₀, by rw [← hnx]; exact h0L, h0⟩, fun k hk => ⟨hexs k (by omega), ?_⟩, ?_⟩⟩
  · intro k hk
    induction k with
    | zero => rw [h0]; exact ExtA.app _ _
    | succ k ih =>
      obtain ⟨L, -, he⟩ := hrest k (by rw [hlen]; omega)
      rw [he]; exact (ih (by omega)).trans (ExtA.app _ _)
  · obtain ⟨L, hL, he⟩ := hrest k (by rw [hlen]; omega)
    have e := hget k hk
    have hs := exAt_succ outs zh fs B0 #[zh] k (by rw [hlen]; omega)
    rw [e] at hL hs
    rw [← hsz k (by omega)] at hs
    exact ⟨L, hL, he, hs.1⟩
  · obtain ⟨L, hL, -⟩ := hrest 12 (by rw [hlen]; omega)
    rw [hcap] at hL
    exact ⟨L, hL⟩

section F
variable {tr : Trace} {P : FinP} {y : List Val × List Bool × Trace} {zh : List Reg}
  {Rs : ℕ → Array Val} {Ex : ℕ → Array (List Reg)} (hF : Fields4 impl p inp tr P y zh Rs Ex)
include hF

/-- The files extend each other. -/
theorem Fields4.chain {j k : ℕ} (hjk : j ≤ k) (hk : k ≤ 12) : ExtA (Rs j) (Rs k) := by
  have hch : ∀ k < 12, ExtA (Rs k) (Rs (k + 1)) := fun k hk => by
    obtain ⟨-, L, -, he, -⟩ := hF.fld k hk; rw [he]; exact ExtA.app _ _
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hjk
  induction d with
  | zero => exact ⟨le_rfl, fun _ _ => rfl⟩
  | succ d ih => exact (ih (by omega) (by omega)).trans (hch _ (by omega))

/-- The `zhat` registers lie in every file. -/
theorem Fields4.zlt' {k : ℕ} (hk : k ≤ 12) : ∀ x ∈ zh, x < (Rs k).size :=
  fun x hx => Nat.lt_of_lt_of_le (hF.zlt x hx) (hF.chain (Nat.zero_le k) hk).1

/-- A named register of field `k`'s input lies in its file. -/
theorem Fields4.sk_lt {k : ℕ} (hk : k ≤ 12) (ex : Array (List Reg)) :
    ∀ name, ∀ x ∈ outsOf ⟨(skeleton4 seq4 p).2.outs, zh, ex⟩ name, x < (Rs k).size :=
  fun name x hx => Nat.lt_of_lt_of_le (outsOf_lt4 (p := p) hF.sk zh ex name x hx) (hF.ext k hk).1

theorem Fields4.pos {k : ℕ} (hk : k ≤ 12) : 0 < (Rs k).size :=
  lt_of_lt_of_le (skel_pos4 hF.sk) (hF.ext k hk).1

end F

end FR.Snd.R4
