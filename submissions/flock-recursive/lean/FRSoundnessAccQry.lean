-- New for `flock-recursive` (BLUEPRINT §3, A.4, A.9, §5.1; stage S-G4, `hFin` step 2b).
import FRSoundnessAccEq

/-!
# `hFin`, step 2b: the squeezes and the queries of the accepted skeleton, on the log

* **`posAllT_path`**: an accepted run of a level's positions leaves, per position, the index
  register (`.n j`) and the fold register (`.k (dotKF w col)`), and its Merkle checks are a path
  from the column to the cap entry on any log that contains the trace and repeats no query:
  `(openPath (frEnc i) col j ss).runLog L = some capD` (`stepsT_path`, `posT_path`).
* **`squeezes_view`**: a squeeze phase's answers are the chain's entries from `phStart n`.
* `phStart_succ`: a phase's Fiat–Shamir items advance `phStart`.
-/

namespace FR.Snd
open RecursionFast FR.Merkle

/-! ## Merkle paths from the trace -/

/-- On a log that repeats no query, an entry is the first one for its query. -/
theorem find_of_mem {L : Log} (hL : (L.map Prod.fst).Nodup) {e : ByteArray × Digest}
    (he : e ∈ L) : L.find? (fun x => decide (x.1 = e.1)) = some e := by
  obtain ⟨e', he'⟩ := Option.isSome_iff_exists.mp
    (List.find?_isSome.mpr ⟨e, he, by simp⟩ : (L.find? fun x => decide (x.1 = e.1)).isSome)
  have hm := List.mem_of_find?_eq_some he'
  have hq : e'.1 = e.1 := by simpa using List.find?_some he'
  rw [he', List.inj_on_of_nodup_map hL hm he hq]

theorem runLog_query_mem {α : Type} {L : Log} (hL : (L.map Prod.fst).Nodup) {q : ByteArray}
    {a : Digest} (he : (q, a) ∈ L) (k : Digest → OProg α) :
    (OProg.query q k).runLog L = (k a).runLog L := by
  simp only [OProg.runLog]
  rw [show (fun e : ByteArray × Digest => decide (e.1 = q)) = fun x => decide (x.1 = (q, a).1)
    from rfl, find_of_mem hL he, Option.bind_some]

variable (κ : Kind) (inp : Input)

/-- **The Merkle steps are a climb on the log**: from depth `h`, the steps that the kind has
(`h < sib`) asked node queries whose answers the climb reads back. -/
theorem stepsT_path {L : Log} (hL : (L.map Prod.fst).Nodup) {i j : ℕ} :
    ∀ (n h so : ℕ) (cur : Digest) (tr : Trace) (x : List Val × Bool × Digest × Trace),
      stepsT κ inp i j n h so cur tr = some x → (∀ e ∈ tr, e ∈ L) → (lvl κ i).sib ≤ h + n →
      ∃ ss : List Digest, ss.length = (lvl κ i).sib - h ∧
        (climb (frEnc i) j h cur ss).runLog L = some x.2.2.1
  | 0, h, _, cur, tr, x, hx, _, hs => by
    simp only [stepsT, Option.some.injEq] at hx; subst hx
    exact ⟨[], by simp; omega, rfl⟩
  | n + 1, h, so, cur, (q, a) :: tr, x, hx, hin, hs => by
    simp only [stepsT, Option.bind_eq_some_iff, Option.map_eq_some_iff] at hx
    obtain ⟨z, hz, y, hy, rfl⟩ := hx
    simp only [stepT, Option.ite_none_right_eq_some] at hz
    obtain ⟨hq, hz⟩ := hz
    simp only [Option.some.injEq] at hz; subst hz
    have hin' : ∀ e ∈ tr, e ∈ L := fun e he => hin e (List.mem_cons_of_mem _ he)
    have hmem : (q, a) ∈ L := hin _ (List.mem_cons_self ..)
    by_cases hact : h < (lvl κ i).sib
    · simp only [hact, decide_true, ite_true] at hq hy ⊢
      obtain ⟨ss, hl, hr⟩ := stepsT_path hL n (h + 1) _ a tr y hy hin' (by omega)
      refine ⟨bytesAt inp.π (absOff fSibs so) 32 :: ss, by simp [hl]; omega, ?_⟩
      have hm' : (stepQ (frEnc i) j h cur (bytesAt inp.π (absOff fSibs so) 32), a) ∈ L := by
        convert hmem using 2; rw [hq]; simp only [stepQ, frEnc]; split_ifs <;> rfl
      rw [climb, runLog_query_mem hL hm']
      exact hr
    · simp only [hact, decide_false, Bool.false_eq_true, ite_false] at hy ⊢
      obtain ⟨ss, hl, hr⟩ := stepsT_path hL n (h + 1) _ cur tr y hy hin' (by omega)
      have hss : ss = [] := List.eq_nil_of_length_eq_zero (by omega)
      subst hss
      exact ⟨[], by simp; omega, by simpa [climb] using hr⟩
  | _ + 1, _, _, _, [], x, hx, _, _ => by simp [stepsT, stepT] at hx

/-- **One position on the log**: the index and fold registers, and a path from the opened column
to the cap entry `capD` on the log. -/
theorem posT_path {L : Log} (hL : (L.map Prod.fst).Nodup) {i co so p : ℕ} {ad : ℕ → Digest}
    {w : Array K} {tr : Trace} {x : List Val × Bool × Trace}
    (hx : posT κ inp i co so ad w p tr = some x) (hin : ∀ e ∈ tr, e ∈ L)
    (hsib : (lvl κ i).sib ≤ (lvlStar i).sib) (hok : x.2.1 = true) :
    let j := idxOf (lvl κ i).logN (ad (p / (lvl κ i).per)) (p % (lvl κ i).per)
    let col := inp.π.extract (absOff fCols (co + p * colBytes i))
      (absOff fCols (co + p * colBytes i) + colBytes i)
    x.1.getD 0 default = .n j ∧ x.1.getD 3 default = .k (dotKF w col) ∧
      (∃ ss : List Digest, ss.length = (lvl κ i).sib ∧ (openPath (frEnc i) col j ss).runLog L =
        some (bytesAt inp.π (absOff fCaps (capOff i) + 32 * (j >>> (lvl κ i).sib)) 32)) ∧
      ∃ seg, tr = seg ++ x.2.2 := by
  intro j col
  rcases tr with _ | ⟨⟨q, a⟩, tr⟩
  · cases hx
  simp only [posT] at hx
  split_ifs at hx with hq
  obtain ⟨y, hy, rfl⟩ := Option.map_eq_some_iff.1 hx
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hok
  obtain ⟨ss, hl, hr⟩ := stepsT_path κ inp hL _ 0 _ a tr y hy
    (fun e he => hin e (List.mem_cons_of_mem _ he)) (by omega)
  obtain ⟨seg, hseg, -⟩ := stepsT_len inp κ hy
  refine ⟨rfl, rfl, ⟨ss, by simpa using hl, ?_⟩, ⟨(q, a) :: seg, by simp [hseg]⟩⟩
  have hmem : (q, a) ∈ L := hin _ (List.mem_cons_self ..)
  rw [openPath, runLog_query_mem hL (show ((frEnc i).colQ col, a) ∈ L by rw [hq] at hmem; exact hmem),
    hr, hok.2]

/-- **All positions of a level on the log** (`posAllT` from position `p`). -/
theorem posAllT_path {L : Log} (hL : (L.map Prod.fst).Nodup) {i co so : ℕ} {ad : ℕ → Digest}
    {w : Array K} (hsib : (lvl κ i).sib ≤ (lvlStar i).sib) :
    ∀ (t p : ℕ) (tr : Trace) (x : List Val × Bool × Trace),
      posAllT κ inp i co so ad w t p tr = some x → (∀ e ∈ tr, e ∈ L) → x.2.1 = true →
      ∀ q < t,
        x.1.getD (posW i * q) default =
          .n (idxOf (lvl κ i).logN (ad ((p + q) / (lvl κ i).per)) ((p + q) % (lvl κ i).per)) ∧
        x.1.getD (posW i * q + 3) default = .k (dotKF w (inp.π.extract
          (absOff fCols (co + (p + q) * colBytes i))
          (absOff fCols (co + (p + q) * colBytes i) + colBytes i))) ∧
        ∃ ss : List Digest, ss.length = (lvl κ i).sib ∧
          (openPath (frEnc i) (inp.π.extract (absOff fCols (co + (p + q) * colBytes i))
            (absOff fCols (co + (p + q) * colBytes i) + colBytes i))
            (idxOf (lvl κ i).logN (ad ((p + q) / (lvl κ i).per)) ((p + q) % (lvl κ i).per))
            ss).runLog L =
          some (bytesAt inp.π (absOff fCaps (capOff i) + 32 *
            (idxOf (lvl κ i).logN (ad ((p + q) / (lvl κ i).per)) ((p + q) % (lvl κ i).per) >>>
              (lvl κ i).sib)) 32)
  | 0, _, _, _, _, _, _, q, hq => absurd hq (by omega)
  | t + 1, p, tr, x, hx, hin, hok, q, hq => by
    simp only [posAllT, Option.bind_eq_some_iff, Option.map_eq_some_iff] at hx
    obtain ⟨z, hz, y, hy, rfl⟩ := hx
    simp only [Bool.and_eq_true] at hok
    obtain ⟨h0, h3, hpath, seg, hseg⟩ := posT_path κ inp hL hz hin hsib hok.1
    have hzl := posT_length κ inp hz
    rcases q with _ | q
    · refine ⟨?_, ?_, ?_⟩
      · rw [Nat.mul_zero, List.getD_append _ _ _ _ (by rw [hzl, posW]; omega)]; simpa using h0
      · rw [Nat.mul_zero, Nat.zero_add, List.getD_append _ _ _ _ (by rw [hzl, posW]; omega)]
        simpa using h3
      · simpa using hpath
    · obtain ⟨i0, i3, ip⟩ := posAllT_path hL hsib t (p + 1) _ y hy
        (fun e he => hin e (by rw [hseg]; exact List.mem_append_right _ he)) hok.2 q (by omega)
      rw [show p + (q + 1) = p + 1 + q by omega]
      refine ⟨?_, ?_, ip⟩
      · rw [show posW i * (q + 1) = z.1.length + posW i * q by rw [hzl]; ring,
          List.getD_append_right _ _ _ _ (by omega), Nat.add_sub_cancel_left, i0]
      · rw [show posW i * (q + 1) + 3 = z.1.length + (posW i * q + 3) by rw [hzl]; ring,
          List.getD_append_right _ _ _ _ (by omega), Nat.add_sub_cancel_left, i3]

end FR.Snd
