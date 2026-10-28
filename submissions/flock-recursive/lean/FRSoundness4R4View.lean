-- New for `flock-recursive` (BLUEPRINT revision 4.1, A.9, A.10; stage R4).
import FRSoundness4R4At

/-!
# Register views of an accepted `gen4` run: squeezes (coordinates, one challenge)

On an accepted run (`SkRun4`), a squeeze phase `n` of `phasesOf seq4` leaves its challenges in the
skeleton's registers, read off the run's Fiat–Shamir entries from `phStart4 n`:

* **`sqz_entries4`**: the phase's answers are the entries' answers (`ansAt`) from `phStart4 n`;
* **`coords_view4`** (`.squeezes k .coords`): `outs[n] = (b + 3k) :: (b + 3⌊x/2⌋ + 1 + x mod 2)_x`,
  register `b + 3⌊x/2⌋ + 1 + x mod 2` holding `chF (ansAt es (phStart4 n + ⌊x/2⌋)) (x mod 2)`;
* **`one_view4`** (`.squeezes 1 .one`): the one out register holds `fAt es (phStart4 n) 0`.
-/

namespace FR.Snd.R4
open RecursionFast Rev4

variable {impl : OpImpl} {p : KindP} {inp : Input}

theorem rd_phase4 {M X : List Val} {R : Array Val} (hext : ExtA (#[] ++ (M ++ X).toArray) R)
    {m : ℕ} (hm : m < X.length) : rd R (M.length + m) = X.getD m default := by
  have hlt : M.length + m < (#[] ++ (M ++ X).toArray).size := by simp; omega
  rw [hext.2 _ hlt, show (#[] : Array Val) ++ (M ++ X).toArray = (#[] ++ M.toArray) ++ X.toArray
    by simp, show M.length = (#[] ++ M.toArray).size by simp, rd_app]

/-- A squeeze phase's answers are the chain's entries from `phStart4 n`. -/
theorem sqz_entries4 {tr trk : Trace} {n k : ℕ} (hn : n < (phasesOf seq4).length) {ch : ChalK}
    (hsh : (phasesOf seq4)[n].2 = .squeezes k ch) (hk : 0 < k) {d : Digest}
    {xs : List Digest × Trace} (hsq : sqzT k d trk = some xs)
    (hdrop : (fsOf tr (itemsOf seq4)).drop (phStart4 n) = fsOf trk (psItems4 seq4 ((phasesOf seq4).drop n))) :
    xs.1.length = k ∧ ∀ l < k, xs.1.getD l zeroD = ansAt (fsOf tr (itemsOf seq4)) (phStart4 n + l) := by
  obtain ⟨seg, hseg, hsl, -, hmap⟩ := sqzT_chain ⟨zeroD, zeroD, ByteArray.empty⟩ hsq 0
  have hit : (phasesOf seq4)[n].2.itemsL seq4.lv = List.replicate k .squeeze := by rw [hsh]; rfl
  rw [List.drop_eq_getElem_cons hn, psItems4, List.flatMap_cons, hit] at hdrop
  obtain ⟨-, hent⟩ := seg_entries hdrop hseg (by simpa using hsl) (replicate_sq_fs k) (by simpa using hk)
  rw [List.length_replicate] at hent
  refine ⟨by rw [← hmap, List.length_map, hsl], fun l hl => ?_⟩
  rw [← hmap, List.getD_eq_getElem _ _ (by simp [hsl, hl]), List.getElem_map, ansAt, entAt,
    ← hent l hl, hseg, List.getD_eq_getElem _ _ (by simp [hsl]; omega),
    List.getElem_append_left (by omega)]

/-- **A coordinates phase on the skeleton's registers.** -/
theorem coords_view4 {tr : Trace} {y : List Val × List Bool × Trace} (h : SkRun4 impl p inp tr y)
    {n : ℕ} (hn : n < (phasesOf seq4).length) {k : ℕ}
    (hsh : (phasesOf seq4)[n].2 = .squeezes k .coords) (hk : 0 < k) :
    ∃ b, (skeleton4 seq4 p).2.outs.getD n [] = (b + 3 * k) ::
        (List.range (2 * k)).map (fun x => b + 3 * (x / 2) + 1 + x % 2) ∧
      b + 3 * k + 1 ≤ (#[] ++ y.1.toArray).size ∧
      ∀ x < 2 * k, rd (#[] ++ y.1.toArray) (b + 3 * (x / 2) + 1 + x % 2) =
        .f (chF (ansAt (fsOf tr (itemsOf seq4)) (phStart4 n + x / 2)) (x % 2)) := by
  obtain ⟨trk, M, x, hx, hb, -, hext, -, hdrop, -⟩ := phase_at4 impl p.tix inp p h.ref hn
  generalize hph : (phasesOf seq4)[n] = ph at hx hsh
  obtain ⟨name, sh⟩ := ph
  simp only at hsh; subst hsh
  simp only [refPhase4] at hx
  obtain ⟨xs, hxs, rfl⟩ := Option.map_eq_some_iff.1 hx
  obtain ⟨hl, hans⟩ := sqz_entries4 hn (by rw [hph]) hk hxs hdrop
  dsimp only at hext
  have hsz := hext.1
  simp only [Array.size_append, List.size_toArray, List.length_append, coordVals_length, hl,
    List.length_singleton, List.size_toArray] at hsz
  refine ⟨M.length, ?_, by simp only [Array.size_append, List.size_toArray] at hsz ⊢; omega,
    fun v hv => ?_⟩
  · rw [skeleton4_outs seq4 p hn, hph]; simp [genPhase4, hb]
  · have h3 : 3 * (v / 2) + (1 + v % 2) < (xs.1.flatMap coordVals).length := by
      rw [coordVals_length, hl]; omega
    rw [show M.length + 3 * (v / 2) + 1 + v % 2 = M.length + (3 * (v / 2) + (1 + v % 2)) by ring,
      rd_phase4 hext (by simp only [List.length_append]; omega),
      List.getD_append _ _ _ _ h3, flatMap_coord_getD _ _ _ (by omega) (by omega), hans _ (by omega)]
    rcases Nat.mod_two_eq_zero_or_one v with h0 | h1
    · rw [h0]; rfl
    · rw [h1]; rfl

/-- **A one-challenge squeeze on the skeleton's registers** (`L1`, `L3β`, `Lr3`, `E3`, `B′`): its
one out register holds `fAt es (phStart4 n) 0`. -/
theorem one_view4 {tr : Trace} {y : List Val × List Bool × Trace} (h : SkRun4 impl p inp tr y)
    {n : ℕ} (hn : n < (phasesOf seq4).length) (hsh : (phasesOf seq4)[n].2 = .squeezes 1 .one) :
    ∃ b, (skeleton4 seq4 p).2.outs.getD n [] = [b] ∧ b < (#[] ++ y.1.toArray).size ∧
      rd (#[] ++ y.1.toArray) b = .f (fAt (fsOf tr (itemsOf seq4)) (phStart4 n) 0) := by
  obtain ⟨trk, M, x, hx, hb, -, hext, -, hdrop, -⟩ := phase_at4 impl p.tix inp p h.ref hn
  generalize hph : (phasesOf seq4)[n] = ph at hx hsh
  obtain ⟨name, sh⟩ := ph
  simp only at hsh; subst hsh
  simp only [refPhase4] at hx
  obtain ⟨xs, hxs, rfl⟩ := Option.map_eq_some_iff.1 hx
  obtain ⟨hl, hans⟩ := sqz_entries4 hn (by rw [hph]) (by norm_num) hxs hdrop
  dsimp only at hext
  have hsz := hext.1
  simp only [Array.size_append, List.size_toArray, List.length_append, List.length_map, hl,
    List.length_singleton] at hsz
  refine ⟨M.length + 1, ?_, by dsimp only [Reg]; simp at hsz ⊢; omega, ?_⟩
  · rw [skeleton4_outs seq4 p hn, hph]; simp [genPhase4, hb]
  · rw [rd_phase4 hext (by simp [hl]), List.getD_append_right _ _ _ _ (by simp [hl]),
      List.length_map, hl, Nat.sub_self, List.getD_cons_zero, fAt]
    obtain ⟨a, ha⟩ : ∃ a, xs.1 = [a] := List.length_eq_one_iff.1 hl
    have h0 := hans 0 (by norm_num)
    rw [ha, Nat.add_zero, List.getD_cons_zero] at h0
    rw [ha, List.headD_cons, h0]

end FR.Snd.R4
