-- New for `flock-recursive` (BLUEPRINT §3, A.4, A.9; stage S-G4, `hFin` step 2b).
-- RET-2: the declarations revision 4.1 reads moved to `FRSoundnessCoreAcc`.
import FRSoundnessAccQry
import FRSoundness4P4aSeg

/-!
# `hFin`, step 2b: the squeeze, query and final-message phases on the log

On an accepted skeleton (`SkRun`):

* **`pos_view`** (`.squeezes k (.pos i)`, P2.i): the out list is `b, …, b + k − 1`, the next
  context's `posAns`; register `b + l` holds the chain's answer at `phStart n + l`.
* **`coords_view`** (`.squeezes k (.coords _)`, P3.i): register `b + 3(x/2) + 1 + x%2` holds F
  coordinate `x % 2` of the answer at `phStart n + x/2`.
* **`queries_view`** (`.queries i`, Q.i): the out list is the fold registers; per position, the
  index register, the fold `dotKF (eqTab fr) col` and a Merkle path from the column to the cap
  entry on the log.
* **`final_view`** (row 47, the final message): a 30-kind's final message is zero past its
  `2^5` elements (`finV_zero`).
-/

namespace FR.Snd
open RecursionFast FR.Merkle

variable {impl : OpImpl} {κ : Kind} {inp : Input}

/-! ## The generator's outs and context -/

theorem genPhase_absorb {n : ℕ} {p : Phase} (c : GCtx) {f len : ℕ} (hsh : p.shape = .absorb f len) :
    (genPhase n p c).2.foldR = c.foldR := by
  obtain ⟨name, sh⟩ := p
  simp only at hsh; subst hsh
  simp only [genPhase]; split_ifs <;> rfl

theorem genPhase_pos {n : ℕ} {p : Phase} (c : GCtx) {k i : ℕ}
    (hsh : p.shape = .squeezes k (.pos i)) :
    (genPhase n p c).2.foldR = c.foldR ∧
      (genPhase n p c).2.posAns = (List.range k).map (c.next + ·) ∧
      (genPhase n p c).2.outs.back?.getD [] = (List.range k).map (c.next + ·) := by
  obtain ⟨name, sh⟩ := p
  simp only at hsh; subst hsh
  simp [genPhase]

theorem genPhase_coords {n : ℕ} {p : Phase} (c : GCtx) {k : ℕ} {nf : Kind → ℕ}
    (hsh : p.shape = .squeezes k (.coords nf)) :
    (genPhase n p c).2.outs.back?.getD [] = (c.next + 3 * k) ::
      (List.range (2 * k)).map (fun x => c.next + 3 * (x / 2) + 1 + x % 2) := by
  obtain ⟨name, sh⟩ := p
  simp only at hsh; subst hsh
  simp [genPhase]

theorem genPhase_queries {n : ℕ} {p : Phase} (c : GCtx) {i : ℕ} (hsh : p.shape = .queries i) :
    (genPhase n p c).2.outs.back?.getD [] =
      (List.range (lvlStar i).t).map (fun p => c.next + 2 + posW i * p + 3) := by
  obtain ⟨name, sh⟩ := p
  simp only at hsh; subst hsh
  simp [genPhase]

/-! ## Reading a phase's registers on the skeleton's -/

theorem rd_phase {M X : List Val} {R : Array Val} (hext : ExtA (#[] ++ (M ++ X).toArray) R)
    {m : ℕ} (hm : m < X.length) : rd R (M.length + m) = X.getD m default := by
  have hlt : M.length + m < (#[] ++ (M ++ X).toArray).size := by simp; omega
  rw [hext.2 _ hlt, show (#[] : Array Val) ++ (M ++ X).toArray = (#[] ++ M.toArray) ++ X.toArray
    by simp, show M.length = (#[] ++ M.toArray).size by simp, rd_app]

theorem rd_pre {M X : List Val} {R : Array Val} (hext : ExtA (#[] ++ (M ++ X).toArray) R)
    {x : ℕ} (hx : x < M.length) : rd R x = rd (#[] ++ M.toArray) x := by
  have hlt : x < (#[] ++ (M ++ X).toArray).size := by simp; omega
  rw [hext.2 _ hlt, show (#[] : Array Val) ++ (M ++ X).toArray = (#[] ++ M.toArray) ++ X.toArray
    by simp, rd_app_left _ _ (by simpa using hx)]

/-! ## Squeezes -/

/-- A squeeze phase's answers are the chain's entries from `phStart n`. -/
theorem sqz_entries {tr trk : Trace} {n k : ℕ} (hn : n < phases.length) {ch : Chal}
    (hsh : phases[n].shape = .squeezes k ch) (hk : 0 < k) {d : Digest}
    {xs : List Digest × Trace} (hsq : sqzT k d trk = some xs)
    (hdrop : (fsOf tr items).drop (phStart n) = fsOf trk (psItems (phases.drop n))) :
    xs.1.length = k ∧ ∀ l < k, xs.1.getD l zeroD = ansAt (fsOf tr items) (phStart n + l) := by
  obtain ⟨seg, hseg, hsl, -, hmap⟩ := sqzT_chain ⟨zeroD, zeroD, ByteArray.empty⟩ hsq 0
  have hit : phases[n].shape.items = List.replicate k .squeeze := by rw [hsh]; rfl
  obtain ⟨-, hent⟩ := phase_entries hn hdrop hseg (by rw [hit]; simpa using hsl)
    (by rw [hit]; exact replicate_sq_fs k) (by rw [hit]; simpa using hk)
  rw [hit, List.length_replicate] at hent
  refine ⟨by rw [← hmap, List.length_map, hsl], fun l hl => ?_⟩
  rw [← hmap, List.getD_eq_getElem _ _ (by simp [hsl, hl]), List.getElem_map, ansAt, entAt,
    ← hent l hl, hseg, List.getD_eq_getElem _ _ (by simp [hsl]; omega),
    List.getElem_append_left (by omega)]

/-- **P2's answers on the skeleton's registers** (`.squeezes k (.pos i)`). -/
theorem pos_view {tr : Trace} {y : List Val × List Bool × Trace} (h : SkRun impl κ inp tr y)
    {n : ℕ} (hn : n < phases.length) {k i : ℕ} (hsh : phases[n].shape = .squeezes k (.pos i))
    (hk : 0 < k) :
    ∃ b, skeleton.2.outs.getD n [] = (List.range k).map (b + ·) ∧
      (cAt (n + 1)).posAns = (List.range k).map (b + ·) ∧ (cAt (n + 1)).foldR = (cAt n).foldR ∧
      b + k ≤ (#[] ++ y.1.toArray).size ∧
      ∀ l < k, rd (#[] ++ y.1.toArray) (b + l) = .d (ansAt (fsOf tr items) (phStart n + l)) := by
  obtain ⟨trk, M, x, hx, hb, -, hext, -, hdrop, -⟩ := phase_at impl κ inp h.ref hn
  simp only [refPhase, hsh] at hx
  obtain ⟨xs, hxs, rfl⟩ := Option.map_eq_some_iff.1 hx
  obtain ⟨hl, hans⟩ := sqz_entries hn hsh hk hxs hdrop
  obtain ⟨g1, g2, g3⟩ := genPhase_pos (n := n) (cAt n) hsh
  have hsz := size_le_of_ext hext
  simp only [List.length_map, hl] at hsz
  refine ⟨M.length, ?_, ?_, ?_, hsz, fun l hlk => ?_⟩
  · rw [skeleton_outs hn, g3, hb]
  · rw [cAt_succ hn, g2, hb]
  · rw [cAt_succ hn, g1]
  · rw [rd_phase hext (by simp [hl, hlk]), List.getD_eq_getElem _ _ (by simp [hl, hlk]),
      List.getElem_map, ← hans l hlk, List.getD_eq_getElem _ _ (by simp [hl, hlk])]

/-- **P3's coordinates on the skeleton's registers** (`.squeezes k (.coords _)`). -/
theorem coords_view {tr : Trace} {y : List Val × List Bool × Trace} (h : SkRun impl κ inp tr y)
    {n : ℕ} (hn : n < phases.length) {k : ℕ} {nf : Kind → ℕ}
    (hsh : phases[n].shape = .squeezes k (.coords nf)) (hk : 0 < k) :
    ∃ b, skeleton.2.outs.getD n [] = (b + 3 * k) ::
        (List.range (2 * k)).map (fun x => b + 3 * (x / 2) + 1 + x % 2) ∧
      b + 3 * k + 1 ≤ (#[] ++ y.1.toArray).size ∧
      ∀ x < 2 * k, rd (#[] ++ y.1.toArray) (b + 3 * (x / 2) + 1 + x % 2) =
        .f (chF (ansAt (fsOf tr items) (phStart n + x / 2)) (x % 2)) := by
  obtain ⟨trk, M, x, hx, hb, -, hext, -, hdrop, -⟩ := phase_at impl κ inp h.ref hn
  simp only [refPhase, hsh] at hx
  obtain ⟨xs, hxs, rfl⟩ := Option.map_eq_some_iff.1 hx
  obtain ⟨hl, hans⟩ := sqz_entries hn hsh hk hxs hdrop
  have hsz := size_le_of_ext hext
  simp only [List.length_append, coordVals_length, hl, List.length_singleton] at hsz
  refine ⟨M.length, ?_, by omega, fun v hv => ?_⟩
  · rw [skeleton_outs hn, genPhase_coords (cAt n) hsh, hb]
  · have h3 : 3 * (v / 2) + (1 + v % 2) < (xs.1.flatMap coordVals).length := by
      rw [coordVals_length, hl]; omega
    rw [show M.length + 3 * (v / 2) + 1 + v % 2 = M.length + (3 * (v / 2) + (1 + v % 2)) by ring,
      rd_phase hext (by simp only [List.length_append]; omega),
      List.getD_append _ _ _ _ h3, flatMap_coord_getD _ _ _ (by omega) (by omega), hans _ (by omega)]
    rcases Nat.mod_two_eq_zero_or_one v with h0 | h1
    · rw [h0]; rfl
    · rw [h1]; rfl

/-! ## The queries -/

/-- **Q.i on the skeleton's registers and the log** (`.queries i`): with `fr` P1.i's challenges
(the context's `foldR`) and `ad` P2.i's answers (`posAns`), per position `q`: the index
register `b + 2 + posW·q`, the fold register `+ 3` holding `dotKF (eqTab fr) col_q`, and a path
on `L` from `col_q` to its cap entry. -/
theorem queries_view {tr : Trace} {y : List Val × List Bool × Trace} (h : SkRun impl κ inp tr y)
    {L : Log} (hL : (L.map Prod.fst).Nodup) (hin : ∀ e ∈ tr, e ∈ L)
    {n : ℕ} (hn : n < phases.length) {i : ℕ} (hsh : phases[n].shape = .queries i)
    (hsib : (lvl κ i).sib ≤ (lvlStar i).sib) :
    ∃ b, skeleton.2.outs.getD n [] =
        (List.range (lvlStar i).t).map (fun p => b + 2 + posW i * p + 3) ∧
      b + 2 + posW i * (lvlStar i).t ≤ (#[] ++ y.1.toArray).size ∧
      ∀ q < (lvlStar i).t,
        let fr := (((cAt n).foldR.map fun x => (rd (#[] ++ y.1.toArray) x).toK)).toArray
        let ad := fun k => (rd (#[] ++ y.1.toArray) ((cAt n).posAns.getD k 0)).toD
        let col := inp.π.extract (absOff fCols (phaseOff n fCols + q * colBytes i))
          (absOff fCols (phaseOff n fCols + q * colBytes i) + colBytes i)
        let j := idxOf (lvl κ i).logN (ad (q / (lvl κ i).per)) (q % (lvl κ i).per)
        rd (#[] ++ y.1.toArray) (b + 2 + posW i * q) = .n j ∧
        rd (#[] ++ y.1.toArray) (b + 2 + posW i * q + 3) = .k (dotKF (eqTab fr) col) ∧
        ∃ ss : List Digest, ss.length = (lvl κ i).sib ∧ (openPath (frEnc i) col j ss).runLog L =
          some (bytesAt inp.π (absOff fCaps (capOff i) + 32 * (j >>> (lvl κ i).sib)) 32) := by
  obtain ⟨trk, M, x, hx, hb, hwf, hext, hflag, -, A, hA⟩ := phase_at impl κ inp h.ref hn
  have hc : CtxOk (cAt n) (#[] ++ M.toArray) := by
    rcases hwf with ⟨h', -⟩ | h'
    · rw [hsh] at h'; cases h'
    · exact h'
  simp only [refPhase, hsh] at hx
  obtain ⟨xq, hxq, rfl⟩ := Option.map_eq_some_iff.1 hx
  have hok : xq.2.1 = true := h.flags _ hflag
  have hql := posAllT_length κ inp hxq
  have hsz := size_le_of_ext hext
  rw [List.length_append, hql] at hsz
  simp only [List.length_cons, List.length_nil] at hsz
  have hM0 : 0 < M.length := by
    rcases M with _ | ⟨m, M⟩
    · exact absurd hc.1 (by simp)
    · simp
  -- the context's registers read the same on the skeleton's registers
  have hfr : (cAt n).foldR.map (fun x => (rd (#[] ++ M.toArray) x).toK) =
      (cAt n).foldR.map (fun x => (rd (#[] ++ y.1.toArray) x).toK) :=
    List.map_congr_left fun x hx => by
      rw [rd_pre hext (by simpa using hc.2.2.2.1 x hx)]
  have had : (fun k => (rd (#[] ++ M.toArray) ((cAt n).posAns.getD k 0)).toD) =
      fun k => (rd (#[] ++ y.1.toArray) ((cAt n).posAns.getD k 0)).toD := by
    funext k
    rw [rd_pre hext]
    rw [List.getD_eq_getElem?_getD]
    rcases hk : (cAt n).posAns[k]? with _ | z
    · simpa using hM0
    · simpa using hc.2.2.1 z (List.mem_of_getElem? hk)
  rw [hfr, had] at hxq
  have hin' : ∀ e ∈ trk, e ∈ L := fun e he => hin e (by rw [hA]; exact List.mem_append_right _ he)
  have hpath := posAllT_path κ inp hL hsib _ 0 trk xq hxq hin' hok
  refine ⟨M.length, ?_, by omega, fun q hq => ?_⟩
  · rw [skeleton_outs hn, genPhase_queries (cAt n) hsh, hb]
  · obtain ⟨p0, p3, pp⟩ := hpath q hq
    simp only [Nat.zero_add] at p0 p3 pp
    have hq' : posW i * q + 3 < posW i * (lvlStar i).t := by
      have : q + 1 ≤ (lvlStar i).t := hq
      have h6 : 4 ≤ posW i := by unfold posW; omega
      nlinarith
    refine ⟨?_, ?_, pp⟩
    · rw [show M.length + 2 + posW i * q = M.length + (2 + posW i * q) by ring,
        rd_phase hext (by simp [hql]; nlinarith), List.getD_append_right _ _ _ _ (by simp),
        show 2 + posW i * q - [Val.ak _, Val.ak _].length = posW i * q by simp, p0]
    · rw [show M.length + 2 + posW i * q + 3 = M.length + (2 + (posW i * q + 3)) by ring,
        rd_phase hext (by simp [hql]; omega), List.getD_append_right _ _ _ _ (by simp),
        show 2 + (posW i * q + 3) - [Val.ak _, Val.ak _].length = posW i * q + 3 by simp, p3]

/-! ## The final message -/

/-- **The final message's absorb** (row 47): a 30-kind's final message is zero past `2^5`
elements. -/
theorem final_view {tr : Trace} {y : List Val × List Bool × Trace} (h : SkRun impl κ inp tr y)
    {n : ℕ} (hn : n < phases.length) {len : ℕ} (hsh : phases[n].shape = .absorb fFinal len) :
    κ = .L32 ∨ (FR.msgAt inp fFinal (2 ^ 5 * 32) ((finalElems - 2 ^ 5) * 32)).data.all (· == 0) =
      true := by
  obtain ⟨trk, M, x, hx, -, -, -, hflag, -⟩ := phase_at impl κ inp h.ref hn
  have hfs : fFinal ≠ fStmt := by decide
  simp only [refPhase, hsh, if_neg hfs, if_true] at hx
  obtain ⟨xa, -, rfl⟩ := Option.map_eq_some_iff.1 hx
  have := h.flags _ hflag
  simpa [Val.isZero] using this

/-- On a 30-kind, the final message's π elements `32 … 127` are zero. -/
theorem finV_zero {π : Proof} {vk c : Digest} (hπ : π.size = piSize)
    (hz : (FR.msgAt ⟨vk, c, π⟩ fFinal (2 ^ 5 * 32) ((finalElems - 2 ^ 5) * 32)).data.all
      (· == 0) = true) {e : ℕ} (he1 : 32 ≤ e) (he2 : e < 128) : finV ⟨vk, c, π⟩ e = 0 := by
  have hz' := allZero_mem hz
  have hb : bytesAt π (absOff fFinal (32 * e)) 32 = Vector.replicate 32 0 := by
    refine Vector.ext fun k hk => ?_
    rw [getElem_bytesAt _ _ _ _ hk, Vector.getElem_replicate]
    by_cases hlt : absOff fFinal (32 * e) + k < π.size
    · refine hz' _ ?_
      rw [FR.msgAt, toList_extract]
      have hoff : absOff fFinal (32 * e) + k = absOff fFinal (2 ^ 5 * 32) + (32 * e - 1024 + k) := by
        simp only [absOff]; omega
      rw [hoff] at hlt ⊢
      rw [List.getD_eq_getElem _ _ (by simpa using hlt)]
      refine List.mem_iff_getElem.2 ⟨32 * e - 1024 + k, ?_, ?_⟩
      · have hab : absOff fFinal (32 * e) = absOff fFinal 1024 + (32 * e - 1024) := by
          simp only [absOff]; omega
        simp [finalElems]; omega
      · simp
    · rw [List.getD_eq_default _ _ (by simpa using not_lt.1 hlt)]
  rw [finV, hb]; decide

/-! ## Every register the skeleton exports is one of its registers -/

/-- A phase's out registers are below the next free register (the rounds' first claim may be
the context's `uni` register). -/
theorem genPhase_out_lt (n : ℕ) (p : Phase) (c : GCtx) (hu : p.shape = .seed ∨ c.uni < c.next) :
    ∀ x ∈ (genPhase n p c).2.outs.back?.getD [], x < (genPhase n p c).2.next := by
  obtain ⟨name, sh⟩ := p
  simp only [Reg]
  cases sh with
  | seed => simp [genPhase]
  | absorb f len =>
    simp only [genPhase]; split_ifs <;> simp
  | squeezes k ch =>
    cases ch with
    | coords nf =>
      simp [genPhase]
      try (intro v hv; omega)
    | one act => simp [genPhase]
    | pos i =>
      simp [genPhase]
  | uni f => simp [genPhase]
  | rounds f k deg inK real =>
    have hu' : c.uni < c.next := by simpa using hu
    have key : ∀ w, 4 ≤ w → ∀ (cl b' : ℕ), cl < b' → ∀ x ∈ cl ::
        ((List.range k).map (fun j => b' + w * j + 3) ++ [if k = 0 then cl else b' + w * k - 1]),
        x < b' + w * k := by
      intro w hw cl b' hcl x hx
      simp only [List.mem_cons, List.mem_append, List.mem_map, List.mem_range, List.not_mem_nil,
        or_false] at hx
      rcases hx with rfl | ⟨j, hj, rfl⟩ | rfl
      · omega
      · nlinarith
      · split <;> omega
    have hR : 4 ≤ roundW deg := by unfold roundW; split <;> omega
    rcases hi : initClaim name with _ | _ | _ <;> cases inK
    · simpa [genPhase, hi, initOps, Init.width, Nat.add_assoc] using key _ hR c.uni c.next hu'
    · simpa [genPhase, hi, initOps, Init.width, Nat.add_assoc] using key 13 (by omega) c.uni c.next hu'
    · simpa [genPhase, hi, initOps, Init.width, Nat.add_assoc] using key _ hR c.next (c.next + 1) (by omega)
    · simpa [genPhase, hi, initOps, Init.width, Nat.add_assoc] using key 13 (by omega) c.next (c.next + 1) (by omega)
    · simpa [genPhase, hi, initOps, Init.width, Nat.add_assoc] using key _ hR (c.next + 2) (c.next + 3) (by omega)
    · simpa [genPhase, hi, initOps, Init.width, Nat.add_assoc] using
        key 13 (by omega) (c.next + 2) (c.next + 3) (by omega)
  | queries i =>
    simp [genPhase]
    intro q hq
    have : 4 ≤ posW i := by unfold posW; omega
    nlinarith

/-- **Every register in the skeleton's `outs`** is below the size of the registers it leaves. -/
theorem skeleton_out_lt {tr : Trace} {y : List Val × List Bool × Trace}
    (h : refPhases impl κ inp phases 0 ctx₀ #[] tr = some y) :
    ∀ n, ∀ x ∈ skeleton.2.outs.getD n [], x < (#[] ++ y.1.toArray).size := by
  intro n x hx
  by_cases hn : n < phases.length
  · obtain ⟨trk, M, x', hx', hb, hwf, hext, -, -, -⟩ := phase_at impl κ inp h hn
    rw [skeleton_outs hn] at hx
    have hu : phases[n].shape = .seed ∨ (cAt n).uni < (cAt n).next := by
      rcases hwf with ⟨h', -⟩ | h'
      · exact .inl h'
      · right; have := h'.2.1; simpa [hb] using this
    have hlt := genPhase_out_lt n phases[n] (cAt n) hu x hx
    obtain ⟨h1, -, -⟩ := genPhase_ctx impl κ inp n phases[n] (cAt n) (#[] ++ M.toArray) trk x'
      (by simpa using hb) hwf hx'
    have := hext.1
    simp at h1 this ⊢
    exact lt_of_lt_of_le (α := ℕ) hlt (by omega)
  · have hs := (genPhases_outs phases 0 ctx₀).1
    have : skeleton.2.outs.getD n [] = [] := by
      rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_none]
      · rfl
      · rw [show skeleton = genPhases phases 0 ctx₀ from rfl, hs]; simp [ctx₀]; omega
    rw [this] at hx; cases hx

end FR.Snd
