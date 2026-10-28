-- New for `flock-recursive` (BLUEPRINT A.10, §5.1; stage S-G9).
import FRSoundnessFrDF

/-!
# The front's dooms and checks read the same off two logs whose words agree

`hstab` and `FrontChainStab` both hand over `Same L X L' X X.length` (`same_stabX`, `same_chain`).
**`SameStab q P`**: `P` reads the same off such logs, on `X` of at least `q` entries. Every part of the
front reads `L` only through `f⁽⁰⁾`, so:

* **`df_ss`**: phase `k`'s doom is `SameStab (phStart k + 1)`;
* **`rejF_ss`**: the checks are `SameStab 0` (each is guarded by its position);
* **`frontChainStab`**: `FrontChainStab (RejF …) (DF …)`; **`df_stab`**: `FrontObl.hstab`'s form.
-/

namespace FR.Snd
open RecursionFast FR.Merkle Finset

set_option linter.constructorNameAsVariable false

/-- **`P` reads the same off two logs whose words agree on `X`**, for `X` of at least `q`
entries. -/
def SameStab (q : ℕ) (P : Log → Log → Prop) : Prop :=
  ∀ L L' X, q ≤ X.length → Same L X L' X X.length → (P L X ↔ P L' X)

section SSLemmas
variable {q q' p : ℕ} {P Q : Log → Log → Prop}

theorem SameStab.mono (h : SameStab q P) (hq : q ≤ q') : SameStab q' P := fun L L' X hx hS => h L L' X (by omega) hS

theorem SameStab.up (h : SameStab q P) (q' : ℕ) (hq : q ≤ q' := by norm_num) : SameStab q' P := h.mono hq

theorem SameStab.or (hP : SameStab q P) (hQ : SameStab q Q) : SameStab q fun L es => P L es ∨ Q L es :=
  fun L L' X hx hS => or_congr (hP L L' X hx hS) (hQ L L' X hx hS)

theorem SameStab.not (hP : SameStab q P) : SameStab q fun L es => ¬ P L es :=
  fun L L' X hx hS => not_congr (hP L L' X hx hS)

theorem ss_reads (h : Reads p P) : SameStab p P := fun L L' X hx hS => h L X L' X hx hx (hS.mono hx)

/-- A check guarded by its position (`p ≤ len`) is `SameStab 0`. -/
theorem ss_guard (h : Reads p P) (hg : ∀ L es, P L es → p ≤ es.length) : SameStab 0 P := by
  intro L L' X _ hS
  by_cases hx : p ≤ X.length
  · exact ss_reads h L L' X hx hS
  · exact ⟨fun h' => absurd (hg _ _ h') hx, fun h' => absurd (hg _ _ h') hx⟩

/-- A part that reads `L` only through `f⁽⁰⁾` (any `Same` from 3 on). -/
theorem ss_log (h : ∀ L L' X p, Same L X L' X p → 3 ≤ p → (P L X ↔ P L' X)) : SameStab 3 P :=
  fun L L' X hx hS => h L L' X _ hS hx

theorem ss_msD {prev fin : Log → Log → Prop} {s0 r : ℕ} (hp : SameStab (s0 + 1) prev) (hf : SameStab q fin)
    (hq : q ≤ s0 + r + 1) : SameStab (s0 + 1) (msD prev fin s0 r) := by
  intro L L' X hx hS
  unfold msD
  split_ifs with h
  · have hl : (X.take (s0 + 1)).length = s0 + 1 := by simp; omega
    exact hp L L' _ hl.ge (by rw [hl]; exact hS.take hx)
  · exact hf L L' X (by omega) hS

theorem ss_false (q : ℕ) : SameStab q fun _ _ => False := fun _ _ _ _ _ => Iff.rfl

end SSLemmas

/-! ## The parts -/

section Parts
variable {fin : Finals} {L3N PendN : Log → Log → Prop}

theorem ss_far0 : SameStab 3 far0 := ss_log fun _ _ _ _ h hp => farL0_same h hp _
theorem ss_nPub : SameStab 3 nPub := ss_log fun _ _ _ _ h hp => (pubOK_same h hp _).not
theorem ss_nS : SameStab 3 nS := ss_log fun _ _ _ _ h hp => (truthS_same h hp).not
theorem ss_nLr : SameStab 3 nLr := ss_reads rowsBad_reads
theorem ss_nE : SameStab 3 (nE fin) := ss_reads rowsBad_reads
theorem ss_pendZ : SameStab 3 PendZ := ss_log fun _ _ _ _ h hp => (zDooms_log (M := zlmFR) h hp).2.2.2.2.1
theorem ss_pendLc : SameStab 3 (PendLc zlmFR) := ss_log fun _ _ _ _ h hp => (lDooms_log (M := zlmFR) h hp).2.2.2

theorem ss_D2S : SameStab 114 D2S := fun _ _ _ hx hS => D2_congrL (TS_same hS hx) rfl

theorem ss_bgZ : SameStab 3 (bgZ fin) :=
  ((ss_far0.or (ss_nPub.or (ss_nLr.or ss_nE))).or ss_nS)

theorem ss_bg5 : SameStab 3 (bg5 fin) := ss_bgZ.or ss_pendZ

theorem ss_bg10 (hP : Reads 99 PendN) : SameStab 99 (bg10 fin PendN) :=
  ((ss_far0.or (ss_nPub.or (ss_nLr.or ss_nE))).up 99).or
    ((ss_pendZ.up 99).or ((ss_pendLc.up 99).or (ss_reads hP)))

theorem ss_bg20 (hP : Reads 99 PendN) : SameStab 114 (bg20 PendN) :=
  (ss_far0.up 114).or ((ss_nPub.up 114).or ((ss_pendZ.up 114).or
    ((ss_pendLc.up 114).or (((ss_reads hP).up 114).or ss_D2S))))

theorem ss_bg12 (hP : Reads 99 PendN) : SameStab 114 (bg12 fin PendN) :=
  (ss_bg20 hP).or (ss_nE.up 114)

theorem ss_bg16 (hP : Reads 99 PendN) : SameStab 210 (bg16 PendN) :=
  ((ss_bg20 hP).up 210).or (ss_reads (batBad_reads (rows := Layout.lRows) (a := 15) (nc := 23) (on := lrOn)
    (b2 := 178) (by norm_num)))

theorem ss_D2F : SameStab 3 (D2F fin) :=
  ss_far0.or (ss_reads (stmt_reads fin sLeaf_reads)).not

theorem ss_DRS0 : SameStab 3 DRS0 := ss_log fun L L' X p h hp => by
  have hq : ∀ ℓ, rsQ (kindOf X) L X ℓ = rsQ (kindOf X) L' X ℓ := fun ℓ => by
    funext i u; simp only [rsQ, fF_same h hp]
  simp only [DRS0, truthRS0, farL0_same h hp, pubOK_same h hp, hq]

theorem ss_DRS1 : SameStab 3 DRS1 := ss_log fun L L' X p h hp => by
  simp only [DRS1, farL0_same h hp, pubOK_same h hp, fipL, fF_same h hp]

theorem ss_DB : SameStab 318 DB := fun L L' X hx hS => by
  have hp1 : p1Start 0 ≤ X.length := by rw [show p1Start 0 = 318 from rfl]; exact hx
  simp only [DB, farL0_same hS (by omega), c₀L,
    lvT_same frontLocal_W0 hS (i := 0) (by norm_num) hp1]

end Parts

/-! ## Each phase's doom -/

section Phases
variable {fin : Finals} {L3N PendN : Log → Log → Prop}

theorem phStart_vals : phStart 2 = 2 ∧ phStart 3 = 3 ∧ phStart 4 = 13 ∧ phStart 5 = 15 ∧
    phStart 6 = 67 ∧ phStart 7 = 68 ∧ phStart 8 = 69 ∧ phStart 9 = 97 ∧ phStart 10 = 98 ∧
    phStart 11 = 99 ∧ phStart 12 = 114 ∧ phStart 13 = 170 ∧ phStart 14 = 178 ∧
    phStart 15 = 208 ∧ phStart 16 = 209 ∧ phStart 17 = 210 ∧ phStart 18 = 221 ∧
    phStart 19 = 263 ∧ phStart 20 = 264 ∧ phStart 21 = 265 ∧ phStart 22 = 311 ∧
    phStart 23 = 312 ∧ phStart 24 = 313 ∧ phStart 25 = 317 := by
  simp only [phStart, fsStarts_eq]; decide

/-- **Phase `k`'s doom reads the same off two logs whose words agree**, on `X` of at least
`phStart k + 1` entries. -/
theorem df_ss (hL3 : Reads 98 L3N) (hP : Reads 99 PendN) :
    ∀ k < 26, SameStab (phStart k + 1) (DF fin L3N PendN k) := by
  obtain ⟨h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19,
    h20, h21, h22, h23, h24, h25⟩ := phStart_vals
  have z := fun {P : Log → Log → Prop} (hz : ∀ L L' X p, Same L X L' X p → 3 ≤ p →
    (P L X ↔ P L' X)) => ss_log hz
  have hS2 : SameStab 114 S2Bad := fun L L' X hx hS => by simp only [S2Bad, TS_same hS hx]
  have hD3 : ∀ {rows : List Circ.Row} {a s0 b2 : ℕ}, 3 ≤ b2 → s0 + 1 + (a + 1) / 2 ≤ b2 + 1 →
      SameStab (b2 + 1) (D3 b2 (fun _ _ => 0) (nr3 a lrOn) outerExpr (T3 rows a 23 lrOn s0)) :=
    fun h3 hb L L' X hx hS => D3_same hS (by omega) (by omega)
  have hPE : SameStab 3 PendE := ss_log fun L L' X p h hp => by simp only [PendE, zC_same h hp]
  intro k hk
  interval_cases k
  · exact ss_false _
  · exact ss_false _
  · rw [h2]; exact ss_D2F
  · rw [h3]; exact (ss_msD ss_D2F (ss_bgZ.or (z fun _ _ _ _ h hp => (zDooms_log h hp).1))
      (by norm_num)).up _
  · rw [h4]; exact (ss_bgZ.or (z fun _ _ _ _ h hp => (zDooms_log h hp).2.1)).up _
  · rw [h5]; exact (ss_bg5.or (z fun _ _ _ _ h hp => (zDooms_log h hp).2.2.1)).up _
  · rw [h6]; exact (ss_bg5.or (z fun _ _ _ _ h hp => (zDooms_log h hp).2.2.2.1)).up _
  · rw [h7]; exact (ss_bg5.or (z fun _ _ _ _ h hp => (lDooms_log h hp).1)).up _
  · rw [h8]; exact (ss_bg5.or (z fun _ _ _ _ h hp => (lDooms_log h hp).2.1)).up _
  · rw [h9]; exact ((ss_bg5.up 98).or (((z fun _ _ _ _ h hp => (lDooms_log h hp).2.2.1).up 98).or
      (ss_reads hL3)))
  · rw [h10]; exact ((ss_bg10 hP).or (ss_nS.up 99)).up _
  · rw [h11]; exact (ss_msD ((ss_bg10 hP).or (ss_nS.up 99)) (((ss_bg10 hP).up 114).or hS2)
      (by norm_num)).up _
  · rw [h12]; exact ((ss_bg12 hP).or (ss_nLr.up 114)).up _
  · rw [h13]; exact (ss_msD (((ss_bg12 hP).or (ss_nLr.up 114)).up 170)
      (((ss_bg12 hP).up 178).or (ss_reads (zcw_reads (rows := Layout.lRows) (a := 15) (nc := 23)
        (on := lrOn) (s0 := 169) (by norm_num)))) (by norm_num)).up _
  · rw [h14]; exact ((ss_bg12 hP).up 179).or (hD3 (by norm_num) (by norm_num))
  · rw [h15]; exact (((ss_bg12 hP).up 209).or (ss_reads (endBad_reads (rows := Layout.lRows) (a := 15) (nc := 23) (on := lrOn)
      (b2 := 178) (by norm_num)))).up _
  · rw [h16]; exact ((ss_bg16 hP).or (ss_nE.up 210)).up _
  · rw [h17]; exact (ss_msD ((ss_bg16 hP).or (ss_nE.up 210))
      (((ss_bg16 hP).up 221).or (ss_reads (zcw_reads (rows := Layout.nodeRows fin) (a := 21)
        (nc := 23) (on := lrOn) (s0 := 209) (by norm_num)))) (by norm_num)).up _
  · rw [h18]; exact ((ss_bg16 hP).up 222).or (hD3 (by norm_num) (by norm_num))
  · rw [h19]; exact (((ss_bg16 hP).up 264).or (ss_reads (endBad_reads (rows := Layout.nodeRows fin) (a := 21) (nc := 23)
      (on := lrOn) (b2 := 221) (by norm_num)))).up _
  · rw [h20]; exact (((ss_bg20 hP).up 265).or (ss_reads batBadE_reads)).up _
  · rw [h21]; exact ((ss_bg20 hP).up 266).or (fun L L' X hx hS => D4E_same hS (by omega))
  · rw [h22]; exact ((ss_bg20 hP).up 312).or (hPE.up 312)
  · rw [h23]; exact ss_DRS0.up _
  · rw [h24]; exact (ss_msD (ss_DRS0.up 313) ss_DRS1 (by norm_num)).up _
  · rw [h25]; exact ss_DB

/-- **`FrontObl.hstab`'s form** from `df_ss` (`same_stabX`). -/
theorem df_stab (hL3 : Reads 98 L3N) (hP : Reads 99 PendN) :
    ∀ k < 26, ∀ L i, ¬ Bad L → IsChain L i → ∀ X,
      StabExt fsRnd (entriesOf L (pathOf L i)) X → phOf (X.length - 1) = k →
        (DF fin L3N PendN k (L.take i) X ↔ DF fin L3N PendN k L X) := by
  intro k hk L i hb hci X hX hph
  have hX1 : 1 ≤ X.length := by
    obtain ⟨s0, r, as, -, hs, -, rfl⟩ := hX
    rw [length_ext, List.length_take]; omega
  obtain ⟨b1, -, -⟩ := phOf_bounds (X.length - 1)
  rw [hph] at b1
  exact df_ss hL3 hP k hk _ _ X (by omega) (same_stabX hb hci hX)

end Phases

/-! ## The checks and `FrontChainStab` -/

section Checks
variable {fin : Finals} {oLc : Kind → Log → F → Prop} {RejN L3N PendN : Log → Log → Prop}

theorem ss_rejF (hN : NodeLF oLc RejN L3N PendN) : SameStab 0 (RejF fin oLc RejN) := by
  have hZ : SameStab 0 (RejZ zlmFR) := fun L L' X _ hS => by
    by_cases hx : 68 ≤ X.length
    · exact and_congr Iff.rfl (rejZ_reads L X L' X hx hx (hS.mono hx))
    · exact ⟨fun h => absurd h.1 hx, fun h => absurd h.1 hx⟩
  have hL2 : SameStab 0 RejL2 := fun L L' X _ _ => by simp only [RejL2, Chk2, clR2L_log L L' X]
  have hLc : SameStab 0 (RejLc2 zlmFR) := fun L L' X _ _ => by simp only [RejLc2, clR2L_log L L' X]
  have hS2 : SameStab 0 RejS2 := fun L L' X _ hS => by
    simp only [RejS2]
    exact exists_congr fun l => and_congr_right fun _ => and_congr_right fun hl =>
      (chkS_same hS hl).not
  have hEnd : ∀ {a s0 b2 : ℕ}, s0 + 1 + (a + 1) / 2 ≤ b2 → 3 ≤ b2 → SameStab 0 (RejEnd a lrOn s0 b2) :=
    fun hs h3 => ss_guard (rejEnd_reads hs h3) fun _ _ h => by have := h.2.1; omega
  have hIn : SameStab 0 RejInE := fun L L' X _ hS => by
    simp only [RejInE]
    exact exists_congr fun l => and_congr_right fun _ => and_congr_right fun hl =>
      (chkE_same hS hl).not
  have hE4 : SameStab 0 (RejE4 (Layout.nodeRows fin)) := fun L L' X _ _ => by
    simp only [RejE4, clR2_same (b := 265) (wd := 16) (rd := readF) (ch := fun d => chF d 0)
      (c0 := c4E) (L := L) (L' := L') (c4E_agree (L := L) (L' := L') (p := 265)
        (fun _ _ => rfl) le_rfl) (l := 23) (fun _ _ => rfl)]
  have hRS : SameStab 0 (RejRS (okF oLc)) := fun _ _ _ _ _ => Iff.rfl
  exact hZ.or (hL2.or (hLc.or (hS2.or ((hEnd (by norm_num) (by norm_num)).or
    ((hEnd (by norm_num) (by norm_num)).or (hIn.or (hE4.or (hRS.or
      (ss_guard hN.rejReads hN.rejLen)))))))))

/-- **`FrontChainStab`**: the front's checks and dooms read the same on the chain itself. -/
theorem frontChainStab (hN : NodeLF oLc RejN L3N PendN) :
    FrontChainStab (RejF fin oLc RejN) (DF fin L3N PendN) := by
  intro L j hb hci
  have hS := same_chain hb hci
  refine ⟨ss_rejF hN _ _ _ (Nat.zero_le _) hS, fun k hk hph => ?_⟩
  have h1 : 1 ≤ (entriesOf L (pathOf L j)).length := List.length_pos_iff.mpr (matches_ne_nil hci.2)
  obtain ⟨b1, -, -⟩ := phOf_bounds ((entriesOf L (pathOf L j)).length - 1)
  rw [hph] at b1
  exact df_ss hN.l3Reads hN.pendReads k hk _ _ _ (by omega) hS

end Checks

/-! ## Controls -/

/-- Control (negative, non-vacuous): a predicate of the whole log `L` is not `SameStab` (two logs with
no word before `X`'s end agree on `X = []`). -/
theorem not_ss_log : ¬ SameStab 0 fun L _ => L = [] := fun h => by
  have := (h [] [default] [] le_rfl ⟨fun _ _ => rfl, fun _ _ _ hc => absurd hc (Nat.not_lt_zero _)⟩).mp rfl
  simp at this

/-- Control (positive): `far₀` is `SameStab` from 3 (`ss_far0`); the empty predicate everywhere. -/
theorem ss_controls : SameStab 3 far0 ∧ SameStab 0 fun _ _ => False := ⟨ss_far0, ss_false 0⟩

end FR.Snd
