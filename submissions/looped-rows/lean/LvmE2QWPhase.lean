-- New for lvm2 E2-FT (E2F-QH5): the `PhaseAt` facts of QH2's front gadgets for `harithF20` (E2F-C's SPEC, in roll 11's
-- `LvmQAsmHarP47.tape_phase`/`wire_phase` form): the root pin, the wiring with its row switch, `KS`'s row switch, the
-- `KS` link; and `tapeD`/`callerD` cut into the GKR part (E2F-QH4's) and these.
import LvmE2QWReplay
import LvmE2QKTapeEq
import LvmQAsmHarTop

/-!
# The front gadgets' phases at S2GF

Every lemma takes the gadget's rows at its pointer (`SegsHold`, and `SegsAssert` where the gadget asserts), the stream
cells (`Streamed`), the gate, the inputs' meaning, and the proof-of-work answers (`PowOkV` on the gadget's
`(answer lane, g)` list, which the PoW blocks give: `powBlk_ok`); it concludes V's phase as `PhaseAt` with a fixed
value, and the gadget's output cells as that value's fields.

* combinators: `phaseAt_bind`, `phaseAt_pure`, `phaseAt_require`; the reads (`sepE2_phase`, `samplesG_phase`,
  `readE2s_phase`);
* **`pin_phase`**: `pinD ν`;
* **`rowSwitch_phase`**: `rowSwitchD z sv` (`KS`'s: the row words `t_j = rowWordD sv j` from `rowAux_sound`);
* **`wire_phase`**: `wireD (P + 5) …` with the wiring's row switch, the claim represented (`Rep2`, E2F-QH4's);
* **`ksLink_phase`**: `ksLinkD hk xl contRowsF` (`contRowsF_eq`);
* **`tapeD_phase`**, **`callerD_phase`**: `tapeD` from the separator, `r`, the scalars, `tapeGkrD`'s phase
  (E2F-QH4's `tape_phase2`), `n`'s range and `wire_phase`; `callerD` from `r`, the scalars, `verifyKeccakD`'s phase
  (E2F-QH4's) and `rowSwitch_phase`.
-/

set_option autoImplicit false

namespace Lvm.Q2

open Lvm Lvm.Loop Lvm.Loop.Build Lvm.Har Lvm.Q1 DM Lvm.E2V

variable {c : Ctx} {M : Mem}

/-! ## Combinators -/

theorem phaseAt_bind {α β : Type} {m : DM α} {f : α → DM β} {sig : ByteArray} {P P' P'' : Nat} {a : α} {b : β}
    (hm : PhaseAt m sig P P' a) (hf : PhaseAt (f a) sig P' P'' b) : PhaseAt (m >>= f) sig P P'' b := by
  intro s hs hok
  obtain ⟨h1, h2, h3⟩ := hm s hs hok
  rw [dbind_run, h1]
  exact hf _ h3 h2

theorem phaseAt_pure {α : Type} {a : α} {sig : ByteArray} {P : Nat} : PhaseAt (pure a : DM α) sig P P a :=
  fun _ hs hok => ⟨rfl, hok, hs⟩

theorem phaseAt_require {b : Bool} (hb : b = true) {sig : ByteArray} {P : Nat} : PhaseAt (require b) sig P P () :=
  fun s hs hok => ⟨rfl, by show (b && s.ok) = true; rw [hb, hok]; rfl, hs⟩

/-- The values of `n` ground challenges from position `P` (answers at `P + 48 + 80 i`). -/
def sampsG (sig : ByteArray) (P n : Nat) : List FE2 := (List.range n).map fun i => fe2At sig (P + 48 + 80 * i)

/-- `n` `E2` scalars from position `P`. -/
def readsE2 (sig : ByteArray) (P n : Nat) : List FE2 := (List.range n).map fun i => fe2At sig (P + 40 + 16 * i)

/-- `n` ground challenges (`g`) from the answer lane `q`, `(answer lane, g)` (lanes `q + 10 i`). -/
def chalsG (q g n : Nat) : List (Nat × Nat) := (List.range n).map fun i => (q + 10 * i, g)

/-! ## The pin -/

theorem pinD_st (sig : ByteArray) (s : RS) {nu : Nat} (hn : 1 ≤ nu) :
    (pinD nu sig s).2 = ⟨s.ent + s.msg + 72 * nu, 24, s.ok⟩ := by
  show (readE sig (samples nu sig s).2).2 = _
  rw [samples_run sig nu s hn, readE_run]

/-- **The pin's phase**: from `P` (`8 qz = P + 40`, value lane `qa = qz + 9 ν`) V's `pinD ν` ends at
`P + 72 ν + 24`; the gadget's claim is its value. -/
theorem pin_phase {sig : ByteArray} {T : Nat} (hS : Streamed M sig T) {nu qz qa P : Nat} (hn : 1 ≤ nu)
    (hP : 8 * qz = P + 40) (hqa : qa = qz + 9 * nu) (hz : qz + 9 * nu + 2 < T) (ha : qa + 2 < T) {p : Ptr}
    (hh : SegsHold c M p (pinG nu qz qa p).2) :
    PhaseAt (pinD nu) sig P (P + 72 * nu + 24) (pinD nu sig ⟨P, 0, true⟩).1 ∧
      (pinG nu qz qa p).1.val M = (.main, (pinD nu sig ⟨P, 0, true⟩).1) := by
  refine ⟨fun s hs hok => ⟨?_, ?_, ?_⟩, pin_replays hS ⟨P, 0, true⟩ hn hP hqa hz ha p hh⟩
  · have hs' : s.ent + s.msg = P := hs
    rw [pinD_run sig s hn, pinD_run sig _ hn, hs']
    rfl
  · rw [pinD_st sig s hn]; exact hok
  · rw [pinD_st sig s hn]; show s.ent + s.msg + 72 * nu + 24 = _; rw [show s.ent + s.msg = P from hs]

/-! ## The row switch -/

/-- **A row switch's phase**: from `P` (`8 qr = P + 40`) V's `rowSwitchD z sv` ends at `P + 504` with the value
`rowValD z sv` of the gadget's `eq(r'', ·)`, whose target is the gadget's; `t_j = rowWordD sv j` (`rowAux_sound`). -/
theorem rowSwitch_phase {sig : ByteArray} {T : Nat} (hS : Streamed M sig T) {qr tB z o : Nat} (hz : M.e z = 0)
    (ho : M.e o = 1) (hT : qr + 9 * 6 + 2 < T) {p : Ptr} (hh : SegsHold c M p (rowG qr tB z o p).2) {P : Nat}
    (hP : 8 * qr = P + 40) (zz sv : List FE2) (ht : ∀ j < 128, M.k (tB + j) = rowWordD sv j) :
    PhaseAt (rowSwitchD zz sv) sig P (P + 504) (rowValD zz sv ((rowG qr tB z o p).1.eqR.map (Cell.val M))) ∧
      (rowValD zz sv ((rowG qr tB z o p).1.eqR.map (Cell.val M))).1.1 = (rowG qr tB z o p).1.target.val M := by
  refine ⟨fun s hs hok => ?_, (rowSwitch_replays hS hz ho hT ⟨P, 0, true⟩ hP zz sv ht p hh).2⟩
  have hs' : rpos s = P := hs
  rw [(rowSwitch_replays hS hz ho hT s (by rw [hs']; exact hP) zz sv ht p hh).1]
  exact ⟨rfl, hok, by show rpos s + 504 + 0 = _; rw [hs']⟩

/-! ## The wiring -/

/-- The wiring's ground answers `(answer lane, g)`: the wiring rounds', then the slot rounds'. -/
def wireChals (w qw : Nat) : List (Nat × Nat) := (sc2Ans w qw ++ sc2Ans 2 (wireLanes w qw).slot).map fun q => (q, gC2)

/-- **The wiring's phase** (`wireD (P + 5)` with its row switch): from `P5` (`8 qw = P5 + 40`) to
`P5 + 112 (P + 5) + 1768`, on a represented claim (`Rep2`, the tape phase's output); the value is read off the
gadgets (`wireG2` at `p`, the row switch `rowG` at `pr`, its row words the slices' transpose). -/
theorem wire_phase {sig : ByteArray} {T : Nat} (hS : Streamed M sig T) {P qw : ℕ} {cv : ℕ → C2}
    {mb sb : List Cell} {zk gate : Cell} (claim : E2V.KClaim FE2) (s' : List FK) (n sbsel dsel : ℕ)
    (hzk : zk.val M = 0) (hg : gate.val M = 1) (hsb : sb.length = 256)
    (hmb : (mb.map fun b => kC2 b zk).map (C2.val M) = bitsF (n - 1) (P + 5)) (hn : n - 1 < 2 ^ (P + 5))
    (hsbv : (sb.map fun b => kC2 b zk).map (C2.val M) = (List.range 256).map fun p => E2V.bitF (sBitsD s' p))
    (hR : Rep2 P (fun j => (cv j).val M) claim false) {P5 : Nat} (hP : 8 * qw = P5 + 40)
    {p : Ptr} (hh : SegsHold c M p (wireG2 P qw cv mb sb zk gate p).2)
    (ha : SegsAssert M p (wireG2 P qw cv mb sb zk gate p).2)
    {tB z o : Nat} (hz : M.e z = 0) (ho : M.e o = 1) {pr : Ptr}
    (hhr : SegsHold c M pr (rowG (wireLanes (P + 5) qw).ring tB z o pr).2)
    (ht : ∀ j < 128, M.k (tB + j) = rowWordD ((wireG2 P qw cv mb sb zk gate p).1.slices.map (C2.val M)) j)
    (hT : (wireLanes (P + 5) qw).ring + 9 * 6 + 2 < T)
    (hpow : PowOkV (feAt sig) (wireChals (P + 5) qw)) :
    let wo := (wireG2 P qw cv mb sb zk gate p).1
    let ro := (rowG (wireLanes (P + 5) qw).ring tB z o pr).1
    let row := rowValD (wo.sigma.map (C2.val M) ++ wo.tau.map (C2.val M) ++ selPtF dsel sbsel)
      (wo.slices.map (C2.val M)) (ro.eqR.map (Cell.val M))
    PhaseAt (wireD (P + 5) sbsel dsel s' n claim) sig P5 (P5 + 112 * (P + 5) + 1768)
      ((wo.sigma.map (C2.val M), wo.final.val M), [wo.gD.val M],
        ((wo.tau.map (C2.val M), scFold2 (fun k => fe2At sig (8 * k)) 2 (wireLanes (P + 5) qw).slot (wo.gD.val M)),
          wo.slices.map (C2.val M), row)) ∧
      row.1.1 = ro.target.val M := by
  intro wo ro row
  have hE := (rowG_spec (c := c) hS hz ho hT pr hhr).1
  have hL : (wireLanes (P + 5) qw).slices + 128 < T := by simp only [wireLanes] at hT ⊢; omega
  have hrow : row.1.1 = ro.target.val M := by
    show (rowValD _ _ _).1.1 = _
    rw [(rowG_spec (c := c) hS hz ho hT pr hhr).2, rowValD, sumE_eq, hE]
    exact congrArg List.sum (List.map_congr_left fun j hj => by rw [ht j (List.mem_range.mp hj)])
  refine ⟨fun s hs hok => ?_, hrow⟩
  have hs' : rpos s = P5 := hs
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := wire_replays hS claim s' n sbsel dsel hzk hg hsb hmb hn hsbv
    hR.value.symm hR.mu.symm hR.point.symm (fun j hj => rep2_lt_posF hR hj) s (by rw [hs']; exact hP) hL p hh ha
  have hok2 : okS gC2 sig (rpos s) (P + 5) = true := okS_true _ _ fun k hk => by
    have := hpow (qw + roundLanes2 * k + 5, gC2) (List.mem_map.mpr ⟨_, List.mem_append_left _
      (List.mem_map.mpr ⟨k, List.mem_range.mpr hk, rfl⟩), rfl⟩)
    rwa [show 8 * (qw + roundLanes2 * k + 5) = rpos s + 80 + 112 * k by simp only [roundLanes2]; omega] at this
  have hok3 : okS gC2 sig (rpos s + 112 * (P + 5) + 16) 2 = true := okS_true _ _ fun k hk => by
    have := hpow ((wireLanes (P + 5) qw).slot + roundLanes2 * k + 5, gC2) (List.mem_map.mpr ⟨_,
      List.mem_append_right _ (List.mem_map.mpr ⟨k, List.mem_range.mpr hk, rfl⟩), rfl⟩)
    rwa [show 8 * ((wireLanes (P + 5) qw).slot + roundLanes2 * k + 5) = rpos s + 112 * (P + 5) + 16 + 80 + 112 * k by
      simp only [wireLanes, roundLanes2]; omega] at this
  have hq : ((List.range 7).map fun k => feAt sig (rpos s + 112 * (P + 5) + 1304 + 72 * k)) =
      (List.range 7).map fun k => feAt sig (8 * ((wireLanes (P + 5) qw).ring + 9 * k)) :=
    List.map_congr_left fun k _ => congrArg _ (by simp only [wireLanes, roundLanes2]; omega)
  rw [hq, ← hE] at h7
  refine ⟨?_, by rw [h5, hok2, hok3, hok]; rfl, by show rpos _ = _; rw [h8, hs']⟩
  generalize (wireD (P + 5) sbsel dsel s' n claim sig s).1 = X at h1 h2 h3 h4 h6 h7
  obtain ⟨⟨xσ, xf⟩, xg, ⟨xτ, xf'⟩, xsv, xrow⟩ := X
  simp only at h1 h2 h3 h4 h6 h7 ⊢
  rw [h1, h2, h3, h4, h6, h7]

/-! ## The `KS` link -/

/-- `contRowsF` in the link gadget's form. -/
theorem contRowsF_eq : E2V.contRowsF = rowsBK (spongeBlocksF P20F accVF) (ksSplit P20 + 399) := rfl

/-- The link's ground answers `(answer lane, g)`: the `hk + 5` challenges, then the shift sumcheck's rounds. -/
def ksLinkChals (hk qa : Nat) : List (Nat × Nat) :=
  chalsG qa gC1 (hk + 5) ++ (sc2Ans hk (ksLinkQ1 hk qa)).map fun q => (q, gC2)

/-- **The `KS` link's phase**: from `P` (`8 qa = P + 48`) V's `ksLinkD hk xl (rowsBK B K)` ends at
`P + 80 (hk + 5) + 112 hk + 64` with the gadget's challenges, shift point, final claim and values. -/
theorem ksLink_phase {sig : ByteArray} {T : Nat} (hS : Streamed M sig T) {hk xl B K qa : Nat} {gate : Cell}
    (hg : gate.val M = 1) (hB : B - 1 < 2 ^ hk) (hK : K + 31 < 2 ^ hk) {P : Nat} (hP : 8 * qa = P + 48)
    (hT : ksLinkQV hk qa + 8 < T) {p : Ptr} (hh : SegsHold c M p (ksLinkG2 hk xl B K qa gate p).2)
    (ha : SegsAssert M p (ksLinkG2 hk xl B K qa gate p).2)
    (hpow : PowOkV (feAt sig) (ksLinkChals hk qa)) :
    let o := (ksLinkG2 hk xl B K qa gate p).1
    PhaseAt (ksLinkD hk xl (rowsBK B K)) sig P (P + 80 * (hk + 5) + 112 * hk + 64)
      (o.kchal.map (C2.val M), (o.shift.map (C2.val M), o.final.val M), o.vals.map (C2.val M)) := by
  intro o s hs hok
  have hs' : rpos s = P := hs
  obtain ⟨h1, h2, h3⟩ := ksLink_replays hS hg hB hK s (by rw [hs']; exact hP) hT p hh ha
  have hg1 : okG gC1 sig (rpos s) (hk + 5) = true := okG_true _ _ fun i hi => by
    have := hpow (qa + 10 * i, gC1) (List.mem_append_left _ (List.mem_map.mpr ⟨i, List.mem_range.mpr hi, rfl⟩))
    rwa [show 8 * (qa + 10 * i) = rpos s + 48 + 80 * i by omega] at this
  have hg2 : okS gC2 sig (rpos s + 80 * (hk + 5)) hk = true := okS_true _ _ fun k hk' => by
    have := hpow (ksLinkQ1 hk qa + roundLanes2 * k + 5, gC2) (List.mem_append_right _
      (List.mem_map.mpr ⟨_, List.mem_map.mpr ⟨k, List.mem_range.mpr hk', rfl⟩, rfl⟩))
    rwa [show 8 * (ksLinkQ1 hk qa + roundLanes2 * k + 5) = rpos s + 80 * (hk + 5) + 80 + 112 * k by
      simp only [ksLinkQ1, roundLanes2]; omega] at this
  exact ⟨h1, by rw [h2, hg1, hg2, hok]; rfl, by show rpos _ = _; rw [h3, hs']⟩

/-! ## `tapeD` and `callerD` from the GKR phases -/

theorem sepE2_phase {sig : ByteArray} {P : Nat} : PhaseAt sepE2 sig P (P + 72) () :=
  fun s hs hok => ⟨rfl, hok, by show s.ent + 72 + s.msg + 0 = _; rw [← hs]; simp only [pos]; omega⟩

theorem samplesG_phase {sig : ByteArray} {g n P q : Nat} (hq : 8 * q = P + 48)
    (hpow : PowOkV (feAt sig) (chalsG q g n)) : PhaseAt (samplesG g n) sig P (P + 80 * n) (sampsG sig P n) := by
  intro s hs hok
  have hs' : rpos s = P := hs
  obtain ⟨h1, h2, h3⟩ := Lvm.Q2.samplesG_run g sig n s
  have hg : okG g sig (rpos s) n = true := okG_true _ _ fun i hi => by
    have := hpow (q + 10 * i, g) (List.mem_map.mpr ⟨i, List.mem_range.mpr hi, rfl⟩)
    rwa [show 8 * (q + 10 * i) = rpos s + 48 + 80 * i by omega] at this
  exact ⟨by rw [h1, hs']; rfl, by rw [h3, hg, hok]; rfl, by show rpos _ = _; rw [h2, hs']⟩

theorem readE2s_phase {sig : ByteArray} {n P : Nat} : PhaseAt (readE2s n) sig P (P + 16 * n) (readsE2 sig P n) := by
  intro s hs hok
  have hs' : rpos s = P := hs
  rw [Lvm.Q2.readE2s_run, hs']
  exact ⟨rfl, hok, by show s.ent + (s.msg + 16 * n) = _; rw [← hs']; simp only [rpos]; omega⟩

/-- **`tapeD` from its parts**: the separator, `r` (`w` ground challenges, answer lanes `qr + 10 i`,
`8 qr = P4 + 120`), the 25 scalars, then the tape GKR's phase (E2F-QH4's `tape_phase2`), `n`'s range and the
wiring's phase (`wire_phase`). -/
theorem tapeD_phase {w sb dsel : Nat} {s : List FK} {n : Nat} {sig : ByteArray} {P4 P5 P6 qr : Nat}
    {claim : KClaim FE2}
    {wo : (List FE2 × FE2) × List FE2 × ((List FE2 × FE2) × List FE2 × ((FE × (List FE → FE)) × List FE))}
    (hqr : 8 * qr = P4 + 120) (hpow : PowOkV (feAt sig) (chalsG qr gC1 w))
    (htg : PhaseAt (tapeGkrD w (sampsG sig (P4 + 72) w) (readsE2 sig (P4 + 72 + 80 * w) 25)) sig
      (P4 + 72 + 80 * w + 400) P5 claim)
    (hn : 1 ≤ n ∧ n ≤ 2 ^ w) (hw : PhaseAt (wireD w sb dsel s n claim) sig P5 P6 wo) :
    PhaseAt (tapeD w sb dsel s n) sig P4 P6
      (sampsG sig (P4 + 72) w, readsE2 sig (P4 + 72 + 80 * w) 25, claim, wo) :=
  phaseAt_bind sepE2_phase (phaseAt_bind (samplesG_phase (by omega) hpow) (phaseAt_bind readE2s_phase
    (phaseAt_bind htg (phaseAt_bind (phaseAt_require (decide_eq_true hn)) (phaseAt_bind hw phaseAt_pure)))))

/-- **`callerD` from its parts**: `h` ground challenges (answer lanes `qr + 10 i`, `8 qr = P3 + 48`), the 25
scalars, `verify_keccak`'s phase (E2F-QH4's), then the row switch's (`rowSwitch_phase`). -/
theorem callerD_phase {h : Nat} {sig : ByteArray} {P3 P3' P4 qr : Nat}
    {res : List (List FE2 × FE2) × List FE2 × List FE2} {row : (FE × (List FE → FE)) × List FE}
    (hqr : 8 * qr = P3 + 48) (hpow : PowOkV (feAt sig) (chalsG qr gC1 h))
    (hk : PhaseAt (verifyKeccakD h (sampsG sig P3 h) (readsE2 sig (P3 + 80 * h) 25)) sig (P3 + 80 * h + 400) P3' res)
    (hr : PhaseAt (rowSwitchD res.2.1 res.2.2) sig P3' P4 row) :
    PhaseAt (callerD h) sig P3 P4 (sampsG sig P3 h, readsE2 sig (P3 + 80 * h) 25, res, row) :=
  phaseAt_bind (samplesG_phase hqr hpow) (phaseAt_bind readE2s_phase
    (phaseAt_bind hk (phaseAt_bind hr phaseAt_pure)))

end Lvm.Q2
