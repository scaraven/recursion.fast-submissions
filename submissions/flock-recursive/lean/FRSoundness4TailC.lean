-- New for `flock-recursive` (BLUEPRINT §5.1, §5.4, A.10; stage T4, S-G13 route C): a copy-port of
-- `FRSoundnessCompose` to revision 4.1's item sequence `seq4` (namespace `FR.Snd.T4`, see `FRSoundness4TailStep`):
-- the declarations that read positions, chains or the kind are copied, the rest is imported.
import FRSoundness4TailM

/-!
# The composed doom and `PhaseObl` at `seq4` (T4)

The 3.x declarations of `FRSoundnessCompose` that read the positions, the chains or the kind, restated in
`FR.Snd.T4` over `fsItems4`/`phStart4`/`fsRnd4`, `G.Matches`/`G.IsChain` and `CKind`
(`kindOfC`, `CKind.lv`). Positions from P1.0 on are 3.x's plus 14 (`phStart4_shift`); the kind
enters through the ladder `lvOf κ.m` only. Changes beyond the renaming are marked `T4:`.
-/

/-! # Port of `FRSoundnessCompose` (its module doc describes the 3.x original) -/

namespace FR.Snd.T4
open RecursionFast FR.Merkle Finset
open scoped NNReal

set_option linter.constructorNameAsVariable false

/-! ## The combined doom -/

/-- The asserted checks: the front's or the tail's. -/
def RejC (RejF : Log → Log → Prop) (c₀ : Log → Log → K) (L es : Log) : Prop :=
  RejF L es ∨ RejT c₀ L es

/-- The phase dooms: the front's before P1.0, the tail's from P1.0 on. -/
def DkC (DF : ℕ → Log → Log → Prop) (W₀ : Log → Log → ℕ → K) (c₀ : Log → Log → K) (k : ℕ) :
    Log → Log → Prop :=
  if k < 26 then DF k else DT W₀ c₀ k

theorem rejOK_or {R₁ R₂ : Log → Log → Prop} (h₁ : RejOK R₁) (h₂ : RejOK R₂) :
    RejOK fun L es => R₁ L es ∨ R₂ L es where
  mono L es x h := h.imp (h₁.mono L es x) (h₂.mono L es x)
  sq L es x hs := or_congr (h₁.sq L es x hs) (h₂.sq L es x hs)
  stab L i hb hci X hX := or_congr (h₁.stab L i hb hci X hX) (h₂.stab L i hb hci X hX)

open Classical in
/-- **What the PIOP front still owes** (phases `0 … 25`, positions before P1.0). -/
structure FrontObl (RejF : Log → Log → Prop) (DF : ℕ → Log → Log → Prop)
    (W₀ : Log → Log → ℕ → K) (c₀ : Log → Log → K) : Prop where
  loc : FrontLocal W₀ c₀
  rej : RejOK RejF
  ms : ∀ s0 r, (s0, r) ∈ fsRanges4 → s0 + 1 < p1Start 0 →
    ∃ fin, DF (phOf4 (s0 + 1)) = msD (DF (phOf4 s0)) fin s0 r
  habs : ∀ L es x len, G.Matches (es ++ [x]) → fsItems4[es.length]? = some (.absorb len) →
    es.length < p1Start 0 → ¬ RejC RejF c₀ L es → DF (phOf4 (es.length - 1)) L es →
      RejC RejF c₀ L (es ++ [x]) ∨ DF (phOf4 es.length) L (es ++ [x])
  handoff : ∀ L es x len, G.Matches (es ++ [x]) → fsItems4[es.length]? = some (.absorb len) →
    es.length = p1Start 0 → ¬ RejC RejF c₀ L es → DF 25 L es →
      RejC RejF c₀ L (es ++ [x]) ∨ D1 W₀ c₀ 0 L (es ++ [x])
  hsingle : ∀ L es, G.Matches es → fsItems4[es.length]? = some .squeeze → fsRnd4 es.length = none →
    es.length < p1Start 0 → ¬ RejC RejF c₀ L es →
      (univ.filter fun a => DF (phOf4 (es.length - 1)) L es ∧
        ¬ DF (phOf4 es.length) L (ext1 es a)).card ≤ 239 * 2 ^ 128
  hfin : ∀ s0 r, (s0, r) ∈ fsRanges4 → s0 + 1 < p1Start 0 → ∀ L es₀, G.Matches es₀ →
    es₀.length = s0 + 1 → ¬ RejC RejF c₀ L es₀ → condCount (DPos (Dp DF)) L es₀ r [] ≤ deltaR
  hstab : ∀ k < 26, ∀ L i, ¬ Bad L → G.IsChain L i → ∀ X,
    StabExt fsRnd4 (entriesOf L (pathOf L i)) X → phOf4 (X.length - 1) = k →
      (DF k (L.take i) X ↔ DF k L X)

/-! ## Position facts -/

theorem front_check : ((List.range 30).all fun j => decide (p1Start 0 ≤ phStart4 (26 + j))) &&
    ((List.range 26).all fun k => decide (phStart4 (k + 1) ≤ p1Start 0)) &&
    phOf4 (p1Start 0 - 1) == 25 &&
    (List.range 5).all (fun i => fsItems4[cStart i]? != some .squeeze) &&
    fsRanges4.all (fun x => decide (x.1 + x.2 < p1Start 0) ||
      (List.range 5).any fun i => x == (cStart i, (lvlStar i).sq) || x == (p3S0 i, 5)) = true := by
  unfold p1Start cStart p3S0 phOf4 phStart4
  rw [fsStarts4_eq, fsRanges4_eq]; decide +kernel

theorem front_facts : (∀ j ≤ 29, p1Start 0 ≤ phStart4 (26 + j)) ∧
    (∀ k < 26, phStart4 (k + 1) ≤ p1Start 0) ∧ phOf4 (p1Start 0 - 1) = 25 ∧
    (∀ i < 5, fsItems4[cStart i]? ≠ some .squeeze) ∧
    ∀ x ∈ fsRanges4, x.1 + x.2 < p1Start 0 ∨
      ∃ i < 5, x = (cStart i, (lvlStar i).sq) ∨ x = (p3S0 i, 5) := by
  have h := front_check
  simp only [Bool.and_eq_true, List.all_eq_true, List.mem_range, decide_eq_true_eq, beq_iff_eq,
    bne_iff_ne, ne_eq, Bool.or_eq_true, List.any_eq_true] at h
  obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := h
  refine ⟨fun j hj => h1 j (by omega), h2, h3, h4, fun x hx => ?_⟩
  rcases h5 x hx with h | ⟨i, hi, h⟩
  · exact Or.inl h
  · exact Or.inr ⟨i, hi, h⟩

theorem phOf_lt_26 {p : ℕ} (hp : p < p1Start 0) : phOf4 p < 26 := by
  by_contra h
  obtain ⟨h1, h2, -⟩ := phOf_bounds p
  have := front_facts.1 (phOf4 p - 26) (by omega)
  rw [show 26 + (phOf4 p - 26) = phOf4 p by omega] at this
  omega

theorem phOf_ge_26 {p : ℕ} (hp : p1Start 0 ≤ p) : 26 ≤ phOf4 p := by
  by_contra h
  obtain ⟨-, -, h3⟩ := phOf_bounds p
  have := front_facts.2.1 (phOf4 p) (by omega)
  have := h3 (by omega)
  omega

theorem DkC_lt {DF : ℕ → Log → Log → Prop} {W₀ : Log → Log → ℕ → K} {c₀ : Log → Log → K}
    {k : ℕ} (h : k < 26) : DkC DF W₀ c₀ k = DF k := by rw [DkC, ite_pos' h]

theorem DkC_ge {DF : ℕ → Log → Log → Prop} {W₀ : Log → Log → ℕ → K} {c₀ : Log → Log → K}
    {k : ℕ} (h : 26 ≤ k) : DkC DF W₀ c₀ k = DT W₀ c₀ k := by rw [DkC, ite_neg' (by omega)]

/-- Checked: the class of every tail position (P1.i's absorb or squeeze, C.i, inside P2.i or
P3.i, Pf's absorb or squeeze), with the phases of it and of its predecessor. -/
def tailCls (p : ℕ) : Bool :=
  (List.range 5).any (fun i => (List.range (hEll i)).any fun l =>
      (p == p1Start i + 2 * l && phOf4 p == 26 + 5 * i &&
        ((l == 0 && phOf4 (p - 1) == 25 + 5 * i) || (l != 0 && phOf4 (p - 1) == 26 + 5 * i))) ||
      (p == p1Start i + 2 * l + 1 && phOf4 p == 26 + 5 * i && phOf4 (p - 1) == 26 + 5 * i)) ||
  (List.range 5).any (fun i => (p == cStart i && phOf4 p == 27 + 5 * i &&
      phOf4 (p - 1) == 26 + 5 * i) || (decide (cStart i < p) && decide (p ≤ p3S0 i + 5))) ||
  (List.range 7).any (fun l =>
      (p == pfStart + 2 * l && phOf4 p == 51 &&
        ((l == 0 && phOf4 (p - 1) == 50) || (l != 0 && phOf4 (p - 1) == 51))) ||
      (p == pfStart + 2 * l + 1 && phOf4 p == 51 && phOf4 (p - 1) == 51))

/-- Checked up to the cap check (`phStart4 52`, revision 4.4.1); its four positions are
`cap_items`'. -/
theorem tailCls_check : (List.range (phStart4 52 - p1Start 0)).all
    (fun j => tailCls (p1Start 0 + j)) = true := by
  unfold tailCls p1Start cStart p3S0 pfStart hEll phOf4 phStart4
  rw [fsStarts4_eq]; decide +kernel

theorem tail_cls {p : ℕ} (h1 : p1Start 0 ≤ p) (h2 : p < phStart4 52) :
    (∃ i < 5, ∃ l < hEll i, p = p1Start i + 2 * l ∧ phOf4 p = 26 + 5 * i ∧
      ((l = 0 ∧ phOf4 (p - 1) = 25 + 5 * i) ∨ (l ≠ 0 ∧ phOf4 (p - 1) = 26 + 5 * i))) ∨
    (∃ i < 5, ∃ l < hEll i, p = p1Start i + 2 * l + 1 ∧ phOf4 p = 26 + 5 * i ∧
      phOf4 (p - 1) = 26 + 5 * i) ∨
    (∃ i < 5, p = cStart i ∧ phOf4 p = 27 + 5 * i ∧ phOf4 (p - 1) = 26 + 5 * i) ∨
    (∃ i < 5, cStart i < p ∧ p ≤ p3S0 i + 5) ∨
    (∃ l < 7, p = pfStart + 2 * l ∧ phOf4 p = 51 ∧
      ((l = 0 ∧ phOf4 (p - 1) = 50) ∨ (l ≠ 0 ∧ phOf4 (p - 1) = 51))) ∨
    (∃ l < 7, p = pfStart + 2 * l + 1 ∧ phOf4 p = 51 ∧ phOf4 (p - 1) = 51) := by
  have h := tailCls_check
  simp only [List.all_eq_true, List.mem_range] at h
  have hc := h (p - p1Start 0) (by omega)
  rw [show p1Start 0 + (p - p1Start 0) = p by omega] at hc
  simp only [tailCls, Bool.or_eq_true, List.any_eq_true, List.mem_range, Bool.and_eq_true,
    beq_iff_eq, bne_iff_ne, ne_eq, decide_eq_true_eq] at hc
  rcases hc with (⟨i, hi, l, hl, h⟩ | ⟨i, hi, h⟩) | ⟨l, hl, h⟩
  · rcases h with ⟨⟨h1, h2⟩, h3⟩ | ⟨⟨h1, h2⟩, h3⟩
    · exact Or.inl ⟨i, hi, l, hl, h1, h2, h3⟩
    · exact Or.inr (Or.inl ⟨i, hi, l, hl, h1, h2, h3⟩)
  · rcases h with ⟨⟨h1, h2⟩, h3⟩ | ⟨h1, h2⟩
    · exact Or.inr (Or.inr (Or.inl ⟨i, hi, h1, h2, h3⟩))
    · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨i, hi, h1, h2⟩)))
  · rcases h with ⟨⟨h1, h2⟩, h3⟩ | ⟨⟨h1, h2⟩, h3⟩
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨l, hl, h1, h2, h3⟩))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨l, hl, h1, h2, h3⟩))))

/-- A position inside a multi-squeeze phase is a squeeze of that phase. -/
theorem sq_of_mem {s0 r p : ℕ} (hx : (s0, r) ∈ fsRanges4) (h1 : s0 < p) (h2 : p ≤ s0 + r) :
    fsItems4[p]? = some .squeeze ∧ fsRnd4 p = some (s0, r) := by
  have h := rangesOK4_eq
  simp only [rangesOK4, List.all_eq_true, List.mem_range, Bool.and_eq_true, beq_iff_eq] at h
  have := h _ hx (p - (s0 + 1)) (by simp; omega)
  rwa [show s0 + 1 + (p - (s0 + 1)) = p by omega] at this

theorem sq_tail {i p : ℕ} (hi : i < 5) (h1 : cStart i < p) (h2 : p ≤ p3S0 i + 5) :
    fsItems4[p]? = some .squeeze ∧ fsRnd4 p ≠ none := by
  obtain ⟨-, -, -, -, -, -, -, -, -, hm2, hm3⟩ := tail_ph hi
  have hsq := (tail_pos hi).2.2.2.1
  by_cases h : p ≤ p3S0 i
  · obtain ⟨a, b⟩ := sq_of_mem hm2 h1 (by omega); exact ⟨a, by rw [b]; simp⟩
  · obtain ⟨a, b⟩ := sq_of_mem hm3 (by omega) h2; exact ⟨a, by rw [b]; simp⟩

theorem lt_length_of_get {p : ℕ} {it : Item} (h : fsItems4[p]? = some it) : p < fsItems4.length := by
  by_contra hc; rw [List.getElem?_eq_none (by omega)] at h; simp at h

/-! ## The cap check's positions and the guarded checks (revision 4.4.1, A3′ run 2) -/

/-- The cap check's items (`CapD` absorb, `CapZeta` squeeze, `CapChk` absorb, `CapChkZ` squeeze), single
squeezes, at the end of the chain. -/
theorem cap_items : fsItems4[phStart4 52]? = some (.absorb 27872) ∧ fsItems4[phStart4 53]? = some .squeeze ∧
    fsItems4[phStart4 54]? = some (.absorb 49152) ∧ fsItems4[phStart4 55]? = some .squeeze ∧
    fsRnd4 (phStart4 53) = none ∧ fsRnd4 (phStart4 55) = none ∧ fsItems4.length = phStart4 55 + 1 := by
  obtain ⟨p52, p53, p54, p55⟩ := capPh_pos
  rw [p52, p53, p54, p55, fsItems4_length]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, rfl⟩
  all_goals first
    | (rw [fsItems4, Rev4.seq4_eq]; decide +kernel)
    | (unfold fsRnd4; rw [fsRanges4_eq]; decide)

/-- **Before `D`, or `D` true**: the guard of the composed checks. -/
def cdOK (es : Log) : Prop := es.length ≤ phStart4 52 ∨ truthCap es

/-- **The composed checks, guarded by the cap truth** (A3′ run 2, journal R2.2): once `D` is in the
chain, a failed level check (`RejT`'s round 0 of P1.(i+1) reads the committed words) counts only if
`D` is true; a false `D` is a doom (`DCapD`). On an accepted chain `RejG` fails either way. -/
def RejG (RejF : Log → Log → Prop) (c₀ : Log → Log → K) (L es : Log) : Prop :=
  RejC RejF c₀ L es ∧ cdOK es

theorem cdOK_append {es : Log} (h : es.length ≠ phStart4 52) (x : ByteArray × Digest) :
    cdOK (es ++ [x]) ↔ cdOK es := by
  unfold cdOK
  rw [List.length_append, List.length_singleton]
  rcases Nat.lt_or_ge es.length (phStart4 52) with hl | hl
  · exact ⟨fun _ => Or.inl (by omega), fun _ => Or.inl (by omega)⟩
  · have hl' : phStart4 53 ≤ es.length := by have := capPh_pos; omega
    rw [(capD_congr (agree_append es [x] hl')).2.2]
    exact ⟨fun h' => h'.resolve_left (by omega) |> Or.inr, fun h' => h'.resolve_left (by omega) |> Or.inr⟩

theorem rejG_of {RejF : Log → Log → Prop} {c₀ : Log → Log → K} {L es : Log}
    (h : RejC RejF c₀ L es) (hl : es.length ≤ phStart4 52) : RejG RejF c₀ L es := ⟨h, Or.inl hl⟩

theorem not_rejC_of {RejF : Log → Log → Prop} {c₀ : Log → Log → K} {L es : Log}
    (h : ¬ RejG RejF c₀ L es) (hl : es.length ≤ phStart4 52) : ¬ RejC RejF c₀ L es := fun h' => h ⟨h', Or.inl hl⟩

theorem rejG_sq {RejF : Log → Log → Prop} {c₀ : Log → Log → K} (hR : RejOK (RejC RejF c₀)) :
    RejSq (RejG RejF c₀) where
  sq L es x hit := by
    have h52 : es.length ≠ phStart4 52 := fun h => by rw [h, cap_items.1] at hit; cases hit
    unfold RejG; rw [hR.sq L es x hit, cdOK_append h52]
  stab L i hb hci X hX := by unfold RejG; rw [hR.stab L i hb hci X hX]

theorem phOf_cap : phOf4 (phStart4 52 - 1) = 51 ∧ phOf4 (phStart4 52) = 52 ∧ phOf4 (phStart4 53) = 53 ∧
    phOf4 (phStart4 54) = 54 ∧ phOf4 (phStart4 55) = 55 := by
  have e : pfStart = 468 := by unfold pfStart phStart4; rw [fsStarts4_eq]; rfl
  obtain ⟨p52, p53, p54, p55⟩ := capPh_pos
  refine ⟨(phOf_ge (by omega)).1 (by omega), (phOf_ge (by omega)).2.1 rfl, (phOf_ge (by omega)).2.2.1 rfl,
    (phOf_ge (by omega)).2.2.2.1 rfl, (phOf_ge (by omega)).2.2.2.2 le_rfl⟩

variable {RejF : Log → Log → Prop} {DF : ℕ → Log → Log → Prop} {W₀ : Log → Log → ℕ → K}
  {c₀ : Log → Log → K}

/-- **`hrej`**: at an absorb a guarded check that held still holds, or (at `CapD`) `D` is false. -/
theorem hrej_G (hR : RejOK (RejC RejF c₀)) (L es : Log) (x : ByteArray × Digest)
    (h : RejG RejF c₀ L es) :
    RejG RejF c₀ L (es ++ [x]) ∨ DkC DF W₀ c₀ (phOf4 es.length) L (es ++ [x]) := by
  have hr := hR.mono L es x h.1
  by_cases h52 : es.length = phStart4 52
  · by_cases ht : truthCap (es ++ [x])
    · exact Or.inl ⟨hr, Or.inr ht⟩
    · right
      rw [h52, phOf_cap.2.1, DkC_ge (by norm_num), (DT_cap W₀ c₀).1]
      exact Or.inr ht
  · exact Or.inl ⟨hr, (cdOK_append h52 x).2 h.2⟩

/-- **The cap check's absorbs** (`CapD`, `CapChk`): an absorb never undooms. -/
theorem habs_cap (hF : FrontLocal W₀ c₀) {L es : Log} {x : ByteArray × Digest} {len : ℕ}
    (hit : fsItems4[es.length]? = some (.absorb len)) (h52 : phStart4 52 ≤ es.length)
    (hd : DT W₀ c₀ (phOf4 (es.length - 1)) L es) : DT W₀ c₀ (phOf4 es.length) L (es ++ [x]) := by
  obtain ⟨i52, i53, i54, i55, -, -, hlen⟩ := cap_items
  obtain ⟨p52, p53, p54, p55⟩ := capPh_pos
  obtain ⟨f51, f52, f53, f54, f55⟩ := phOf_cap
  obtain ⟨d52, d53, d54, d55⟩ := DT_cap W₀ c₀
  have hlt := lt_length_of_get hit
  have hpf : pfStart + 14 ≤ es.length := by rw [pfStart_eq]; omega
  have e : es.length = phStart4 52 ∨ es.length = phStart4 54 := by
    rcases (show es.length = 482 ∨ es.length = 483 ∨ es.length = 484 ∨ es.length = 485 by omega) with
      h | h | h | h
    · exact Or.inl (by omega)
    · rw [show es.length = phStart4 53 by omega, i53] at hit; cases hit
    · exact Or.inr (by omega)
    · rw [show es.length = phStart4 55 by omega, i55] at hit; cases hit
  rcases e with e | e
  · rw [e, f52, d52]
    rw [show es.length - 1 = phStart4 52 - 1 by omega, f51, DT_Pf] at hd
    exact Or.inl ((DPf_append hF hpf x).2 hd)
  · rw [e, f54, d54]
    rw [show es.length - 1 = phStart4 53 by omega, f53, d53] at hd
    have hag : Agree (es ++ [x]) es (phStart4 54) := agree_append es [x] (by omega)
    have ht := (capD_congr (hag.mono (by omega))).2.2
    have hs := (capZeta_congr hag).2.2.2.1
    rcases hd with ⟨hp, htc⟩ | ⟨htc, hsg⟩
    · exact Or.inl ⟨(DPf_append hF hpf x).2 hp, ht.2 htc⟩
    · by_cases ha : aHon (es ++ [x])
      · exact Or.inr (Or.inl ⟨ha, fun h => htc (ht.1 h), fun h => hsg (hs.1 h)⟩)
      · exact Or.inr (Or.inr ha)

open Classical in
/-- **The cap check's squeezes** (`CapZeta`, `CapChkZ`): the escapes are `DZeta` (`≤ 870`) and
`DZ` (`≤ 1,535`) answers. -/
theorem single_cap (hF : FrontLocal W₀ c₀) {L es : Log} (hit : fsItems4[es.length]? = some .squeeze)
    (h52 : phStart4 52 ≤ es.length) :
    (univ.filter fun a => DT W₀ c₀ (phOf4 (es.length - 1)) L es ∧
      ¬ DT W₀ c₀ (phOf4 es.length) L (ext1 es a)).card ≤ 239 * 2 ^ 128 := by
  obtain ⟨i52, i53, i54, i55, -, -, hlen⟩ := cap_items
  obtain ⟨p52, p53, p54, p55⟩ := capPh_pos
  obtain ⟨f51, f52, f53, f54, f55⟩ := phOf_cap
  obtain ⟨d52, d53, d54, d55⟩ := DT_cap W₀ c₀
  have hlt := lt_length_of_get hit
  have hpf : pfStart + 14 ≤ es.length := by rw [pfStart_eq]; omega
  have hP : ∀ a, DPf W₀ c₀ L (ext1 es a) ↔ DPf W₀ c₀ L es := fun a => DPf_append hF hpf _
  have e : es.length = phStart4 53 ∨ es.length = phStart4 55 := by
    rcases (show es.length = 482 ∨ es.length = 483 ∨ es.length = 484 ∨ es.length = 485 by omega) with
      h | h | h | h
    · rw [show es.length = phStart4 52 by omega, i52] at hit; cases hit
    · exact Or.inl (by omega)
    · rw [show es.length = phStart4 54 by omega, i54] at hit; cases hit
    · exact Or.inr (by omega)
  rcases e with e | e
  · rw [e, f53, d53, show phStart4 53 - 1 = phStart4 52 by omega, f52, d52]
    have hag : ∀ a, Agree (ext1 es a) es (phStart4 53) := fun a => by
      rw [ext1]; exact agree_append es _ (by omega)
    have ht : ∀ a, truthCap (ext1 es a) ↔ truthCap es := fun a => (capD_congr (hag a)).2.2
    by_cases htc : truthCap es
    · rw [filter_false_of_mem fun a _ h => h.2 (Or.inl ⟨(hP a).2 (h.1.resolve_right (not_not.2 htc)),
        (ht a).2 htc⟩)]
      simp
    · refine le_trans (card_le_card fun a ha => ?_) ((card_dZeta e htc).trans (by norm_num))
      simp only [mem_filter, mem_univ, true_and] at ha ⊢
      by_contra hs
      exact ha.2 (Or.inr ⟨fun h => htc ((ht a).1 h), hs⟩)
  · rw [e, f55, d55, show phStart4 55 - 1 = phStart4 54 by omega, f54, d54]
    have hag : ∀ a, Agree (ext1 es a) es (phStart4 55) := fun a => by
      rw [ext1]; exact agree_append es _ (by omega)
    have ht : ∀ a, truthCap (ext1 es a) ↔ truthCap es := fun a => (capD_congr ((hag a).mono (by omega))).2.2
    have hs : ∀ a, capSig0 (ext1 es a) ↔ capSig0 es := fun a => (capZeta_congr ((hag a).mono (by omega))).2.2.2.1
    have hon : ∀ a, aHon (ext1 es a) ↔ aHon es := fun a => (capA_congr (hag a)).2
    by_cases ha : aHon es
    · rw [filter_false_of_mem fun a _ h => ?_]
      · simp
      rcases h.1 with ⟨hp, htc⟩ | ⟨-, htc, hsg⟩ | hna
      · exact h.2 (Or.inl ⟨(hP a).2 hp, (ht a).2 htc⟩)
      · exact h.2 (Or.inr (Or.inl ⟨(hon a).2 ha, fun h' => htc ((ht a).1 h'), fun h' => hsg ((hs a).1 h')⟩))
      · exact hna ha
    · refine le_trans (card_le_card fun a hm => ?_) ((card_dZ e ha).trans (by norm_num))
      simp only [mem_filter, mem_univ, true_and] at hm ⊢
      by_contra hne
      exact hm.2 (Or.inr (Or.inr ⟨fun h' => ha ((hon a).1 h'), hne⟩))

/-! ## `PhaseObl` -/

/-- **The per-phase obligations of the whole transcript**, from the front's and the tail's. -/
theorem phaseObl_of (hFr : FrontObl RejF DF W₀ c₀) :
    PhaseObl (RejG RejF c₀) (DkC DF W₀ c₀) (239 * 2 ^ 128) where
  rej := rejG_sq (rejOK_or hFr.rej (rejT_ok hFr.loc))
  hrej L es x _ _ _ h := hrej_G (rejOK_or hFr.rej (rejT_ok hFr.loc)) L es x h
  ms s0 r hmem := by
    by_cases h : s0 + 1 < p1Start 0
    · obtain ⟨fin, hf⟩ := hFr.ms s0 r hmem h
      exact ⟨fin, by rw [DkC_lt (phOf_lt_26 h), DkC_lt (phOf_lt_26 (by omega)), hf]⟩
    rcases front_facts.2.2.2.2 _ hmem with hx | ⟨i, hi, hx | hx⟩
    · have := (ms_phOf hmem).1; simp at hx; omega
    · simp only [Prod.mk.injEq] at hx; obtain ⟨rfl, rfl⟩ := hx
      exact ⟨_, ms_P2 hi (by rw [DkC_ge (by omega), DT_C W₀ c₀ hi])
        (by rw [DkC_ge (by omega), DT_P2 W₀ c₀ hi])⟩
    · simp only [Prod.mk.injEq] at hx; obtain ⟨rfl, rfl⟩ := hx
      exact ⟨_, ms_P3 hi (by rw [DkC_ge (by omega), DT_P2 W₀ c₀ hi])
        (by rw [DkC_ge (by omega), DT_P3 W₀ c₀ hi])⟩
  habs L es x len hm hit hr hd := by
    have hlt := lt_length_of_get hit
    have h0 : p1Start 0 < phStart4 52 := by
      unfold p1Start phStart4; rw [fsStarts4_eq]; decide
    by_cases hcap : phStart4 52 ≤ es.length
    · right
      rw [DkC_ge (phOf_ge_26 (by omega))] at hd
      rw [DkC_ge (phOf_ge_26 (by omega))]
      exact habs_cap hFr.loc hit hcap hd
    have hr' := not_rejC_of hr (by omega)
    by_cases hp : es.length < p1Start 0
    · rw [DkC_lt (phOf_lt_26 (by omega))] at hd
      rw [DkC_lt (phOf_lt_26 hp)]
      exact (hFr.habs L es x len hm hit hp hr' hd).imp_left fun h => rejG_of h (by simp; omega)
    by_cases hp' : es.length = p1Start 0
    · rw [hp', front_facts.2.2.1, DkC_lt (by norm_num)] at hd
      have := (hFr.handoff L es x len hm hit hp' hr' hd).imp_left fun h => rejG_of h (by simp; omega)
      have hD : DT W₀ c₀ 26 = D1 W₀ c₀ 0 := DT_P1 W₀ c₀ (i := 0) (by norm_num)
      rwa [hp', (tail_ph (show 0 < 5 by norm_num)).1, DkC_ge le_rfl, hD]
    rcases tail_cls (by omega) (by omega : es.length < phStart4 52) with ⟨i, hi, l, hl, he, h1, h2⟩ | ⟨i, hi, l, hl, he, -, -⟩ |
      ⟨i, hi, he, h1, h2⟩ | ⟨i, hi, h1, h2⟩ | ⟨l, hl, he, h1, h2⟩ | ⟨l, hl, he, -, -⟩
    · right
      rw [h1, DkC_ge (by omega), DT_P1 W₀ c₀ hi]
      rcases h2 with ⟨rfl, h2⟩ | ⟨hl0, h2⟩
      · obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by
          rcases Nat.eq_zero_or_pos i with rfl | h
          · simp at he; omega
          · omega⟩
        rw [h2, show 25 + 5 * (j + 1) = 30 + 5 * j by ring, DkC_ge (by omega),
          DT_P3 W₀ c₀ (by omega), DP3, msD, ite_neg' (by
            have := (tail_pos (show j < 5 by omega)).2.2.2.2
            rw [nxStart_le hi] at this; omega)] at hd
        exact habs_P1_next hFr.loc x hi (by omega) hd
      · rw [h2, DkC_ge (by omega), DT_P1 W₀ c₀ hi] at hd
        exact habs_P1 hFr.loc x hi (by omega) he hd
    · have := (rounds_P1 hi hl).2; rw [← he, hit] at this; simp at this
    · right
      rw [h2, DkC_ge (by omega), DT_P1 W₀ c₀ hi] at hd
      rw [h1, DkC_ge (by omega), DT_C W₀ c₀ hi]
      exact habs_C hFr.loc x hi he hd
    · have := (sq_tail hi h1 h2).1; rw [hit] at this; simp at this
    · right
      rw [h1, DkC_ge (by omega), DT_Pf]
      rcases h2 with ⟨rfl, h2⟩ | ⟨hl0, h2⟩
      · rw [h2, show (50 : ℕ) = 30 + 5 * 4 by norm_num, DkC_ge (by omega),
          DT_P3 W₀ c₀ (by norm_num), DP3, msD, ite_neg' (by
            have := (tail_pos (show 4 < 5 by norm_num)).2.2.2.2
            have hnx : nxStart 4 = pfStart := rfl
            omega)] at hd
        exact habs_Pf_first hFr.loc x (by omega) hd
      · rw [h2, DkC_ge (by omega), DT_Pf] at hd
        exact habs_Pf hFr.loc x (by omega) he hd
    · have := (rounds_Pf hl).2; rw [← he, hit] at this; simp at this
  hsingle L es hm hit hrnd hr := by
    have hlt := lt_length_of_get hit
    have h0 : p1Start 0 < phStart4 52 := by
      unfold p1Start phStart4; rw [fsStarts4_eq]; decide
    by_cases hcap : phStart4 52 ≤ es.length
    · have e1 : 26 ≤ phOf4 (es.length - 1) := phOf_ge_26 (by omega)
      have e2 : 26 ≤ phOf4 es.length := phOf_ge_26 (by omega)
      have hc := single_cap hFr.loc hit hcap (L := L)
      refine le_trans (card_le_card ?_) hc
      intro a ha
      simp only [mem_filter, mem_univ, true_and] at ha ⊢
      rwa [DkC_ge e1, DkC_ge e2] at ha
    have hr' := not_rejC_of hr (by omega)
    by_cases hp : es.length < p1Start 0
    · rw [DkC_lt (phOf_lt_26 (by omega)), DkC_lt (phOf_lt_26 hp)]
      exact hFr.hsingle L es hm hit hrnd hp hr'
    have hrT : ¬ RejT c₀ L es := fun h => hr' (Or.inr h)
    rcases tail_cls (by omega) (by omega : es.length < phStart4 52) with ⟨i, hi, l, hl, he, -, -⟩ | ⟨i, hi, l, hl, he, h1, h2⟩ |
      ⟨i, hi, he, -, -⟩ | ⟨i, hi, h1, h2⟩ | ⟨l, hl, he, -, -⟩ | ⟨l, hl, he, h1, h2⟩
    · have := (rounds_P1 hi hl).1; rw [← he, hit] at this; simp at this
    · rw [h1, h2, DkC_ge (by omega), DT_P1 W₀ c₀ hi]
      exact (single_P1 hFr.loc hi hl he hrT).trans (p1_N_le _ hi)
    · exact absurd (he ▸ hit) (front_facts.2.2.2.1 i hi)
    · exact absurd hrnd (sq_tail hi h1 h2).2
    · have := (rounds_Pf hl).1; rw [← he, hit] at this; simp at this
    · rw [h1, h2, DkC_ge (by omega), DT_Pf]
      exact (single_Pf hFr.loc he hrT).trans (by norm_num)
  hfin s0 r hmem L es₀ hm hl hr := by
    by_cases h : s0 + 1 < p1Start 0
    · have hb : s0 + r < p1Start 0 := by
        rcases front_facts.2.2.2.2 _ hmem with hx | ⟨i, hi, hx | hx⟩
        · exact hx
        all_goals
          simp only [Prod.mk.injEq] at hx; obtain ⟨rfl, rfl⟩ := hx
          have h0 : p1Start 0 ≤ p1Start i := front_facts.1 (5 * i) (by omega)
          obtain ⟨-, -, h3, h4, -⟩ := tail_pos hi
          omega
      have h0 : p1Start 0 < phStart4 52 := by
        unfold p1Start phStart4; rw [fsStarts4_eq]; decide
      refine le_trans (le_of_eq (condCount_congr fun as has => ?_))
        (hFr.hfin s0 r hmem h L es₀ hm hl (not_rejC_of hr (by omega)))
      have hlx := length_ext as es₀
      have hd : (ext es₀ as).dropLast.length = s0 + r := by
        rw [List.length_dropLast]; omega
      simp only [EscAtG, DPos, Dp, hd, hlx, hl, has]
      rw [DkC_lt (phOf_lt_26 (by omega)), DkC_lt (phOf_lt_26 (by omega))]
    rcases front_facts.2.2.2.2 _ hmem with hx | ⟨i, hi, hx | hx⟩
    · have := (ms_phOf hmem).1; simp at hx; omega
    · simp only [Prod.mk.injEq] at hx; obtain ⟨rfl, rfl⟩ := hx
      exact hfin_P2 hFr.loc hi (by rw [DkC_ge (by omega), DT_C W₀ c₀ hi])
        (by rw [DkC_ge (by omega), DT_P2 W₀ c₀ hi]) L es₀ hl
    · simp only [Prod.mk.injEq] at hx; obtain ⟨rfl, rfl⟩ := hx
      exact hfin_P3 hFr.loc hi (by rw [DkC_ge (by omega), DT_P2 W₀ c₀ hi])
        (by rw [DkC_ge (by omega), DT_P3 W₀ c₀ hi]) L es₀ hl
  hstab k L i hb hci X hX hk := by
    by_cases h : k < 26
    · rw [DkC_lt h]; exact hFr.hstab k h L i hb hci X hX hk
    rw [DkC_ge (by omega)]
    have hX1 : 1 ≤ X.length := by
      obtain ⟨s0, r, as, -, hs, -, rfl⟩ := hX
      rw [length_ext, List.length_take]; omega
    obtain ⟨h1, h2, -⟩ := phOf_bounds (X.length - 1)
    rw [hk] at h1 h2
    exact DT_stab hFr.loc (by omega) h2 (same_stabX hb hci hX) le_rfl (by omega)

/-- T4: **the potential's laws at `εR` from the front's obligations** (3.x's `kstate_of_front`
without 3.x's `KState`/`FinalLaw`, whose verifier is 3.x's): `muT (RejG …) (DkC …)` starts at `0`
and meets the contract's `step` law at `εR = 15/2^124`. These are `ks4_of`'s `h0` and `hstep`
(`ks4_of_front`, `FRSoundness4TailLig`). -/
theorem muT_laws_of_front (hFr : FrontObl RejF DF W₀ c₀) :
    muT (RejG RejF c₀) (DkC DF W₀ c₀) [] = 0 ∧
    ∀ L q, L.length < logCap → muT (RejG RejF c₀) (DkC DF W₀ c₀) L < 1 → q ∉ L.map Prod.fst →
      ∑ a : Digest, muT (RejG RejF c₀) (DkC DF W₀ c₀) (L ++ [(q, a)]) ≤
        (muT (RejG RejF c₀) (DkC DF W₀ c₀) L + epsR) * 2 ^ 256 :=
  ⟨muT_empty _ _, fun L q hl hμ hq => muT_step N_le (phaseObl_of hFr) L q hl hμ hq⟩

/-! ## Stability on the chain itself (`ChainStab`, S-G1h deviation 1) -/

/-- On a non-bad log, a chain reads the same off the log before its last entry and off the log
(its caps are real entries, `capOK_of_matches`, `wordK_stab`). -/
theorem same_chain {L : Log} (hb : ¬ Bad L) {j : ℕ} (hci : G.IsChain L j) :
    Same (L.take j) (entriesOf L (pathOf L j)) L (entriesOf L (pathOf L j))
      (entriesOf L (pathOf L j)).length := by
  set es := entriesOf L (pathOf L j)
  have hes : ext (es.take es.length) [] = es := by rw [ext_nil, List.take_length]
  refine ⟨fun _ _ => rfl, fun κ i hi hc => ?_⟩
  have hw := wordK_stab hb hci es.length [] hi κ (by rw [hes]; exact capOK_of_matches hci.2 hi hc)
  rwa [hes] at hw

/-- The tail's asserted checks read the same off two logs whose words agree. -/
theorem rejT_same (hF : FrontLocal W₀ c₀) {L L' Y : Log} {p : ℕ} (hS : Same L Y L' Y p)
    (hY : Y.length ≤ p) : RejT c₀ L Y ↔ RejT c₀ L' Y := by
  refine or_congr ⟨fun ⟨i, hi, j, hj, hlt, hc⟩ => ⟨i, hi, j, hj, hlt, fun h' => hc ?_⟩,
    fun ⟨i, hi, j, hj, hlt, hc⟩ => ⟨i, hi, j, hj, hlt, fun h' => hc ?_⟩⟩
    ⟨fun ⟨j, hj, hlt, hc⟩ => ⟨j, hj, hlt, fun h' => hc ?_⟩,
    fun ⟨j, hj, hlt, hc⟩ => ⟨j, hj, hlt, fun h' => hc ?_⟩⟩
  · exact (chk2_same hS (by omega) (lvC_same hF hS hi (by omega))).mpr h'
  · exact (chk2_same hS (by omega) (lvC_same hF hS hi (by omega))).mp h'
  · exact (chk2_same hS (by omega) (lvC5_same hF hS (by omega))).mpr h'
  · exact (chk2_same hS (by omega) (lvC5_same hF hS (by omega))).mp h'

/-- What the front owes for `ChainStab`: its checks and dooms read the same on the chain itself. -/
def FrontChainStab (RejF : Log → Log → Prop) (DF : ℕ → Log → Log → Prop) : Prop :=
  ∀ L j, ¬ Bad L → G.IsChain L j →
    (RejF (L.take j) (entriesOf L (pathOf L j)) ↔ RejF L (entriesOf L (pathOf L j))) ∧
    ∀ k < 26, phOf4 ((entriesOf L (pathOf L j)).length - 1) = k →
      (DF k (L.take j) (entriesOf L (pathOf L j)) ↔ DF k L (entriesOf L (pathOf L j)))

/-- **`ChainStab` for the whole transcript's doom** (what `final`'s walk needs, S-G1h deviation 1;
revision 4.4.1: the checks guarded, `RejG`):
the tail's part is proved (`same_chain`, `DT_stab`, `rejT_same`); the front's is `FrontChainStab`. -/
theorem chainStab_of (hF : FrontLocal W₀ c₀) (hFS : FrontChainStab RejF DF) :
    ChainStab (DC (RejG RejF c₀) (Dp (DkC DF W₀ c₀))) := by
  intro L j hb hci
  set es := entriesOf L (pathOf L j)
  have hS := same_chain hb hci
  obtain ⟨hR, hD⟩ := hFS L j hb hci
  have h1 : 1 ≤ es.length := List.length_pos_iff.mpr (G.matches_ne_nil hci.2)
  unfold DC RejG RejC DPos Dp
  refine or_congr (and_congr (or_congr hR (rejT_same hF hS le_rfl)) Iff.rfl) ?_
  by_cases hk : phOf4 (es.length - 1) < 26
  · rw [DkC_lt hk]; exact hD _ hk rfl
  rw [DkC_ge (by omega)]
  obtain ⟨b1, b2, -⟩ := phOf_bounds (es.length - 1)
  have hl : (entriesOf L (pathOf L j)).length = es.length := rfl
  exact DT_stab hF (by omega) b2 hS le_rfl (by rw [hl]; omega)

/-! ## Controls -/

/-- Control (positive): on the empty log every intermediate fold is close (the word is `0`). -/
theorem closeP_nil (κ : CKind) (es : Log) {i l : ℕ} (hl : l ≤ (CKind.lv κ i).ell) :
    closeP κ [] es i l := closeP_of_not_far (not_farL_nil κ es i) l hl

/-- Control (positive): a far word before P1.i's first answer dooms P1.i (the far part is live). -/
theorem D1_of_far {i : ℕ} {L es : Log} (h0 : hRnd es i = 0) (hf : farL (kindOfC es) L es i) :
    D1 W₀ c₀ i L es := Or.inl (by rw [h0, closeP_zero, not_not]; exact hf)

/-- Control (negative): on the empty log, before P1.i's first absorb, P1.i is not doomed. -/
theorem not_D1_nil {i : ℕ} {es : Log} (hl : es.length ≤ p1Start i) : ¬ D1 W₀ c₀ i [] es := by
  rintro (h | ⟨-, hd⟩)
  · have h0 : hRnd es i = 0 := by unfold hRnd; omega
    rw [h0] at h; exact h (closeP_nil _ _ (Nat.zero_le _))
  · exact not_D2_short hl hd

/-- Control (negative): with every query consistent and no offset, P3.i's table is zero. -/
theorem p3T_zero {κ : CKind} {L es : Log} {i : ℕ} (h : truthP3 κ L es i) :
    tbl 9 (p3T κ L es i 0) = 0 := by
  funext q
  rw [tbl_p3T, add_zero]
  split_ifs with hq
  · exact h q hq
  · rfl

/-- Control (negative): no tail check fails before P1.0's first absorb. -/
theorem not_rejT_short {L es : Log} (hl : es.length ≤ p1Start 0) : ¬ RejT c₀ L es := by
  rintro (⟨i, hi, j, -, hlt, -⟩ | ⟨j, -, hlt, -⟩)
  · have : p1Start 0 ≤ p1Start i := front_facts.1 (5 * i) (by omega)
    omega
  · have : p1Start 0 ≤ pfStart := front_facts.1 25 (by norm_num)
    omega

open Classical in
/-- Control (positive, satisfiability): the empty front with constant `W₀`, `c₀` meets
`FrontObl` (the interface is not contradictory). -/
theorem frontObl_false :
    FrontObl (fun _ _ => False) (fun _ _ _ => False) (fun _ _ _ => 0) (fun _ _ => 0) where
  loc _ _ _ _ _ _ _ := ⟨rfl, rfl⟩
  rej := rejOK_false
  ms _ _ _ _ := ⟨fun _ _ => False, by funext L es; simp only [msD, eq_iff_iff]; split_ifs <;> rfl⟩
  habs _ _ _ _ _ _ _ _ h := h.elim
  handoff _ _ _ _ _ _ _ _ h := h.elim
  hsingle _ _ _ _ _ _ _ := by simp
  hfin _ _ _ _ L es₀ _ _ _ := by
    rw [condCount_eq_zero fun _ _ h => h.2.1]; exact zero_le
  hstab _ _ _ _ _ _ _ _ _ := Iff.rfl

end FR.Snd.T4

