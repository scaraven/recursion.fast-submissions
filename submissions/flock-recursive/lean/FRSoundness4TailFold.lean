-- New for `flock-recursive` (BLUEPRINT §5.1, §5.4, A.10; stage T4, S-G13 route C): a copy-port of
-- `FRSoundnessWalk`, `FRSoundnessWeights` and `FRSoundnessFold` to revision 4.1's item sequence `seq4` (namespace `FR.Snd.T4`, see `FRSoundness4TailStep`):
-- the declarations that read positions, chains or the kind are copied, the rest is imported.
import FRSoundness4TailHide

/-!
# The walk, the weights and the folds at `seq4` (T4)

The 3.x declarations of `FRSoundnessWalk`, `FRSoundnessWeights` and `FRSoundnessFold` that read the positions, the chains or the kind, restated in
`FR.Snd.T4` over `fsItems4`/`phStart4`/`fsRnd4`, `G.Matches`/`G.IsChain` and `CKind`
(`kindOfC`, `CKind.lv`). Positions from P1.0 on are 3.x's plus 14 (`phStart4_shift`); the kind
enters through the ladder `lvOf κ.m` only. Changes beyond the renaming are marked `T4:`.
-/

/-! # Port of `FRSoundnessWalk` (its module doc describes the 3.x original) -/

namespace FR.Snd.T4
open RecursionFast FR.Merkle

/-! ## Part A: logs and their prefixes -/

theorem isChain_take {L : Log} {j : ℕ} (h : G.IsChain L j) {t : ℕ} (ht : j < t) :
    G.IsChain (L.take t) j :=
  ⟨by simp; exact ⟨ht, h.1⟩, by rw [entriesOf_pathOf_take L ht]; exact h.2⟩

/-! ## Part B: the walk -/

/-- **Stability of a doom on chains**: on a non-bad log, `D` reads the same off the log before a
chain's last entry and off the log, on the chain itself (the reads of A.10's `hstab` column, on
the real chain). -/
def ChainStab (D : Log → Log → Prop) : Prop :=
  ∀ L j, ¬ Bad L → G.IsChain L j →
    (D (L.take j) (entriesOf L (pathOf L j)) ↔ D L (entriesOf L (pathOf L j)))

/-- A nonempty prefix of a matching chain matches. -/
theorem matches_take {es : Log} (h : G.Matches es) : ∀ d k, es.length = k + d → 1 ≤ k →
    G.Matches (es.take k) := by
  intro d
  induction d with
  | zero => intro k hk _; rw [List.take_of_length_le (by omega)]; exact h
  | succ d ih =>
    intro k hk h1
    have h' := ih (k + 1) (by omega) (by omega)
    rw [List.take_add_one, List.getElem?_eq_getElem (by omega), Option.toList_some] at h'
    exact G.matches_of_append (fun he => by
      have := congrArg List.length he; rw [List.length_take, List.length_nil] at this; omega) h'

theorem isChain_prefix {L : Log} {i : ℕ} (hci : G.IsChain L i) {m : ℕ}
    (hm : m < (pathOf L i).length) : G.IsChain L (pathOf L i)[m] := by
  refine ⟨lt_of_le_of_lt (mem_pathOf_le (List.getElem_mem _)) hci.1, ?_⟩
  rw [entriesOf_prefix L i hm]
  exact matches_take hci.2 ((pathOf L i).length - (m + 1)) (m + 1)
    (by rw [length_entriesOf]; omega) (by omega)

/-- **One step of the walk**: with no escape, `D` on the chain's first `m + 1` entries (charged at
the `(m+1)`-th) gives `D` on its first `m + 2` (charged at the `(m+2)`-th). -/
theorem walk_step {D : Log → Log → Prop} (hS : ChainStab D) {L : Log} (hb : ¬ Bad L)
    (hE : ¬ G.EscG D L) {i : ℕ} (hci : G.IsChain L i) {m : ℕ} (hm : m + 1 < (pathOf L i).length)
    (hD : D (L.take (pathOf L i)[m]) ((entriesOf L (pathOf L i)).take (m + 1))) :
    D (L.take (pathOf L i)[m + 1]) ((entriesOf L (pathOf L i)).take (m + 2)) := by
  set p := pathOf L i
  set es := entriesOf L p
  have hlt : p[m] < p[m + 1] := pathOf_lt hm
  -- transport `D` on the `(m+1)`-prefix from `L.take p[m]` to `L.take p[m+1]`
  have hb' := not_bad_take hb p[m + 1]
  have hc' : G.IsChain (L.take p[m + 1]) p[m] := isChain_take (isChain_prefix hci (by omega)) hlt
  have key := hS _ _ hb' hc'
  rw [List.take_take, min_eq_left hlt.le, entriesOf_pathOf_take L hlt,
    entriesOf_prefix L i (by omega)] at key
  have hD' := key.mp hD
  -- no escape at the chain of `p[m+1]`
  by_contra hnd
  refine hE ⟨p[m + 1], G.mem_chains.mpr (isChain_prefix hci hm), ?_⟩
  rw [entriesOf_prefix L i hm]
  refine ⟨by rw [List.length_take, length_entriesOf]; omega, ?_, hnd⟩
  rw [List.dropLast_eq_take, List.length_take, length_entriesOf, List.take_take,
    show min (m + 2) p.length - 1 = m + 1 by omega, min_eq_left (by omega)]
  exact hD'

/-- **The walk forwards**: with no escape, `D` on a prefix carries to the whole chain (charged at
its last entry). -/
theorem walk_fwd {D : Log → Log → Prop} (hS : ChainStab D) {L : Log} (hb : ¬ Bad L)
    (hE : ¬ G.EscG D L) {i : ℕ} (hci : G.IsChain L i) {m : ℕ} (hm : m < (pathOf L i).length)
    (hD : D (L.take (pathOf L i)[m]) ((entriesOf L (pathOf L i)).take (m + 1))) :
    D (L.take i) (entriesOf L (pathOf L i)) := by
  have hn : ∀ d, ∀ m (hm : m < (pathOf L i).length), (pathOf L i).length - (m + 1) = d →
      D (L.take (pathOf L i)[m]) ((entriesOf L (pathOf L i)).take (m + 1)) →
      D (L.take i) (entriesOf L (pathOf L i)) := by
    intro d
    induction d with
    | zero =>
      intro m hm hd hD
      have hlast : (pathOf L i)[m] = i := by
        have := pathOf_getLast? L i
        rw [List.getLast?_eq_getElem?] at this
        have h2 : (pathOf L i)[m]? = some i := by
          rw [show m = (pathOf L i).length - 1 by omega]; exact this
        rw [List.getElem?_eq_getElem hm] at h2
        exact Option.some.inj h2
      rw [hlast, List.take_of_length_le (l := entriesOf L (pathOf L i))
        (by rw [length_entriesOf]; omega)] at hD
      exact hD
    | succ d ih =>
      intro m hm hd hD
      exact ih (m + 1) (by omega) (by omega) (walk_step hS hb hE hci (by omega) hD)
  exact hn _ m hm rfl hD

/-- **The walk backwards** (A.10: "by induction from Pf upwards"): with no escape, `¬ D` at the
chain's end gives `¬ D` on every prefix. -/
theorem walk_back {D : Log → Log → Prop} (hS : ChainStab D) {L : Log} (hb : ¬ Bad L)
    (hE : ¬ G.EscG D L) {i : ℕ} (hci : G.IsChain L i) (hend : ¬ D (L.take i) (entriesOf L (pathOf L i)))
    {m : ℕ} (hm : m < (pathOf L i).length) :
    ¬ D (L.take (pathOf L i)[m]) ((entriesOf L (pathOf L i)).take (m + 1)) :=
  fun hD => hend (walk_fwd hS hb hE hci hm hD)

/-! ## Part C: the Hide potential's walk -/

/-- **The Hide doom is stable on chains**: before P1.i a level holds on both logs; after, the
chain's cap is a real entry (`capOK_of_matches`), so the word reads the same (`wordK_stab`). -/
theorem DH_chainStab : ChainStab DH := by
  intro L j hb hci
  refine forall₂_congr fun i hi => ?_
  set es := entriesOf L (pathOf L j)
  by_cases h0 : hRnd es i = 0
  · exact ⟨fun _ => noHide_zero h0, fun _ => noHide_zero h0⟩
  have hl : capPos i < es.length := by
    have := capPos_lt hi; unfold hRnd at h0; omega
  have hc := capOK_of_matches hci.2 hi hl
  have hes : ext (es.take es.length) [] = es := by rw [ext_nil, List.take_length]
  have hw := wordK_stab hb hci es.length [] hi (kindOfC es) (by rw [hes]; exact hc)
  rw [hes] at hw
  have hd := decodeL_congr hw
  unfold noHide hDiff farL
  rw [hw, hd]

/-- **No Hide escape keeps `DH` on every chain** (it holds at the seed, `DH_short`). -/
theorem DH_of_noEsc {L : Log} (hb : ¬ Bad L) (hE : ¬ G.EscG DH L) {i : ℕ} (hci : G.IsChain L i) :
    DH L (entriesOf L (pathOf L i)) := by
  have hne : 0 < (pathOf L i).length := List.length_pos_iff.mpr (pathOf_ne_nil L i)
  have h0 : DH (L.take (pathOf L i)[0]) ((entriesOf L (pathOf L i)).take (0 + 1)) :=
    DH_short (by
      have := (p1_phase (i := 0) (by norm_num)).hb1
      simp only [List.length_take]; omega)
  exact (DH_chainStab L i hb hci).mp (walk_fwd DH_chainStab hb hE hci hne h0)

/-- **What `final` gets from `μ_Hide`** (§10 changes 14–15): on a non-bad log with no Hide escape,
a chain past P1.i whose level `i` is close and whose next message is the fold has
`A_c = jointAgree`. -/
theorem consSet_eq_of_noEsc {L : Log} (hb : ¬ Bad L) (hE : ¬ G.EscG DH L) {j : ℕ}
    (hci : G.IsChain L j) {i : ℕ} (hi : i < 5)
    (hlen : p1Start i + 2 * hEll i ≤ (entriesOf L (pathOf L j)).length)
    (hfar : ¬ farL (kindOfC (entriesOf L (pathOf L j))) L (entriesOf L (pathOf L j)) i)
    (hC : truthC (kindOfC (entriesOf L (pathOf L j))) L (entriesOf L (pathOf L j)) i) :
    consSet (kindOfC (entriesOf L (pathOf L j))) L (entriesOf L (pathOf L j)) i =
      jointAgree (wordK (kindOfC (entriesOf L (pathOf L j))) L (entriesOf L (pathOf L j)) i)
        (decodeL (kindOfC (entriesOf L (pathOf L j))) L (entriesOf L (pathOf L j)) i) :=
  consSet_eq_of_DH hi hlen (DH_of_noEsc hb hE hci) hfar hC

/-- Control (positive): a doom that reads only the chain is stable. -/
theorem chainStab_const (P : Log → Prop) : ChainStab fun _ es => P es :=
  fun _ _ _ _ => Iff.rfl

end FR.Snd.T4

/-! # Port of `FRSoundnessWeights` (its module doc describes the 3.x original) -/

namespace FR.Snd.T4
open RecursionFast FR.Merkle Finset

/-! ## Part A: extensions of ℕ-indexed tables -/

/-- **The codeword weight's extension is the tensor weight** (A.1; `tensorTwin`, the spec of
`tensorW`): `G̃_p(ρ) = Π_v (1 − ρ_v + ρ_v Ŵ_v(D[p]))`. -/
theorem mleN_gW (κ : CKind) (i p : ℕ) (ρ : Fin (mLog κ i) → K) :
    mleN (mLog κ i) (gW κ i p) ρ =
      tensorTwin D logNMax (mLog κ i) (fun v => if h : v < mLog κ i then ρ ⟨v, h⟩ else 0) p := by
  simp only [mleN, gW]
  rw [mle_bitProd, tensorTwin, ← Fin.prod_univ_eq_prod_range]
  refine prod_congr rfl fun v _ => ?_
  simp [wAtD]

/-- **P3.i's table's extension** (A.9 `finP i`): the folded weight's plus the queried positions'
tensor weights. -/
theorem mleN_wNext (κ : CKind) (es : Log) (i : ℕ) (Wf : ℕ → K) (ρ : Fin (mLog κ i) → K) :
    mleN (mLog κ i) (wNext κ es i Wf) ρ = mleN (mLog κ i) Wf ρ +
      ∑ q ∈ range (CKind.lv κ i).t, algebraMap F K (eqBits (kcAt es i) 9 q) *
        mleN (mLog κ i) (gW κ i (qPos κ es i q)) ρ := by
  have h : (fun u : Fin (2 ^ mLog κ i) => wNext κ es i Wf u) =
      (fun u : Fin (2 ^ mLog κ i) => Wf u) + fun u : Fin (2 ^ mLog κ i) =>
      ∑ q ∈ range (CKind.lv κ i).t, algebraMap F K (eqBits (kcAt es i) 9 q) *
        gW κ i (qPos κ es i q) u := by
    funext u; simp only [wNext, Pi.add_apply, K.smulF_eq_mul]; rfl
  rw [mleN, h, mle_add, mle_sum]
  rfl

/-! ## Part B: the next level's table -/

/-- **Level `i + 1`'s table** (A.10 P3.i → P1.(i+1)): level `i`'s table bound at `sᵢ`, plus
the queried codeword weights, split. -/
noncomputable def nextW (κ : CKind) (es : Log) (i : ℕ) (W : ℕ → K) : ℕ → K :=
  wSplit (wNext κ es i (foldW (CKind.lv κ i).ell (sAt es i) W))

/-- **The claim moves to the next level** (A.10 P1.i, C.i, P2.i, P3.i): if P1.i's folded claim
is `⟨foldW W, fold_z(f⁽ⁱ⁾)⟩`, the next message is the fold (`truthC`) and every query is
consistent (`truthP3`), the batched claim is `⟨nextW W, f⁽ⁱ⁺¹⁾⟩`. -/
theorem truthP1_next {κ : CKind} {L es : Log} {i : ℕ} (hi : i + 1 < 5) {W : ℕ → K} {c : K}
    (hc : c = ∑ x ∈ range (2 ^ mLog κ i), foldW (CKind.lv κ i).ell (sAt es i) W x * foldMsg κ L es i x)
    (hC : truthC κ L es i) (h3 : truthP3 κ L es i) :
    truthP1 κ L es (i + 1) (nextW κ es i W) (vNext κ L es i c) := fun _ => by
  rw [nextW, wSplit_sum hi, vNext_eq hc hC h3]

/-- **`finPf`'s level step at the spec** (`lvStepV`): the next table's extension at
`(β, ρ)` is `û(β)·(W̃(sᵢ, ρ) + Σ_q eq(κ_c, bits₉(q))·tensorW(p_q, ρ))`. -/
theorem mleN_nextW (κ : CKind) (es : Log) (i : ℕ) (W : ℕ → K) (ρ : Fin (mLog κ i + 1) → K) :
    mleN (mLog κ i + 1) (nextW κ es i W) ρ = uHat (ρ 0) *
      (mleN ((CKind.lv κ i).ell + mLog κ i) W (Fin.append (fun v : Fin (CKind.lv κ i).ell => sAt es i v)
          (Fin.tail ρ)) +
        ∑ q ∈ range (CKind.lv κ i).t, algebraMap F K (eqBits (kcAt es i) 9 q) *
          tensorTwin D logNMax (mLog κ i)
            (fun v => if h : v < mLog κ i then Fin.tail ρ ⟨v, h⟩ else 0) (qPos κ es i q)) := by
  rw [nextW, mleN_wSplit, mleN_wNext, mleN_foldW]
  simp only [mleN_gW]

/-! ## T4: the level-0 message in F (from `FRSoundnessPIOP` Part A; `LigeritoOut.claim0` reads it) -/

/-- **A.10's `f⁽⁰⁾` in F**: element `e` is the constant coefficient of the decoded level-0
message's element `e` (`fTab`, row bits first). -/
noncomputable def fF (κ : CKind) (L es : Log) (e : ℕ) : F := (fTab κ L es 0 e).f₀

/-- **A close level-0 word decodes to F-messages** (`interp_F_D`): every decoded row's message is
F-valued. -/
theorem msgOf_F {κ : CKind} {L es : Log} (hfar : ¬ farL κ L es 0) (r x : ℕ) :
    msgOf κ L es 0 r x = algebraMap F K (msgOf κ L es 0 r x).f₀ := by
  by_cases hr : r < (CKind.lv κ 0).rows
  swap
  · simp only [msgOf, hr, dite_false]; rfl
  by_cases hx : x < 2 ^ mLog κ 0
  swap
  · simp only [msgOf, hr, hx, dite_true, dite_false]; rfl
  obtain ⟨hek, hN, -, hk, hn⟩ := lv_params κ (i := 0) (by norm_num)
  have hkN : 2 ^ mLog κ 0 ≤ nMax := by rw [← hk]; unfold lvK; exact (Nat.div_le_self _ _).trans hN
  have hnN : 2 ^ (CKind.lv κ 0).logN ≤ nMax := hn ▸ hN
  obtain ⟨hV, hJ⟩ := decodeL_spec hfar
  set rr : Fin (CKind.lv κ 0).rows := ⟨r, hr⟩
  have hv := hV rr
  rw [codeK, hk, ← encCode_D hkN] at hv
  have hA : 2 ^ mLog κ 0 ≤ (jointAgree (wordK κ L es 0) (decodeL κ L es 0)).card := by
    have : lvK κ 0 ≤ 2 ^ (CKind.lv κ 0).logN - lvE κ 0 := by rw [← hn]; omega
    rw [← hk]; exact this.trans hJ
  obtain ⟨c, hc⟩ := interp_F_D hnN hkN hv (fun j => wordOf κ L es 0 rr j) _ hA fun j hj => by
    rw [mem_jointAgree] at hj; rw [← hj rr]; rfl
  have := msgOf_eq (i := 0) (by norm_num) (r := rr) hc.symm ⟨x, hx⟩
  rw [this, algebraMap_f₀]

/-- **`f⁽⁰⁾` is F-valued**: on a close level-0 word, `fTab … 0 = ι ∘ fF`. -/
theorem fTab_F {κ : CKind} {L es : Log} (hfar : ¬ farL κ L es 0) (e : ℕ) :
    fTab κ L es 0 e = algebraMap F K (fF κ L es e) := msgOf_F hfar _ _

/-! T4: the witness bits `z = unpack f⁽⁰⁾` (from `FRSoundnessPIOP` Part B; P4a's dooms read `zW`) -/

/-- **A.10's `z := unpack f⁽⁰⁾`** (A.7's pack map): bit `b` of `z` is bit `b mod 128` of
`f[b / 128]`. -/
noncomputable def zW (κ : CKind) (L es : Log) (b : ℕ) : F :=
  unpack (fF κ L es (b / 128)) ⟨b % 128, Nat.mod_lt _ (by norm_num)⟩

/-- Block `blk`'s positions (A.7: block element `k` is `f[blk·128 + k]`, `2^14` bits). -/
noncomputable def zBlk (κ : CKind) (L es : Log) (blk : ℕ) : Block.Pos → F :=
  fun k => zW κ L es (blk * 2 ^ Blake2sCircuit.m + k.val)

/-- Block `blk`'s element `k` is `f[blk·128 + k]`: its bits are positions `128k … 128k + 127`. -/
theorem zBlk_elem (κ : CKind) (L es : Log) (blk : ℕ) (k : Block.Pos) :
    zBlk κ L es blk k = unpack (fF κ L es (blk * 128 + k.val / 128))
      ⟨k.val % 128, Nat.mod_lt _ (by norm_num)⟩ := by
  have hm : (2 : ℕ) ^ Blake2sCircuit.m = 128 * 128 := by decide
  have h1 : (blk * (128 * 128) + k.val) / 128 = blk * 128 + k.val / 128 := by omega
  have h2 : (blk * (128 * 128) + k.val) % 128 = k.val % 128 := by omega
  simp only [zBlk, zW, hm, h1, h2]

/-- **The unpacked witness is Boolean** (`leaf_sound`'s `hbool`). -/
theorem zBlk_bool (κ : CKind) (L es : Log) (blk : ℕ) (k : Block.Pos) :
    BlockR1CS.IsBool (zBlk κ L es blk k) :=
  unpack_boolean _ _


/-! ## Part C: level 0 (T4: `truthP1_zero` is B′'s handoff, unused downstream; not copied) -/

section Level0
open Circ

end Level0

end FR.Snd.T4

/-! # Port of `FRSoundnessFold` (its module doc describes the 3.x original) -/

namespace FR.Snd.T4
open RecursionFast FR.Merkle Finset

set_option linter.constructorNameAsVariable false

/-! ## Part A: intermediate folds -/

section Generic

variable {K' : Type*} [Field K'] [DecidableEq K'] {n : ℕ}

end Generic

/-- Level `i`'s word with ℕ-indexed rows (`0` past the rows). -/
noncomputable def wN (κ : CKind) (L es : Log) (i r : ℕ) : Fin (2 ^ (CKind.lv κ i).logN) → K :=
  fun j => if h : r < (CKind.lv κ i).rows then wordK κ L es i ⟨r, h⟩ j else 0

/-- **Level `i`'s word after `l` fold rounds**: row `r` is `Σ_{u<2^l} eq(sᵢ, u)·W[u + 2^l r]`
(the rounds bind the row bits low first). -/
noncomputable def pf (κ : CKind) (L es : Log) (i l r : ℕ) : Fin (2 ^ (CKind.lv κ i).logN) → K :=
  fun j => ∑ u ∈ range (2 ^ l), eqBits (sAt es i) l u * wN κ L es i (u + 2 ^ l * r) j

/-- **The intermediate fold is close**: its `2^(ℓᵢ−l)` rows are jointly `eᵢ`-close to `C_K`. P1.i's
far doom is `¬ closeP` at the rounds answered. -/
def closeP (κ : CKind) (L es : Log) (i l : ℕ) : Prop :=
  CloseN (codeK κ i) (lvE κ i) (2 ^ ((CKind.lv κ i).ell - l)) (pf κ L es i l)

/-- One more round folds rows `2r`, `2r + 1` at `s_l`. -/
theorem pf_succ (κ : CKind) (L es : Log) (i l : ℕ) :
    pf κ L es i (l + 1) = foldN (sAt es i l) (pf κ L es i l) := by
  funext r j
  set s := sAt es i
  have e1 : ∀ u ∈ range (2 ^ l), eqBits s (l + 1) u = eqBits s l u * (1 - s l) :=
    fun u hu => bitSel_succ_lo _ _ (mem_range.1 hu)
  have e2 : ∀ u ∈ range (2 ^ l), eqBits s (l + 1) (2 ^ l + u) = eqBits s l u * s l :=
    fun u hu => bitSel_succ_hi _ _ (mem_range.1 hu)
  have hA : ∀ u, u + 2 ^ (l + 1) * r = u + 2 ^ l * (2 * r) := fun u => by ring
  have hB : ∀ u, 2 ^ l + u + 2 ^ (l + 1) * r = u + 2 ^ l * (2 * r + 1) := fun u => by ring
  simp only [pf, foldN, Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
  have hr : range (2 ^ (l + 1)) = range (2 ^ l + 2 ^ l) := by congr 1; ring
  have s1 : ∑ u ∈ range (2 ^ l), eqBits s (l + 1) u * wN κ L es i (u + 2 ^ (l + 1) * r) j =
      ∑ u ∈ range (2 ^ l), eqBits s l u * (1 - s l) * wN κ L es i (u + 2 ^ l * (2 * r)) j :=
    sum_congr rfl fun u hu => by rw [e1 u hu, hA]
  have s2 : ∑ u ∈ range (2 ^ l),
      eqBits s (l + 1) (2 ^ l + u) * wN κ L es i (2 ^ l + u + 2 ^ (l + 1) * r) j =
      ∑ u ∈ range (2 ^ l), eqBits s l u * s l * wN κ L es i (u + 2 ^ l * (2 * r + 1)) j :=
    sum_congr rfl fun u hu => by rw [e2 u hu, hB]
  rw [hr, sum_range_add, s1, s2, mul_sub, mul_sum, mul_sum, ← sum_sub_distrib,
    ← sum_add_distrib, ← sum_add_distrib]
  exact sum_congr rfl fun u _ => by ring

theorem pf_zero (κ : CKind) (L es : Log) (i r : ℕ) : pf κ L es i 0 r = wN κ L es i r := by
  funext j; simp [pf, eqBits, bitSel]

/-- **`closeP 0` is `¬ far_i`.** -/
theorem closeP_zero {κ : CKind} {L es : Log} {i : ℕ} : closeP κ L es i 0 ↔ ¬ farL κ L es i := by
  have hrow : (CKind.lv κ i).rows = 2 ^ ((CKind.lv κ i).ell - 0) := by rw [Nat.sub_zero]; rfl
  have heq : (fun r : Fin (2 ^ ((CKind.lv κ i).ell - 0)) => pf κ L es i 0 r) =
      wordK κ L es i ∘ finCongr hrow.symm := by
    funext r j
    simp only [pf_zero, wN, Function.comp_apply, finCongr_apply, Fin.cast]
    have hr : (r : ℕ) < (CKind.lv κ i).rows := by rw [hrow]; exact r.2
    simp only [hr, ↓reduceDIte]
  simp only [closeP, CloseN, heq, jointClose_equiv, farL, not_forall, not_not]

/-- Closeness survives the rounds. -/
theorem closeP_succ {κ : CKind} {L es : Log} {i l : ℕ} (hl : l < (CKind.lv κ i).ell)
    (h : closeP κ L es i l) : closeP κ L es i (l + 1) := by
  unfold closeP at h ⊢
  rw [two_pow_sub hl] at h
  rw [pf_succ]
  exact closeN_fold _ h

theorem closeP_of_not_far {κ : CKind} {L es : Log} {i : ℕ} (hf : ¬ farL κ L es i) :
    ∀ l ≤ (CKind.lv κ i).ell, closeP κ L es i l
  | 0, _ => closeP_zero.mpr hf
  | l + 1, hl => closeP_succ (by omega) (closeP_of_not_far hf l (by omega))

/-- The bad set of round `l` (`round_bad_cover`): at most `2^(ℓᵢ−l−1)·C_mca(nᵢ, kᵢ, eᵢ)` values. -/
theorem closeP_cover {κ : CKind} {i : ℕ} (hi : i < 5) (L es : Log) {l : ℕ}
    (hl : l < (CKind.lv κ i).ell) :
    ∃ B : Finset K, B.card ≤ 2 ^ ((CKind.lv κ i).ell - (l + 1)) * cMca (lvN κ i) (lvK κ i) (lvE κ i) ∧
      ∀ z ∉ B, closeP κ L es i l ∨ ¬ CloseN (codeK κ i) (lvE κ i) (2 ^ ((CKind.lv κ i).ell - (l + 1)))
        (foldN z (pf κ L es i l)) := by
  obtain ⟨hek, hN, -, -, hn⟩ := lv_params κ hi
  have hnN : 2 ^ (CKind.lv κ i).logN ≤ nMax := hn ▸ hN
  obtain ⟨B, hB, hsub⟩ := round_bad_cover (Dpts_injective hnN) (by rw [← hn]; exact hek)
    (fun c : Fin (2 ^ ((CKind.lv κ i).ell - (l + 1))) => pf κ L es i l (2 * c))
    (fun c => pf κ L es i l (2 * c + 1))
  refine ⟨B, by simpa [lvN, Fintype.card_fin] using hB, fun z hz => ?_⟩
  by_cases hc : CloseN (codeK κ i) (lvE κ i) (2 ^ ((CKind.lv κ i).ell - (l + 1)))
    (foldN z (pf κ L es i l))
  · left
    unfold closeP
    rw [two_pow_sub hl]
    exact closeN_unfold (Dpts_injective hnN) (by rw [← hn]; exact hek)
      (fun c hzc => hz (hsub c hzc)) hc
  · exact Or.inr hc

/-- Level `i`'s encoding is a codeword of `C_K`. -/
theorem encAt_eq_enc {κ : CKind} {i : ℕ} (hi : i < 5) (m : ℕ → K)
    (j : Fin (2 ^ (CKind.lv κ i).logN)) :
    encAt κ i m j = enc D (2 ^ (CKind.lv κ i).logN) _ (fun x : Fin (2 ^ mLog κ i) => m x) j := by
  obtain ⟨-, hN, hm, -, hn⟩ := lv_params κ hi
  rw [encAt, encF_eq hm (lt_of_lt_of_le j.2 (hn ▸ hN)), enc_eq_encN]

theorem enc_mem_codeK {κ : CKind} {i : ℕ} (hi : i < 5) (c : Fin (2 ^ mLog κ i) → K) :
    enc D (2 ^ (CKind.lv κ i).logN) _ c ∈ codeK κ i := by
  obtain ⟨-, hN, -, hk, hn⟩ := lv_params κ hi
  have hkn : 2 ^ mLog κ i ≤ 2 ^ (CKind.lv κ i).logN := by
    rw [← hk, ← hn]; unfold lvK; exact Nat.div_le_self _ _
  rw [codeK, hk, ← encCode_D (hkn.trans (hn ▸ hN))]
  exact LinearMap.mem_range_self _ c

/-- After all rounds the single row is the column fold `foldAt`. -/
theorem pf_full (κ : CKind) (L es : Log) (i : ℕ) (j : Fin (2 ^ (CKind.lv κ i).logN)) :
    pf κ L es i (CKind.lv κ i).ell 0 j = foldAt κ L es i j := by
  simp only [pf, mul_zero, add_zero, foldAt]
  rw [← Fin.sum_univ_eq_sum_range (fun u => eqBits (sAt es i) (CKind.lv κ i).ell u * wN κ L es i u j)]
  refine sum_congr rfl fun u _ => ?_
  simp only [wN, Level.rows, u.2, ↓reduceDIte]

/-- **A close next codeword makes the full fold close** (`truthP2`): a far fold refutes it. -/
theorem closeP_of_truthP2 {κ : CKind} {L es : Log} {i : ℕ} (hi : i < 5)
    (h : truthP2 κ L es i) : closeP κ L es i (CKind.lv κ i).ell := by
  classical
  refine ⟨consSet κ L es i, h, fun _ => enc D _ _ fun x : Fin (2 ^ mLog κ i) =>
    nextMsg κ L es i x, fun _ => enc_mem_codeK hi _, ?_⟩
  ext j
  simp only [mem_jointAgree, consSet, mem_filter, mem_univ, true_and]
  rw [encAt_eq_enc hi]
  constructor
  · intro hj; have := hj 0; rwa [Fin.val_zero, pf_full] at this
  · intro hj r
    have hr0 : (r : ℕ) = 0 := by have := r.2; simp only [Nat.sub_self, pow_zero] at this; omega
    rw [hr0, pf_full]; exact hj

/-! ## Part B: P3.i's batched table -/

/-- **P3.i's table** (512 entries over `κ_c`'s 9 coordinates): query `q`'s consistency error
(`0` past `tᵢ`), plus the folded claim's offset `d`. -/
noncomputable def p3T (κ : CKind) (L es : Log) (i : ℕ) (d : K) : Array K :=
  Array.ofFn (n := 2 ^ 9) fun q => (if (q : ℕ) < (CKind.lv κ i).t then consErr κ L es i q else 0) + d

theorem p3T_size (κ : CKind) (L es : Log) (i : ℕ) (d : K) : (p3T κ L es i d).size = 2 ^ 9 :=
  Array.size_ofFn

theorem tbl_p3T (κ : CKind) (L es : Log) (i : ℕ) (d : K) (q : Fin (2 ^ 9)) :
    tbl 9 (p3T κ L es i d) q = (if (q : ℕ) < (CKind.lv κ i).t then consErr κ L es i q else 0) + d := by
  simp [tbl, p3T, Array.getD_eq_getD_getElem?]

theorem lvl_t_lt (κ : CKind) {i : ℕ} (hi : i < 5) : (CKind.lv κ i).t < 2 ^ 9 - 1 := by
  rcases κ with (_|_|_) | (_|_|_) <;> interval_cases i <;> decide

/-- **The table's extension at `κ_c`** is `d + p3Batch`. -/
theorem p3T_mle (κ : CKind) (L es : Log) {i : ℕ} (hi : i < 5) (d : K) :
    ∑ q : Fin (2 ^ 9), eqBits (fun v => algebraMap F K (kcAt es i v)) 9 q *
      tbl 9 (p3T κ L es i d) q = d + p3Batch κ L es i := by
  set e : ℕ → K := fun q => eqBits (fun v => algebraMap F K (kcAt es i v)) 9 q
  set g : ℕ → K := fun q => if q < (CKind.lv κ i).t then consErr κ L es i q else 0
  have h1 : ∀ q : Fin (2 ^ 9), e q * tbl 9 (p3T κ L es i d) q = e q * g q + e q * d :=
    fun q => by rw [tbl_p3T, mul_add]
  rw [sum_congr rfl fun q _ => h1 q, sum_add_distrib, ← sum_mul,
    Fin.sum_univ_eq_sum_range e, Fin.sum_univ_eq_sum_range (fun q => e q * g q)]
  suffices hs : ∑ q ∈ range (2 ^ 9), e q * g q = p3Batch κ L es i by
    rw [hs, show ∑ q ∈ range (2 ^ 9), e q = 1 from sum_eqBits_one _ _, one_mul, add_comm]
  have ht : (CKind.lv κ i).t ≤ 2 ^ 9 := by have := lvl_t_lt κ hi; omega
  rw [← Finset.sum_range_add_sum_Ico _ ht, Finset.sum_eq_zero (s := Ico _ _) fun q hq => by
    have : ¬ q < (CKind.lv κ i).t := by simp only [mem_Ico] at hq; omega
    simp only [g, this, ↓reduceIte, mul_zero],
    add_zero, p3Batch]
  refine sum_congr rfl fun q hq => ?_
  simp only [g, e, mem_range.1 hq, ↓reduceIte, K.smulF_eq_mul, ← K.algebraMap_eq_ofF,
    algebraMap_eqBits]

/-- **The next claim's error** (A.10 P3.i): `v_{i+1} − ⟨wNext Wf, f⁽ⁱ⁺¹⁾⟩ = d + p3Batch`, with
`d = c − ⟨Wf, f⁽ⁱ⁺¹⁾⟩` over level `i`'s folded message. -/
theorem vNext_sub (κ : CKind) (L es : Log) (i : ℕ) (Wf : ℕ → K) (c : K) :
    vNext κ L es i c - ∑ x ∈ range (2 ^ mLog κ i), wNext κ es i Wf x * nextMsg κ L es i x =
      (c - ∑ x ∈ range (2 ^ mLog κ i), Wf x * nextMsg κ L es i x) + p3Batch κ L es i := by
  have hq : ∀ q, foldAtN κ L es i (qPos κ es i q) = consErr κ L es i q +
      ∑ x ∈ range (2 ^ mLog κ i), nextMsg κ L es i x * gW κ i (qPos κ es i q) x := by
    intro q; rw [consErr, ← encAt_eq_sum]; ring
  simp only [vNext, p3Batch, wNext, hq, K.smulF_eq_mul, mul_add, sum_add_distrib, add_mul,
    mul_sum, sum_mul]
  rw [sum_comm (s := range (CKind.lv κ i).t)]
  have hc : ∑ y ∈ range (2 ^ mLog κ i), ∑ q ∈ range (CKind.lv κ i).t,
      K.ofF (eqBits (kcAt es i) 9 q) * (nextMsg κ L es i y * gW κ i (qPos κ es i q) y) =
      ∑ y ∈ range (2 ^ mLog κ i), ∑ q ∈ range (CKind.lv κ i).t,
        K.ofF (eqBits (kcAt es i) 9 q) * gW κ i (qPos κ es i q) y * nextMsg κ L es i y :=
    sum_congr rfl fun _ _ => sum_congr rfl fun _ _ => by ring
  rw [hc]
  ring

/-- **The table is nonzero** when a query is inconsistent or the offset is nonzero (`tᵢ < 511`,
so the last entry is `d`). -/
theorem p3T_ne_zero {κ : CKind} {L es : Log} {i : ℕ} (hi : i < 5) {d : K}
    (h : ¬ truthP3 κ L es i ∨ d ≠ 0) : tbl 9 (p3T κ L es i d) ≠ 0 := by
  intro hz
  have ht := lvl_t_lt κ hi
  have hd : d = 0 := by
    have := congrFun hz ⟨2 ^ 9 - 1, by omega⟩
    rwa [tbl_p3T, ite_eq_right_iff.mpr fun h => absurd h (by simp; omega), zero_add] at this
  rcases h with h | h
  · refine h fun q hq => ?_
    have := congrFun hz ⟨q, by omega⟩
    rwa [tbl_p3T, ite_eq_left_iff.mpr fun h => absurd hq h, hd, add_zero] at this
  · exact h hd

end FR.Snd.T4

