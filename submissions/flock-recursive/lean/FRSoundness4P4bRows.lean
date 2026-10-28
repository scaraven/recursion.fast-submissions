-- New for `flock-recursive` (BLUEPRINT A.10 rows Lr1–Lr3 and E1–E4, §5.2; stage P4b): the row
-- Spartan unit of `FRSoundnessRows` over an entries source, an abstract `FSrc` and separate real
-- and slot counts, and O1 (the E truth over indexed rows, as `evalMS` reads `nodeIRows`).
import FRSoundness4P4bNames
import FRVIRTplFast

/-!
# The row Spartan unit over an entries source (P4b), and O1

The unit's dooms (`FRSoundness4P4bNames`: `RowsBadG`, `ZCwG`, `D3G`, `EndBadG`, `BatBadG`, the check
`RejEndG`) with their obligations, as `FRSoundnessRows` proves them for 3.x, now over any `FSrc` `R`
and entries source `E`, `a` real rows' bits, `nc` cell bits, the zerocheck after `s0`, `A` outer
slots from `b2` (end absorb at `b2 + 2A`, `a ≤ A`):

* **reads** (`ReadsS`): `rowsBadG_reads`, `zcwG_reads`, `endBadG_reads`, `batBadG_reads`,
  `D3G_reads` (once every slot is answered), `rejEndG_reads`; locality `T3G_local`;
* **the zerocheck's charge** `zcG_count` (`ml_round_le`, `≤ a/2^128`): the count of any phase doom
  whose escapes clear `ZCwG`, from `RowsBadG` at the phase's entry;
* **the handoffs**: `habsG_outer` (into the rounds), `habsG_end` (at the end absorb: `RejEndG` or a
  wrong triple), `singleG_batch` (`≤ 2·2^128` answers at `κ`), `singleG_outer`, `outerG_append`;
* **checks**: `RejLog4` (monotone, unchanged at a `seq4` squeeze, independent of the charging log),
  `rejEndG_log`.

**O1** (ruling S-N1 O1, S-G12′ F3): **`truthEI rows w`** (every indexed row holds at `w`) and
**`sat_entMatI_iff`**: on indexed rows that fit (`RowsFitI`: indices distinct and `< 2^a`, cells
`< 2^b`), the R1CS of `ESrc.ofIRows rows`, the matrices `evalMS` evaluates, is "every row holds".
`matMle_entMat` (the unit's `matMle` is `Eval.matMLE`, `evalMS`'s value) and `mle_wInn` bridge the
E4 weight to the verifier's `evalM`/`evalL`. 3.x instances: `truthE3_iffI` (the E truth at
`nodeIRows (planOf fin)`) and `sat_ofRows_iff` (3.x's `sat_rowMat_iff` at `ESrc.ofRows`).
-/

namespace FR.Snd.P4b
open RecursionFast FR.Merkle FR.Rev4 Finset
open scoped NNReal

set_option linter.constructorNameAsVariable false

/-! ## `ReadsS` -/

section ReadsS
variable {R : FSrc} {p : ℕ} {P Q : Log → Log → Prop}

theorem ReadsS.mono (h : ReadsS R p P) {q : ℕ} (hq : p ≤ q) : ReadsS R q P :=
  fun L es L' es' h1 h2 hS => h L es L' es' (by omega) (by omega) (R.mono hS hq)

theorem ReadsS.or (hP : ReadsS R p P) (hQ : ReadsS R p Q) : ReadsS R p fun L es => P L es ∨ Q L es :=
  fun L es L' es' h1 h2 hS => or_congr (hP L es L' es' h1 h2 hS) (hQ L es L' es' h1 h2 hS)

theorem ReadsS.not (hP : ReadsS R p P) : ReadsS R p fun L es => ¬ P L es :=
  fun L es L' es' h1 h2 hS => not_congr (hP L es L' es' h1 h2 hS)

/-- Appending to a chain of at least `p` entries does not change `P`. -/
theorem ReadsS.append (h : ReadsS R p P) (L es xs : Log) (hp : p ≤ es.length) :
    P L (es ++ xs) ↔ P L es :=
  h L _ L es (by simp; omega) hp (R.ofAgree L (agree_append es xs hp))

/-- A predicate of the log alone reads at any `R`. -/
theorem readsS_of_agree (h : ∀ L es L' es', Agree es es' p → (P L es ↔ P L' es')) : ReadsS R p P :=
  fun L es L' es' _ _ hS => h L es L' es' (R.agree hS)

end ReadsS

/-! ## Checks that read only the log -/

/-- **A check at revision 4.1** (T4's `RejOK` without its `stab`, which a log-only check meets for
any charging log): monotone, unchanged by an entry at a `seq4` squeeze, independent of `L`. -/
structure RejLog4 (Rej : Log → Log → Prop) : Prop where
  mono : ∀ L es x, Rej L es → Rej L (es ++ [x])
  sq : ∀ L es x, fsItems4[es.length]? = some .squeeze → (Rej L (es ++ [x]) ↔ Rej L es)
  log : ∀ L L' es, Rej L es ↔ Rej L' es

/-- A check that reads the log before `q` and whose position `q − 1` is not a squeeze. -/
theorem rejLog4_of {Rej : Log → Log → Prop} {q : ℕ} (hq : 1 ≤ q)
    (hlen : ∀ L es, Rej L es → q ≤ es.length)
    (hreads : ∀ L es L' es', q ≤ es.length → q ≤ es'.length → Agree es es' q →
      (Rej L es ↔ Rej L' es'))
    (hpe : fsItems4[q - 1]? ≠ some .squeeze) : RejLog4 Rej where
  mono L es x h := (hreads L (es ++ [x]) L es (by simp; have := hlen L es h; omega) (hlen L es h)
    (agree_append es [x] (hlen L es h))).mpr h
  sq L es x hit := by
    by_cases hle : q ≤ es.length
    · exact hreads L (es ++ [x]) L es (by simp; omega) hle (agree_append es [x] hle)
    · constructor
      · intro h
        have h1 := hlen L _ h
        simp only [List.length_append, List.length_singleton] at h1
        rw [show es.length = q - 1 by omega] at hit
        exact absurd hit hpe
      · intro h; exact absurd (hlen L es h) hle
  log L L' es := by
    by_cases hle : q ≤ es.length
    · exact hreads L es L' es hle hle (fun _ _ => rfl)
    · exact ⟨fun h => absurd (hlen L es h) hle, fun h => absurd (hlen L' es h) hle⟩

/-! ## The unit's lemmas -/

section Unit
variable (R : FSrc) (E : ESrc) (a nc : ℕ)

theorem zCG_same {L es L' es' : Log} {p : ℕ} (h : R.Sm L es L' es' p) (hp : 3 ≤ p) :
    zCG R nc L es = zCG R nc L' es' := by
  funext y; simp only [zCG, R.fz_same h hp]

theorem rowsBadG_reads : ReadsS R 3 (RowsBadG R E a nc) :=
  fun L es L' es' _ _ h => by simp only [RowsBadG, zCG_same R nc h le_rfl]

variable (s0 b2 A : ℕ)

theorem zcwG_reads (hp : 3 ≤ s0 + 1 + (a + 1) / 2) :
    ReadsS R (s0 + 1 + (a + 1) / 2) (ZCwG R E a nc s0) :=
  fun L es L' es' _ _ h => by
    simp only [ZCwG, zCG_same R nc h hp, tauS_agree (R.agree h) le_rfl]

theorem T3G_same {L es L' es' : Log} {p : ℕ} (h : R.Sm L es L' es' p) (hp3 : 3 ≤ p)
    (hs : s0 + 1 + (a + 1) / 2 ≤ p) : T3G R E a nc s0 L es = T3G R E a nc s0 L' es' := by
  simp only [T3G, zCG_same R nc h hp3, tauS_agree (R.agree h) hs]

/-- The outer tables read the entries before `b2`. -/
theorem T3G_local (hs : s0 + 1 + (a + 1) / 2 ≤ b2) (h3 : 3 ≤ b2) :
    TruthLocal b2 (fun _ _ => 0) (T3G R E a nc s0) := fun L _ _ h =>
  ⟨T3G_same R E a nc s0 (R.ofAgree L h) h3 hs, rfl⟩

theorem T3G_size (L es : Log) :
    ∀ t ∈ T3G R E a nc s0 L es, t.size = 2 ^ (fun _ : Kind => a) (kindOf es) :=
  outer_sizes _ (by simp [tauS]) _ _ _ _

theorem triTG_same {L es L' es' : Log} {p : ℕ} (h : R.Sm L es L' es' p) (hp3 : 3 ≤ p)
    (hp : b2 + 2 * a ≤ p) : triTG R E a nc b2 L es = triTG R E a nc b2 L' es' := by
  simp only [triTG, zCG_same R nc h hp3, rxs_agree (R.agree h) hp]

theorem endBadG_reads (h3 : 3 ≤ b2) (haA : a ≤ A) :
    ReadsS R (b2 + 2 * A + 1) (EndBadG R E a nc b2 A) := fun L es L' es' h1 h2 h => by
  simp only [EndBadG, triTG_same R E a nc b2 h (by omega) (by omega : b2 + 2 * a ≤ b2 + 2 * A + 1),
    vEnd_agree (R.agree h) le_rfl]
  exact and_congr_left fun _ => ⟨fun _ => by omega, fun _ => by omega⟩

theorem T4G_same {L es L' es' : Log} {p : ℕ} (h : R.Sm L es L' es' p) (hp3 : 3 ≤ p)
    (haA : a ≤ A) (hp : b2 + 2 * A + 2 ≤ p) :
    T4G R E a nc b2 A L es = T4G R E a nc b2 A L' es' := by
  simp only [T4G, zCG_same R nc h hp3, rxs_agree (R.agree h) (by omega : b2 + 2 * a ≤ p),
    kapB_agree (R.agree h) hp]

theorem batBadG_reads (h3 : 3 ≤ b2) (haA : a ≤ A) :
    ReadsS R (b2 + 2 * A + 2) (BatBadG R E a nc b2 A) := fun L es L' es' h1 h2 h => by
  simp only [BatBadG, T4G_same R E a nc b2 A h (by omega) haA le_rfl,
    c4_agree (L := L) (L' := L') (R.agree h) le_rfl]
  exact and_congr_left fun _ => ⟨fun _ => by omega, fun _ => by omega⟩

/-! ### The zerocheck's charge -/

open Classical in
/-- **The zerocheck's charge** (A.10 Lr1/E1, `ml_round_le`): if the statement fails at the phase's
entry and every escape of `D` over the phase's `r` squeezes clears `ZCwG`, the phase costs at most
`a/2^128`. -/
theorem zcG_count {D : Log → Log → Prop} {L es₀ : Log} {r : ℕ} (hl : es₀.length = s0 + 1)
    (h2 : 2 ≤ s0) (ha : a ≤ r * 2) (hd : RowsBadG R E a nc L es₀)
    (hesc : ∀ as : List Digest, as.length = r → EscAtG D L (ext es₀ as) →
      ¬ ZCwG R E a nc s0 L (ext es₀ as)) :
    condCount D L es₀ r [] ≤ (a : ℝ≥0) / 2 ^ 128 := by
  set t := Array.ofFn (residual (entMat E.ea a nc) (entMat E.eb a nc) (entMat E.ec a nc)
    (zCG R nc L es₀))
  have ht : t.size = 2 ^ a := by simp [t]
  refine ml_round_le hl ha ht (zc_start hd) fun as has he => ?_
  have hnf := hesc as has he
  obtain ⟨ys, hy⟩ := ext_eq_append es₀ as
  have hag : Agree (ext es₀ as) es₀ (s0 + 1) := by rw [hy, ← hl]; exact agree_append es₀ ys le_rfl
  have hz : zCG R nc L (ext es₀ as) = zCG R nc L es₀ := zCG_same R nc (R.ofAgree L hag) (by omega)
  have hlen : a ≤ (List.ofFn fun j : Fin (r * 2) => coordAt (ext es₀ as) s0 j).length := by
    simp; omega
  rw [mlDoom_full t ht _ hlen, tbl_ofFn]
  intro hm
  apply hnf
  unfold ZCwG
  rw [hz]
  rwa [take_ofFn_coord (ext es₀ as) ha] at hm

/-! ### The handoffs -/

/-- **Into the outer rounds** (`habs` at `b2`). -/
theorem habsG_outer (hs : s0 + 1 + (a + 1) / 2 ≤ b2) (h3 : 3 ≤ b2) {L es : Log}
    (x : ByteArray × Digest) (hl : es.length = b2) (hz : ZCwG R E a nc s0 L es) :
    D3G R E a nc s0 b2 L (es ++ [x]) := by
  refine ⟨by simp; omega, ?_⟩
  have ha0 : ans3 b2 (fun _ => a) (es ++ [x]) = 0 := by
    simp only [ans3, List.length_append, List.length_singleton, hl]
    rw [show b2 + 1 - b2 = 1 by omega]; simp
  rw [ha0]
  simp only [Wrong3, clR, rchs, List.range_zero, List.map_nil, bindAll, Nat.sub_zero]
  rw [T3G_same R E a nc s0 (R.ofAgree L (agree_append es [x] le_rfl)) (by omega) (by omega)]
  exact outer_start _ (by simp [tauS]) hz

/-- **At the end absorb** (`habs` at `b2 + 2A`): with every real round answered, a doomed outer
claim gives the end check's failure or a wrong triple. -/
theorem habsG_end (hs : s0 + 1 + (a + 1) / 2 ≤ b2) (h3 : 3 ≤ b2) (haA : a ≤ A) {L es : Log}
    (x : ByteArray × Digest) (hl : es.length = b2 + 2 * A)
    (hd : D3G R E a nc s0 b2 L es) :
    RejEndG a s0 b2 A L (es ++ [x]) ∨ EndBadG R E a nc b2 A L (es ++ [x]) := by
  obtain ⟨-, hw⟩ := hd
  have ha : ans3 b2 (fun _ => a) es = a := by
    simp only [ans3, hl]; rw [show b2 + 2 * A - b2 = 2 * A by omega]; omega
  rw [ha] at hw
  unfold Wrong3 at hw
  have hfin : trueSum outerExpr (bindAll (T3G R E a nc s0 L es) (rchs b2 es a)) (a - a) =
      eq (ptOf a (tauS a s0 es)) (ptOf a (rxs a b2 es)) *
        ((triTG R E a nc b2 L es).1 * (triTG R E a nc b2 L es).2.1 +
          (triTG R E a nc b2 L es).2.2) := by
    simp only [T3G, Nat.sub_self]
    exact outer_final _ _ (by simp [tauS]) (by simp [rchs]) _ _ _ _
  rw [hfin] at hw
  have hag := agree_append es [x] (le_of_eq hl.symm)
  have hc : clR b2 (fun _ _ => 0) L (es ++ [x]) a = clR b2 (fun _ _ => 0) L es a :=
    clR_congr (b := b2) (c0 := fun _ _ => (0 : F)) (L := L) (es := es ++ [x]) (es' := es) rfl
      (l := a) (hag.mono (by omega))
  have hτ := tauS_agree (a := a) (s0 := s0) hag (by omega)
  have hr := rxs_agree (a := a) (b2 := b2) hag (by omega)
  by_cases hrej : RejEndG a s0 b2 A L (es ++ [x])
  · exact Or.inl hrej
  right
  refine ⟨by simp; omega, ?_⟩
  have hchk : clR b2 (fun _ _ => 0) L (es ++ [x]) a =
      eq (ptOf a (tauS a s0 (es ++ [x]))) (ptOf a (rxs a b2 (es ++ [x]))) *
        (vEnd A b2 (es ++ [x]) 0 * vEnd A b2 (es ++ [x]) 1 + vEnd A b2 (es ++ [x]) 2) := by
    by_contra hne; exact hrej ⟨by simp; omega, hne⟩
  rw [triTG_same R E a nc b2 (R.ofAgree L hag) (by omega) (by omega)]
  rw [hc, hτ, hr] at hchk
  intro heq
  rw [Prod.mk.injEq, Prod.mk.injEq] at heq
  apply hw
  rw [hchk, heq.1, heq.2.1, heq.2.2]

open Classical in
/-- **At the batching squeeze** (`hsingle` at `b2 + 2A + 1`, `batch_escape_le`): from a wrong
triple, at most `2·2^128` answers make the batched claim true. -/
theorem singleG_batch (h3 : 3 ≤ b2) (haA : a ≤ A) (L es : Log) (hl : es.length = b2 + 2 * A + 1) :
    (univ.filter fun d => EndBadG R E a nc b2 A L es ∧
      ¬ BatBadG R E a nc b2 A L (ext1 es d)).card ≤ 2 * 2 ^ 128 := by
  by_cases hd : EndBadG R E a nc b2 A L es
  swap
  · rw [filter_false_of_mem fun d _ h => hd h.1]; simp
  obtain ⟨-, hne⟩ := hd
  set S := univ.filter fun ρ : F => vEnd A b2 es 0 + ρ * vEnd A b2 es 1 + ρ ^ 2 * vEnd A b2 es 2 =
    trueSum innerExpr (innerTables (ptOf a (rxs a b2 es)) ρ (entMat E.ea a nc) (entMat E.eb a nc)
      (entMat E.ec a nc) (zCG R nc L es)) nc
  have hSc : S.card ≤ 2 := batch_escape_le _ _ _ _ _ (by unfold triTG at hne; exact hne)
  refine le_trans (card_le_card (t := univ.filter fun d : Digest => chF d 0 ∈ S)
    fun d hd' => ?_) (by rw [card_chF_fiber]; exact Nat.mul_le_mul_right _ hSc)
  simp only [mem_filter, mem_univ, true_and] at hd' ⊢
  obtain ⟨-, hnb⟩ := hd'
  simp only [S, mem_filter, mem_univ, true_and]
  have hag : Agree (ext1 es d) es es.length := agree_append es _ le_rfl
  have hκ : kapB A b2 (ext1 es d) = chF d 0 := by
    simp only [kapB, fAt, ansAt, ← hl]
    exact congrArg (chF · 0) (entAt_ext1 es d)
  by_contra hc
  apply hnb
  refine ⟨by simp [ext1]; omega, ?_⟩
  have hr := rxs_agree (a := a) (b2 := b2) hag (by omega)
  have hv := fun j => vEnd_agree (a := A) (b2 := b2) hag (by omega) j
  have hz := zCG_same R nc (R.ofAgree L hag) (by omega)
  unfold c4 T4G
  rw [hκ, hz, hr, hv 0, hv 1, hv 2]
  exact hc

open Classical in
/-- **An outer round's squeeze** (`D3_single`): at most `3·2^128` answers escape. -/
theorem singleG_outer (hs : s0 + 1 + (a + 1) / 2 ≤ b2) (h3 : 3 ≤ b2) (L es : Log) :
    (univ.filter fun d => D3G R E a nc s0 b2 L es ∧ ¬ D3G R E a nc s0 b2 L (ext1 es d)).card ≤
      3 * 2 ^ 128 :=
  D3_single (by omega) (T3G_local R E a nc s0 b2 hs h3) outerExpr_deg (T3G_size R E a nc s0) L es

/-- An outer round's absorb, or a dummy slot's items, keeps the outer doom. -/
theorem outerG_append (hs : s0 + 1 + (a + 1) / 2 ≤ b2) (h3 : 3 ≤ b2) {L es : Log}
    (x : ByteArray × Digest) (hlen : b2 < es.length)
    (hc : (es.length - b2) % 2 = 0 ∨ a ≤ (es.length - b2) / 2) :
    D3G R E a nc s0 b2 L (es ++ [x]) ↔ D3G R E a nc s0 b2 L es :=
  D3_append_iff (by omega) (T3G_local R E a nc s0 b2 hs h3) x hlen hc

/-- The outer doom reads the same off two logs whose words agree (`hstab`). -/
theorem D3G_same {L L' X : Log} {p : ℕ} (h : R.Sm L X L' X p) (hp3 : 3 ≤ p)
    (hs : s0 + 1 + (a + 1) / 2 ≤ p) :
    D3G R E a nc s0 b2 L X ↔ D3G R E a nc s0 b2 L' X :=
  (D3_log_congr (b := b2) (c0 := fun _ _ => (0 : F)) (nr := fun _ => a) (e := outerExpr)
    (T3G_same R E a nc s0 h hp3 hs).symm rfl).symm

/-- **Once every real round is answered, the outer doom reads before `b2 + 2a + 1`.** -/
theorem D3G_reads (hs : s0 + 1 + (a + 1) / 2 ≤ b2) (h3 : 3 ≤ b2) :
    ReadsS R (b2 + 2 * a + 1) (D3G R E a nc s0 b2) := fun L es L' es' h1 h2 h => by
  have hans : ∀ Y : Log, b2 + 2 * a ≤ Y.length → ans3 b2 (fun _ => a) Y = a := fun Y hY => by
    unfold ans3; simp; omega
  unfold D3G D3 Wrong3
  rw [hans es (by omega), hans es' (by omega), T3G_same R E a nc s0 h (by omega) (by omega),
    clR_log_congr (b := b2) (c0 := fun _ _ => (0 : F)) (L := L') (L' := L) rfl,
    clR_congr (b := b2) (c0 := fun _ _ => (0 : F)) (L := L') (es := es) (es' := es') rfl
      ((R.agree h).mono (by omega)),
    rchs_congr ((R.agree h).mono (by omega))]
  exact and_congr_left fun _ => ⟨fun _ => by omega, fun _ => by omega⟩

end Unit

/-! ## The end check -/

theorem rejEndG_agree {a s0 b2 A : ℕ} (hs : s0 + 1 + (a + 1) / 2 ≤ b2) (haA : a ≤ A) {L es L' es' : Log}
    (h : Agree es es' (b2 + 2 * A + 1)) (hl : b2 + 2 * A + 1 ≤ es.length)
    (hl' : b2 + 2 * A + 1 ≤ es'.length) :
    RejEndG a s0 b2 A L es ↔ RejEndG a s0 b2 A L' es' := by
  have hc : clR b2 (fun _ _ => (0 : F)) L es a = clR b2 (fun _ _ => 0) L' es' a :=
    (clR_log_congr (b := b2) (c0 := fun _ _ => (0 : F)) (L := L') (L' := L) rfl a).trans
      (clR_congr (b := b2) (c0 := fun _ _ => (0 : F)) (L := L') (es := es) (es' := es') rfl
        (l := a) (h.mono (by omega)))
  have hτ := tauS_agree (a := a) (s0 := s0) h (by omega)
  have hr := rxs_agree (a := a) (b2 := b2) h (by omega)
  have hv := fun j => vEnd_agree (a := A) (b2 := b2) h le_rfl j
  unfold RejEndG
  rw [hc, hτ, hr, hv 0, hv 1, hv 2]
  exact and_congr_left fun _ => ⟨fun _ => by omega, fun _ => by omega⟩

/-- **The end check is a revision 4.1 check** (its absorb at `b2 + 2A` is not a squeeze). -/
theorem rejEndG_log {a s0 b2 A : ℕ} (hs : s0 + 1 + (a + 1) / 2 ≤ b2) (haA : a ≤ A)
    (hpe : fsItems4[b2 + 2 * A]? ≠ some .squeeze) : RejLog4 (RejEndG a s0 b2 A) :=
  rejLog4_of (q := b2 + 2 * A + 1) (by omega) (fun _ _ h => by have := h.1; omega)
    (fun _ _ _ _ h1 h2 h => rejEndG_agree hs haA h h1 h2) (by simpa using hpe)

/-! ## O1: the E truth over indexed rows -/

section O1
open Circ

/-- **Indexed rows fit** `2^a` rows and `2^b` cells, with **distinct** row indices (two rows at one
index would add up into one matrix row). -/
def RowsFitI (rows : List (ℕ × Row)) (a b : ℕ) : Prop :=
  (rows.map Prod.fst).Nodup ∧ (∀ p ∈ rows, p.1 < 2 ^ a) ∧
    ∀ p ∈ rows, ∀ t ∈ p.2.a ++ p.2.b ++ p.2.c, t.1 < 2 ^ b

/-- **The E truth over indexed rows**: every row holds at `w`. -/
def truthEI (rows : List (ℕ × Row)) (w : Asg) : Prop := ∀ p ∈ rows, p.2.Holds w

theorem sum_ite_none {β : Type*} (g : ℕ × β → F) (x : ℕ) :
    ∀ rows : List (ℕ × β), (∀ q ∈ rows, q.1 ≠ x) →
      (rows.map fun q => if q.1 = x then g q else 0).sum = 0
  | [], _ => by simp
  | q :: rs, h => by
    simp only [List.map_cons, List.sum_cons, ite_neg' (h q List.mem_cons_self),
      sum_ite_none g x rs fun q' hq' => h q' (List.mem_cons_of_mem _ hq'), add_zero]

theorem sum_ite_key {β : Type*} (g : ℕ × β → F) :
    ∀ rows : List (ℕ × β), (rows.map Prod.fst).Nodup → ∀ p ∈ rows,
      (rows.map fun q => if q.1 = p.1 then g q else 0).sum = g p
  | [], _, p, hp => by simp at hp
  | q :: rs, hnd, p, hp => by
    simp only [List.map_cons, List.nodup_cons, List.mem_map] at hnd
    simp only [List.map_cons, List.sum_cons]
    rcases List.mem_cons.1 hp with rfl | hp
    · rw [ite_pos' rfl, sum_ite_none g _ rs fun q' hq' h => hnd.1 ⟨q', hq', h⟩, add_zero]
    · have hne : q.1 ≠ p.1 := fun h => hnd.1 ⟨p, hp, h.symm⟩
      rw [ite_neg' hne, zero_add, sum_ite_key g rs hnd.2 p hp]

theorem sum_entriesI (s : TEval.Mat) (w : Asg) (x : ℕ) :
    ∀ rows : List (ℕ × Row),
      ((TEval.entriesI s rows).map fun e => if e.1 = x then e.2.2 * w e.2.1 else 0).sum =
        (rows.map fun q => if q.1 = x then (s.r q.2).ev w else 0).sum
  | [] => by simp [TEval.entriesI]
  | q :: rs => by
    have ih := sum_entriesI s w x rs
    simp only [TEval.entriesI, List.flatMap_cons, List.map_append, List.sum_append,
      List.map_cons, List.sum_cons] at ih ⊢
    rw [ih]
    congr 1
    by_cases hq : q.1 = x
    · simp [hq, Lin.ev, Function.comp_def]
    · simp [hq, Function.comp_def]

/-- **The matrix product of indexed rows**: on rows whose cells fit, `(M w)(x)` is the sum of the
forms of the rows at index `x`. -/
theorem matVec_entMatI (s : TEval.Mat) (rows : List (ℕ × Row)) {a b : ℕ}
    (hc : ∀ p ∈ rows, ∀ t ∈ s.r p.2, t.1 < 2 ^ b) (w : Asg) (x : Fin (2 ^ a)) :
    matVec (entMat (TEval.entriesI s rows) a b) (fun y => w y) x =
      (rows.map fun q => if q.1 = x.val then (s.r q.2).ev w else 0).sum := by
  have hE : ∀ e ∈ TEval.entriesI s rows, e.2.1 < 2 ^ b := by
    intro e he
    simp only [TEval.entriesI, List.mem_flatMap, List.mem_map] at he
    obtain ⟨p, hp, t, ht, rfl⟩ := he
    exact hc p hp t ht
  rw [matVec]
  exact (sum_entry_mul _ _ w hE).trans (sum_entriesI s w x rows)

/-- **O1: the R1CS of the indexed rows is "every row holds"** (`evalMS`'s matrices). -/
theorem sat_entMatI_iff (rows : List (ℕ × Row)) {a b : ℕ} (hf : RowsFitI rows a b) (w : Asg) :
    Sat (entMat (ESrc.ofIRows rows).ea a b) (entMat (ESrc.ofIRows rows).eb a b)
      (entMat (ESrc.ofIRows rows).ec a b) (fun y => w y) ↔ truthEI rows w := by
  have hc : ∀ s : TEval.Mat, ∀ p ∈ rows, ∀ t ∈ s.r p.2, t.1 < 2 ^ b := by
    intro s p hp t ht
    refine hf.2.2 p hp t ?_
    cases s <;> simp_all [TEval.Mat.r]
  unfold Sat
  simp only [ESrc.ofIRows, matVec_entMatI _ _ (hc _)]
  constructor
  · intro h p hp
    have := h ⟨p.1, hf.2.1 p hp⟩
    simp only [sum_ite_key _ rows hf.1 p hp] at this
    exact this
  · intro h x
    by_cases hx : ∃ p ∈ rows, p.1 = x.val
    · obtain ⟨p, hp, hpx⟩ := hx
      rw [← hpx, sum_ite_key _ rows hf.1 p hp, sum_ite_key _ rows hf.1 p hp,
        sum_ite_key _ rows hf.1 p hp]
      exact h p hp
    · push Not at hx
      rw [sum_ite_none _ _ rows hx, sum_ite_none _ _ rows hx, sum_ite_none _ _ rows hx, zero_mul]

/-- `¬ RowsBadG` over indexed rows is the E truth at `f⁽⁰⁾`. -/
theorem rowsBadG_ofIRows_iff (R : FSrc) (rows : List (ℕ × Row)) {a nc : ℕ}
    (hf : RowsFitI rows a nc) (L es : Log) :
    RowsBadG R (ESrc.ofIRows rows) a nc L es ↔ ¬ truthEI rows (R.fz L es) :=
  not_congr (sat_entMatI_iff rows hf (R.fz L es))

/-- **3.x's row list is an instance** (`sat_rowMat_iff` at `ESrc.ofRows`). -/
theorem sat_ofRows_iff (rows : List Row) {a b : ℕ} (hf : RowsFit rows a b) (w : Asg) :
    Sat (entMat (ESrc.ofRows rows).ea a b) (entMat (ESrc.ofRows rows).eb a b)
      (entMat (ESrc.ofRows rows).ec a b) (fun y => w y) ↔ ∀ r ∈ rows, r.Holds w :=
  sat_rowMat_iff rows hf w

/-- **O1 at 3.x**: the E truth at the templated, indexed rows `evalMS` reads
(`nodeIRows (planOf fin)`, 21 row bits, 23 cells), given that they fit (`hfit`). -/
theorem truthE3_iffI (fin : Finals) (hfit : RowsFitI (TEval.nodeIRows (TEval.planOf fin)) 21 23)
    (κ : Kind) (L es : Log) :
    truthEI (TEval.nodeIRows (TEval.planOf fin)) (fF κ L es) ↔
      Sat (entMat (ESrc.ofIRows (TEval.nodeIRows (TEval.planOf fin))).ea 21 23)
        (entMat (ESrc.ofIRows (TEval.nodeIRows (TEval.planOf fin))).eb 21 23)
        (entMat (ESrc.ofIRows (TEval.nodeIRows (TEval.planOf fin))).ec 21 23) (fun y => fF κ L es y) :=
  (sat_entMatI_iff _ hfit _).symm

/-- **The unit's matrix MLE is `evalMS`'s** (`Eval.matMLE`). -/
theorem matMle_entMat (E : Eval.Entries) {a b : ℕ} (τ : Fin a → F) (σ : Fin b → F) :
    matMle (entMat E a b) τ σ = Eval.matMLE E τ σ := rfl

/-- **E4's weight at `r′`** is the three matrix MLEs at `(r_x, r′)`, batched by `ρ`. -/
theorem mle_wInn {a nc : ℕ} (A B C : Fin (2 ^ a) → Fin (2 ^ nc) → F) (rx : Fin a → F) (ρ : F)
    (r : Fin nc → F) :
    mle (wInn A B C rx ρ) r = matMle A rx r + ρ * matMle B rx r + ρ ^ 2 * matMle C rx r := by
  have h := mle_comb (fun y => matMle A rx (cube y)) (fun y => matMle B rx (cube y))
    (fun y => matMle C rx (cube y)) ρ r
  simp only [mle_matMle] at h
  exact h

end O1

/-! ## Controls -/

/-- (−) Two rows at one index do not fit (`RowsFitI` asks for distinct indices). -/
theorem not_rowsFitI_dup (r : Circ.Row) : ¬ RowsFitI [(0, r), (0, r)] 1 1 := fun h => by
  simp [RowsFitI] at h

/-- (+) The empty indexed row list is satisfied by every assignment. -/
theorem sat_entMatI_nil (a b : ℕ) (w : Circ.Asg) :
    Sat (entMat (ESrc.ofIRows []).ea a b) (entMat (ESrc.ofIRows []).eb a b)
      (entMat (ESrc.ofIRows []).ec a b) (fun y => w y) :=
  (sat_entMatI_iff [] ⟨by simp, by simp, by simp⟩ w).mpr (by simp [truthEI])

/-- (−) An indexed row `1 · 1 = 0` at index 1 makes the R1CS fail. -/
theorem not_sat_entMatI_one (w : Circ.Asg) (hw : w 0 = 1) :
    ¬ Sat (entMat (ESrc.ofIRows [(1, ⟨Circ.Lin.cell 0, Circ.Lin.cell 0, []⟩)]).ea 1 1)
      (entMat (ESrc.ofIRows [(1, ⟨Circ.Lin.cell 0, Circ.Lin.cell 0, []⟩)]).eb 1 1)
      (entMat (ESrc.ofIRows [(1, ⟨Circ.Lin.cell 0, Circ.Lin.cell 0, []⟩)]).ec 1 1) (fun y => w y) := by
  rw [sat_entMatI_iff _ ⟨by simp, by simp, by simp [Circ.Lin.cell]⟩]
  intro h
  have := h _ List.mem_cons_self
  simp [Circ.Row.Holds, hw] at this

end FR.Snd.P4b
