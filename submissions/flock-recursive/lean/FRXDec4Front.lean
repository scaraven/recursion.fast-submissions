-- G6: this module also holds the former modules `FRXDec4Level`, `FRXLagT`, `FRXDecLv`, `FRXDec4Back` (one section each, in import order).
import FRXLevel
import FRSoundness4TailFold
import FRXLag
import FRXMsg
import FRXAgree

section G6_FRXDec4Level

-- New for `flock-recursive` (BLUEPRINT revision 4.2, §6.2 step 4; stage S-H4, pass 2, item 2).

/-!
# One level's decoding at revision 4.1's kinds, pure (`level_decode4`)

`FRXLevel` proves, at 3.x's `Kind`, that interpolating a close word's rows on the first `kᵢ`
agreement positions and running the butterflies gives S-G's `msgOf`. This module restates it
over T4's `CKind` copies (`FR.Snd.T4`: `wordOf`, `consSet`, `decodeL`, `farL`, `msgOf`, `mLog`, the
ladder `CKind.lv κ i = lvOf κ.m i`). The proofs are 3.x's: only the level parameters
(`lv_params`) are per kind.

* `foldAt4_f₀`/`_f₁`, `mem_consSet4_iff`: the agreement flag in `F` coordinates;
* `nextMsg4_coords`: below level 4 the next message is two decoded rows;
* **`level_decode4`** and `msgOf4_embed`.
-/

namespace FR.X

open RecursionFast FR Finset FR.Snd.T4

-- G2: `entryK`/`storeM`/`runPrims` are never unfolded while unifying states (elaboration time).
attribute [local irreducible] entryK storeM runPrims

/-- **The column fold's `f₀`** at a 4.1 kind. -/
theorem foldAt4_f₀ (κ : Snd.CKind) (L es : Log) (i : ℕ) (j : Fin (2 ^ (Snd.CKind.lv κ i).logN)) :
    (Snd.T4.foldAt κ L es i j).f₀ = ∑ r : Fin (Snd.CKind.lv κ i).rows,
      Snd.T4.wordOf κ L es i r j * (eqBits (Snd.T4.sAt es i) (Snd.CKind.lv κ i).ell r).f₀ := by
  rw [Snd.T4.foldAt, K_sum_f₀]
  refine sum_congr rfl fun r _ => ?_
  rw [Snd.T4.wordK, mul_comm, algebraMap_mul_K]

/-- The column fold's `f₁` at a 4.1 kind. -/
theorem foldAt4_f₁ (κ : Snd.CKind) (L es : Log) (i : ℕ) (j : Fin (2 ^ (Snd.CKind.lv κ i).logN)) :
    (Snd.T4.foldAt κ L es i j).f₁ = ∑ r : Fin (Snd.CKind.lv κ i).rows,
      Snd.T4.wordOf κ L es i r j * (eqBits (Snd.T4.sAt es i) (Snd.CKind.lv κ i).ell r).f₁ := by
  rw [Snd.T4.foldAt, K_sum_f₁]
  refine sum_congr rfl fun r _ => ?_
  rw [Snd.T4.wordK, mul_comm, algebraMap_mul_K]

/-- **The agreement flag in coordinates** at a 4.1 kind. -/
theorem mem_consSet4_iff (κ : Snd.CKind) (L es : Log) (i : ℕ) (j : Fin (2 ^ (Snd.CKind.lv κ i).logN)) :
    j ∈ Snd.T4.consSet κ L es i ↔
      (∑ r : Fin (Snd.CKind.lv κ i).rows, Snd.T4.wordOf κ L es i r j * (eqBits (Snd.T4.sAt es i) (Snd.CKind.lv κ i).ell r).f₀ =
        encF (Snd.T4.mLog κ i) (fun x => (Snd.T4.nextMsg κ L es i x).f₀) j) ∧
      (∑ r : Fin (Snd.CKind.lv κ i).rows, Snd.T4.wordOf κ L es i r j * (eqBits (Snd.T4.sAt es i) (Snd.CKind.lv κ i).ell r).f₁ =
        encF (Snd.T4.mLog κ i) (fun x => (Snd.T4.nextMsg κ L es i x).f₁) j) := by
  rw [Snd.T4.consSet, Finset.mem_filter]
  simp only [mem_univ, true_and, Snd.T4.encAt]
  rw [← foldAt4_f₀, ← foldAt4_f₁, ← encF_f₀, ← encF_f₁]
  exact ⟨fun h => ⟨by rw [h], by rw [h]⟩, fun h => K_ext' h.1 h.2⟩

/-- **The next message from level `i + 1`'s rows** (`i < 4`) at a 4.1 kind. -/
theorem nextMsg4_coords {κ : Snd.CKind} {L es : Log} {i : ℕ} (hi : i + 1 < nLevels)
    (hF : ∀ r x, Snd.T4.msgOf κ L es (i + 1) r x = algebraMap F K (Snd.T4.msgOf κ L es (i + 1) r x).f₀)
    (x : ℕ) :
    Snd.T4.nextMsg κ L es i x = ⟨(Snd.T4.msgOf κ L es (i + 1) (2 * (x % 8)) (x / 8)).f₀,
      (Snd.T4.msgOf κ L es (i + 1) (2 * (x % 8) + 1) (x / 8)).f₀⟩ := by
  rw [Snd.T4.nextMsg, if_pos hi, hF (2 * (x % 8)), hF (2 * (x % 8) + 1), ofF_add_u_mul]
  rfl

/-- Level `i`'s agreement set as positions in `ℕ` (a 4.1 kind). -/
noncomputable def consN4 (κ : Snd.CKind) (L es : Log) (i : ℕ) : Finset ℕ :=
  (Snd.T4.consSet κ L es i).map Fin.valEmbedding

/-- Level `i`'s row `r` as an `ℕ`-indexed word (`0` past the positions). -/
def wordN4 (κ : Snd.CKind) (L es : Log) (i : ℕ) (r : Fin (Snd.CKind.lv κ i).rows) (j : ℕ) : F :=
  if hj : j < 2 ^ (Snd.CKind.lv κ i).logN then Snd.T4.wordOf κ L es i r ⟨j, hj⟩ else 0

theorem mem_consN4 {κ : Snd.CKind} {L es : Log} {i j : ℕ} :
    j ∈ consN4 κ L es i ↔ ∃ h : j < 2 ^ (Snd.CKind.lv κ i).logN, (⟨j, h⟩ : Fin _) ∈ Snd.T4.consSet κ L es i := by
  simp only [consN4, mem_map, Fin.valEmbedding_apply]
  constructor
  · rintro ⟨a, ha, rfl⟩; exact ⟨a.2, ha⟩
  · rintro ⟨h, hm⟩; exact ⟨_, hm, rfl⟩

/-- **One level's decoding at a 4.1 kind**: on a close word with `A_c = jointAgree`, interpolating
row `r` on the first `kᵢ` positions of `A_c` and running the `mLog` butterflies gives
`T4.msgOf κ L es i r` (in `K`). -/
theorem level_decode4 {κ : Snd.CKind} {L es : Log} {i : ℕ} (hi : i < 5) (hfar : ¬ Snd.T4.farL κ L es i)
    (hA : Snd.T4.consSet κ L es i = jointAgree (Snd.T4.wordK κ L es i) (Snd.T4.decodeL κ L es i))
    (r : Fin (Snd.CKind.lv κ i).rows) (x : Fin (2 ^ Snd.T4.mLog κ i)) :
    algebraMap F K (bflyRun (M := F) D logNMax 0 (Snd.T4.mLog κ i)
        (interpF D (firstK (2 ^ (Snd.CKind.lv κ i).logN) (consN4 κ L es i) (2 ^ Snd.T4.mLog κ i))
          (wordN4 κ L es i r)) x) = Snd.T4.msgOf κ L es i r x := by
  classical
  obtain ⟨hek, hN, hm, hk, hn⟩ := Snd.T4.lv_params κ hi
  have hnN : 2 ^ (Snd.CKind.lv κ i).logN ≤ nMax := hn ▸ hN
  obtain ⟨hV, hJ⟩ := Snd.T4.decodeL_spec hfar
  obtain ⟨c, hc⟩ := Snd.T4.exists_msg hi (hV r)
  rw [Snd.T4.msgOf_eq hi hc x, bflyRun_map]
  simp only [interpF_map]
  refine decode_agree hm hnN (fun j hj => (mem_consN4.1 hj).1) ?_ c _ (fun j hj => ?_) x
  · rw [consN4, card_map, hA]
    have : Snd.T4.lvK κ i ≤ 2 ^ (Snd.CKind.lv κ i).logN - Snd.T4.lvE κ i := by rw [← hn]; omega
    rw [← hk]; exact this.trans hJ
  · obtain ⟨hj', hmem⟩ := mem_consN4.1 hj
    rw [hA, mem_jointAgree] at hmem
    have h1 := hmem r
    rw [Snd.T4.wordK] at h1
    simp only [wordN4, hj', dite_true]
    rw [h1, ← hc, enc_eq_encN]

/-- **The decoded messages are `F`-valued** (a 4.1 kind, close word, `A_c = jointAgree`). -/
theorem msgOf4_embed {κ : Snd.CKind} {L es : Log} {i : ℕ} (hi : i < 5) (hfar : ¬ Snd.T4.farL κ L es i)
    (hA : Snd.T4.consSet κ L es i = jointAgree (Snd.T4.wordK κ L es i) (Snd.T4.decodeL κ L es i)) (r x : ℕ) :
    Snd.T4.msgOf κ L es i r x = algebraMap F K (Snd.T4.msgOf κ L es i r x).f₀ := by
  by_cases hr : r < (Snd.CKind.lv κ i).rows
  swap
  · simp only [Snd.T4.msgOf, hr, dite_false]; rfl
  by_cases hx : x < 2 ^ Snd.T4.mLog κ i
  swap
  · simp only [Snd.T4.msgOf, hr, hx, dite_true, dite_false]; rfl
  rw [← level_decode4 hi hfar hA ⟨r, hr⟩ ⟨x, hx⟩]
  rfl

end FR.X

end G6_FRXDec4Level

section G6_FRXLagT

-- New for `flock-recursive` (BLUEPRINT revision 4.2, §10 changes 27 (A)(ii); stage S-H4, pass 2).

/-!
# The target half of `lagIR`: the forward and backward passes, the outputs

`FRXLag` proves the weights and values (`yTab_sem`). This module proves the target loop `tgIR`:

* `fwdLoop_sem`: the forward pass stores the prefix products `P_t = preP J s t` at `pb + t`;
* `accIR_sem`: the `C` unrolled rows add `e · Y_c[t]` to the accumulators;
* `bwdLoop_sem`: the backward pass leaves `acc_c = Σ_{t<k} P_t · Q_t · Y_c[t]`
  (`Q_t = sufP J k s (t + 1)`);
* `stAcc_sem`: the `C` outputs, row `c` at `o + 2kc`;
* `tgIR_sem`: every target `s < k`; then **`lagIR_sem`** (output row `c` at target `s` is
  `lagVal J k s y_{c₀+c}`) and **`lagIR_interp`** (the same is `interpF D J y s`).
-/

namespace FR.X

open RecursionFast FR Finset

-- G2: `entryK`/`storeM`/`runPrims` are never unfolded while unifying states (elaboration time).
attribute [local irreducible] entryK storeM runPrims

/-! ## The forward pass -/

theorem fwd_blk (M : Mem) (hM : Inv M) {a b : ℕ} (hA : rd M lgA = toWord a) (hB : rd M lgB = toWord b) :
    let M' := runPrims ([.op .xor lgD lgS lgJ, .op .add lgA lgA cOne, .op .add lgB lgB cOne] ++
      mulBC lgP lgP lgD) M
    rd M' lgA = toWord (a + 1) ∧ rd M' lgB = toWord (b + 1) ∧
    rdB M' lgP = rdB M lgP * wB (rd M lgS ^^^ rd M lgJ) ∧
    (∀ i, i ≠ lgD → i ≠ lgA → i ≠ lgB → i ≠ lgP → (i < 5 ∨ 9 ≤ i) → rd M' i = rd M i) ∧ Inv M' := by
  intro M'
  have hs : 256 ≤ M.size := hM.1
  have h1 : rd M cOne = 1 := hM.2 0 (by decide)
  have e : M' = runPrims (mulBC lgP lgP lgD)
      (runPrims [.op .xor lgD lgS lgJ, .op .add lgA lgA cOne, .op .add lgB lgB cOne] M) :=
    runPrims_append ..
  have hI : Inv (runPrims [.op .xor lgD lgS lgJ, .op .add lgA lgA cOne, .op .add lgB lgB cOne] M) :=
    inv_runPrims (by simp [Prim.dst, lgD, lgA, lgB]) hM
  have r : ∀ i, i ≠ lgD → i ≠ lgA → i ≠ lgB →
      rd (runPrims [.op .xor lgD lgS lgJ, .op .add lgA lgA cOne, .op .add lgB lgB cOne] M) i =
        rd M i := fun i a b c =>
    rd_runPrims_of_not_writes (by simp [Prim.dst]; exact ⟨Ne.symm a, Ne.symm b, Ne.symm c⟩) _
  rw [e]
  refine ⟨?_, ?_, ?_, fun i h1 h2 h3 h4 h5 => ?_, mulBC_inv _ _ _ (by decide) hI⟩
  · rw [mulBC_frame _ _ _ (by decide) (by decide)]
    simp only [runPrims_cons, runPrims_nil, Prim.run]
    simp (disch := first | decide | (simp only [size_set, lgA, lgB, lgD]; omega)) only
      [rd_set_self, rd_set_ne]
    rw [hA, h1, add_one_toWord]
  · rw [mulBC_frame _ _ _ (by decide) (by decide)]
    simp only [runPrims_cons, runPrims_nil, Prim.run]
    simp (disch := first | decide | (simp only [size_set, lgA, lgB, lgD]; omega)) only
      [rd_set_self, rd_set_ne]
    rw [hB, h1, add_one_toWord]
  · rw [rdB, mulBC_run hI (by decide) (by decide) (by decide) (by decide), mulBW_spec,
      r _ (by decide) (by decide) (by decide)]
    simp only [rdB, runPrims_cons, runPrims_nil, Prim.run]
    simp (disch := first | decide | (simp only [size_set, lgA, lgB, lgD]; omega)) only
      [rd_set_self, rd_set_ne, eval_xor]
  · rw [mulBC_frame _ _ _ h5 h4, r _ h1 h2 h3]

/-- **The forward step**: `M[b] := P`, `P *= S ⊕ M[a]`, `lgA, lgB += 1`. -/
theorem fwdL_sem (I : Array Word) (s : St) (hM : Inv s.M) {a b : ℕ} (hA : rd s.M lgA = toWord a)
    (hB : rd s.M lgB = toWord b) (ha : a + 1 < 2 ^ 64) (hb : regs ≤ b) (hb2 : b + 1 < 2 ^ 64)
    (hbs : b < s.M.size) :
    rd (semXIR I fwdL s).M lgA = toWord (a + 1) ∧ rd (semXIR I fwdL s).M lgB = toWord (b + 1) ∧
    rd (semXIR I fwdL s).M b = rd s.M lgP ∧
    rdB (semXIR I fwdL s).M lgP = rdB s.M lgP * wB (rd s.M lgS ^^^ rd s.M a) ∧
    (∀ i, regs ≤ i → i ≠ b → rd (semXIR I fwdL s).M i = rd s.M i) ∧
    Inv (semXIR I fwdL s).M := by
  simp only [regs] at hb
  simp only [fwdL, semXIR_seq, semB]
  obtain ⟨l1, l1f⟩ := bload_sem I s hM (d := lgJ) (a := lgA) (x := a) (by decide) hA (by omega)
  have hM1 := inv_sem I (P := .load lgJ lgA) (by simp [WF, lgJ]) hM
  have z1 := size_sem I (.load lgJ lgA) s
  generalize semXIR I (.load lgJ lgA) s = s1 at l1 l1f hM1 z1 ⊢
  have a2 := fun i (hi : i ≠ cTmp) => st_rd I s1 hM1 ((l1f lgB (by decide)).trans hB)
    (by simp only [regs]; omega) (by omega) (by omega) (by decide) (by decide) (v := lgP) hi
  have hM2 := inv_sem I (P := .store lgB lgP) (s := s1) (by simp [WF, lgB, cTmp]) hM1
  generalize semXIR I (.store lgB lgP) s1 = s2 at a2 hM2 ⊢
  have r2 : ∀ i, i ≠ cTmp → i ≠ b → i ≠ lgJ → rd s2.M i = rd s.M i := fun i hT hb hJ => by
    rw [a2 i hT, if_neg hb, l1f i hJ]
  have hJ2 : rd s2.M lgJ = rd s.M a := by rw [a2 _ (by decide), if_neg (by simp only [lgJ]; omega), l1]
  obtain ⟨f1, f2, f3, f4, f5⟩ := fwd_blk s2.M hM2 (a := a) (b := b)
    (by rw [r2 _ (by decide) (by simp only [lgA]; omega) (by decide), hA])
    (by rw [r2 _ (by decide) (by simp only [lgB]; omega) (by decide), hB])
  refine ⟨f1, f2, ?_, ?_, fun i hi hib => ?_, f5⟩
  · rw [f4 _ (by simp only [lgD]; omega) (by simp only [lgA]; omega) (by simp only [lgB]; omega)
      (by simp only [lgP]; omega) (.inr (by omega)), a2 _ (by simp only [cTmp]; omega), if_pos rfl,
      l1f _ (by decide)]
  · rw [f3, hJ2, rdB, rdB, r2 _ (by decide) (by simp only [lgP]; omega) (by decide),
      r2 _ (by decide) (by simp only [lgS]; omega) (by decide)]
  · simp only [regs] at hi
    rw [f4 _ (by simp only [lgD]; omega) (by simp only [lgA]; omega) (by simp only [lgB]; omega)
      (by simp only [lgP]; omega) (.inr (by omega)),
      r2 _ (by simp only [cTmp]; omega) hib (by simp only [lgJ]; omega)]

theorem wf_fwdL : WF fwdL := by simp [fwdL, WF, mulBC, redC, Prim.dst, lgJ, lgB, cTmp, lgD, lgA, lgP]

theorem nw_fwdL {i : ℕ} (h1 : i ≠ lgJ) (h2 : i ≠ lgD) (h3 : i ≠ lgA) (h4 : i ≠ lgB) (h5 : i ≠ lgP)
    (h6 : i ≠ cTmp) (h7 : i < 5 ∨ 9 ≤ i) : ¬ Writes fwdL i := by
  intro h
  simp [fwdL, Writes, mulBC, redC, Prim.dst] at h
  simp only [lgJ, lgD, lgA, lgB, lgP, cTmp] at *
  omega

/-- **The forward pass**: from `P = 1`, `lgA = jb`, `lgB = pb`, the prefix products
`P_t = preP J s t` at `pb + t` for `t < k`; the heap outside `[pb, pb + k)` is kept. -/
theorem fwdLoop_sem (I : Array Word) (s : St) (hM : Inv s.M) {k jb pb sv : ℕ} {Jl : List ℕ}
    (hk : k < 2 ^ 64) (hjb : regs ≤ jb) (hjp : jb + k ≤ pb) (hpb2 : pb + k + 1 < 2 ^ 64)
    (hps : pb + k ≤ s.M.size) (hA : rd s.M lgA = toWord jb) (hB : rd s.M lgB = toWord pb)
    (hN : rd s.M lgN2 = toWord k) (hP : rdB s.M lgP = 1) (hS : rd s.M lgS = toWord sv)
    (hJ : ∀ u < k, rd s.M (jb + u) = jw Jl u) :
    rd (semXIR I (.loopK lgC2 lgN2 (toWord k) fwdL) s).M lgA = toWord (jb + k) ∧
    rd (semXIR I (.loopK lgC2 lgN2 (toWord k) fwdL) s).M lgB = toWord (pb + k) ∧
    (∀ t < k, rdB (semXIR I (.loopK lgC2 lgN2 (toWord k) fwdL) s).M (pb + t) = preP Jl sv t) ∧
    (∀ i, regs ≤ i → (i < pb ∨ pb + k ≤ i) →
      rd (semXIR I (.loopK lgC2 lgN2 (toWord k) fwdL) s).M i = rd s.M i) ∧
    Inv (semXIR I (.loopK lgC2 lgN2 (toWord k) fwdL) s).M := by
  simp only [regs] at hjb
  let P : ℕ → St → Prop := fun j st => Inv st.M ∧ st.M.size = s.M.size ∧
    rd st.M lgA = toWord (jb + j) ∧ rd st.M lgB = toWord (pb + j) ∧ rdB st.M lgP = preP Jl sv j ∧
    rd st.M lgS = toWord sv ∧ (∀ t < j, rdB st.M (pb + t) = preP Jl sv t) ∧
    (∀ i, regs ≤ i → (i < pb ∨ pb + j ≤ i) → rd st.M i = rd s.M i)
  have ef : ∀ i, i ≠ lgC2 → i ≠ cTmp → rd (entryK lgC2 lgN2 (toWord k) s.M) i = rd s.M i :=
    fun i a b => entryK_frame _ (Ne.symm a) (Ne.symm b)
  have h := loopK_run I fwdL P s hM (by decide) (by decide) (by decide) hN hk
    ⟨inv_entryK hM (by decide), size_entryK .., by rw [ef _ (by decide) (by decide), hA]; rfl,
      by rw [ef _ (by decide) (by decide), hB]; rfl,
      by rw [rdB, ef _ (by decide) (by decide), ← rdB, hP]; rfl,
      by rw [ef _ (by decide) (by decide), hS], fun t ht => absurd ht (Nat.not_lt_zero _),
      fun i hi _ => ef i (by simp only [regs, lgC2] at hi ⊢; omega)
        (by simp only [regs, cTmp] at hi ⊢; omega)⟩ ?_
  · exact ⟨h.2.2.1, h.2.2.2.1, h.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2, h.1⟩
  rintro j st hj ⟨hI, hz, hA', hB', hP', hS', hV, hH⟩
  obtain ⟨b1, b2, b3, b4, b5, hI2⟩ := fwdL_sem I st hI (a := jb + j) (b := pb + j) hA' hB'
    (by omega) (by simp only [regs]; omega) (by omega) (by omega)
  have hS2 : rd (semXIR I fwdL st).M lgS = toWord sv := by
    rw [frame I _ _ wf_fwdL hI _ (by decide) (nw_fwdL (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide)), hS']
  have hd : ∀ i, regs ≤ i → rd (decS lgC2 (semXIR I fwdL st)).M i = rd (semXIR I fwdL st).M i :=
    fun i hi => rd_decS (by simp only [regs, lgC2] at hi ⊢; omega) _
  refine ⟨inv_decS hI2 (by decide), by rw [size_decS, size_sem, hz], ?_, ?_, ?_, ?_,
    fun t ht => ?_, fun i hi hi2 => ?_⟩
  · rw [rd_decS (by decide), b1]; exact congrArg toWord (by omega)
  · rw [rd_decS (by decide), b2]; exact congrArg toWord (by omega)
  · rw [rdB, rd_decS (by decide), ← rdB, b4, hP', hS', hH _ (by simp only [regs]; omega)
      (.inl (by omega)), hJ j hj, preP, preP, Finset.prod_range_succ]; rfl
  · rw [rd_decS (by decide), hS2]
  · rw [rdB, hd _ (by simp only [regs]; omega), ← rdB]
    rcases Nat.lt_succ_iff_lt_or_eq.1 ht with ht | rfl
    · rw [rdB, b5 _ (by simp only [regs]; omega) (by omega), ← rdB]; exact hV t ht
    · rw [rdB, b3, ← rdB, hP']
  · rw [hd i hi, b5 i hi (by omega), hH i hi (by omega)]

/-! ## The rows' accumulation -/

theorem rdF_mk (M : Mem) (a : ℕ) : rdF M a = ⟨wB (rd M a), wB (rd M (a + 1))⟩ := rfl

/-- **Row `c`'s step**: `acc_c += e · M[x]` (`F`, two words), `lgX += 2`. -/
theorem accRow_sem (I : Array Word) (s : St) (hM : Inv s.M) {c x : ℕ} (hc : c < 16)
    (hX : rd s.M lgX = toWord x) (hx : regs ≤ x) (hx2 : x + 2 < 2 ^ 64) :
    rd (semXIR I (accRow c) s).M lgX = toWord (x + 2) ∧
    rdF (semXIR I (accRow c) s).M (lgAc + 2 * c) =
      rdF s.M (lgAc + 2 * c) + F.smulBase (rdB s.M lgE) (rdF s.M x) ∧
    (∀ i, i ≠ lgX → i ≠ lgV → i ≠ lgV1 → i ≠ lgAc + 2 * c → i ≠ lgAc + 2 * c + 1 → (i < 5 ∨ 9 ≤ i) →
      rd (semXIR I (accRow c) s).M i = rd s.M i) ∧
    Inv (semXIR I (accRow c) s).M := by
  simp only [regs] at hx
  simp only [accRow, semXIR_seq, semB]
  obtain ⟨l1, l1f⟩ := bload_sem I s hM (d := lgV) (a := lgX) (x := x) (by decide) hX (by omega)
  have hM1 := inv_sem I (P := .load lgV lgX) (by simp [WF, lgV]) hM
  generalize semXIR I (.load lgV lgX) s = s1 at l1 l1f hM1 ⊢
  obtain ⟨i2, i2f⟩ := incr_sem s1.M hM1 (r := lgX) (x := x) (by decide) (by decide)
    ((l1f _ (by decide)).trans hX)
  have hM2 : Inv (runPrims [.op .add lgX lgX cOne] s1.M) := inv_runPrims (by simp [Prim.dst, lgX]) hM1
  generalize runPrims [.op .add lgX lgX cOne] s1.M = M2 at i2 i2f hM2 ⊢
  obtain ⟨l3, l3f⟩ := bload_sem I ⟨M2, s1.o⟩ hM2 (d := lgV1) (a := lgX) (x := x + 1) (by decide) i2
    (by omega)
  have hM3 := inv_sem I (P := .load lgV1 lgX) (s := ⟨M2, s1.o⟩) (by simp [WF, lgV1]) hM2
  generalize semXIR I (.load lgV1 lgX) ⟨M2, s1.o⟩ = s3 at l3 l3f hM3 ⊢
  have hX3 : rd s3.M lgX = toWord (x + 1) := (l3f _ (by decide)).trans i2
  have hb : ∀ i, i ≠ lgX → i ≠ lgV → i ≠ lgV1 → rd s3.M i = rd s.M i := fun i h1 h2 h3 =>
    (l3f _ h3).trans ((i2f _ h1).trans (l1f _ h2))
  obtain ⟨a1, a2, a3, a4⟩ := amm_run hM3 (r := lgX) (a := lgV) (b := lgV1) (q := lgE) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) hX3
  have hM4 : Inv (runPrims ([.op .add lgX lgX cOne] ++ mulBC lgV lgV lgE ++ mulBC lgV1 lgV1 lgE) s3.M) := by
    rw [runPrims_append, runPrims_append]
    exact mulBC_inv _ _ _ (by decide) (mulBC_inv _ _ _ (by decide)
      (inv_runPrims (by simp [Prim.dst, lgX]) hM3))
  rw [runPrims_append]
  generalize runPrims ([.op .add lgX lgX cOne] ++ mulBC lgV lgV lgE ++ mulBC lgV1 lgV1 lgE) s3.M = M4
    at a1 a2 a3 a4 hM4 ⊢
  have hs4 : 256 ≤ M4.size := hM4.1
  have hA : lgAc + 2 * c + 1 < 256 := by simp only [lgAc]; omega
  have x1 : rd (runPrims [.op .xor (lgAc + 2 * c) (lgAc + 2 * c) lgV,
      .op .xor (lgAc + 2 * c + 1) (lgAc + 2 * c + 1) lgV1] M4) (lgAc + 2 * c) =
      rd M4 (lgAc + 2 * c) ^^^ rd M4 lgV := by
    simp only [runPrims_cons, runPrims_nil, Prim.run]
    rw [rd_set_ne (by omega), rd_set_self (by omega), eval_xor]
  have x2 : rd (runPrims [.op .xor (lgAc + 2 * c) (lgAc + 2 * c) lgV,
      .op .xor (lgAc + 2 * c + 1) (lgAc + 2 * c + 1) lgV1] M4) (lgAc + 2 * c + 1) =
      rd M4 (lgAc + 2 * c + 1) ^^^ rd M4 lgV1 := by
    simp only [runPrims_cons, runPrims_nil, Prim.run]
    rw [rd_set_self (by rw [size_set]; omega), eval_xor, rd_set_ne (by omega),
      rd_set_ne (by simp only [lgAc, lgV1]; omega)]
  have xf : ∀ i, i ≠ lgAc + 2 * c → i ≠ lgAc + 2 * c + 1 →
      rd (runPrims [.op .xor (lgAc + 2 * c) (lgAc + 2 * c) lgV,
        .op .xor (lgAc + 2 * c + 1) (lgAc + 2 * c + 1) lgV1] M4) i = rd M4 i := fun i h1 h2 =>
    rd_runPrims_of_not_writes (by simp [Prim.dst]; exact ⟨Ne.symm h1, Ne.symm h2⟩) _
  have hAc : ∀ e < 2, rd M4 (lgAc + 2 * c + e) = rd s.M (lgAc + 2 * c + e) := fun e he => by
    rw [a4 _ (by simp only [lgAc, lgX]; omega) (by simp only [lgAc, lgV]; omega)
      (by simp only [lgAc, lgV1]; omega) (.inr (by simp only [lgAc]; omega)),
      hb _ (by simp only [lgAc, lgX]; omega) (by simp only [lgAc, lgV]; omega)
        (by simp only [lgAc, lgV1]; omega)]
  have hE : rd s3.M lgE = rd s.M lgE := hb _ (by decide) (by decide) (by decide)
  refine ⟨?_, ?_, fun i h1 h2 h3 h4 h5 h6 => ?_,
    inv_runPrims (fun p hp => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl <;> simp only [Prim.dst, lgAc] <;> omega) hM4⟩
  · rw [xf _ (by simp only [lgAc, lgX]; omega) (by simp only [lgAc, lgX]; omega), a1]
  · rw [rdF_mk, rdF_mk, rdF_mk, x1, x2, a2, a3, hE, l3f _ (by decide), i2f _ (by decide), l1, l3,
      i2f _ (by simp only [lgX]; omega), l1f _ (by simp only [lgV]; omega),
      show lgAc + 2 * c = lgAc + 2 * c + 0 from rfl, hAc 0 (by omega), hAc 1 (by omega)]
    show F.mk _ _ = F.mk _ _
    rw [wB_xor, wB_xor, mulBW_spec, mulBW_spec]
    exact congrArg₂ F.mk (congrArg (_ + ·) (mul_comm _ _)) (congrArg (_ + ·) (mul_comm _ _))
  · rw [xf _ h4 h5, a4 _ h1 h2 h3 h6, hb _ h1 h2 h3]

theorem wf_accRow (c : ℕ) : WF (accRow c) := by
  simp [accRow, WF, mulBC, redC, Prim.dst, lgV, lgV1, lgX, lgAc]
  constructor <;> omega

/-- **The `C` rows**: `acc_c += e · M[x + 2c]` for `c < C` (`C ≤ 16`), `lgX += 2C`. -/
theorem accIR_sem (I : Array Word) : ∀ (C : ℕ) (s : St), Inv s.M → ∀ {x : ℕ}, C ≤ 16 →
    rd s.M lgX = toWord x → regs ≤ x → x + 2 * C + 2 < 2 ^ 64 →
    rd (semXIR I (accIR C) s).M lgX = toWord (x + 2 * C) ∧
    (∀ c < C, rdF (semXIR I (accIR C) s).M (lgAc + 2 * c) =
      rdF s.M (lgAc + 2 * c) + F.smulBase (rdB s.M lgE) (rdF s.M (x + 2 * c))) ∧
    (∀ i, i ≠ lgX → i ≠ lgV → i ≠ lgV1 → (i < lgAc ∨ lgAc + 2 * C ≤ i) → (i < 5 ∨ 9 ≤ i) →
      rd (semXIR I (accIR C) s).M i = rd s.M i) ∧
    Inv (semXIR I (accIR C) s).M
  | 0, s, hM, x, _, hX, _, _ => by
    have e : semXIR I (accIR 0) s = s := by rw [accIR, semB, runPrims_nil]
    rw [e]
    exact ⟨by rw [Nat.mul_zero, Nat.add_zero]; exact hX, fun c hc => absurd hc (Nat.not_lt_zero _),
      fun _ _ _ _ _ _ => rfl, hM⟩
  | C + 1, s, hM, x, hC, hX, hx, hx2 => by
    obtain ⟨a1, a2, a3, hM1⟩ := accIR_sem I C s hM (by omega) hX hx (by omega)
    rw [accIR, semXIR_seq]
    generalize semXIR I (accIR C) s = s1 at a1 a2 a3 hM1 ⊢
    obtain ⟨b1, b2, b3, hM2⟩ := accRow_sem I s1 hM1 (c := C) (by omega) a1
      (by simp only [regs] at hx ⊢; omega) (by omega)
    have hH : ∀ i, regs ≤ i → rd s1.M i = rd s.M i := fun i hi => by
      simp only [regs] at hi
      exact a3 i (by simp only [lgX]; omega) (by simp only [lgV]; omega) (by simp only [lgV1]; omega)
        (.inr (by simp only [lgAc]; omega)) (.inr (by omega))
    have hE : rd s1.M lgE = rd s.M lgE := a3 _ (by decide) (by decide) (by decide) (.inl (by decide))
      (.inr (by decide))
    refine ⟨b1.trans (congrArg toWord (by omega)), fun c hc => ?_,
      fun i h1 h2 h3 h4 h5 => ?_, hM2⟩
    · have q0 : lgAc + 2 * c ≠ lgX ∧ lgAc + 2 * c ≠ lgV ∧ lgAc + 2 * c ≠ lgV1 ∧
          9 ≤ lgAc + 2 * c := by simp only [lgAc, lgX, lgV, lgV1]; omega
      have q1 : lgAc + 2 * c + 1 ≠ lgX ∧ lgAc + 2 * c + 1 ≠ lgV ∧ lgAc + 2 * c + 1 ≠ lgV1 ∧
          9 ≤ lgAc + 2 * c + 1 := by simp only [lgAc, lgX, lgV, lgV1]; omega
      rcases Nat.lt_succ_iff_lt_or_eq.1 hc with hc | rfl
      · obtain ⟨u1, u2, u3, u4⟩ := q0
        obtain ⟨v1, v2, v3, v4⟩ := q1
        rw [rdF_eq (b3 (lgAc + 2 * c) u1 u2 u3 (by omega) (by omega) (.inr u4))
          (b3 (lgAc + 2 * c + 1) v1 v2 v3 (by omega) (by omega) (.inr v4))]
        exact a2 c hc
      · obtain ⟨u1, u2, u3, u4⟩ := q0
        obtain ⟨v1, v2, v3, v4⟩ := q1
        simp only [regs] at hx
        rw [b2, rdB, hE, ← rdB, rdF_eq (hH (x + 2 * c) (by simp only [regs]; omega))
          (hH (x + 2 * c + 1) (by simp only [regs]; omega)),
          rdF_eq (a3 (lgAc + 2 * c) u1 u2 u3 (.inr (by omega)) (.inr u4))
            (a3 (lgAc + 2 * c + 1) v1 v2 v3 (.inr (by omega)) (.inr v4))]
    · rw [b3 i h1 h2 h3 (by omega) (by omega) h5, a3 i h1 h2 h3 (by omega) h5]

/-! ## The backward pass -/

/-- The backward step's pointer block: `lgA, lgB −= 1`, `lgY −= 2C`, `lgX := lgY`. -/
theorem bwd_ptr (M : Mem) (hM : Inv M) {a b y C : ℕ} (hA : rd M lgA = toWord (a + 1))
    (hB : rd M lgB = toWord (b + 1)) (hY : rd M lgY = toWord (y + 2 * C)) (hK : rd M lgK = toWord (2 * C))
    (ha : a + 1 < 2 ^ 64) (hb : b + 1 < 2 ^ 64) (hy : y + 2 * C < 2 ^ 64) :
    let M' := runPrims [.op .sub lgA lgA cOne, .op .sub lgB lgB cOne, .op .sub lgY lgY lgK,
      .op .or lgX lgY lgY] M
    rd M' lgA = toWord a ∧ rd M' lgB = toWord b ∧ rd M' lgY = toWord y ∧ rd M' lgX = toWord y ∧
    (∀ i, i ≠ lgA → i ≠ lgB → i ≠ lgY → i ≠ lgX → rd M' i = rd M i) ∧ Inv M' := by
  intro M'
  have hs : 256 ≤ M.size := hM.1
  have h1 : rd M cOne = toWord 1 := hM.2 0 (by decide)
  have hy' : rd (runPrims [.op .sub lgA lgA cOne, .op .sub lgB lgB cOne, .op .sub lgY lgY lgK] M) lgY =
      toWord y := by
    simp only [runPrims_cons, runPrims_nil, Prim.run]
    simp (disch := first | decide | (simp only [size_set, lgA, lgB, lgY]; omega)) only
      [rd_set_self, rd_set_ne]
    rw [hY, hK, sub_toWord hy (by omega), Nat.add_sub_cancel]
  have e := runPrims_append [.op .sub lgA lgA cOne, .op .sub lgB lgB cOne, .op .sub lgY lgY lgK]
    [.op .or lgX lgY lgY] M
  simp only [List.cons_append, List.nil_append] at e
  refine ⟨?_, ?_, ?_, ?_, fun i h1 h2 h3 h4 =>
    rd_runPrims_of_not_writes (by simp [Prim.dst]; exact ⟨Ne.symm h1, Ne.symm h2, Ne.symm h3, Ne.symm h4⟩) _,
    inv_runPrims (by simp [Prim.dst, lgA, lgB, lgY, lgX]) hM⟩
  · simp only [M', runPrims_cons, runPrims_nil, Prim.run]
    simp (disch := first | decide | (simp only [size_set, lgA, lgB, lgY, lgX]; omega)) only
      [rd_set_self, rd_set_ne]
    rw [hA, h1, sub_toWord ha (by omega), Nat.add_sub_cancel]
  · simp only [M', runPrims_cons, runPrims_nil, Prim.run]
    simp (disch := first | decide | (simp only [size_set, lgA, lgB, lgY, lgX]; omega)) only
      [rd_set_self, rd_set_ne]
    rw [hB, h1, sub_toWord hb (by omega), Nat.add_sub_cancel]
  · simp only [M', e]
    rw [rd_runPrims_of_not_writes (by simp [Prim.dst, lgX, lgY]), hy']
  · simp only [M', e]
    simp only [runPrims_cons (.op .or lgX lgY lgY), runPrims_nil, Prim.run]
    rw [rd_set_self (by simp only [size_runPrims, lgX]; omega), hy', or_self_eval]

/-- The backward step's products: `D := S ⊕ J`, `E *= Q`, `Q *= D`. -/
theorem bwd_mul (M : Mem) (hM : Inv M) :
    let M' := runPrims ([.op .xor lgD lgS lgJ] ++ mulBC lgE lgE lgQ ++ mulBC lgQ lgQ lgD) M
    rdB M' lgE = rdB M lgE * rdB M lgQ ∧ rdB M' lgQ = rdB M lgQ * wB (rd M lgS ^^^ rd M lgJ) ∧
    (∀ i, i ≠ lgD → i ≠ lgE → i ≠ lgQ → (i < 5 ∨ 9 ≤ i) → rd M' i = rd M i) ∧ Inv M' := by
  intro M'
  have hs : 256 ≤ M.size := hM.1
  have hI1 : Inv (runPrims [.op .xor lgD lgS lgJ] M) := inv_runPrims (by simp [Prim.dst, lgD]) hM
  have hI2 := mulBC_inv lgE lgE lgQ (by decide) hI1
  have d1 : rd (runPrims [.op .xor lgD lgS lgJ] M) lgD = rd M lgS ^^^ rd M lgJ := by
    simp only [runPrims_cons, runPrims_nil, Prim.run]
    rw [rd_set_self (by simp only [lgD]; omega), eval_xor]
  have d1f : ∀ i, i ≠ lgD → rd (runPrims [.op .xor lgD lgS lgJ] M) i = rd M i := fun i h =>
    rd_runPrims_of_not_writes (by simp [Prim.dst]; exact Ne.symm h) _
  have e : M' = runPrims (mulBC lgQ lgQ lgD) (runPrims (mulBC lgE lgE lgQ)
      (runPrims [.op .xor lgD lgS lgJ] M)) := by simp only [M', runPrims_append]
  rw [e]
  refine ⟨?_, ?_, fun i h1 h2 h3 h4 => ?_, mulBC_inv _ _ _ (by decide) hI2⟩
  · rw [rdB, mulBC_frame _ _ _ (by decide) (by decide), mulBC_run hI1 (by decide) (by decide)
      (by decide) (by decide), mulBW_spec, d1f _ (by decide), d1f _ (by decide)]; rfl
  · rw [rdB, mulBC_run hI2 (by decide) (by decide) (by decide) (by decide), mulBW_spec,
      mulBC_frame _ _ _ (by decide) (by decide), mulBC_frame _ _ _ (by decide) (by decide), d1,
      d1f _ (by decide)]; rfl
  · rw [mulBC_frame _ _ _ h4 h3, mulBC_frame _ _ _ h4 h2, d1f _ h1]

/-- **The backward step** (`t` from `k − 1` down): `lgA, lgB −= 1`, `lgY −= 2C`;
`acc_c += (M[b] · Q) · M[y + 2c]`, `Q *= S ⊕ M[a]`. -/
theorem bwdL_sem (I : Array Word) (s : St) (hM : Inv s.M) {C a b y : ℕ} (hC : C ≤ 16)
    (hA : rd s.M lgA = toWord (a + 1)) (hB : rd s.M lgB = toWord (b + 1))
    (hY : rd s.M lgY = toWord (y + 2 * C)) (hK : rd s.M lgK = toWord (2 * C))
    (ha : a + 1 < 2 ^ 64) (hb : b + 1 < 2 ^ 64) (ha0 : regs ≤ a) (hb0 : regs ≤ b) (hy : regs ≤ y)
    (hy2 : y + 2 * C + 2 < 2 ^ 64) :
    rd (semXIR I (bwdL C) s).M lgA = toWord a ∧ rd (semXIR I (bwdL C) s).M lgB = toWord b ∧
    rd (semXIR I (bwdL C) s).M lgY = toWord y ∧
    rdB (semXIR I (bwdL C) s).M lgQ = rdB s.M lgQ * wB (rd s.M lgS ^^^ rd s.M a) ∧
    (∀ c < C, rdF (semXIR I (bwdL C) s).M (lgAc + 2 * c) =
      rdF s.M (lgAc + 2 * c) + F.smulBase (rdB s.M b * rdB s.M lgQ) (rdF s.M (y + 2 * c))) ∧
    rd (semXIR I (bwdL C) s).M lgS = rd s.M lgS ∧ rd (semXIR I (bwdL C) s).M lgK = rd s.M lgK ∧
    (∀ i, regs ≤ i → rd (semXIR I (bwdL C) s).M i = rd s.M i) ∧
    Inv (semXIR I (bwdL C) s).M := by
  simp only [regs] at hy ha0 hb0
  simp only [bwdL, semXIR_seq, semB]
  obtain ⟨p1, p2, p3, p4, pf, hM1⟩ := bwd_ptr s.M hM hA hB hY hK ha hb (by omega)
  generalize runPrims [.op .sub lgA lgA cOne, .op .sub lgB lgB cOne, .op .sub lgY lgY lgK,
      .op .or lgX lgY lgY] s.M = M1 at p1 p2 p3 p4 pf hM1 ⊢
  have hH1 : ∀ i, regs ≤ i → rd M1 i = rd s.M i := fun i hi => pf i
    (by simp only [regs, lgA] at hi ⊢; omega) (by simp only [regs, lgB] at hi ⊢; omega)
    (by simp only [regs, lgY] at hi ⊢; omega) (by simp only [regs, lgX] at hi ⊢; omega)
  obtain ⟨l2, l2f⟩ := bload_sem I ⟨M1, s.o⟩ hM1 (d := lgJ) (a := lgA) (x := a) (by decide) p1 (by omega)
  have hM2 := inv_sem I (P := .load lgJ lgA) (s := ⟨M1, s.o⟩) (by simp [WF, lgJ]) hM1
  generalize semXIR I (.load lgJ lgA) ⟨M1, s.o⟩ = s2 at l2 l2f hM2 ⊢
  obtain ⟨l3, l3f⟩ := bload_sem I s2 hM2 (d := lgE) (a := lgB) (x := b)
    (by decide) ((l2f _ (by decide)).trans p2) (by omega)
  have hM3 := inv_sem I (P := .load lgE lgB) (s := s2) (by simp [WF, lgE]) hM2
  generalize semXIR I (.load lgE lgB) s2 = s3 at l3 l3f hM3 ⊢
  have r3 : ∀ i, i ≠ lgJ → i ≠ lgE → rd s3.M i = rd M1 i := fun i h1 h2 => (l3f _ h2).trans (l2f _ h1)
  obtain ⟨m1, m2, mf, hM4⟩ := bwd_mul s3.M hM3
  generalize runPrims ([.op .xor lgD lgS lgJ] ++ mulBC lgE lgE lgQ ++ mulBC lgQ lgQ lgD) s3.M = M4
    at m1 m2 mf hM4 ⊢
  have r4 : ∀ i, i ≠ lgJ → i ≠ lgE → i ≠ lgD → i ≠ lgQ → (i < 5 ∨ 9 ≤ i) → rd M4 i = rd M1 i :=
    fun i h1 h2 h3 h4 h5 => (mf i h3 h2 h4 h5).trans (r3 i h1 h2)
  obtain ⟨a1, a2, a3, hM5⟩ := accIR_sem I C ⟨M4, s3.o⟩ hM4 hC
    ((r4 _ (by decide) (by decide) (by decide) (by decide) (by decide)).trans p4)
    (by simp only [regs]; omega) (by omega)
  have q5 : ∀ i, i ≠ lgX → i ≠ lgV → i ≠ lgV1 → (i < lgAc ∨ lgAc + 2 * C ≤ i) → (i < 5 ∨ 9 ≤ i) →
      i ≠ lgJ → i ≠ lgE → i ≠ lgD → i ≠ lgQ →
      rd (semXIR I (accIR C) ⟨M4, s3.o⟩).M i = rd M1 i := fun i h1 h2 h3 h4 h5 h6 h7 h8 h9 =>
    (a3 i h1 h2 h3 h4 h5).trans (r4 i h6 h7 h8 h9 h5)
  have hQ3 : rd s3.M lgQ = rd s.M lgQ := (r3 _ (by decide) (by decide)).trans
    (pf _ (by decide) (by decide) (by decide) (by decide))
  have hS3 : rd s3.M lgS = rd s.M lgS := (r3 _ (by decide) (by decide)).trans
    (pf _ (by decide) (by decide) (by decide) (by decide))
  have hE3 : rd s3.M lgE = rd s.M b := by rw [l3, l2f _ (by simp only [lgJ]; omega), hH1 b (by
    simp only [regs]; omega)]
  have hJ3 : rd s3.M lgJ = rd s.M a := by
    rw [l3f _ (by decide), l2, hH1 a (by simp only [regs]; omega)]
  refine ⟨?_, ?_, ?_, ?_, fun c hc => ?_, ?_, ?_, fun i hi => ?_, hM5⟩
  · rw [q5 _ (by decide) (by decide) (by decide) (.inl (by decide)) (.inr (by decide)) (by decide)
      (by decide) (by decide) (by decide), p1]
  · rw [q5 _ (by decide) (by decide) (by decide) (.inl (by decide)) (.inr (by decide)) (by decide)
      (by decide) (by decide) (by decide), p2]
  · rw [q5 _ (by decide) (by decide) (by decide) (.inl (by decide)) (.inr (by decide)) (by decide)
      (by decide) (by decide) (by decide), p3]
  · rw [rdB, a3 _ (by decide) (by decide) (by decide) (.inl (by decide)) (.inr (by decide)), ← rdB, m2]
    unfold rdB
    rw [hQ3, hS3, hJ3]
  · rw [a2 c hc]
    have e1 : rdF M4 (lgAc + 2 * c) = rdF s.M (lgAc + 2 * c) := by
      have q0 : lgAc + 2 * c ≠ lgJ ∧ lgAc + 2 * c ≠ lgE ∧ lgAc + 2 * c ≠ lgD ∧ lgAc + 2 * c ≠ lgQ ∧
          lgAc + 2 * c + 1 ≠ lgJ ∧ lgAc + 2 * c + 1 ≠ lgE ∧ lgAc + 2 * c + 1 ≠ lgD ∧
          lgAc + 2 * c + 1 ≠ lgQ ∧ lgAc + 2 * c ≠ lgA ∧ lgAc + 2 * c ≠ lgB ∧ lgAc + 2 * c ≠ lgY ∧
          lgAc + 2 * c ≠ lgX ∧ lgAc + 2 * c + 1 ≠ lgA ∧ lgAc + 2 * c + 1 ≠ lgB ∧
          lgAc + 2 * c + 1 ≠ lgY ∧ lgAc + 2 * c + 1 ≠ lgX ∧ 9 ≤ lgAc + 2 * c := by
        simp only [lgAc, lgJ, lgE, lgD, lgQ, lgA, lgB, lgY, lgX]; omega
      obtain ⟨u1, u2, u3, u4, v1, v2, v3, v4, w1, w2, w3, w4, x1, x2, x3, x4, u5⟩ := q0
      exact rdF_eq ((r4 _ u1 u2 u3 u4 (.inr u5)).trans (pf _ w1 w2 w3 w4))
        ((r4 _ v1 v2 v3 v4 (.inr (by omega))).trans (pf _ x1 x2 x3 x4))
    have e2 : rdF M4 (y + 2 * c) = rdF s.M (y + 2 * c) := by
      refine rdF_eq ?_ ?_
      · rw [r4 _ (by simp only [lgJ]; omega) (by simp only [lgE]; omega) (by simp only [lgD]; omega)
          (by simp only [lgQ]; omega) (.inr (by omega)), hH1 _ (by simp only [regs]; omega)]
      · rw [r4 _ (by simp only [lgJ]; omega) (by simp only [lgE]; omega) (by simp only [lgD]; omega)
          (by simp only [lgQ]; omega) (.inr (by omega)), hH1 _ (by simp only [regs]; omega)]
    rw [e1, e2]
    show _ + F.smulBase (rdB M4 lgE) _ = _
    rw [m1]
    unfold rdB
    rw [hE3, hQ3]
  · rw [q5 _ (by decide) (by decide) (by decide) (.inl (by decide)) (.inr (by decide)) (by decide)
      (by decide) (by decide) (by decide), pf _ (by decide) (by decide) (by decide) (by decide)]
  · rw [q5 _ (by decide) (by decide) (by decide) (.inl (by decide)) (.inr (by decide)) (by decide)
      (by decide) (by decide) (by decide), pf _ (by decide) (by decide) (by decide) (by decide)]
  · simp only [regs] at hi
    rw [q5 i (by simp only [lgX]; omega) (by simp only [lgV]; omega) (by simp only [lgV1]; omega)
      (.inr (by simp only [lgAc]; omega)) (.inr (by omega)) (by simp only [lgJ]; omega)
      (by simp only [lgE]; omega) (by simp only [lgD]; omega) (by simp only [lgQ]; omega),
      hH1 i (by simp only [regs]; omega)]

theorem wf_bwdL (C : ℕ) : WF (bwdL C) := by
  simp only [bwdL, WF, wf_accIR C, and_true]
  simp [mulBC, redC, Prim.dst, lgA, lgB, lgY, lgX, lgJ, lgE, lgD, lgQ]

/-- **The backward pass**: from `lgA = jb + k`, `lgB = pb + k`, `lgY = yb + 2Ck`, `Q = 1` and zero
accumulators, `acc_c = Σ_{t<k} (M[pb + t] · Q_t) · Y_c[t]` with `Q_t = sufP J k s (t + 1)`. -/
theorem bwdLoop_sem (I : Array Word) (s : St) (hM : Inv s.M) {k C jb pb yb sv : ℕ} {Jl : List ℕ}
    (hk : k < 2 ^ 64) (hC : C ≤ 16) (hjb : regs ≤ jb) (hpb : regs ≤ pb) (hyb : regs ≤ yb)
    (hjb2 : jb + k < 2 ^ 64) (hpb2 : pb + k < 2 ^ 64) (hy2 : yb + 2 * C * k + 2 < 2 ^ 64)
    (hA : rd s.M lgA = toWord (jb + k)) (hB : rd s.M lgB = toWord (pb + k))
    (hY : rd s.M lgY = toWord (yb + 2 * C * k)) (hK : rd s.M lgK = toWord (2 * C))
    (hN : rd s.M lgN2 = toWord k) (hQ : rdB s.M lgQ = 1) (hS : rd s.M lgS = toWord sv)
    (h0 : ∀ c < C, rdF s.M (lgAc + 2 * c) = 0) (hJ : ∀ u < k, rd s.M (jb + u) = jw Jl u) :
    (∀ c < C, rdF (semXIR I (.loopK lgC2 lgN2 (toWord k) (bwdL C)) s).M (lgAc + 2 * c) =
      ∑ t ∈ range k, F.smulBase (rdB s.M (pb + t) * sufP Jl k sv (t + 1))
        (rdF s.M (yb + 2 * (C * t + c)))) ∧
    (∀ i, regs ≤ i → rd (semXIR I (.loopK lgC2 lgN2 (toWord k) (bwdL C)) s).M i = rd s.M i) ∧
    Inv (semXIR I (.loopK lgC2 lgN2 (toWord k) (bwdL C)) s).M := by
  simp only [regs] at hjb hpb hyb
  let P : ℕ → St → Prop := fun j st => Inv st.M ∧
    rd st.M lgA = toWord (jb + (k - j)) ∧ rd st.M lgB = toWord (pb + (k - j)) ∧
    rd st.M lgY = toWord (yb + 2 * C * (k - j)) ∧ rd st.M lgK = toWord (2 * C) ∧
    rd st.M lgS = toWord sv ∧ rdB st.M lgQ = sufP Jl k sv (k - j) ∧
    (∀ c < C, rdF st.M (lgAc + 2 * c) = ∑ t ∈ Ico (k - j) k,
      F.smulBase (rdB s.M (pb + t) * sufP Jl k sv (t + 1)) (rdF s.M (yb + 2 * (C * t + c)))) ∧
    (∀ i, regs ≤ i → rd st.M i = rd s.M i)
  have ef : ∀ i, i ≠ lgC2 → i ≠ cTmp → rd (entryK lgC2 lgN2 (toWord k) s.M) i = rd s.M i :=
    fun i a b => entryK_frame _ (Ne.symm a) (Ne.symm b)
  have h := loopK_run I (bwdL C) P s hM (by decide) (by decide) (by decide) hN hk
    ⟨inv_entryK hM (by decide), by rw [ef _ (by decide) (by decide), hA, Nat.sub_zero],
      by rw [ef _ (by decide) (by decide), hB, Nat.sub_zero],
      by rw [ef _ (by decide) (by decide), hY, Nat.sub_zero],
      by rw [ef _ (by decide) (by decide), hK], by rw [ef _ (by decide) (by decide), hS],
      by rw [rdB, ef _ (by decide) (by decide), ← rdB, hQ, Nat.sub_zero, sufP, Finset.Ico_self,
        Finset.prod_empty],
      fun c hc => by
        have q : lgAc + 2 * c ≠ lgC2 ∧ lgAc + 2 * c ≠ cTmp ∧ lgAc + 2 * c + 1 ≠ lgC2 ∧
            lgAc + 2 * c + 1 ≠ cTmp := by simp only [lgAc, lgC2, cTmp]; omega
        rw [rdF_eq (ef _ q.1 q.2.1) (ef _ q.2.2.1 q.2.2.2), h0 c hc, Nat.sub_zero, Finset.Ico_self,
          Finset.sum_empty],
      fun i hi => ef i (by simp only [regs, lgC2] at hi ⊢; omega)
        (by simp only [regs, cTmp] at hi ⊢; omega)⟩ ?_
  · refine ⟨fun c hc => ?_, h.2.2.2.2.2.2.2.2, h.1⟩
    rw [h.2.2.2.2.2.2.2.1 c hc, Nat.sub_self, ← Finset.range_eq_Ico]
  rintro j st hj ⟨hI, hA', hB', hY', hK', hS', hQ', hV, hH⟩
  obtain ⟨t, ht⟩ : ∃ t, k - j = t + 1 := ⟨k - j - 1, by omega⟩
  rw [ht] at hA' hB' hY' hQ' hV
  have htk : t < k := by omega
  have e1 : k - (j + 1) = t := by omega
  dsimp only [P]
  rw [e1]
  obtain ⟨b1, b2, b3, b4, b5, b6, b7, b8, hI2⟩ := bwdL_sem I st hI (C := C) (a := jb + t) (b := pb + t)
    (y := yb + 2 * C * t) hC hA' hB' (hY'.trans (congrArg toWord (by ring))) hK' (by omega)
    (by omega) (by simp only [regs]; omega) (by simp only [regs]; omega) (by simp only [regs]; omega)
    (by have : 2 * C * t + 2 * C ≤ 2 * C * k := by rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left _ htk
        omega)
  have hd : ∀ i, i ≠ lgC2 → rd (decS lgC2 (semXIR I (bwdL C) st)).M i = rd (semXIR I (bwdL C) st).M i :=
    fun i hi => rd_decS (Ne.symm hi) _
  refine ⟨inv_decS hI2 (by decide), by rw [hd _ (by decide), b1], by rw [hd _ (by decide), b2],
    by rw [hd _ (by decide), b3], by rw [hd _ (by decide), b7, hK'],
    by rw [hd _ (by decide), b6, hS'], ?_, fun c hc => ?_, fun i hi => ?_⟩
  · rw [rdB, hd _ (by decide), ← rdB, b4, hQ', hS', hH _ (by simp only [regs]; omega), hJ t htk, sufP,
      sufP, Finset.prod_eq_prod_Ico_succ_bot htk, mul_comm]; rfl
  · have q : lgAc + 2 * c ≠ lgC2 ∧ lgAc + 2 * c + 1 ≠ lgC2 := by simp only [lgAc, lgC2]; omega
    rw [rdF_eq (hd _ q.1) (hd _ q.2), b5 c (by omega), hV c hc, Finset.sum_eq_sum_Ico_succ_bot htk,
      add_comm, rdF_eq (hH _ (by simp only [regs]; omega)) (hH _ (by simp only [regs]; omega)), hQ',
      show yb + 2 * C * t + 2 * c = yb + 2 * (C * t + c) by ring,
      rdB, hH _ (by simp only [regs]; omega), ← rdB]
  · rw [hd _ (by simp only [regs, lgC2] at hi ⊢; omega), b8 i hi, hH i hi]

/-! ## The outputs -/

/-- **Row `c`'s output**: `M[o], M[o + 1] := acc_c`, `lgO += 2k`. -/
theorem stRow_sem (I : Array Word) (s : St) (hM : Inv s.M) {c o k : ℕ} (hc : c < 16)
    (hO : rd s.M lgO = toWord o) (hK : rd s.M lgK = toWord (2 * k)) (ho : regs ≤ o)
    (ho2 : o + 2 * k + 2 < 2 ^ 64) (hos : o + 1 < s.M.size) :
    rd (semXIR I (stRow c) s).M lgO = toWord (o + 2 * k) ∧
    rd (semXIR I (stRow c) s).M o = rd s.M (lgAc + 2 * c) ∧
    rd (semXIR I (stRow c) s).M (o + 1) = rd s.M (lgAc + 2 * c + 1) ∧
    (∀ i, i ≠ lgO → i ≠ cTmp → i ≠ o → i ≠ o + 1 → rd (semXIR I (stRow c) s).M i = rd s.M i) ∧
    Inv (semXIR I (stRow c) s).M := by
  simp only [regs] at ho
  have hA : lgAc + 2 * c + 1 < 256 := by simp only [lgAc]; omega
  simp only [stRow, semXIR_seq, semB]
  have a1 := fun i (hi : i ≠ cTmp) => st_rd I s hM hO (by simp only [regs]; omega) (by omega)
    (by omega) (by decide) (by simp only [lgAc, cTmp]; omega) (v := lgAc + 2 * c) hi
  have hM1 := inv_sem I (P := .store lgO (lgAc + 2 * c)) (by simp [WF, lgO, cTmp]) hM
  have z1 := size_sem I (.store lgO (lgAc + 2 * c)) s
  generalize semXIR I (.store lgO (lgAc + 2 * c)) s = s1 at a1 hM1 z1 ⊢
  obtain ⟨i2, i2f⟩ := incr_sem s1.M hM1 (r := lgO) (x := o) (by decide) (by decide)
    ((a1 _ (by decide)).trans (by rw [if_neg (by simp only [lgO]; omega), hO]))
  have hM2 : Inv (runPrims [.op .add lgO lgO cOne] s1.M) := inv_runPrims (by simp [Prim.dst, lgO]) hM1
  have z2 := size_runPrims [.op .add lgO lgO cOne] s1.M
  generalize runPrims [.op .add lgO lgO cOne] s1.M = M2 at i2 i2f hM2 z2 ⊢
  have a3 := fun i (hi : i ≠ cTmp) => st_rd I ⟨M2, s1.o⟩ hM2 i2 (by simp only [regs]; omega)
    (by omega) (by show o + 1 < M2.size; omega) (by decide) (by simp only [lgAc, cTmp]; omega)
    (v := lgAc + 2 * c + 1) hi
  have hM3 := inv_sem I (P := .store lgO (lgAc + 2 * c + 1)) (s := ⟨M2, s1.o⟩) (by simp [WF, lgO, cTmp]) hM2
  generalize semXIR I (.store lgO (lgAc + 2 * c + 1)) ⟨M2, s1.o⟩ = s3 at a3 hM3 ⊢
  have hs3 : 256 ≤ s3.M.size := hM3.1
  have hO3 : rd s3.M lgO = toWord (o + 1) := by rw [a3 _ (by decide), if_neg (by simp only [lgO]; omega), i2]
  have hK3 : rd s3.M lgK = toWord (2 * k) := by
    rw [a3 _ (by decide), if_neg (by simp only [lgK]; omega), i2f _ (by decide), a1 _ (by decide),
      if_neg (by simp only [lgK]; omega), hK]
  have h1 : rd s3.M cOne = toWord 1 := hM3.2 0 (by decide)
  have hf : ∀ i, i ≠ lgO → rd (runPrims [.op .sub lgO lgO cOne, .op .add lgO lgO lgK] s3.M) i = rd s3.M i :=
    fun i h => rd_runPrims_of_not_writes (by simp [Prim.dst]; exact Ne.symm h) _
  refine ⟨?_, ?_, ?_, fun i h1 h2 h3 h4 => ?_, inv_runPrims (by simp [Prim.dst, lgO]) hM3⟩
  · simp only [runPrims_cons, runPrims_nil, Prim.run]
    simp (disch := first | decide | (simp only [size_set, lgO]; omega)) only [rd_set_self, rd_set_ne]
    rw [hO3, h1, sub_toWord (by omega) (by omega), Nat.add_sub_cancel, hK3, add_toWord]
  · rw [hf _ (by simp only [lgO]; omega), a3 _ (by simp only [cTmp]; omega), if_neg (by omega),
      i2f _ (by simp only [lgO]; omega), a1 _ (by simp only [cTmp]; omega), if_pos rfl]
  · rw [hf _ (by simp only [lgO]; omega), a3 _ (by simp only [cTmp]; omega), if_pos rfl,
      i2f _ (by simp only [lgO, lgAc]; omega), a1 _ (by simp only [lgAc, cTmp]; omega),
      if_neg (by simp only [lgAc]; omega)]
  · rw [hf _ h1, a3 _ h2, if_neg h4, i2f _ h1, a1 _ h2, if_neg h3]

theorem wf_stRow (c : ℕ) : WF (stRow c) := by simp [stRow, WF, Prim.dst, lgO, cTmp]

/-- **The `C` outputs**: row `c`'s accumulator at `o + 2kc` (`k ≥ 1`, `C ≤ 16`), `lgO += 2kC`;
the heap outside those cells is kept. -/
theorem stAcc_sem (I : Array Word) : ∀ (C : ℕ) (s : St), Inv s.M → ∀ {o k : ℕ}, C ≤ 16 → 1 ≤ k →
    rd s.M lgO = toWord o → rd s.M lgK = toWord (2 * k) → regs ≤ o → o + 2 * k * C + 2 < 2 ^ 64 →
    o + 2 * k * C ≤ s.M.size →
    rd (semXIR I (stAcc C) s).M lgO = toWord (o + 2 * k * C) ∧
    (∀ c < C, rd (semXIR I (stAcc C) s).M (o + 2 * k * c) = rd s.M (lgAc + 2 * c) ∧
      rd (semXIR I (stAcc C) s).M (o + 2 * k * c + 1) = rd s.M (lgAc + 2 * c + 1)) ∧
    (∀ i, regs ≤ i → (∀ c < C, i ≠ o + 2 * k * c ∧ i ≠ o + 2 * k * c + 1) →
      rd (semXIR I (stAcc C) s).M i = rd s.M i) ∧
    Inv (semXIR I (stAcc C) s).M
  | 0, s, hM, o, k, _, _, hO, _, _, _, _ => by
    have e : semXIR I (stAcc 0) s = s := by rw [stAcc, semB, runPrims_nil]
    rw [e]
    exact ⟨by rw [Nat.mul_zero, Nat.add_zero]; exact hO, fun c hc => absurd hc (Nat.not_lt_zero _),
      fun _ _ _ => rfl, hM⟩
  | C + 1, s, hM, o, k, hC, hk, hO, hK, ho, ho2, hos => by
    have hkC : 2 * k * (C + 1) = 2 * k * C + 2 * k := Nat.mul_succ _ _
    obtain ⟨a1, a2, a3, hM1⟩ := stAcc_sem I C s hM (by omega) hk hO hK ho (by omega) (by omega)
    rw [stAcc, semXIR_seq]
    have r1 : ∀ i, i < regs → i ≠ lgO → i ≠ cTmp → rd (semXIR I (stAcc C) s).M i = rd s.M i :=
      fun i hi h1 h2 => frame I _ s ((wf_stAcc C).2 trivial) hM i hi
        (fun h => (nw_stAcc i h2 h1 C).1 h)
    have z1 := size_sem I (stAcc C) s
    generalize semXIR I (stAcc C) s = s1 at a1 a2 a3 hM1 r1 z1 ⊢
    obtain ⟨b1, b2, b3, b4, hM2⟩ := stRow_sem I s1 hM1 (c := C) (o := o + 2 * k * C) (k := k)
      (by omega) a1 ((r1 _ (by decide) (by decide) (by decide)).trans hK) (by simp only [regs] at ho ⊢; omega)
      (by omega) (by omega)
    have q : ∀ c < C + 1, lgAc + 2 * c ≠ lgO ∧ lgAc + 2 * c ≠ cTmp ∧ lgAc + 2 * c + 1 ≠ lgO ∧
        lgAc + 2 * c + 1 ≠ cTmp ∧ lgAc + 2 * c + 1 < regs := fun c hc => by
      simp only [lgAc, lgO, cTmp, regs]; omega
    simp only [regs] at ho
    refine ⟨b1.trans (congrArg toWord (by rw [Nat.mul_succ]; omega)), fun c hc => ?_,
      fun i hi hne => ?_, hM2⟩
    · rcases Nat.lt_succ_iff_lt_or_eq.1 hc with hc' | rfl
      · have hlt : 2 * k * c + 2 ≤ 2 * k * C := by
          have := Nat.mul_le_mul_left (2 * k) (show c + 1 ≤ C by omega); rw [Nat.mul_succ] at this; omega
        rw [b4 _ (by simp only [lgO]; omega) (by simp only [cTmp]; omega) (by omega) (by omega),
          b4 _ (by simp only [lgO]; omega) (by simp only [cTmp]; omega) (by omega) (by omega)]
        exact a2 c hc'
      · obtain ⟨q1, q2, q3, q4, q5⟩ := q c hc
        rw [b2, b3, r1 _ (by omega) q1 q2, r1 _ q5 q3 q4]; exact ⟨rfl, rfl⟩
    · obtain ⟨n1, n2⟩ := hne C (by omega)
      rw [b4 i (by simp only [regs, lgO] at hi ⊢; omega) (by simp only [regs, cTmp] at hi ⊢; omega) n1 n2,
        a3 i hi fun c hc => hne c (by omega)]

/-! ## One target -/

theorem rd_zeros (M : Mem) (hs : regs ≤ M.size) : ∀ (n i : ℕ), lgAc + n ≤ regs →
    rd (runPrims ((List.range n).map fun j => .const (lgAc + j) 0) M) i =
      if lgAc ≤ i ∧ i < lgAc + n then 0 else rd M i
  | 0, i, _ => by simp [runPrims]
  | n + 1, i, hn => by
    rw [List.range_succ, List.map_append, runPrims_append]
    simp only [List.map_cons, List.map_nil, runPrims_cons, runPrims_nil, Prim.run, rd_set, size_runPrims]
    rw [rd_zeros M hs n i (by omega)]
    by_cases h : lgAc + n = i
    · rw [if_pos ⟨h, by simp only [regs] at hs hn; omega⟩, if_pos (by omega)]
    · rw [if_neg (fun e => h e.1)]
      by_cases h2 : lgAc ≤ i ∧ i < lgAc + n
      · rw [if_pos h2, if_pos (by omega)]
      · rw [if_neg h2, if_neg (by omega)]

theorem wf_fwdLoop (k : ℕ) : WF (.loopK lgC2 lgN2 (toWord k) fwdL) :=
  ⟨⟨by decide, by decide, by decide⟩, by decide, by
    simp [fwdL, Writes, mulBC, redC, Prim.dst, lgJ, lgD, lgA, lgB, lgP, lgC2, cTmp], wf_fwdL⟩

theorem wf_bwdLoop (k C : ℕ) : WF (.loopK lgC2 lgN2 (toWord k) (bwdL C)) :=
  ⟨⟨by decide, by decide, by decide⟩, by decide, by
    simp [bwdL, Writes, mulBC, redC, Prim.dst, lgJ, lgD, lgA, lgB, lgY, lgX, lgE, lgQ, lgC2,
      nw_accIR 177 (by decide) (by decide) (by decide) (by decide) (by decide)], wf_bwdL C⟩

/-- Registers `lgS` (174), `lgK` (173) and `lgC1`, `lgN1` (175, 176) survive the backward pass. -/
theorem nw_bwdLoop (k C : ℕ) {i : ℕ} (h1 : 173 ≤ i) (h2 : i ≤ 176) :
    ¬ Writes (.loopK lgC2 lgN2 (toWord k) (bwdL C)) i := by
  have := nw_accIR i (by omega) (by simp only [lgAc]; omega) (by simp only [lgV]; omega)
    (by simp only [lgV1]; omega) (by simp only [lgX]; omega) C
  intro h
  simp [Writes, bwdL, mulBC, redC, Prim.dst, this] at h
  simp only [lgJ, lgD, lgA, lgB, lgY, lgX, lgE, lgQ, lgC2, cTmp] at h
  omega

theorem nw_fwdLoop (k : ℕ) {i : ℕ} (h1 : 173 ≤ i) (h2 : i ≤ 176) :
    ¬ Writes (.loopK lgC2 lgN2 (toWord k) fwdL) i := by
  intro h
  simp [Writes, fwdL, mulBC, redC, Prim.dst] at h
  simp only [lgJ, lgD, lgA, lgB, lgP, lgC2, cTmp] at h
  omega

/-- **One target `s`**: output row `c` at `ob + 2s + 2kc` is
`Σ_{t<k} (P_t · Q_t) · Y_c[t]`; `lgS += 1`; the heap outside the prefix table and these outputs is
kept. -/
theorem tgBody_sem (I : Array Word) (s : St) (hM : Inv s.M) {k C jb pb yb ob sv : ℕ} {Jl : List ℕ}
    (hk1 : 1 ≤ k) (hk : k < 2 ^ 64) (hC : C ≤ 16) (hsv : sv < k) (hjb : regs ≤ jb)
    (hjp : jb + k ≤ pb) (hpy : pb + k ≤ yb) (hyo : yb + 2 * C * k ≤ ob)
    (hos : ob + 2 * k * (C + 1) ≤ s.M.size) (ho2 : ob + 2 * k * (C + 1) + 2 < 2 ^ 64)
    (hS : rd s.M lgS = toWord sv) (hJ : ∀ u < k, rd s.M (jb + u) = jw Jl u) :
    (∀ c < C, rdF (semXIR I (tgBody k C jb pb yb ob) s).M (ob + 2 * sv + 2 * k * c) =
      ∑ t ∈ range k, F.smulBase (preP Jl sv t * sufP Jl k sv (t + 1))
        (rdF s.M (yb + 2 * (C * t + c)))) ∧
    rd (semXIR I (tgBody k C jb pb yb ob) s).M lgS = toWord (sv + 1) ∧
    (∀ i, regs ≤ i → (i < pb ∨ pb + k ≤ i) →
      (∀ c < C, i ≠ ob + 2 * sv + 2 * k * c ∧ i ≠ ob + 2 * sv + 2 * k * c + 1) →
      rd (semXIR I (tgBody k C jb pb yb ob) s).M i = rd s.M i) ∧
    Inv (semXIR I (tgBody k C jb pb yb ob) s).M := by
  have hs : 256 ≤ s.M.size := hM.1
  have hkC : 2 * k * (C + 1) = 2 * k * C + 2 * k := Nat.mul_succ _ _
  have hCk : 2 * C * k = 2 * k * C := by ring
  simp only [regs] at hjb
  simp only [tgBody, semXIR_seq, semB]
  -- the pointers of the forward pass
  have c1 : rd (runPrims [.const lgP 1, .const lgA (toWord jb), .const lgB (toWord pb),
        .const lgN2 (toWord k)] s.M) lgP = 1 ∧
      rd (runPrims [.const lgP 1, .const lgA (toWord jb), .const lgB (toWord pb),
        .const lgN2 (toWord k)] s.M) lgA = toWord jb ∧
      rd (runPrims [.const lgP 1, .const lgA (toWord jb), .const lgB (toWord pb),
        .const lgN2 (toWord k)] s.M) lgB = toWord pb ∧
      rd (runPrims [.const lgP 1, .const lgA (toWord jb), .const lgB (toWord pb),
        .const lgN2 (toWord k)] s.M) lgN2 = toWord k := by
    simp only [runPrims_cons, runPrims_nil, Prim.run]
    refine ⟨?_, ?_, ?_, ?_⟩ <;>
    simp (disch := first | decide | (simp only [size_set, lgP, lgA, lgB, lgN2]; omega)) only
      [rd_set_self, rd_set_ne]
  have c1f : ∀ i, i ≠ lgP → i ≠ lgA → i ≠ lgB → i ≠ lgN2 →
      rd (runPrims [.const lgP 1, .const lgA (toWord jb), .const lgB (toWord pb),
        .const lgN2 (toWord k)] s.M) i = rd s.M i := fun i a b c d =>
    rd_runPrims_of_not_writes (by simp [Prim.dst]; exact ⟨Ne.symm a, Ne.symm b, Ne.symm c, Ne.symm d⟩) _
  have hM1 : Inv (runPrims [.const lgP 1, .const lgA (toWord jb), .const lgB (toWord pb),
      .const lgN2 (toWord k)] s.M) := inv_runPrims (by simp [Prim.dst, lgP, lgA, lgB, lgN2]) hM
  have z1 := size_runPrims [.const lgP 1, .const lgA (toWord jb), .const lgB (toWord pb),
      .const lgN2 (toWord k)] s.M
  generalize runPrims [.const lgP 1, .const lgA (toWord jb), .const lgB (toWord pb),
      .const lgN2 (toWord k)] s.M = M1 at c1 c1f hM1 z1 ⊢
  have H1 : ∀ i, regs ≤ i → rd M1 i = rd s.M i := fun i hi => by
    simp only [regs] at hi
    exact c1f i (by simp only [lgP]; omega) (by simp only [lgA]; omega) (by simp only [lgB]; omega)
      (by simp only [lgN2]; omega)
  -- the forward pass
  have hP1 : rdB M1 lgP = 1 := by rw [rdB, c1.1]; rfl
  have hS1 : rd M1 lgS = toWord sv := by rw [c1f _ (by decide) (by decide) (by decide) (by decide)]; exact hS
  have hJ1 : ∀ u < k, rd M1 (jb + u) = jw Jl u := fun u hu => by
    rw [H1 _ (by simp only [regs]; omega)]; exact hJ u hu
  obtain ⟨f1, f2, f3, f4, hM2⟩ := fwdLoop_sem I ⟨M1, s.o⟩ hM1 (Jl := Jl) (sv := sv) hk
    (by simp only [regs]; omega) hjp (by omega) (by show _ ≤ M1.size; omega) c1.2.1 c1.2.2.1 c1.2.2.2
    hP1 hS1 hJ1
  have r2 : ∀ i, 173 ≤ i → i ≤ 176 →
      rd (semXIR I (.loopK lgC2 lgN2 (toWord k) fwdL) ⟨M1, s.o⟩).M i = rd M1 i := fun i h1 h2 =>
    frame I _ _ (wf_fwdLoop k) hM1 i (by simp only [regs]; omega) (nw_fwdLoop k h1 h2)
  have z2 := size_sem I (.loopK lgC2 lgN2 (toWord k) fwdL) ⟨M1, s.o⟩
  dsimp only at f1 f2 f3 f4 z2
  generalize semXIR I (.loopK lgC2 lgN2 (toWord k) fwdL) ⟨M1, s.o⟩ = s2 at f1 f2 f3 f4 hM2 r2 z2 ⊢
  -- the constants and the zero accumulators
  have hs2 : 256 ≤ s2.M.size := hM2.1
  have c3 : rdB (runPrims ([.const lgQ 1, .const lgY (toWord (yb + 2 * C * k)), .const lgK (toWord (2 * C)),
        .const lgN2 (toWord k)] ++ zeroPs C) s2.M) lgQ = 1 ∧
      rd (runPrims ([.const lgQ 1, .const lgY (toWord (yb + 2 * C * k)), .const lgK (toWord (2 * C)),
        .const lgN2 (toWord k)] ++ zeroPs C) s2.M) lgY = toWord (yb + 2 * C * k) ∧
      rd (runPrims ([.const lgQ 1, .const lgY (toWord (yb + 2 * C * k)), .const lgK (toWord (2 * C)),
        .const lgN2 (toWord k)] ++ zeroPs C) s2.M) lgK = toWord (2 * C) ∧
      rd (runPrims ([.const lgQ 1, .const lgY (toWord (yb + 2 * C * k)), .const lgK (toWord (2 * C)),
        .const lgN2 (toWord k)] ++ zeroPs C) s2.M) lgN2 = toWord k ∧
      (∀ c < C, rdF (runPrims ([.const lgQ 1, .const lgY (toWord (yb + 2 * C * k)),
        .const lgK (toWord (2 * C)), .const lgN2 (toWord k)] ++ zeroPs C) s2.M) (lgAc + 2 * c) = 0) ∧
      (∀ i, i ≠ lgQ → i ≠ lgY → i ≠ lgK → i ≠ lgN2 → (i < lgAc ∨ lgAc + 2 * C ≤ i) →
        rd (runPrims ([.const lgQ 1, .const lgY (toWord (yb + 2 * C * k)), .const lgK (toWord (2 * C)),
          .const lgN2 (toWord k)] ++ zeroPs C) s2.M) i = rd s2.M i) := by
    rw [runPrims_append]
    have hz := rd_zeros (runPrims [.const lgQ 1, .const lgY (toWord (yb + 2 * C * k)),
      .const lgK (toWord (2 * C)), .const lgN2 (toWord k)] s2.M) (by simp only [size_runPrims, regs]; omega)
      (2 * C)
    have hf : ∀ i, i ≠ lgQ → i ≠ lgY → i ≠ lgK → i ≠ lgN2 → rd (runPrims [.const lgQ 1,
        .const lgY (toWord (yb + 2 * C * k)), .const lgK (toWord (2 * C)), .const lgN2 (toWord k)]
        s2.M) i = rd s2.M i := fun i a b c d =>
      rd_runPrims_of_not_writes (by simp [Prim.dst]; exact ⟨Ne.symm a, Ne.symm b, Ne.symm c, Ne.symm d⟩) _
    have hA : lgAc + 2 * C ≤ regs := by simp only [lgAc, regs]; omega
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [rdB, zeroPs, hz _ hA, if_neg (by simp only [lgQ, lgAc]; omega)]
      simp only [runPrims_cons, runPrims_nil, Prim.run]
      simp (disch := first | decide | (simp only [size_set, lgQ, lgY, lgK, lgN2]; omega)) only
        [rd_set_self, rd_set_ne]
      rfl
    · rw [zeroPs, hz _ hA, if_neg (by simp only [lgY, lgAc]; omega)]
      simp only [runPrims_cons, runPrims_nil, Prim.run]
      simp (disch := first | decide | (simp only [size_set, lgQ, lgY, lgK, lgN2]; omega)) only
        [rd_set_self, rd_set_ne]
    · rw [zeroPs, hz _ hA, if_neg (by simp only [lgK, lgAc]; omega)]
      simp only [runPrims_cons, runPrims_nil, Prim.run]
      simp (disch := first | decide | (simp only [size_set, lgQ, lgY, lgK, lgN2]; omega)) only
        [rd_set_self, rd_set_ne]
    · rw [zeroPs, hz _ hA, if_neg (by simp only [lgN2, lgAc]; omega)]
      simp only [runPrims_cons, runPrims_nil, Prim.run]
      simp (disch := first | decide | (simp only [size_set, lgQ, lgY, lgK, lgN2]; omega)) only
        [rd_set_self]
    · intro c hc
      rw [rdF_mk, zeroPs, hz _ hA, hz _ hA, if_pos (by omega), if_pos (by omega)]; rfl
    · intro i h1 h2 h3 h4 h5
      rw [zeroPs, hz _ hA, if_neg (by omega), hf i h1 h2 h3 h4]
  obtain ⟨d1, d2, d3, d4, d5, d6⟩ := c3
  have hM3 : Inv (runPrims ([.const lgQ 1, .const lgY (toWord (yb + 2 * C * k)),
      .const lgK (toWord (2 * C)), .const lgN2 (toWord k)] ++ zeroPs C) s2.M) := by
    refine inv_runPrims (fun p hp => ?_) hM2
    simp only [zeroPs, List.mem_append, List.mem_cons, List.mem_map, List.mem_range, List.not_mem_nil,
      or_false] at hp
    rcases hp with (rfl | rfl | rfl | rfl) | ⟨j, -, rfl⟩ <;> simp only [Prim.dst, lgQ, lgY, lgK, lgN2, lgAc] <;>
      omega
  have z3 := size_runPrims ([.const lgQ 1, .const lgY (toWord (yb + 2 * C * k)),
      .const lgK (toWord (2 * C)), .const lgN2 (toWord k)] ++ zeroPs C) s2.M
  generalize runPrims ([.const lgQ 1, .const lgY (toWord (yb + 2 * C * k)), .const lgK (toWord (2 * C)),
      .const lgN2 (toWord k)] ++ zeroPs C) s2.M = M3 at d1 d2 d3 d4 d5 d6 hM3 z3 ⊢
  have H3 : ∀ i, regs ≤ i → rd M3 i = rd s2.M i := fun i hi => by
    simp only [regs] at hi
    exact d6 i (by simp only [lgQ]; omega) (by simp only [lgY]; omega) (by simp only [lgK]; omega)
      (by simp only [lgN2]; omega) (.inr (by simp only [lgAc]; omega))
  have hS3 : rd M3 lgS = toWord sv := by
    rw [d6 _ (by decide) (by decide) (by decide) (by decide) (.inl (by decide)), r2 _ (by decide) (by decide),
      c1f _ (by decide) (by decide) (by decide) (by decide), hS]
  -- the backward pass
  obtain ⟨g1, g2, hM4⟩ := bwdLoop_sem I ⟨M3, s2.o⟩ hM3 (Jl := Jl) (sv := sv) (jb := jb) (pb := pb)
    (yb := yb) hk hC (by simp only [regs]; omega) (by simp only [regs]; omega) (by simp only [regs]; omega)
    (by omega) (by omega) (by omega)
    (by rw [d6 _ (by decide) (by decide) (by decide) (by decide) (.inl (by decide))]; exact f1)
    (by rw [d6 _ (by decide) (by decide) (by decide) (by decide) (.inl (by decide))]; exact f2)
    d2 d3 d4 d1 hS3 d5
    (fun u hu => by
      show rd M3 _ = _
      rw [H3 _ (by simp only [regs]; omega), f4 _ (by simp only [regs]; omega) (.inl (by omega)),
        H1 _ (by simp only [regs]; omega), hJ u hu])
  have r4 : ∀ i, 173 ≤ i → i ≤ 176 →
      rd (semXIR I (.loopK lgC2 lgN2 (toWord k) (bwdL C)) ⟨M3, s2.o⟩).M i = rd M3 i := fun i h1 h2 =>
    frame I _ _ (wf_bwdLoop k C) hM3 i (by simp only [regs]; omega) (nw_bwdLoop k C h1 h2)
  have z4 : (semXIR I (.loopK lgC2 lgN2 (toWord k) (bwdL C)) ⟨M3, s2.o⟩).M.size = M3.size :=
    size_sem ..
  dsimp only at g1 g2
  generalize semXIR I (.loopK lgC2 lgN2 (toWord k) (bwdL C)) ⟨M3, s2.o⟩ = s4 at g1 g2 hM4 r4 z4 ⊢
  have hS4 : rd s4.M lgS = toWord sv := (r4 _ (by decide) (by decide)).trans hS3
  -- the output pointer
  have hs4 : 256 ≤ s4.M.size := hM4.1
  have c5 : rd (runPrims [.const lgK (toWord (2 * k)), .const lgO (toWord ob), .op .add lgO lgO lgS,
        .op .add lgO lgO lgS] s4.M) lgO = toWord (ob + 2 * sv) ∧
      rd (runPrims [.const lgK (toWord (2 * k)), .const lgO (toWord ob), .op .add lgO lgO lgS,
        .op .add lgO lgO lgS] s4.M) lgK = toWord (2 * k) := by
    simp only [runPrims_cons, runPrims_nil, Prim.run]
    refine ⟨?_, ?_⟩ <;>
    simp (disch := first | decide | (simp only [size_set, lgK, lgO, lgS]; omega)) only
      [rd_set_self, rd_set_ne]
    rw [hS4, add_toWord, add_toWord]; exact congrArg toWord (by omega)
  have c5f : ∀ i, i ≠ lgK → i ≠ lgO → rd (runPrims [.const lgK (toWord (2 * k)), .const lgO (toWord ob),
      .op .add lgO lgO lgS, .op .add lgO lgO lgS] s4.M) i = rd s4.M i := fun i a b =>
    rd_runPrims_of_not_writes (by simp [Prim.dst]; exact ⟨Ne.symm a, Ne.symm b⟩) _
  have hM5 : Inv (runPrims [.const lgK (toWord (2 * k)), .const lgO (toWord ob), .op .add lgO lgO lgS,
      .op .add lgO lgO lgS] s4.M) := inv_runPrims (by simp [Prim.dst, lgK, lgO]) hM4
  have z5 := size_runPrims [.const lgK (toWord (2 * k)), .const lgO (toWord ob), .op .add lgO lgO lgS,
      .op .add lgO lgO lgS] s4.M
  generalize runPrims [.const lgK (toWord (2 * k)), .const lgO (toWord ob), .op .add lgO lgO lgS,
      .op .add lgO lgO lgS] s4.M = M5 at c5 c5f hM5 z5 ⊢
  have sz : s.M.size = M5.size := by
    rw [z5, z4, z3, z2, z1]
  -- the outputs
  have hsv2 : 2 * sv + 2 ≤ 2 * k := by omega
  obtain ⟨o1, o2, o3, hM6⟩ := stAcc_sem I C ⟨M5, s4.o⟩ hM5 (o := ob + 2 * sv) (k := k) hC hk1 c5.1 c5.2
    (by simp only [regs] at hs ⊢; omega) (by omega) (by show _ ≤ M5.size; omega)
  have r6 : ∀ i, i < regs → i ≠ lgO → i ≠ cTmp →
      rd (semXIR I (stAcc C) ⟨M5, s4.o⟩).M i = rd M5 i := fun i hi h1 h2 =>
    frame I _ _ ((wf_stAcc C).2 trivial) hM5 i hi (fun h => (nw_stAcc i h2 h1 C).1 h)
  generalize semXIR I (stAcc C) ⟨M5, s4.o⟩ = s6 at o1 o2 o3 hM6 r6 ⊢
  -- `lgS += 1`
  obtain ⟨i7, i7f⟩ := incr_sem s6.M hM6 (r := lgS) (x := sv) (by decide) (by decide)
    (by rw [r6 _ (by decide) (by decide) (by decide), c5f _ (by decide) (by decide), hS4])
  have hM7 : Inv (runPrims [.op .add lgS lgS cOne] s6.M) := inv_runPrims (by simp [Prim.dst, lgS]) hM6
  generalize runPrims [.op .add lgS lgS cOne] s6.M = M7 at i7 i7f hM7 ⊢
  refine ⟨fun c hc => ?_, i7, fun i hi hp hne => ?_, hM7⟩
  · have q : lgAc + 2 * c + 1 < regs ∧ lgAc + 2 * c ≠ lgO ∧ lgAc + 2 * c ≠ cTmp ∧
        lgAc + 2 * c + 1 ≠ lgO ∧ lgAc + 2 * c + 1 ≠ cTmp ∧ lgAc + 2 * c ≠ lgK ∧
        lgAc + 2 * c + 1 ≠ lgK := by simp only [lgAc, lgO, cTmp, regs, lgK]; omega
    have hc2 : 2 * k * c + 2 ≤ 2 * k * C := by
      have := Nat.mul_le_mul_left (2 * k) (show c + 1 ≤ C by omega); rw [Nat.mul_succ] at this; omega
    rw [rdF_mk, i7f (ob + 2 * sv + 2 * k * c) (by simp only [lgS]; omega),
      i7f (ob + 2 * sv + 2 * k * c + 1) (by simp only [lgS]; omega), (o2 c hc).1, (o2 c hc).2,
      c5f _ q.2.2.2.2.2.1 q.2.1, c5f _ q.2.2.2.2.2.2 q.2.2.2.1, ← rdF_mk, g1 c hc]
    refine Finset.sum_congr rfl fun t ht => ?_
    have ht' := Finset.mem_range.1 ht
    have hCt : C * t + c + 1 ≤ C * k := by
      have := Nat.mul_le_mul_left C (show t + 1 ≤ k by omega); rw [Nat.mul_succ] at this; omega
    rw [rdB, H3 _ (by simp only [regs]; omega), ← rdB, f3 t ht',
      rdF_eq (H3 _ (by simp only [regs]; omega)) (H3 _ (by simp only [regs]; omega)),
      rdF_eq (f4 _ (by simp only [regs]; omega) (.inr (by omega)))
        (f4 _ (by simp only [regs]; omega) (.inr (by omega))),
      rdF_eq (H1 _ (by simp only [regs]; omega)) (H1 _ (by simp only [regs]; omega))]
  · simp only [regs] at hi
    rw [i7f _ (by simp only [lgS]; omega), o3 i (by simp only [regs]; omega) hne,
      c5f _ (by simp only [lgK]; omega) (by simp only [lgO]; omega), g2 i (by simp only [regs]; omega),
      H3 i (by simp only [regs]; omega), f4 i (by simp only [regs]; omega) hp,
      H1 i (by simp only [regs]; omega)]

/-! ## The targets, and the interpolation -/

/-- Distinct targets' output cells are distinct (`a, b < k`; offsets `e, e' < 2`). -/
theorem out_ne {k a b c d e e' : ℕ} (ha : a < k) (hb : b < k) (hab : a ≠ b) (he : e < 2) (he' : e' < 2)
    (o : ℕ) : o + 2 * a + 2 * k * c + e ≠ o + 2 * b + 2 * k * d + e' := by
  intro H
  rw [Nat.mul_assoc 2 k c, Nat.mul_assoc 2 k d] at H
  have h1 : a + k * c = b + k * d := by omega
  have h2 := congrArg (· % k) h1
  simp only [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] at h2
  exact hab h2

/-- The output cells of a target lie in `[ob, ob + 2kC)`. -/
theorem outC_lt {k a c C : ℕ} (ha : a < k) (hc : c < C) (o : ℕ) : o + 2 * a + 2 * k * c + 1 < o + 2 * k * C := by
  have := Nat.mul_le_mul_left (2 * k) (show c + 1 ≤ C by omega)
  rw [Nat.mul_succ] at this
  omega

/-- **The target loop**: for `s < k`, `c < C`, output row `c` at `ob + 2s + 2kc` is
`Σ_{t<k} (P_t Q_t) · Y_c[t]`; the heap outside the prefix table and `[ob, ob + 2kC)` is kept. -/
theorem tgIR_sem (I : Array Word) (s : St) (hM : Inv s.M) {k C jb pb yb ob : ℕ} {Jl : List ℕ}
    (hk1 : 1 ≤ k) (hk : k < 2 ^ 64) (hC : C ≤ 16) (hjb : regs ≤ jb)
    (hjp : jb + k ≤ pb) (hpy : pb + k ≤ yb) (hyo : yb + 2 * C * k ≤ ob)
    (hos : ob + 2 * k * (C + 1) ≤ s.M.size) (ho2 : ob + 2 * k * (C + 1) + 2 < 2 ^ 64)
    (hJ : ∀ u < k, rd s.M (jb + u) = jw Jl u) :
    (∀ sv < k, ∀ c < C, rdF (semXIR I (tgIR k C jb pb yb ob) s).M (ob + 2 * sv + 2 * k * c) =
      ∑ t ∈ range k, F.smulBase (preP Jl sv t * sufP Jl k sv (t + 1))
        (rdF s.M (yb + 2 * (C * t + c)))) ∧
    (∀ i, regs ≤ i → (i < pb ∨ pb + k ≤ i) → (i < ob ∨ ob + 2 * k * C ≤ i) →
      rd (semXIR I (tgIR k C jb pb yb ob) s).M i = rd s.M i) ∧
    Inv (semXIR I (tgIR k C jb pb yb ob) s).M := by
  have hs : 256 ≤ s.M.size := hM.1
  simp only [regs] at hjb
  rw [tgIR, semXIR_seq, semB]
  have c1 : rd (runPrims [.const lgS 0, .const lgN1 (toWord k)] s.M) lgS = toWord 0 ∧
      rd (runPrims [.const lgS 0, .const lgN1 (toWord k)] s.M) lgN1 = toWord k := by
    simp only [runPrims_cons, runPrims_nil, Prim.run]
    refine ⟨?_, ?_⟩ <;>
    simp (disch := first | decide | (simp only [size_set, lgS, lgN1]; omega)) only
      [rd_set_self, rd_set_ne]
    all_goals rfl
  have c1f : ∀ i, regs ≤ i → rd (runPrims [.const lgS 0, .const lgN1 (toWord k)] s.M) i = rd s.M i :=
    fun i hi => rd_runPrims_of_not_writes (by simp only [regs] at hi; simp [Prim.dst, lgS, lgN1]; omega) _
  have hM1 : Inv (runPrims [.const lgS 0, .const lgN1 (toWord k)] s.M) :=
    inv_runPrims (by simp [Prim.dst, lgS, lgN1]) hM
  have z1 := size_runPrims [.const lgS 0, .const lgN1 (toWord k)] s.M
  generalize runPrims [.const lgS 0, .const lgN1 (toWord k)] s.M = M1 at c1 c1f hM1 z1 ⊢
  let P : ℕ → St → Prop := fun j st => Inv st.M ∧ st.M.size = s.M.size ∧ rd st.M lgS = toWord j ∧
    (∀ sv < j, ∀ c < C, rdF st.M (ob + 2 * sv + 2 * k * c) =
      ∑ t ∈ range k, F.smulBase (preP Jl sv t * sufP Jl k sv (t + 1))
        (rdF s.M (yb + 2 * (C * t + c)))) ∧
    (∀ i, regs ≤ i → (i < pb ∨ pb + k ≤ i) → (i < ob ∨ ob + 2 * k * C ≤ i) → rd st.M i = rd s.M i)
  have ef : ∀ i, i ≠ lgC1 → i ≠ cTmp → rd (entryK lgC1 lgN1 (toWord k) M1) i = rd M1 i :=
    fun i a b => entryK_frame _ (Ne.symm a) (Ne.symm b)
  have h := loopK_run I (tgBody k C jb pb yb ob) P ⟨M1, s.o⟩ hM1 (by decide) (by decide) (by decide)
    c1.2 hk ⟨inv_entryK hM1 (by decide), by rw [size_entryK, z1],
      by rw [ef _ (by decide) (by decide), c1.1],
      fun sv hsv => absurd hsv (Nat.not_lt_zero _),
      fun i hi _ _ => (ef i (by simp only [regs, lgC1] at hi ⊢; omega)
        (by simp only [regs, cTmp] at hi ⊢; omega)).trans (c1f i hi)⟩ ?_
  · exact ⟨h.2.2.2.1, h.2.2.2.2, h.1⟩
  rintro j st hj ⟨hI, hz, hS', hV, hH⟩
  obtain ⟨b1, b2, b3, hI2⟩ := tgBody_sem I st hI (Jl := Jl) hk1 hk hC hj (by simp only [regs]; omega)
    hjp hpy hyo (by rw [hz]; exact hos) ho2 hS'
    (fun u hu => by rw [hH _ (by simp only [regs]; omega) (.inl (by omega)) (.inl (by omega)), hJ u hu])
  have hd : ∀ i, regs ≤ i → rd (decS lgC1 (semXIR I (tgBody k C jb pb yb ob) st)).M i =
      rd (semXIR I (tgBody k C jb pb yb ob) st).M i :=
    fun i hi => rd_decS (by simp only [regs, lgC1] at hi ⊢; omega) _
  have hY : ∀ t < k, ∀ c < C, rdF st.M (yb + 2 * (C * t + c)) = rdF s.M (yb + 2 * (C * t + c)) :=
    fun t ht c hc => by
      have : C * t + c + 1 ≤ C * k := by
        have := Nat.mul_le_mul_left C (show t + 1 ≤ k by omega); rw [Nat.mul_succ] at this; omega
      have e2 : 2 * C * k = 2 * (C * k) := Nat.mul_assoc ..
      exact rdF_eq (hH _ (by simp only [regs]; omega) (.inr (by omega)) (.inl (by omega)))
        (hH _ (by simp only [regs]; omega) (.inr (by omega)) (.inl (by omega)))
  refine ⟨inv_decS hI2 (by decide), by rw [size_decS, size_sem, hz], by rw [rd_decS (by decide), b2],
    fun sv hsv c hc => ?_, fun i hi hp ho => ?_⟩
  · have hlt := outC_lt (k := k) (a := sv) (c := c) (C := C) (by omega) hc ob
    have hge : regs ≤ ob + 2 * sv + 2 * k * c := by simp only [regs]; omega
    rw [rdF_eq (hd _ hge) (hd _ (by simp only [regs] at hge ⊢; omega))]
    rcases Nat.lt_succ_iff_lt_or_eq.1 hsv with hsv | rfl
    · have hne : ∀ c' < C, ∀ e < 2, ob + 2 * sv + 2 * k * c + e ≠ ob + 2 * j + 2 * k * c' ∧
          ob + 2 * sv + 2 * k * c + e ≠ ob + 2 * j + 2 * k * c' + 1 := fun c' _ e he =>
        ⟨fun H => out_ne (e' := 0) (by omega) hj (by omega) he (by omega) ob (H.trans rfl),
          out_ne (by omega) hj (by omega) he (by omega) ob⟩
      rw [rdF_eq (b3 _ hge (.inr (by omega)) fun c' hc' => (hne c' hc' 0 (by omega)))
        (b3 _ (by simp only [regs] at hge ⊢; omega) (.inr (by omega))
          fun c' hc' => (hne c' hc' 1 (by omega)))]
      exact hV sv hsv c hc
    · rw [b1 c hc]
      exact Finset.sum_congr rfl fun t ht => by rw [hY t (Finset.mem_range.1 ht) c hc]
  · rw [hd i hi, b3 i hi hp fun c hc => ⟨fun e => by
        have := outC_lt (k := k) (a := j) (c := c) (C := C) hj hc ob; omega, fun e => by
        have := outC_lt (k := k) (a := j) (c := c) (C := C) hj hc ob; omega⟩,
      hH i hi hp ho]

/-- **The interpolation of rows `c₀ … c₀ + C − 1`** (`lagIR`): on the layout
`regs ≤ jb`, `jb + k ≤ pb`, `pb + k ≤ yb`, `yb + 2Ck ≤ ob`, `yb + 2Ck ≤ cb`, output row `c` at target
`s < k` (cell `ob + 2s + 2kc`) is `lagVal J k s y_{c₀+c}` with `y_c(j)` the `F` element at
`cb + cs·j + 2(c₀ + c)`. The heap outside `[pb, ob + 2kC)` is kept. -/
theorem lagIR_sem (I : Array Word) (s : St) (hM : Inv s.M) {k C c0 jb pb yb ob cb cs : ℕ}
    {Jl : List ℕ} (hk1 : 1 ≤ k) (hk : k < 2 ^ 64) (hC : C ≤ 16) (hjb : regs ≤ jb)
    (hjp : jb + k ≤ pb) (hpy : pb + k ≤ yb) (hyo : yb + 2 * C * k ≤ ob) (hcb : yb + 2 * C * k ≤ cb)
    (hos : ob + 2 * k * (C + 1) ≤ s.M.size) (ho2 : ob + 2 * k * (C + 1) + 2 < 2 ^ 64)
    (hcb2 : ∀ t < k, cb + cs * Jl.getD t 0 + 2 * c0 + 2 * C + 2 < 2 ^ 64)
    (hJ : ∀ u < k, rd s.M (jb + u) = jw Jl u) :
    (∀ sv < k, ∀ c < C, rdF (semXIR I (lagIR k C c0 jb pb yb ob cb cs) s).M (ob + 2 * sv + 2 * k * c) =
      lagVal Jl k sv fun j => rdF s.M (cb + cs * j + 2 * c0 + 2 * c)) ∧
    (∀ i, regs ≤ i → (i < pb ∨ ob + 2 * k * C ≤ i) →
      rd (semXIR I (lagIR k C c0 jb pb yb ob cb cs) s).M i = rd s.M i) ∧
    Inv (semXIR I (lagIR k C c0 jb pb yb ob cb cs) s).M := by
  have hCk : 2 * C * k = 2 * k * C := by ring
  rw [lagIR, semXIR_seq]
  obtain ⟨y1, y2, hM1⟩ := yTab_sem I s hM (J := fun t => Jl.getD t 0) (cb := cb) (cs := cs) (c0 := c0)
    hk (by omega) hjb (by omega) (by omega) (by omega) hcb hcb2 hJ
  have z1 := size_sem I (yTabIR k C jb yb cb cs c0) s
  generalize semXIR I (yTabIR k C jb yb cb cs c0) s = s1 at y1 y2 hM1 z1 ⊢
  simp only [regs] at hjb
  obtain ⟨t1, t2, hM2⟩ := tgIR_sem I s1 hM1 (Jl := Jl) (C := C) (yb := yb) hk1 hk hC
    (by simp only [regs]; omega) hjp hpy hyo (by rw [z1]; exact hos) ho2
    (fun u hu => by rw [y2 _ (by simp only [regs]; omega) (.inl (by omega)), hJ u hu])
  refine ⟨fun sv hsv c hc => ?_, fun i hi hi2 => ?_, hM2⟩
  · rw [t1 sv hsv c hc, lagVal]
    refine Finset.sum_congr rfl fun t ht => ?_
    have h := y1 t (Finset.mem_range.1 ht) c hc
    rw [lagTerm, yv, rdF_mk, ← rdB, ← rdB, h.1, h.2]
    show F.smulBase _ ⟨_, _⟩ = F.smulBase _ ⟨_, _⟩
    rw [mul_comm (rdB s.M _), mul_comm (rdB s.M _)]
    rfl
  · rw [t2 i hi (by omega) (by omega), y2 i hi (by omega)]

/-- **`lagIR` interpolates**: with `J` listed without repeats below `2^20` and `k = |J|`, output row
`c` at target `s` is `interpF D J y_{c₀+c} s`. -/
theorem lagIR_interp (I : Array Word) (s : St) (hM : Inv s.M) {C c0 jb pb yb ob cb cs : ℕ}
    {Jl : List ℕ} (hnd : Jl.Nodup) (hJn : ∀ j ∈ Jl, j < nMax) (hk1 : 1 ≤ Jl.length)
    (hk : Jl.length < 2 ^ 64) (hC : C ≤ 16) (hjb : regs ≤ jb)
    (hjp : jb + Jl.length ≤ pb) (hpy : pb + Jl.length ≤ yb) (hyo : yb + 2 * C * Jl.length ≤ ob)
    (hcb : yb + 2 * C * Jl.length ≤ cb) (hos : ob + 2 * Jl.length * (C + 1) ≤ s.M.size)
    (ho2 : ob + 2 * Jl.length * (C + 1) + 2 < 2 ^ 64)
    (hcb2 : ∀ t < Jl.length, cb + cs * Jl.getD t 0 + 2 * c0 + 2 * C + 2 < 2 ^ 64)
    (hJ : ∀ u < Jl.length, rd s.M (jb + u) = jw Jl u) :
    ∀ sv < Jl.length, ∀ c < C,
      rdF (semXIR I (lagIR Jl.length C c0 jb pb yb ob cb cs) s).M (ob + 2 * sv + 2 * Jl.length * c) =
        interpF D Jl.toFinset (fun j => rdF s.M (cb + cs * j + 2 * c0 + 2 * c)) sv :=
  fun sv hsv c hc => by
    rw [(lagIR_sem I s hM hk1 hk hC hjb hjp hpy hyo hcb hos ho2 hcb2 hJ).1 sv hsv c hc, lagVal_eq hnd hJn]

/-! ## Controls -/

/-- (+) **`lagIR` returns the data at a listed position**: a target `s ∈ J` gets row `c₀ + c`'s
value `y(s)`. -/
theorem lagIR_node_ctl (I : Array Word) (s : St) (hM : Inv s.M) {C c0 jb pb yb ob cb cs : ℕ}
    {Jl : List ℕ} (hnd : Jl.Nodup) (hJn : ∀ j ∈ Jl, j < nMax) (hk1 : 1 ≤ Jl.length)
    (hk : Jl.length < 2 ^ 64) (hC : C ≤ 16) (hjb : regs ≤ jb)
    (hjp : jb + Jl.length ≤ pb) (hpy : pb + Jl.length ≤ yb) (hyo : yb + 2 * C * Jl.length ≤ ob)
    (hcb : yb + 2 * C * Jl.length ≤ cb) (hos : ob + 2 * Jl.length * (C + 1) ≤ s.M.size)
    (ho2 : ob + 2 * Jl.length * (C + 1) + 2 < 2 ^ 64)
    (hcb2 : ∀ t < Jl.length, cb + cs * Jl.getD t 0 + 2 * c0 + 2 * C + 2 < 2 ^ 64)
    (hJ : ∀ u < Jl.length, rd s.M (jb + u) = jw Jl u) {sv c : ℕ} (hsv : sv < Jl.length)
    (hsJ : sv ∈ Jl) (hc : c < C) :
    rdF (semXIR I (lagIR Jl.length C c0 jb pb yb ob cb cs) s).M (ob + 2 * sv + 2 * Jl.length * c) =
      rdF s.M (cb + cs * sv + 2 * c0 + 2 * c) := by
  rw [lagIR_interp I s hM hnd hJn hk1 hk hC hjb hjp hpy hyo hcb hos ho2 hcb2 hJ sv hsv c hc]
  exact interpF_self (fun a ha b hb h => D_injOn_nMax (hJn a (List.mem_toFinset.1 ha))
    (hJn b (List.mem_toFinset.1 hb)) h) _ (List.mem_toFinset.2 hsJ)

/-- (−) **`lagIR` reads its own row window**: where rows `c₀ + c` and `c₀ + c + 1` differ at a
listed target, output row `c` is not row `c₀ + c + 1`'s value. -/
theorem lagIR_row_ctl (I : Array Word) (s : St) (hM : Inv s.M) {C c0 jb pb yb ob cb cs : ℕ}
    {Jl : List ℕ} (hnd : Jl.Nodup) (hJn : ∀ j ∈ Jl, j < nMax) (hk1 : 1 ≤ Jl.length)
    (hk : Jl.length < 2 ^ 64) (hC : C ≤ 16) (hjb : regs ≤ jb)
    (hjp : jb + Jl.length ≤ pb) (hpy : pb + Jl.length ≤ yb) (hyo : yb + 2 * C * Jl.length ≤ ob)
    (hcb : yb + 2 * C * Jl.length ≤ cb) (hos : ob + 2 * Jl.length * (C + 1) ≤ s.M.size)
    (ho2 : ob + 2 * Jl.length * (C + 1) + 2 < 2 ^ 64)
    (hcb2 : ∀ t < Jl.length, cb + cs * Jl.getD t 0 + 2 * c0 + 2 * C + 2 < 2 ^ 64)
    (hJ : ∀ u < Jl.length, rd s.M (jb + u) = jw Jl u) {sv c : ℕ} (hsv : sv < Jl.length)
    (hsJ : sv ∈ Jl) (hc : c < C)
    (hne : rdF s.M (cb + cs * sv + 2 * c0 + 2 * c) ≠ rdF s.M (cb + cs * sv + 2 * c0 + 2 * (c + 1))) :
    rdF (semXIR I (lagIR Jl.length C c0 jb pb yb ob cb cs) s).M (ob + 2 * sv + 2 * Jl.length * c) ≠
      rdF s.M (cb + cs * sv + 2 * c0 + 2 * (c + 1)) := by
  rw [lagIR_node_ctl I s hM hnd hJn hk1 hk hC hjb hjp hpy hyo hcb hos ho2 hcb2 hJ hsv hsJ hc]
  exact hne

end FR.X

end G6_FRXLagT

section G6_FRXDecLv

-- New for `flock-recursive` (BLUEPRINT §6.2 step 4, one level's decode composed; stage S-H2,
-- track L-ext).

/-!
# One level's decode on the machine

The decode of level `i` (BLUEPRINT §6.2 step 4) is

`eqtIR ; msg ; fwdIR ×2 ; flagIR ; scanIR ; baryIR k R ; bflyIR ×R`

on a fixed memory map (words; `k = 2^mLog`, `n = 2^logN`, `R` rows):

| region | base | size |
|---|---|---|
| basis table (`wtabIR`) | `tb0 = 2^20` | 800 |
| `J` (the scan's list) | `jb0 = 2^21` | `k` |
| flags | `fbF = 2^21 + 2^18` | `n` |
| `DJ`, `W`, `E` | `djb0`, `wb0`, `eb0` | `2k` each |
| decoded rows, levels 1–4 | `obL = 2^22 + 2^21` | `2kR` |
| chain answers | `chB … chEnd` | (read) |
| `eq` table | `eqB = 2^23 + 2^15` | `4·2^ℓ` |
| `X`, `Y` (the next message, then `Enc`) | `xbM = 2^23 + 2^16`, `ybM = xbM + 2^19` | `2n` each |
| the word `W⁽ⁱ⁾` | `stB` (levels 1–4), `colBase` (level 0) | (read) |

* `bfRowsIR`: the butterflies on each of the `R` decoded rows (unrolled; `bfRows_sem`);
* `decFrontIR` (`eqtIR ; msg ; fwdIR ×2 ; flagIR`), `decFront_sem`: the flags mark `A_c`;
* `decBackIR` (`scanIR ; baryIR ; bfRowsIR`), `decBack_sem`: the rows are `msgOf` (`level_decode`);
* **`decLv_sem`**: one level, `decLvU_sem` (levels 1–4, the word at `stB`, the rows at `obL`) and
  `decLv0_sem` (level 0, the word at `colBase`, the rows at `ob0`);
* `MsgOk`: what the message step owes; `msgOk_four` (level 4, from π's tape and the chain link
  `finalAt = finPi`), `msgOk_lower` (levels 0–3, from the next level's decoded rows).
-/

namespace FR.X

open RecursionFast FR Finset

/-! ## The butterflies on the rows -/

/-- `rA0 := b`. -/
def setA (b : ℕ) : XIR := .blk [.const rA0 (toWord b)]

/-- **The butterflies on rows `0 … R − 1`** (row `c` of `2^m` entries at `ob + 2·2^m·c`). -/
def bfRowsIR (m ob tb : ℕ) : ℕ → XIR
  | 0 => .blk []
  | R + 1 => .seq (bfRowsIR m ob tb R) (.seq (setA (ob + 2 * 2 ^ m * R)) (bflyIR m tb))

theorem wf_bfRowsIR (m ob tb : ℕ) : ∀ R, WF (bfRowsIR m ob tb R)
  | 0 => by simp [bfRowsIR, WF]
  | R + 1 => ⟨wf_bfRowsIR m ob tb R, by simp [setA, WF, Prim.dst, rA0], wf_bflyIR m tb⟩

theorem noLoopT_bfRowsIR (m ob tb : ℕ) : ∀ R, NoLoopT (bfRowsIR m ob tb R)
  | 0 => by simp [bfRowsIR, NoLoopT]
  | R + 1 => ⟨noLoopT_bfRowsIR m ob tb R, by simp [setA, NoLoopT], noLoopT_bflyIR m tb⟩

theorem outs_bfRowsIR (m ob tb t : ℕ) : ∀ R, outs (bfRowsIR m ob tb R) t = 0
  | 0 => by simp [bfRowsIR, outs]
  | R + 1 => by simp [bfRowsIR, outs, outs_bfRowsIR m ob tb t R, setA, outs_bflyIR]

theorem cost_bfRowsIR (m ob tb t : ℕ) (hm : 2 ^ (m - 1) < 2 ^ 64) (hm' : m < 2 ^ 64) :
    ∀ R, cost (bfRowsIR m ob tb R) t = 1 + R * (17 + m * (741 * 2 ^ (m - 1) + 23))
  | 0 => by simp [bfRowsIR, cost, blkSteps]
  | R + 1 => by
    simp only [bfRowsIR, cost, cost_bfRowsIR m ob tb t hm hm' R, setA, blkSteps, List.length_cons,
      List.length_nil, cost_bflyIR m tb t hm hm']
    norm_num; ring

theorem setA_sem (I : Array Word) (s : St) (hM : Inv s.M) (b : ℕ) :
    rd (semXIR I (setA b) s).M rA0 = toWord b ∧
    (∀ x, regs ≤ x → rd (semXIR I (setA b) s).M x = rd s.M x) ∧ Inv (semXIR I (setA b) s).M := by
  have hs := hM.1
  simp only [regs] at hs
  refine ⟨?_, hframe I (setA b) s (by simp [setA, Lo, Prim.dst, rA0, regs]),
    inv_sem I (by simp [setA, WF, Prim.dst, rA0]) hM⟩
  simp only [setA, semXIR, runPrims, List.foldl, Prim.run]
  exact rd_set_self (by simp only [rA0]; omega)

/-- **The butterflies on the rows**: with row `c < R` holding `Y c` (`2^m` entries at
`ob + 2·2^m·c`) and the basis table at `tb`, `bfRowsIR m ob tb R` leaves `bflyRun … (Y c)` in
each row and keeps the heap outside `[ob, ob + 2·2^m·R)`. -/
theorem bfRows_sem (I : Array Word) {m ob tb : ℕ} (hm1 : 1 ≤ m) (hm : m ≤ 20) (hob : regs ≤ ob)
    (htb : regs ≤ tb) (htb2 : tb + 800 < 2 ^ 64) {Y : ℕ → ℕ → F} :
    ∀ R (s : St), Inv s.M → ob + 2 * 2 ^ m * R + 1 < 2 ^ 64 → ob + 2 * 2 ^ m * R ≤ s.M.size →
      (tb + 800 ≤ ob ∨ ob + 2 * 2 ^ m * R ≤ tb) →
      (∀ v < 20, ∀ i < 20, rdF s.M (tb + 40 * v + 2 * i) = (wRow D logNMax v).getD i 0) →
      (∀ c < R, ∀ x < 2 ^ m, rdF s.M (ob + 2 * 2 ^ m * c + 2 * x) = Y c x) →
      (∀ c < R, ∀ x < 2 ^ m, rdF (semXIR I (bfRowsIR m ob tb R) s).M (ob + 2 * 2 ^ m * c + 2 * x) =
        bflyRun (M := F) D logNMax 0 m (Y c) x) ∧
      (∀ y, regs ≤ y → (y < ob ∨ ob + 2 * 2 ^ m * R ≤ y) →
        rd (semXIR I (bfRowsIR m ob tb R) s).M y = rd s.M y) ∧
      Inv (semXIR I (bfRowsIR m ob tb R) s).M
  | 0, s, hM, _, _, _, _, _ => ⟨fun c hc => absurd hc (Nat.not_lt_zero _), fun _ _ _ => rfl, hM⟩
  | R + 1, s, hM, h2, hsz, hd, hW, hY => by
    have hs := hM.1
    simp only [regs] at hs hob htb
    have hR : 2 * 2 ^ m * R + 2 * 2 ^ m = 2 * 2 ^ m * (R + 1) := by ring
    obtain ⟨a1, a2, hM1⟩ := bfRows_sem I hm1 hm (by simp only [regs]; omega)
      (by simp only [regs]; omega) htb2 R s hM (by omega) (by omega) (by omega) hW
      (fun c hc x hx => hY c (by omega) x hx)
    rw [bfRowsIR, semXIR_seq, semXIR_seq]
    have z1 := size_sem I (bfRowsIR m ob tb R) s
    generalize semXIR I (bfRowsIR m ob tb R) s = s1 at a1 a2 hM1 z1
    obtain ⟨b1, b2, hM2⟩ := setA_sem I s1 hM1 (ob + 2 * 2 ^ m * R)
    have z2 := size_sem I (setA (ob + 2 * 2 ^ m * R)) s1
    generalize semXIR I (setA (ob + 2 * 2 ^ m * R)) s1 = s2 at b1 b2 hM2 z2
    have h2s : ∀ y, regs ≤ y → (y < ob + 2 * 2 ^ m * R ∨ ob + 2 * 2 ^ m * (R + 1) ≤ y) →
        rd s2.M y = rd s1.M y := fun y hy _ => b2 y hy
    have hW2 : ∀ v < 20, ∀ i < 20, rdF s2.M (tb + 40 * v + 2 * i) = (wRow D logNMax v).getD i 0 :=
      fun v hv i hi => by
        rw [← hW v hv i hi]
        exact rdF_eq ((b2 _ (by simp only [regs]; omega)).trans
            (a2 _ (by simp only [regs]; omega) (by omega)))
          ((b2 _ (by simp only [regs]; omega)).trans (a2 _ (by simp only [regs]; omega) (by omega)))
    have hY2 : ∀ x < 2 ^ m, rdF s2.M (ob + 2 * 2 ^ m * R + 2 * x) = Y R x := fun x hx => by
      rw [← hY R (by omega) x hx]
      exact rdF_eq ((b2 _ (by simp only [regs]; omega)).trans
          (a2 _ (by simp only [regs]; omega) (by omega)))
        ((b2 _ (by simp only [regs]; omega)).trans (a2 _ (by simp only [regs]; omega) (by omega)))
    obtain ⟨c1, c2, hM3⟩ := bflyIR_sem I s2 hM2 (A := ob + 2 * 2 ^ m * R) (tb := tb) (ℓ := m)
      (Y := Y R) hm1 hm (by simp only [regs]; omega) (by omega) (by omega)
      (by simp only [regs]; omega) htb2 (by omega) b1 hW2 hY2
    refine ⟨fun c hc x hx => ?_, fun y hy hy2 => ?_, hM3⟩
    · rcases Nat.lt_succ_iff_lt_or_eq.mp hc with h | rfl
      · rw [← a1 c h x hx]
        have hcx : 2 * 2 ^ m * c + 2 * 2 ^ m ≤ 2 * 2 ^ m * R := by
          rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left _ h
        exact rdF_eq ((c2 _ (by simp only [regs]; omega) (by omega)).trans
            (b2 _ (by simp only [regs]; omega)))
          ((c2 _ (by simp only [regs]; omega) (by omega)).trans (b2 _ (by simp only [regs]; omega)))
      · exact c1 x hx
    · rw [c2 y hy (by omega), b2 y hy, a2 y hy (by omega)]

/-! ## The memory map -/

/-- The flags (`2^21 + 2^18`). -/ def fbF : ℕ := 2359296
/-- The decoded rows of levels 1–4 (`2^22 + 2^21`). -/ def obL : ℕ := 6291456
/-- The `eq` table (`2^23 + 2^15`). -/ def eqB : ℕ := 8421376
/-- `X` (`2^23 + 2^16`). -/ def xbM : ℕ := 8454144
/-- `Y` (`xbM + 2^19`). -/ def ybM : ℕ := 8978432

/-! ## The back half: the scan, the interpolation, the butterflies -/

/-- **The back half** of a level: the first `k` flagged positions to `J`, the interpolation of the
`R` rows of the word (at `cb + cs·j + 2r`) to `ob`, the butterflies on each row. -/
def decBackIR (n m R cs cb ob : ℕ) : XIR :=
  .seq (scanIR n (2 ^ m) fbF jb0)
    (.seq (baryIR (2 ^ m) R jb0 djb0 wb0 eb0 cb cs ob tb0) (bfRowsIR m ob tb0 R))

open FR.Snd in
/-- **The back half decodes** (`level_decode`): if the flags at `fbF` mark `A_c`, the word of
level `i` sits at `cb + cs·j + 2r`, the word is close and `A_c = jointAgree` (what `final` hands
over), then row `r` at `ob + 2kr` holds the `F` values of S-G's `msgOf (i) r`. -/
theorem decBack_sem (I : Array Word) (s : St) (hM : Inv s.M) {L es : Log} {i cs cb ob : ℕ}
    (hi : i < 5) (hfar : ¬ farL .N30 L es i)
    (hA : consSet .N30 L es i = jointAgree (wordK .N30 L es i) (decodeL .N30 L es i))
    (hsz : memX ≤ s.M.size)
    (hL : BaryLay (2 ^ mLog .N30 i) (lvl .N30 i).rows jb0 djb0 wb0 eb0 cb ob tb0)
    (hcb : cb + 128 * 2 ^ 20 + 256 < 2 ^ 64) (hcs : cs ≤ 128) (hob : ob + 2 * 2 ^ mLog .N30 i * (lvl .N30 i).rows ≤ memX)
    (hT : ∀ v < 20, ∀ i < 20, rdF s.M (tb0 + 40 * v + 2 * i) = (wRow D logNMax v).getD i 0)
    (hW : ∀ j (hj : j < 2 ^ (lvl .N30 i).logN) (r : Fin (lvl .N30 i).rows),
      rdF s.M (cb + cs * j + 2 * r) = wordOf .N30 L es i r ⟨j, hj⟩)
    (hF : ∀ j < 2 ^ (lvl .N30 i).logN, (j ∈ consN .N30 L es i ↔ rd s.M (fbF + j) ≠ 0)) :
    (∀ r < (lvl .N30 i).rows, ∀ x < 2 ^ mLog .N30 i,
      algebraMap F K (rdF (semXIR I (decBackIR (2 ^ (lvl .N30 i).logN) (mLog .N30 i)
        (lvl .N30 i).rows cs cb ob) s).M (ob + 2 * 2 ^ mLog .N30 i * r + 2 * x)) =
      msgOf .N30 L es i r x) ∧
    (∀ y, regs ≤ y → (y < jb0 ∨ (jb0 + 2 ^ mLog .N30 i ≤ y ∧ y < djb0) ∨
        (eb0 + 2 * 2 ^ mLog .N30 i ≤ y ∧ y < ob) ∨ ob + 2 * 2 ^ mLog .N30 i * (lvl .N30 i).rows ≤ y) →
      rd (semXIR I (decBackIR (2 ^ (lvl .N30 i).logN) (mLog .N30 i)
        (lvl .N30 i).rows cs cb ob) s).M y = rd s.M y) ∧
    Inv (semXIR I (decBackIR (2 ^ (lvl .N30 i).logN) (mLog .N30 i)
        (lvl .N30 i).rows cs cb ob) s).M := by
  classical
  obtain ⟨htb, htj, hjd, hdw, hwe, heo, hoc⟩ := hL
  have hs := hM.1
  simp only [regs] at hs htb
  have hm1 : 1 ≤ mLog .N30 i := by interval_cases i <;> decide
  have hm20 : mLog .N30 i ≤ 17 := by interval_cases i <;> decide
  have hn18 : (lvl .N30 i).logN ≤ 18 := by interval_cases i <;> decide
  have hmn : mLog .N30 i ≤ (lvl .N30 i).logN := by interval_cases i <;> decide
  have hR64 : (lvl .N30 i).rows ≤ 64 := by interval_cases i <;> decide
  have hP : 2 ^ (lvl .N30 i).logN ≤ 2 ^ 18 := Nat.pow_le_pow_right (by norm_num) hn18
  have hPm : 2 ^ mLog .N30 i ≤ 2 ^ (lvl .N30 i).logN := Nat.pow_le_pow_right (by norm_num) hmn
  have hmem : memX = 67108864 := rfl
  have etb : tb0 = 1048576 := rfl
  have ejb : jb0 = 2097152 := rfl
  have edj : djb0 = 4194304 := rfl
  have ewb : wb0 = 4718592 := rfl
  have eeb : eb0 = 5242880 := rfl
  have efb : fbF = 2359296 := rfl
  have enM : nMax = 1048576 := rfl
  -- the agreement set is large enough
  have hcard : (2 ^ mLog .N30 i) ≤ (consN .N30 L es i).card := by
    obtain ⟨-, -, -, hk', hn'⟩ := lv_params .N30 hi
    obtain ⟨-, hJ⟩ := decodeL_spec hfar
    rw [consN, card_map, hA]
    have : lvK .N30 i ≤ 2 ^ (lvl .N30 i).logN - lvE .N30 i := by
      rw [← hn']; obtain ⟨h1, -⟩ := lv_params .N30 hi; omega
    rw [← hk']; exact this.trans hJ
  -- the scan
  rw [decBackIR, semXIR_seq]
  obtain ⟨a1, a2, a3, hM1⟩ := scanIR_sem I s hM (n := 2 ^ (lvl .N30 i).logN) (k := 2 ^ mLog .N30 i) (fb := fbF) (lb := jb0)
    (f := fun j => rd s.M (fbF + j)) (by simp only [regs, jb0]; omega)
    (by simp only [jb0]; omega) (by simp only [jb0, memX] at *; omega)
    (by simp only [regs, fbF]; omega) (by simp only [fbF]; omega) (by omega)
    (.inr (by simp only [jb0, fbF]; omega)) (fun j _ => rfl)
  have z1 := size_sem I (scanIR (2 ^ (lvl .N30 i).logN) (2 ^ mLog .N30 i) fbF jb0) s
  generalize semXIR I (scanIR (2 ^ (lvl .N30 i).logN) (2 ^ mLog .N30 i) fbF jb0) s = s1 at a1 a2 a3 hM1 z1
  have hA' : ∀ j < (2 ^ (lvl .N30 i).logN), j ∈ consN .N30 L es i ↔ rd s.M (fbF + j) ≠ 0 := hF
  obtain ⟨SL, hSL⟩ : ∃ SL, SL = scanL (2 ^ (lvl .N30 i).logN) fun j => rd s.M (fbF + j) := ⟨_, rfl⟩
  rw [← hSL] at a1 a2
  obtain ⟨Jl, hJl⟩ : ∃ Jl, Jl = SL.take (2 ^ mLog .N30 i) := ⟨_, rfl⟩
  have hfk : firstK (2 ^ (lvl .N30 i).logN) (consN .N30 L es i) (2 ^ mLog .N30 i) = Jl.toFinset := by
    rw [hJl, hSL]; exact firstK_scan hA'
  have hlen : Jl.length = 2 ^ mLog .N30 i := by
    have h1 := firstK_card (n := 2 ^ (lvl .N30 i).logN) (A := consN .N30 L es i)
      (fun j hj => (mem_consN.1 hj).1) hcard
    rw [hfk] at h1
    have h2 := List.toFinset_card_le Jl
    have h3 : Jl.length ≤ 2 ^ mLog .N30 i := by rw [hJl]; exact List.length_take_le _ _
    omega
  have hlen0 : 2 ^ mLog .N30 i ≤ SL.length := by
    have := List.length_take_le' (2 ^ mLog .N30 i) SL
    rw [← hJl] at this; omega
  have hmin : min SL.length (2 ^ mLog .N30 i) = 2 ^ mLog .N30 i := by omega
  have hnd : Jl.Nodup := by
    rw [hJl, hSL]
    exact List.Nodup.sublist (List.take_sublist _ _) (List.Nodup.filter _ List.nodup_range)
  have hJmem : ∀ j ∈ Jl, j < 2 ^ (lvl .N30 i).logN := fun j hj => by
    rw [hJl, hSL] at hj
    have := List.mem_of_mem_take hj
    simp only [scanL, List.mem_filter, List.mem_range] at this
    exact this.1
  have hJ1 : ∀ t < Jl.length, rd s1.M (jb0 + t) = toWord (Jl.getD t 0) := fun t ht => by
    rw [a2 t (by omega), hJl, List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
      List.getElem?_take_of_lt (by omega)]
  have k1 : ∀ y, regs ≤ y → (y < jb0 ∨ jb0 + (2 ^ mLog .N30 i) ≤ y) → rd s1.M y = rd s.M y := a3
  -- the interpolation
  rw [semXIR_seq]
  have hL' : BaryLay Jl.length (lvl .N30 i).rows jb0 djb0 wb0 eb0 cb ob tb0 := by
    rw [hlen]; exact ⟨by simp only [regs]; omega, htj, hjd, hdw, hwe, heo, hoc⟩
  have hT1 : ∀ v < 20, ∀ i' < 20, rdF s1.M (tb0 + 40 * v + 2 * i') = (wRow D logNMax v).getD i' 0 :=
    fun v hv i' hi' => by
      rw [← hT v hv i' hi']
      exact rdF_eq (k1 _ (by simp only [regs]; omega) (.inl (by omega)))
        (k1 _ (by simp only [regs]; omega) (.inl (by omega)))
  have hb := baryIR_interp I s1 hM1 (C := (lvl .N30 i).rows) (cs := cs) hL' hnd
    (fun j hj => lt_of_lt_of_le (hJmem j hj) (by omega)) (by rw [hlen]; omega)
    (by omega) (by omega) (fun j hj c hc => by
      have : cs * j ≤ 128 * 2 ^ 20 := Nat.mul_le_mul hcs (by omega)
      omega)
    (by rw [hlen]; omega) (fun i' hi' => by simpa using hT1 0 (by norm_num) i' hi') hJ1
  rw [hlen] at hb
  obtain ⟨-, b2, hM2⟩ := baryIR_sem I s1 hM1 (Jl := Jl) (C := (lvl .N30 i).rows) (cs := cs) hL'
    (by rw [hlen]; omega) (by omega) (by omega) (fun j hj c hc => by
      have : cs * j ≤ 128 * 2 ^ 20 := Nat.mul_le_mul hcs (by omega)
      omega) (by rw [hlen]; omega)
    (fun t ht => lt_of_lt_of_le (hJmem _ (by rw [List.getD_eq_getElem _ _ ht]; exact List.getElem_mem ht))
      (by omega))
    (fun i' hi' => by simpa using hT1 0 (by norm_num) i' hi') hJ1
  rw [hlen] at b2 hM2
  have z2 := size_sem I (baryIR Jl.length (lvl .N30 i).rows jb0 djb0 wb0 eb0 cb cs ob tb0) s1
  rw [hlen] at z2
  generalize semXIR I (baryIR (2 ^ mLog .N30 i) (lvl .N30 i).rows jb0 djb0 wb0 eb0 cb cs ob tb0) s1 = s2 at hb b2 hM2 z2
  -- the butterflies
  have hT2 : ∀ v < 20, ∀ i' < 20, rdF s2.M (tb0 + 40 * v + 2 * i') = (wRow D logNMax v).getD i' 0 :=
    fun v hv i' hi' => by
      rw [← hT1 v hv i' hi']
      exact rdF_eq (b2 _ (by simp only [regs]; omega) (.inl (by omega)) (.inl (by omega)))
        (b2 _ (by simp only [regs]; omega) (.inl (by omega)) (.inl (by omega)))
  obtain ⟨c1, c2, hM3⟩ := bfRows_sem I (m := mLog .N30 i) (ob := ob) (tb := tb0)
    (Y := fun c => interpF D Jl.toFinset (fun j => rdF s1.M (cb + cs * j + 2 * c))) hm1
    (by omega) (by simp only [regs]; omega) (by simp only [regs]; omega) (by simp only [tb0]; omega)
    (lvl .N30 i).rows s2 hM2 (by rw [hmem] at hob; omega) (by rw [z2, z1]; exact hob.trans hsz)
    (.inl ((show tb0 + 800 ≤ eb0 by decide).trans ((Nat.le_add_right _ _).trans heo))) hT2
    (fun c hc x hx => hb x hx c hc)
  refine ⟨fun r hr x hx => ?_, fun y hy hy2 => ?_, hM3⟩
  · rw [c1 r hr x hx]
    have e : (fun j => rdF s1.M (cb + cs * j + 2 * r)) = fun j => rdF s1.M (cb + cs * j + 2 * r) := rfl
    have hY : interpF D Jl.toFinset (fun j => rdF s1.M (cb + cs * j + 2 * r)) =
        interpF D (firstK (2 ^ (lvl .N30 i).logN) (consN .N30 L es i) (2 ^ mLog .N30 i))
          (wordN .N30 L es i ⟨r, hr⟩) := by
      funext x'
      rw [hfk]
      refine interpF_congr D _ (fun j hj => ?_) x'
      have hjn := hJmem j (List.mem_toFinset.1 hj)
      have hc : cs * j ≤ cs * (2 ^ (lvl .N30 i).logN) := Nat.mul_le_mul_left _ hjn.le
      rw [rdF_eq (k1 _ (by simp only [regs]; omega) (.inr (by omega)))
        (k1 _ (by simp only [regs]; omega) (.inr (by omega))), hW j hjn ⟨r, hr⟩]
      simp only [wordN, hjn, dite_true]
    rw [hY]
    exact level_decode hi hfar hA ⟨r, hr⟩ ⟨x, hx⟩
  · rw [c2 y hy (by omega), b2 y hy (by omega) (by omega), k1 y hy (by omega)]

/-! ## The front half: the `eq` table, the next message, `Enc`, the flags -/

/-- **The front half** of a level: the `eq` table of the `ℓ` challenges at `cbS`, the next
message's rows (`msg`), `Enc` of each row (`n = log₂` of the positions), the flags. -/
def decFrontIR (msg : XIR) (ℓ n R cs cb cbS : ℕ) : XIR :=
  .seq (eqtIR ℓ cbS eqB) (.seq msg (.seq (setA xbM) (.seq (fwdIR n tb0) (.seq (setA ybM)
    (.seq (fwdIR n tb0) (flagIR (2 ^ n) R cs cb eqB xbM ybM fbF))))))

/-- What the message step of a level provides (`msgH_next`, `msg4_next`): from every state
that agrees with `s` on the heap outside the `eq` table, `msg` writes the next message's
coordinate rows at `xbM` and `ybM`, zero-padded, and keeps the heap outside `[xbM, ybM + 2^19)`. -/
def MsgOk (I : Array Word) (msg : XIR) (s : St) (n m : ℕ) (g : ℕ → K) : Prop :=
  ∀ s' : St, Inv s'.M → s'.M.size = s.M.size →
    (∀ y, regs ≤ y → (y < eqB ∨ eqB + 256 ≤ y) → rd s'.M y = rd s.M y) →
    (∀ j < 2 ^ n, rdF (semXIR I msg s').M (xbM + 2 * j) = (if j < 2 ^ m then (g j).f₀ else 0) ∧
      rdF (semXIR I msg s').M (ybM + 2 * j) = (if j < 2 ^ m then (g j).f₁ else 0)) ∧
    (∀ y, regs ≤ y → (y < xbM ∨ ybM + 2 ^ 19 ≤ y) → rd (semXIR I msg s').M y = rd s'.M y) ∧
    Inv (semXIR I msg s').M

open FR.Snd in
/-- **The front half marks `A_c`** (`flagV_consSet`): with the basis table at `tb0`, the word
of level `i` at `cb + cs·j + 2r` (above `2^24`), P1.i's challenges at `cbS`, and a message step
that lays out `nextMsg i`, the flag at `fbF + j` is nonzero iff `j ∈ A_c`. -/
theorem decFront_sem (I : Array Word) (s : St) (hM : Inv s.M) {L es : Log} {i cs cb cbS : ℕ}
    {msg : XIR} (hi : i < 5) (hsz : memX ≤ s.M.size) (hcs : 2 * (lvl .N30 i).rows ≤ cs)
    (hcb : 2 ^ 24 ≤ cb) (hcb2 : cb + cs * 2 ^ (lvl .N30 i).logN + 2 < 2 ^ 64)
    (hcS : regs ≤ cbS) (hcS2 : cbS + 8 * (lvl .N30 i).ell + 4 ≤ eqB)
    (hT : ∀ v < 20, ∀ i < 20, rdF s.M (tb0 + 40 * v + 2 * i) = (wRow D logNMax v).getD i 0)
    (hW : ∀ j (hj : j < 2 ^ (lvl .N30 i).logN) (r : Fin (lvl .N30 i).rows),
      rdF s.M (cb + cs * j + 2 * r) = wordOf .N30 L es i r ⟨j, hj⟩)
    (hS : ∀ v < (lvl .N30 i).ell, rdK s.M (cbS + 8 * v) = sAt es i v)
    (hmsg : MsgOk I msg (semXIR I (eqtIR (lvl .N30 i).ell cbS eqB) s) (lvl .N30 i).logN
      (mLog .N30 i) (nextMsg .N30 L es i)) :
    (∀ j < 2 ^ (lvl .N30 i).logN, (j ∈ consN .N30 L es i ↔
      rd (semXIR I (decFrontIR msg (lvl .N30 i).ell (lvl .N30 i).logN (lvl .N30 i).rows cs cb cbS)
        s).M (fbF + j) ≠ 0)) ∧
    (∀ y, regs ≤ y → (y < fbF ∨ (fbF + 2 ^ 18 ≤ y ∧ y < eqB) ∨ 2 ^ 24 ≤ y) →
      rd (semXIR I (decFrontIR msg (lvl .N30 i).ell (lvl .N30 i).logN (lvl .N30 i).rows cs cb cbS)
        s).M y = rd s.M y) ∧
    Inv (semXIR I (decFrontIR msg (lvl .N30 i).ell (lvl .N30 i).logN (lvl .N30 i).rows cs cb cbS)
        s).M := by
  have hs := hM.1
  simp only [regs] at hs hcS
  have hl6 : (lvl .N30 i).ell ≤ 6 := by interval_cases i <;> decide
  have hn1 : 1 ≤ (lvl .N30 i).logN := by interval_cases i <;> decide
  have hn18 : (lvl .N30 i).logN ≤ 18 := by interval_cases i <;> decide
  have hmn : mLog .N30 i ≤ (lvl .N30 i).logN := by interval_cases i <;> decide
  have hRe : (lvl .N30 i).rows = 2 ^ (lvl .N30 i).ell := rfl
  have hP : 2 ^ (lvl .N30 i).logN ≤ 2 ^ 18 := Nat.pow_le_pow_right (by norm_num) hn18
  have hPl : 2 ^ (lvl .N30 i).ell ≤ 2 ^ 6 := Nat.pow_le_pow_right (by norm_num) hl6
  have hmem : memX = 67108864 := rfl
  have etb : tb0 = 1048576 := rfl
  have efb : fbF = 2359296 := rfl
  have eqb : eqB = 8421376 := rfl
  have exb : xbM = 8454144 := rfl
  have eyb : ybM = 8978432 := rfl
  have dX : tb0 + 800 ≤ xbM := by decide
  have dY : tb0 + 800 ≤ ybM := by decide
  -- the `eq` table
  rw [decFrontIR, semXIR_seq]
  obtain ⟨e1, e2, hM1⟩ := eqtIR_sem I s hM (ℓ := (lvl .N30 i).ell) (cb := cbS) (eb := eqB)
    (S := sAt es i) (by omega) (by simp only [regs]; omega) (by omega) (by simp only [regs]; omega)
    (by omega) (by omega) (.inl (by omega)) hS
  have z1 := size_sem I (eqtIR (lvl .N30 i).ell cbS eqB) s
  have h256 : 4 * 2 ^ (lvl .N30 i).ell ≤ 256 := by
    have := Nat.mul_le_mul_left 4 hPl; simpa using this
  have e2' : ∀ y, regs ≤ y → (y < eqB ∨ eqB + 256 ≤ y) →
      rd (semXIR I (eqtIR (lvl .N30 i).ell cbS eqB) s).M y = rd s.M y := fun y hy h =>
    e2 y hy (h.imp_right fun h' => le_trans (Nat.add_le_add_left h256 _) h')
  have hmsg' := hmsg
  generalize semXIR I (eqtIR (lvl .N30 i).ell cbS eqB) s = s1 at e1 e2' hM1 z1 hmsg'
  clear e2
  -- the message
  rw [semXIR_seq]
  obtain ⟨m1, m2, hM2⟩ := hmsg' s1 hM1 rfl fun y _ _ => rfl
  have z2 := size_sem I msg s1
  generalize semXIR I msg s1 = s2 at m1 m2 hM2 z2
  -- `Enc` of `X`
  rw [semXIR_seq, semXIR_seq]
  obtain ⟨a1, a2, hM3⟩ := setA_sem I s2 hM2 xbM
  have z3 := size_sem I (setA xbM) s2
  generalize semXIR I (setA xbM) s2 = s3 at a1 a2 hM3 z3
  have h31 : ∀ y, regs ≤ y → (y < xbM ∨ ybM + 2 ^ 19 ≤ y) → (y < eqB ∨ eqB + 256 ≤ y) →
      rd s3.M y = rd s.M y := fun y hy h1 h2 => by rw [a2 y hy, m2 y hy h1, e2' y hy h2]
  have hT3 : ∀ v < 20, ∀ i' < 20, rdF s3.M (tb0 + 40 * v + 2 * i') = (wRow D logNMax v).getD i' 0 :=
    fun v hv i' hi' => by
      rw [← hT v hv i' hi']
      exact rdF_eq (h31 _ (by simp only [regs]; omega) (.inl (by omega)) (.inl (by omega)))
        (h31 _ (by simp only [regs]; omega) (.inl (by omega)) (.inl (by omega)))
  have hX3 : ∀ j < 2 ^ (lvl .N30 i).logN, rdF s3.M (xbM + 2 * j) =
      if h : j < 2 ^ mLog .N30 i then (fun x : Fin (2 ^ mLog .N30 i) => (nextMsg .N30 L es i x).f₀) ⟨j, h⟩
      else 0 := fun j hj => by
    rw [rdF_eq (a2 _ (by simp only [regs]; omega)) (a2 _ (by simp only [regs]; omega)), (m1 j hj).1]
    by_cases h : j < 2 ^ mLog .N30 i
    · rw [if_pos h, dif_pos h]
    · rw [if_neg h, dif_neg h]
  have f1 := fwdIR_enc I s3 hM3 (A := xbM) (tb := tb0) hn1 (by omega) hmn
    (by simp only [regs]; omega) (by omega) (by omega) (by simp only [regs]; omega)
    (by omega) (.inl dX) a1 hT3
    (fun x : Fin (2 ^ mLog .N30 i) => (nextMsg .N30 L es i x).f₀) hX3
  obtain ⟨-, f2, hM4⟩ := fwdIR_sem I s3 hM3 (A := xbM) (tb := tb0) hn1 (by omega)
    (by simp only [regs]; omega) (by omega) (by omega) (by simp only [regs]; omega)
    (by omega) (.inl dX) a1 hT3 (Y := fun j => if h : j < 2 ^ mLog .N30 i then
      (fun x : Fin (2 ^ mLog .N30 i) => (nextMsg .N30 L es i x).f₀) ⟨j, h⟩ else 0) hX3
  have z4 := size_sem I (fwdIR (lvl .N30 i).logN tb0) s3
  generalize semXIR I (fwdIR (lvl .N30 i).logN tb0) s3 = s4 at f1 f2 hM4 z4
  -- `Enc` of `Y`
  rw [semXIR_seq, semXIR_seq]
  obtain ⟨b1, b2, hM5⟩ := setA_sem I s4 hM4 ybM
  have z5 := size_sem I (setA ybM) s4
  generalize semXIR I (setA ybM) s4 = s5 at b1 b2 hM5 z5
  have hT5 : ∀ v < 20, ∀ i' < 20, rdF s5.M (tb0 + 40 * v + 2 * i') = (wRow D logNMax v).getD i' 0 :=
    fun v hv i' hi' => by
      rw [← hT3 v hv i' hi']
      exact rdF_eq ((b2 _ (by simp only [regs]; omega)).trans
          (f2 _ (by simp only [regs]; omega) (.inl (by omega))))
        ((b2 _ (by simp only [regs]; omega)).trans (f2 _ (by simp only [regs]; omega) (.inl (by omega))))
  have hY5 : ∀ j < 2 ^ (lvl .N30 i).logN, rdF s5.M (ybM + 2 * j) =
      if h : j < 2 ^ mLog .N30 i then (fun x : Fin (2 ^ mLog .N30 i) => (nextMsg .N30 L es i x).f₁) ⟨j, h⟩
      else 0 := fun j hj => by
    rw [rdF_eq ((b2 _ (by simp only [regs]; omega)).trans
        (f2 _ (by simp only [regs]; omega) (.inr (by omega))))
      ((b2 _ (by simp only [regs]; omega)).trans (f2 _ (by simp only [regs]; omega) (.inr (by omega)))),
      rdF_eq (a2 _ (by simp only [regs]; omega)) (a2 _ (by simp only [regs]; omega)), (m1 j hj).2]
    by_cases h : j < 2 ^ mLog .N30 i
    · rw [if_pos h, dif_pos h]
    · rw [if_neg h, dif_neg h]
  have g1 := fwdIR_enc I s5 hM5 (A := ybM) (tb := tb0) hn1 (by omega) hmn
    (by simp only [regs]; omega) (by omega) (by omega) (by simp only [regs]; omega)
    (by omega) (.inl dY) b1 hT5
    (fun x : Fin (2 ^ mLog .N30 i) => (nextMsg .N30 L es i x).f₁) hY5
  obtain ⟨-, g2, hM6⟩ := fwdIR_sem I s5 hM5 (A := ybM) (tb := tb0) hn1 (by omega)
    (by simp only [regs]; omega) (by omega) (by omega) (by simp only [regs]; omega)
    (by omega) (.inl dY) b1 hT5 (Y := fun j => if h : j < 2 ^ mLog .N30 i then
      (fun x : Fin (2 ^ mLog .N30 i) => (nextMsg .N30 L es i x).f₁) ⟨j, h⟩ else 0) hY5
  have z6 := size_sem I (fwdIR (lvl .N30 i).logN tb0) s5
  generalize semXIR I (fwdIR (lvl .N30 i).logN tb0) s5 = s6 at g1 g2 hM6 z6
  -- the heap of `s6`
  have h6 : ∀ y, regs ≤ y → (y < xbM ∨ ybM + 2 ^ 19 ≤ y) →
      (y < eqB ∨ eqB + 256 ≤ y) → rd s6.M y = rd s.M y := fun y hy h1 h2 => by
    rw [g2 y hy (by omega), b2 y hy, f2 y hy (by omega), h31 y hy h1 h2]
  have hb6 : ∀ y, cb ≤ y → rd s6.M y = rd s.M y := fun y hy =>
    h6 y ((show regs ≤ 2 ^ 24 by decide).trans (hcb.trans hy))
      (.inr ((show ybM + 2 ^ 19 ≤ 2 ^ 24 by decide).trans (hcb.trans hy)))
      (.inr ((show eqB + 256 ≤ 2 ^ 24 by decide).trans (hcb.trans hy)))
  have hW6 : ∀ j (hj : j < 2 ^ (lvl .N30 i).logN) (r : Fin (lvl .N30 i).rows),
      rdF s6.M (cb + cs * j + 2 * r) = wordOf .N30 L es i r ⟨j, hj⟩ := fun j hj r => by
    rw [← hW j hj r]
    have l1 : cb ≤ cb + cs * j + 2 * r := (Nat.le_add_right cb _).trans (Nat.le_add_right _ _)
    exact rdF_eq (hb6 _ l1) (hb6 _ (l1.trans (Nat.le_add_right _ _)))
  have hE6 : ∀ r < (lvl .N30 i).rows, rdK s6.M (eqB + 4 * r) = eqBits (sAt es i) (lvl .N30 i).ell r :=
    fun r hr => by
      rw [← e1 r (by rw [← hRe]; exact hr)]
      refine rdK_eq fun t ht => ?_
      have hr64 : r < 64 := lt_of_lt_of_le hr (by rw [hRe]; simpa using hPl)
      rw [g2 _ (by simp only [regs]; omega) (by omega), b2 _ (by simp only [regs]; omega),
        f2 _ (by simp only [regs]; omega) (by omega), a2 _ (by simp only [regs]; omega),
        m2 _ (by simp only [regs]; omega) (.inl (by omega))]
  have hX6 : ∀ j < 2 ^ (lvl .N30 i).logN,
      rdF s6.M (xbM + 2 * j) = encF (mLog .N30 i) (fun x => (nextMsg .N30 L es i x).f₀) j :=
    fun j hj => by
      rw [← f1 j hj]
      exact rdF_eq ((g2 _ (by simp only [regs]; omega) (.inl (by omega))).trans
          (b2 _ (by simp only [regs]; omega)))
        ((g2 _ (by simp only [regs]; omega) (.inl (by omega))).trans (b2 _ (by simp only [regs]; omega)))
  -- the flags
  obtain ⟨k1, k2, hM7⟩ := flagIR_sem I s6 hM6 (n := 2 ^ (lvl .N30 i).logN) (R := (lvl .N30 i).rows)
    (cs := cs) (cb := cb) (eb := eqB) (xb := xbM) (yb := ybM) (fb := fbF) (by omega) (by omega) hcs
    (by simp only [regs]; omega) hcb2 (by simp only [regs]; omega) (by omega)
    (by simp only [regs]; omega) (by omega) (by simp only [regs]; omega) (by omega)
    (by simp only [regs]; omega) (by omega) (by omega) (.inr (by omega)) (.inr (by omega))
    (.inr (by omega)) (.inr (by omega))
  have hc := flagV_consSet (M := s6.M) (cs := cs) (cb := cb) (eb := eqB) (xb := xbM) (yb := ybM)
    hW6 hE6 hX6 g1
  refine ⟨fun j hj => by rw [k1 j hj]; exact hc j hj, fun y hy hy2 => ?_, hM7⟩
  rw [k2 y hy (by omega), h6 y hy (by omega) (by omega)]

/-! ## One level -/

open FR.Snd in
/-- **The decode of level `i`** (`κ = N30`): the front half (`eq` table, the next message's rows
by `msg`, `Enc`, the flags), then the back half (scan, interpolation, butterflies) into `ob`. -/
def decLvIR (msg : XIR) (i cs cb cbS ob : ℕ) : XIR :=
  .seq (decFrontIR msg (lvl .N30 i).ell (lvl .N30 i).logN (lvl .N30 i).rows cs cb cbS)
    (decBackIR (2 ^ (lvl .N30 i).logN) (mLog .N30 i) (lvl .N30 i).rows cs cb ob)

open FR.Snd in
/-- **One level decodes on the machine** (BLUEPRINT §6.2 step 4, `level_decode`): with the basis
table at `tb0`, level `i`'s word at `cb + cs·j + 2r`, P1.i's challenges at `cbS`, a message step
that lays out `nextMsg i`, a close word and `A_c = jointAgree` (what `final` hands over), row `r`
of the decoded message sits at `ob + 2kr` as the `F` values of S-G's `msgOf i r`; the heap below
`jb0`, between `chB` and `eqB`, and from `2^24` on outside the rows, is kept. -/
theorem decLv_sem (I : Array Word) (s : St) (hM : Inv s.M) {L es : Log} {i cs cb cbS ob : ℕ}
    {msg : XIR} (hi : i < 5) (hfar : ¬ farL .N30 L es i)
    (hA : consSet .N30 L es i = jointAgree (wordK .N30 L es i) (decodeL .N30 L es i))
    (hsz : memX ≤ s.M.size) (hcs : 2 * (lvl .N30 i).rows ≤ cs) (hcs2 : cs ≤ 128)
    (hcb : 2 ^ 24 ≤ cb) (hcb2 : cb + 128 * 2 ^ 20 + 256 < 2 ^ 64)
    (hcS : regs ≤ cbS) (hcS2 : cbS + 8 * (lvl .N30 i).ell + 4 ≤ eqB)
    (hL : BaryLay (2 ^ mLog .N30 i) (lvl .N30 i).rows jb0 djb0 wb0 eb0 cb ob tb0)
    (hob : ob + 2 * 2 ^ mLog .N30 i * (lvl .N30 i).rows ≤ memX)
    (hobc : ob + 2 * 2 ^ mLog .N30 i * (lvl .N30 i).rows ≤ chB ∨ 2 ^ 24 ≤ ob)
    (hT : ∀ v < 20, ∀ i < 20, rdF s.M (tb0 + 40 * v + 2 * i) = (wRow D logNMax v).getD i 0)
    (hW : ∀ j (hj : j < 2 ^ (lvl .N30 i).logN) (r : Fin (lvl .N30 i).rows),
      rdF s.M (cb + cs * j + 2 * r) = wordOf .N30 L es i r ⟨j, hj⟩)
    (hS : ∀ v < (lvl .N30 i).ell, rdK s.M (cbS + 8 * v) = sAt es i v)
    (hmsg : MsgOk I msg (semXIR I (eqtIR (lvl .N30 i).ell cbS eqB) s) (lvl .N30 i).logN
      (mLog .N30 i) (nextMsg .N30 L es i)) :
    (∀ r < (lvl .N30 i).rows, ∀ x < 2 ^ mLog .N30 i,
      algebraMap F K (rdF (semXIR I (decLvIR msg i cs cb cbS ob) s).M
        (ob + 2 * 2 ^ mLog .N30 i * r + 2 * x)) = msgOf .N30 L es i r x) ∧
    (∀ y, regs ≤ y → (y < jb0 ∨ (chB ≤ y ∧ y < eqB) ∨
        (2 ^ 24 ≤ y ∧ (y < ob ∨ ob + 2 * 2 ^ mLog .N30 i * (lvl .N30 i).rows ≤ y))) →
      rd (semXIR I (decLvIR msg i cs cb cbS ob) s).M y = rd s.M y) ∧
    Inv (semXIR I (decLvIR msg i cs cb cbS ob) s).M := by
  have hn18 : (lvl .N30 i).logN ≤ 18 := by interval_cases i <;> decide
  have hP : 2 ^ (lvl .N30 i).logN ≤ 2 ^ 18 := Nat.pow_le_pow_right (by norm_num) hn18
  have hcbx : cb + cs * 2 ^ (lvl .N30 i).logN + 2 < 2 ^ 64 := by
    have : cs * 2 ^ (lvl .N30 i).logN ≤ 128 * 2 ^ 20 := Nat.mul_le_mul hcs2 (hP.trans (by norm_num))
    omega
  obtain ⟨a1, a2, hM1⟩ := decFront_sem I s hM (L := L) (es := es) (i := i) (cs := cs) (cb := cb)
    (cbS := cbS) (msg := msg) hi hsz hcs hcb hcbx hcS hcS2 hT hW hS hmsg
  rw [decLvIR, semXIR_seq]
  have z1 := size_sem I (decFrontIR msg (lvl .N30 i).ell (lvl .N30 i).logN (lvl .N30 i).rows cs cb
    cbS) s
  generalize semXIR I (decFrontIR msg (lvl .N30 i).ell (lvl .N30 i).logN (lvl .N30 i).rows cs cb
    cbS) s = s1 at a1 a2 hM1 z1
  have hb1 : ∀ y, cb ≤ y → rd s1.M y = rd s.M y := fun y hy =>
    a2 y ((show regs ≤ 2 ^ 24 by decide).trans (hcb.trans hy)) (.inr (.inr (hcb.trans hy)))
  have hT1 : ∀ v < 20, ∀ i' < 20, rdF s1.M (tb0 + 40 * v + 2 * i') = (wRow D logNMax v).getD i' 0 :=
    fun v hv i' hi' => by
      rw [← hT v hv i' hi']
      have l1 : tb0 + 40 * v + 2 * i' + 1 < fbF := by simp only [tb0, fbF]; omega
      exact rdF_eq (a2 _ (by simp only [regs, tb0]; omega) (.inl (by omega)))
        (a2 _ (by simp only [regs, tb0]; omega) (.inl l1))
  have hW1 : ∀ j (hj : j < 2 ^ (lvl .N30 i).logN) (r : Fin (lvl .N30 i).rows),
      rdF s1.M (cb + cs * j + 2 * r) = wordOf .N30 L es i r ⟨j, hj⟩ := fun j hj r => by
    rw [← hW j hj r]
    have l1 : cb ≤ cb + cs * j + 2 * r := (Nat.le_add_right cb _).trans (Nat.le_add_right _ _)
    exact rdF_eq (hb1 _ l1) (hb1 _ (l1.trans (Nat.le_add_right _ _)))
  obtain ⟨b1, b2, hM2⟩ := decBack_sem I s1 hM1 (L := L) (es := es) (i := i) (cs := cs) (cb := cb)
    (ob := ob) hi hfar hA (by rw [z1]; exact hsz) hL hcb2 hcs2 hob hT1 hW1 a1
  refine ⟨b1, fun y hy hy2 => ?_, hM2⟩
  obtain ⟨-, -, -, -, -, heo, -⟩ := hL
  have ejb : jb0 = 2097152 := rfl
  have edj : djb0 = 4194304 := rfl
  have eeb : eb0 = 5242880 := rfl
  have efb : fbF = 2359296 := rfl
  have ech : chB = 8388608 := rfl
  have eqb : eqB = 8421376 := rfl
  have hm17 : mLog .N30 i ≤ 17 := by interval_cases i <;> decide
  have hk : 2 ^ mLog .N30 i ≤ 2 ^ 17 := Nat.pow_le_pow_right (by norm_num) hm17
  rw [b2 y hy (by omega), a2 y hy (by omega)]

/-! ## The levels' layouts and message steps -/

open FR.Snd

/-- **The layout of levels 1–4**: the word at `stB`, the decoded rows at `obL`. -/
theorem layLv {i : ℕ} (hi1 : 1 ≤ i) (hi : i ≤ 4) :
    BaryLay (2 ^ mLog .N30 i) (lvl .N30 i).rows jb0 djb0 wb0 eb0 stB obL tb0 := by
  interval_cases i <;>
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide

/-- **The layout of level 0**: the word at `colBase`, the decoded rows at `ob0` (`lay0`). -/
theorem layLv0 : BaryLay (2 ^ mLog .N30 0) (lvl .N30 0).rows jb0 djb0 wb0 eb0 colBase ob0 tb0 :=
  lay0

/-- **Level 4's message step** (`msg4_next`): with the chain link `finalAt es x = finPi π x`. -/
theorem msgOk_four (c : Digest) (π : Proof) (L es : Log) (hs : π.size = piSize)
    (hfin : ∀ x < 32, finalAt es x = finPi π x) (s : St) (hsz : memX ≤ s.M.size) :
    MsgOk (tp c π L) (msgTIR 10 32 finW xbM ybM) s (lvl .N30 4).logN (mLog .N30 4)
      (nextMsg .N30 L es 4) := by
  intro s' hM' hsz' _
  have e : (lvl .N30 4).logN = 10 := rfl
  rw [e]
  have hX : xbM + 2 * 2 ^ 10 ≤ s'.M.size := by rw [hsz']; exact le_trans (by decide) hsz
  have hY : ybM + 2 * 2 ^ 10 ≤ s'.M.size := by rw [hsz']; exact le_trans (by decide) hsz
  have r1 : regs ≤ xbM := by decide
  have r2 : regs ≤ ybM := by decide
  have b1 : xbM + 2 * 2 ^ 10 < 2 ^ 64 := by decide
  have b2 : ybM + 2 * 2 ^ 10 < 2 ^ 64 := by decide
  have d : xbM + 2 * 2 ^ 10 ≤ ybM := by decide
  obtain ⟨-, h2, h3⟩ := msgTIR_sem (tp c π L) s' hM' (n := 10) (k := 32) (tw := finW) (xb := xbM)
    (yb := ybM) (by norm_num) (by norm_num) (by simp only [finW, finOff]; norm_num) r1 r2 b1 b2 hX hY
    (.inl d)
  refine ⟨msg4_next c π L es hs hfin s' hM' r1 r2 b1 b2 hX hY (.inl d), fun y hy hy2 => ?_, h3⟩
  exact h2 y hy (hy2.imp_right fun h => le_trans (by decide) h)
    (hy2.imp (fun h => lt_of_lt_of_le h (by decide)) fun h => le_trans (by decide) h)

/-- **The message step of levels 0–3** (`msgH_next`): if level `i + 1`'s decoded rows sit at
`obL` as the `F` values of `msgOf (i + 1)`, `msgHIR` lays out `nextMsg i`. -/
theorem msgOk_lower {L es : Log} {i : ℕ} (hi : i < 4) (I : Array Word) (s : St)
    (hsz : memX ≤ s.M.size)
    (hdec : ∀ r < 16, ∀ x < 2 ^ mLog .N30 (i + 1),
      algebraMap F K (rdF s.M (obL + 2 * 2 ^ mLog .N30 (i + 1) * r + 2 * x)) =
        msgOf .N30 L es (i + 1) r x)
    (hF : ∀ r x, msgOf .N30 L es (i + 1) r x = algebraMap F K (msgOf .N30 L es (i + 1) r x).f₀) :
    MsgOk I (msgHIR (lvl .N30 i).logN (2 ^ mLog .N30 (i + 1)) obL xbM ybM) s (lvl .N30 i).logN
      (mLog .N30 i) (nextMsg .N30 L es i) := by
  intro s' hM' hsz' hag
  have hn18 : (lvl .N30 i).logN ≤ 18 := by interval_cases i <;> decide
  have hP : 2 ^ (lvl .N30 i).logN ≤ 2 ^ 18 := Nat.pow_le_pow_right (by norm_num) hn18
  have hm : mLog .N30 (i + 1) ≤ 14 := by interval_cases i <;> decide
  have hk : 2 ^ mLog .N30 (i + 1) ≤ 2 ^ 14 := Nat.pow_le_pow_right (by norm_num) hm
  have hk8 : 8 * 2 ^ mLog .N30 (i + 1) ≤ 2 ^ (lvl .N30 i).logN := by interval_cases i <;> decide
  have hmem : memX = 67108864 := rfl
  have exb : xbM = 8454144 := rfl
  have eyb : ybM = 8978432 := rfl
  have eob : obL = 6291456 := rfl
  have eqb : eqB = 8421376 := rfl
  have hdec' : ∀ r < 16, ∀ x < 2 ^ mLog .N30 (i + 1),
      algebraMap F K (rdF s'.M (obL + 2 * 2 ^ mLog .N30 (i + 1) * r + 2 * x)) =
        msgOf .N30 L es (i + 1) r x := fun r hr x hx => by
    rw [← hdec r hr x hx]
    have : 2 * 2 ^ mLog .N30 (i + 1) * r ≤ 2 * 2 ^ 14 * 16 :=
      Nat.mul_le_mul (Nat.mul_le_mul_left 2 hk) hr.le
    congr 1
    exact rdF_eq (hag _ (by simp only [regs]; omega) (.inl (by omega)))
      (hag _ (by simp only [regs]; omega) (.inl (by omega)))
  obtain ⟨-, h2, h3⟩ := msgHIR_sem I s' hM' (n := (lvl .N30 i).logN) (k := 2 ^ mLog .N30 (i + 1))
    (ob := obL) (xb := xbM) (yb := ybM) (by omega) hk8 (by simp only [regs]; omega) (by omega)
    (by simp only [regs]; omega) (by simp only [regs]; omega) (by omega) (by omega) (by omega)
    (by omega) (.inl (by omega)) (.inl (by omega)) (.inl (by omega))
  refine ⟨msgH_next hi I s' hM' hdec' hF (by simp only [regs]; omega) (by omega)
    (by simp only [regs]; omega) (by simp only [regs]; omega) (by omega) (by omega) (by omega)
    (by omega) (.inl (by omega)) (.inl (by omega)) (.inl (by omega)), fun y hy hy2 => ?_, h3⟩
  exact h2 y hy (by omega) (by omega)

/-! ## The levels instantiated -/

/-- P1.i's challenges in the chain's answers: `s_v` at `cbS i + 8v` (`sAt_words`). -/
def cbS (i : ℕ) : ℕ := ansB + 4 * (phStart (26 + 5 * i) + 1)

theorem phStart_P1 {i : ℕ} (hi : i < 5) : phStart (26 + 5 * i) ≤ 434 := by
  unfold phStart; rw [fsStarts_eq]; interval_cases i <;> decide

theorem cbS_le {i : ℕ} (hi : i < 5) : regs ≤ cbS i ∧ cbS i + 8 * (lvl .N30 i).ell + 4 ≤ eqB := by
  have h := phStart_P1 hi
  have hl : (lvl .N30 i).ell ≤ 6 := by interval_cases i <;> decide
  have ea : ansB = 8392704 := rfl
  have eq : eqB = 8421376 := rfl
  simp only [cbS, regs]; omega

/-- **Levels 1–4 decode** (`decLv_sem` on the layout of `readLv`: the word at `stB`, 32 words a
position; the rows at `obL`). -/
theorem decLvU_sem (I : Array Word) (s : St) (hM : Inv s.M) {L es : Log} {i : ℕ} {msg : XIR}
    (hi1 : 1 ≤ i) (hi : i ≤ 4) (hfar : ¬ farL .N30 L es i)
    (hA : consSet .N30 L es i = jointAgree (wordK .N30 L es i) (decodeL .N30 L es i))
    (hsz : memX ≤ s.M.size)
    (hT : ∀ v < 20, ∀ i < 20, rdF s.M (tb0 + 40 * v + 2 * i) = (wRow D logNMax v).getD i 0)
    (hW : ∀ j (hj : j < 2 ^ (lvl .N30 i).logN) (r : Fin (lvl .N30 i).rows),
      rdF s.M (stB + 32 * j + 2 * r) = wordOf .N30 L es i r ⟨j, hj⟩)
    (hS : ∀ v < (lvl .N30 i).ell, rdK s.M (cbS i + 8 * v) = sAt es i v)
    (hmsg : MsgOk I msg (semXIR I (eqtIR (lvl .N30 i).ell (cbS i) eqB) s) (lvl .N30 i).logN
      (mLog .N30 i) (nextMsg .N30 L es i)) :
    (∀ r < (lvl .N30 i).rows, ∀ x < 2 ^ mLog .N30 i,
      algebraMap F K (rdF (semXIR I (decLvIR msg i 32 stB (cbS i) obL) s).M
        (obL + 2 * 2 ^ mLog .N30 i * r + 2 * x)) = msgOf .N30 L es i r x) ∧
    (∀ y, regs ≤ y → (y < jb0 ∨ (chB ≤ y ∧ y < eqB) ∨ 2 ^ 24 ≤ y) →
      rd (semXIR I (decLvIR msg i 32 stB (cbS i) obL) s).M y = rd s.M y) ∧
    Inv (semXIR I (decLvIR msg i 32 stB (cbS i) obL) s).M := by
  have hi5 : i < 5 := by omega
  have hR : (lvl .N30 i).rows = 16 := by interval_cases i <;> rfl
  have hm : 2 ^ mLog .N30 i ≤ 2 ^ 14 := by interval_cases i <;> decide
  have hob : obL + 2 * 2 ^ mLog .N30 i * (lvl .N30 i).rows ≤ chB := by
    rw [hR]; have : 2 * 2 ^ mLog .N30 i * 16 ≤ 2 * 2 ^ 14 * 16 :=
      Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ hm)
    exact le_trans (Nat.add_le_add_left this _) (by decide)
  obtain ⟨b1, b2, b3⟩ := decLv_sem I s hM (cs := 32) (cb := stB) (cbS := cbS i) (ob := obL)
    hi5 hfar hA hsz (by rw [hR]) (by norm_num) (by decide) (by decide) (cbS_le hi5).1
    (cbS_le hi5).2 (layLv hi1 hi) (hob.trans (by decide)) (.inl hob) hT hW hS hmsg
  refine ⟨b1, fun y hy hy2 => b2 y hy ?_, b3⟩
  rcases hy2 with h | h | h
  · exact .inl h
  · exact .inr (.inl h)
  · exact .inr (.inr ⟨h, .inr (le_trans (hob.trans (by decide)) h)⟩)

/-- **Level 0 decodes** (`decLv_sem` on the layout of `read0`: the word at `colBase`, 128 words
a position; the rows at `ob0`, row `c` at `ob0 + 2^18 c`). -/
theorem decLv0_sem (I : Array Word) (s : St) (hM : Inv s.M) {L es : Log} {msg : XIR}
    (hfar : ¬ farL .N30 L es 0)
    (hA : consSet .N30 L es 0 = jointAgree (wordK .N30 L es 0) (decodeL .N30 L es 0))
    (hsz : memX ≤ s.M.size)
    (hT : ∀ v < 20, ∀ i < 20, rdF s.M (tb0 + 40 * v + 2 * i) = (wRow D logNMax v).getD i 0)
    (hW : ∀ j (hj : j < 2 ^ (lvl .N30 0).logN) (r : Fin (lvl .N30 0).rows),
      rdF s.M (colBase + 128 * j + 2 * r) = wordOf .N30 L es 0 r ⟨j, hj⟩)
    (hS : ∀ v < (lvl .N30 0).ell, rdK s.M (cbS 0 + 8 * v) = sAt es 0 v)
    (hmsg : MsgOk I msg (semXIR I (eqtIR (lvl .N30 0).ell (cbS 0) eqB) s) (lvl .N30 0).logN
      (mLog .N30 0) (nextMsg .N30 L es 0)) :
    (∀ r < (lvl .N30 0).rows, ∀ x < 2 ^ mLog .N30 0,
      algebraMap F K (rdF (semXIR I (decLvIR msg 0 128 colBase (cbS 0) ob0) s).M
        (ob0 + 2 * 2 ^ mLog .N30 0 * r + 2 * x)) = msgOf .N30 L es 0 r x) ∧
    (∀ y, regs ≤ y → (y < jb0 ∨ (chB ≤ y ∧ y < eqB) ∨ 2 ^ 25 ≤ y) →
      rd (semXIR I (decLvIR msg 0 128 colBase (cbS 0) ob0) s).M y = rd s.M y) ∧
    Inv (semXIR I (decLvIR msg 0 128 colBase (cbS 0) ob0) s).M := by
  obtain ⟨b1, b2, b3⟩ := decLv_sem I s hM (cs := 128) (cb := colBase) (cbS := cbS 0) (ob := ob0)
    (by norm_num) hfar hA hsz (by decide) le_rfl (by decide) (by decide) (cbS_le (by norm_num)).1
    (cbS_le (by norm_num)).2 layLv0 (by decide) (.inr (by decide)) hT hW hS hmsg
  refine ⟨b1, fun y hy hy2 => b2 y hy ?_, b3⟩
  rcases hy2 with h | h | h
  · exact .inl h
  · exact .inr (.inl h)
  · exact .inr (.inr ⟨le_trans (by decide) h, .inr (le_trans (by decide) h)⟩)

end FR.X

end G6_FRXDecLv

section G6_FRXDec4Back

-- New for `flock-recursive` (BLUEPRINT revision 4.2, §6.2 step 4; stage S-H4, pass 2, item 2).

/-!
# The back half of one level's decode at revision 4.1's kinds: scan, `lagIR`, butterflies

`decBack4IR n m C c0 cs cb tb fb jb pb yb ob` is

`scanIR n 2^m fb jb ; lagIR 2^m C c0 jb pb yb ob cb cs ; bfRowsIR m ob tb C`:

the first `k = 2^m` flagged positions to `J`, the interpolation of the word's rows
`c₀ … c₀ + C − 1` (row `r` of position `j` at `cb + cs·j + 2r`) at the targets `0 … k − 1`, then
the butterflies on each of the `C` rows. Level 0 decodes rows 4–7 only (`c₀ = 4`, `C = 4`, the rows
the output reads); levels 1–4 decode all 16 rows (`c₀ = 0`, `C = 16`).

**The memory map is a parameter** (`BackLay4`): the basis table at `tb` (800 words), the flags at
`fb` (`n`), `J` at `jb` (`k`), the prefix table at `pb` (`k`), `Y` at `yb` (`2Ck`), the output at
`ob` (`2kC`, row `c` at `ob + 2kc`, plus `2k` words of slack), in this order; the word's column
store at `cb ≥ yb + 2Ck`.

**`decBack4_sem`**: if the flags mark `A_c` (`consN4`), the word is close and
`A_c = jointAgree`, then row `c` at `ob + 2kc` holds the `F` values of `T4.msgOf κ L es i (c₀ + c)`
(`level_decode4`). The heap outside `[jb, jb + k)` and `[pb, ob + 2kC)` is kept.
-/

namespace FR.X

open RecursionFast FR Finset FR.Snd.T4

-- G2: `entryK`/`storeM`/`runPrims` are never unfolded while unifying states (elaboration time).
attribute [local irreducible] entryK storeM runPrims

/-- **The back half's memory map** (`n` positions, `k` targets, `C` rows). -/
def BackLay4 (n k C tb fb jb pb yb ob : ℕ) : Prop :=
  regs ≤ tb ∧ tb + 800 ≤ fb ∧ fb + n ≤ jb ∧ jb + k ≤ pb ∧ pb + k ≤ yb ∧ yb + 2 * C * k ≤ ob ∧
    ob + 2 * k * (C + 1) + 2 < 2 ^ 64

/-- **The back half** at a 4.1 level: scan, interpolation of rows `c₀ … c₀ + C − 1`, butterflies. -/
def decBack4IR (n m C c0 cs cb tb fb jb pb yb ob : ℕ) : XIR :=
  .seq (scanIR n (2 ^ m) fb jb)
    (.seq (lagIR (2 ^ m) C c0 jb pb yb ob cb cs) (bfRowsIR m ob tb C))

theorem wf_decBack4IR (n m C c0 cs cb tb fb jb pb yb ob : ℕ) :
    WF (decBack4IR n m C c0 cs cb tb fb jb pb yb ob) :=
  ⟨wf_scanIR .., wf_lagIR .., wf_bfRowsIR ..⟩

theorem noLoopT_decBack4IR (n m C c0 cs cb tb fb jb pb yb ob : ℕ) :
    NoLoopT (decBack4IR n m C c0 cs cb tb fb jb pb yb ob) :=
  ⟨noLoopT_scanIR .., noLoopT_lagIR .., noLoopT_bfRowsIR ..⟩

theorem outs_decBack4IR (n m C c0 cs cb tb fb jb pb yb ob t : ℕ) :
    outs (decBack4IR n m C c0 cs cb tb fb jb pb yb ob) t = 0 := by
  simp only [decBack4IR, outs, outs_scanIR, outs_lagIR, outs_bfRowsIR]

/-- **The back half's cost** (exact): the scan `16 + 32n`, `lagIR` at `k = 2^m`, the butterflies. -/
theorem cost_decBack4IR (n m C c0 cs cb tb fb jb pb yb ob t : ℕ) (hn : n < 2 ^ 64) (hm : m < 64)
    (hC : C < 2 ^ 64) :
    cost (decBack4IR n m C c0 cs cb tb fb jb pb yb ob) t =
      (16 + n * 32) + (27 + 2 ^ m * (1122 + 72 * C) + (2 ^ m) ^ 2 * (101 + 40 * C)) +
        (1 + C * (17 + m * (741 * 2 ^ (m - 1) + 23))) + 2 := by
  have h1 : 2 ^ m < 2 ^ 64 := Nat.pow_lt_pow_right (by norm_num) hm
  have h2 : 2 ^ (m - 1) < 2 ^ 64 := Nat.pow_lt_pow_right (by norm_num) (by omega)
  simp only [decBack4IR, cost, cost_scanIR n _ fb jb t hn, cost_lagIR _ C c0 jb pb yb ob cb cs t h1 hC,
    cost_bfRowsIR m ob tb t h2 (by omega)]
  ring

/-- The level parameters the machine needs (every kind, every level). -/
theorem lv4_bounds (κ : Snd.CKind) {i : ℕ} (hi : i < 5) :
    1 ≤ Snd.T4.mLog κ i ∧ Snd.T4.mLog κ i ≤ 19 ∧ Snd.T4.mLog κ i ≤ (Snd.CKind.lv κ i).logN ∧
      (Snd.CKind.lv κ i).logN ≤ 20 := by
  rcases κ with (_|_|_) | (_|_|_) <;> interval_cases i <;> decide

/-- **The back half decodes** (`level_decode4`). -/
theorem decBack4_sem (I : Array Word) (s : St) (hM : Inv s.M) {κ : Snd.CKind} {L es : Log}
    {i C c0 cs cb tb fb jb pb yb ob : ℕ} (hi : i < 5) (hfar : ¬ Snd.T4.farL κ L es i)
    (hA : Snd.T4.consSet κ L es i = jointAgree (Snd.T4.wordK κ L es i) (Snd.T4.decodeL κ L es i))
    (hC1 : 1 ≤ C) (hC : C ≤ 16) (hcr : c0 + C ≤ (Snd.CKind.lv κ i).rows)
    (hL : BackLay4 (2 ^ (Snd.CKind.lv κ i).logN) (2 ^ Snd.T4.mLog κ i) C tb fb jb pb yb ob)
    (hcb : yb + 2 * C * 2 ^ Snd.T4.mLog κ i ≤ cb)
    (hcb2 : cb + cs * 2 ^ (Snd.CKind.lv κ i).logN + 2 * (c0 + C) + 2 < 2 ^ 64)
    (hsz : ob + 2 * 2 ^ Snd.T4.mLog κ i * (C + 1) ≤ s.M.size)
    (hT : ∀ v < 20, ∀ i < 20, rdF s.M (tb + 40 * v + 2 * i) = (wRow D logNMax v).getD i 0)
    (hW : ∀ j (hj : j < 2 ^ (Snd.CKind.lv κ i).logN) (r : Fin (Snd.CKind.lv κ i).rows),
      rdF s.M (cb + cs * j + 2 * r) = Snd.T4.wordOf κ L es i r ⟨j, hj⟩)
    (hF : ∀ j < 2 ^ (Snd.CKind.lv κ i).logN, (j ∈ consN4 κ L es i ↔ rd s.M (fb + j) ≠ 0)) :
    (∀ c < C, ∀ x < 2 ^ Snd.T4.mLog κ i,
      algebraMap F K (rdF (semXIR I (decBack4IR (2 ^ (Snd.CKind.lv κ i).logN) (Snd.T4.mLog κ i) C c0 cs cb
        tb fb jb pb yb ob) s).M (ob + 2 * 2 ^ Snd.T4.mLog κ i * c + 2 * x)) =
      Snd.T4.msgOf κ L es i (c0 + c) x) ∧
    (∀ y, regs ≤ y → (y < jb ∨ (jb + 2 ^ Snd.T4.mLog κ i ≤ y ∧ y < pb) ∨
        ob + 2 * 2 ^ Snd.T4.mLog κ i * C ≤ y) →
      rd (semXIR I (decBack4IR (2 ^ (Snd.CKind.lv κ i).logN) (Snd.T4.mLog κ i) C c0 cs cb
        tb fb jb pb yb ob) s).M y = rd s.M y) ∧
    Inv (semXIR I (decBack4IR (2 ^ (Snd.CKind.lv κ i).logN) (Snd.T4.mLog κ i) C c0 cs cb
        tb fb jb pb yb ob) s).M := by
  classical
  obtain ⟨htb, htf, hfj, hjp, hpy, hyo, ho2⟩ := hL
  obtain ⟨hm1, hm19, hmn, hn20⟩ := lv4_bounds κ hi
  have hs := hM.1
  simp only [regs] at hs htb
  have hP : 2 ^ (Snd.CKind.lv κ i).logN ≤ 2 ^ 20 := Nat.pow_le_pow_right (by norm_num) hn20
  have hPm : 2 ^ Snd.T4.mLog κ i ≤ 2 ^ (Snd.CKind.lv κ i).logN := Nat.pow_le_pow_right (by norm_num) hmn
  have hk1 : 1 ≤ 2 ^ Snd.T4.mLog κ i := Nat.one_le_two_pow
  have enM : nMax = 1048576 := rfl
  -- the agreement set is large enough
  have hcard : 2 ^ Snd.T4.mLog κ i ≤ (consN4 κ L es i).card := by
    obtain ⟨h1, -, -, hk', hn'⟩ := Snd.T4.lv_params κ hi
    obtain ⟨-, hJ⟩ := Snd.T4.decodeL_spec hfar
    rw [consN4, card_map, hA]
    have : Snd.T4.lvK κ i ≤ 2 ^ (Snd.CKind.lv κ i).logN - Snd.T4.lvE κ i := by rw [← hn']; omega
    rw [← hk']; exact this.trans hJ
  -- the scan
  rw [decBack4IR, semXIR_seq]
  obtain ⟨a1, a2, a3, hM1⟩ := scanIR_sem I s hM (n := 2 ^ (Snd.CKind.lv κ i).logN) (k := 2 ^ Snd.T4.mLog κ i)
    (fb := fb) (lb := jb) (f := fun j => rd s.M (fb + j)) (by simp only [regs]; omega)
    (by omega) (by omega) (by simp only [regs]; omega) (by omega) (by omega) (.inl hfj) (fun j _ => rfl)
  have z1 := size_sem I (scanIR (2 ^ (Snd.CKind.lv κ i).logN) (2 ^ Snd.T4.mLog κ i) fb jb) s
  generalize semXIR I (scanIR (2 ^ (Snd.CKind.lv κ i).logN) (2 ^ Snd.T4.mLog κ i) fb jb) s = s1 at a1 a2 a3 hM1 z1
  obtain ⟨SL, hSL⟩ : ∃ SL, SL = scanL (2 ^ (Snd.CKind.lv κ i).logN) fun j => rd s.M (fb + j) := ⟨_, rfl⟩
  rw [← hSL] at a1 a2
  obtain ⟨Jl, hJl⟩ : ∃ Jl, Jl = SL.take (2 ^ Snd.T4.mLog κ i) := ⟨_, rfl⟩
  have hfk : firstK (2 ^ (Snd.CKind.lv κ i).logN) (consN4 κ L es i) (2 ^ Snd.T4.mLog κ i) = Jl.toFinset := by
    rw [hJl, hSL]; exact firstK_scan hF
  have hlen : Jl.length = 2 ^ Snd.T4.mLog κ i := by
    have h1 := firstK_card (n := 2 ^ (Snd.CKind.lv κ i).logN) (A := consN4 κ L es i)
      (fun j hj => (mem_consN4.1 hj).1) hcard
    rw [hfk] at h1
    have h2 := List.toFinset_card_le Jl
    have h3 : Jl.length ≤ 2 ^ Snd.T4.mLog κ i := by rw [hJl]; exact List.length_take_le _ _
    omega
  have hlen0 : 2 ^ Snd.T4.mLog κ i ≤ SL.length := by
    have := List.length_take_le' (2 ^ Snd.T4.mLog κ i) SL
    rw [← hJl] at this; omega
  have hnd : Jl.Nodup := by
    rw [hJl, hSL]
    exact List.Nodup.sublist (List.take_sublist _ _) (List.Nodup.filter _ List.nodup_range)
  have hJmem : ∀ j ∈ Jl, j < 2 ^ (Snd.CKind.lv κ i).logN := fun j hj => by
    rw [hJl, hSL] at hj
    have := List.mem_of_mem_take hj
    simp only [scanL, List.mem_filter, List.mem_range] at this
    exact this.1
  have hJ1 : ∀ t < 2 ^ Snd.T4.mLog κ i, rd s1.M (jb + t) = jw Jl t := fun t ht => by
    rw [a2 t (by omega), jw, hJl, List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
      List.getElem?_take_of_lt (by omega)]
  have hget : ∀ t < 2 ^ Snd.T4.mLog κ i, Jl.getD t 0 < 2 ^ (Snd.CKind.lv κ i).logN := fun t ht =>
    hJmem _ (by rw [List.getD_eq_getElem _ _ (by omega)]; exact List.getElem_mem _)
  have k1 : ∀ y, regs ≤ y → (y < jb ∨ jb + 2 ^ Snd.T4.mLog κ i ≤ y) → rd s1.M y = rd s.M y := a3
  -- the interpolation
  rw [semXIR_seq]
  obtain ⟨b1, b2, hM2⟩ := lagIR_sem I s1 hM1 (k := 2 ^ Snd.T4.mLog κ i) (C := C) (c0 := c0) (cb := cb)
    (cs := cs) (Jl := Jl) hk1 (by omega) hC (by simp only [regs]; omega) hjp hpy hyo hcb
    (by rw [z1]; exact hsz) ho2 (fun t ht => by
      have : cs * Jl.getD t 0 ≤ cs * 2 ^ (Snd.CKind.lv κ i).logN := Nat.mul_le_mul_left _ (hget t ht).le
      omega) hJ1
  have z2 := size_sem I (lagIR (2 ^ Snd.T4.mLog κ i) C c0 jb pb yb ob cb cs) s1
  generalize semXIR I (lagIR (2 ^ Snd.T4.mLog κ i) C c0 jb pb yb ob cb cs) s1 = s2 at b1 b2 hM2 z2
  -- the butterflies
  have hT1 : ∀ v < 20, ∀ i' < 20, rdF s2.M (tb + 40 * v + 2 * i') = (wRow D logNMax v).getD i' 0 :=
    fun v hv i' hi' => by
      rw [← hT v hv i' hi']
      exact rdF_eq ((b2 _ (by simp only [regs]; omega) (.inl (by omega))).trans
          (k1 _ (by simp only [regs]; omega) (.inl (by omega))))
        ((b2 _ (by simp only [regs]; omega) (.inl (by omega))).trans
          (k1 _ (by simp only [regs]; omega) (.inl (by omega))))
  have hCk : 2 * 2 ^ Snd.T4.mLog κ i * (C + 1) = 2 * 2 ^ Snd.T4.mLog κ i * C + 2 * 2 ^ Snd.T4.mLog κ i :=
    Nat.mul_succ _ _
  obtain ⟨c1, c2, hM3⟩ := bfRows_sem I (m := Snd.T4.mLog κ i) (ob := ob) (tb := tb)
    (Y := fun c x => lagVal Jl (2 ^ Snd.T4.mLog κ i) x fun j => rdF s1.M (cb + cs * j + 2 * c0 + 2 * c))
    hm1 (by omega) (by simp only [regs]; omega) (by simp only [regs]; omega) (by omega) C s2 hM2
    (by omega) (by rw [z2, z1]; omega) (.inl (by omega)) hT1
    (fun c hc x hx => by rw [show ob + 2 * 2 ^ Snd.T4.mLog κ i * c + 2 * x =
      ob + 2 * x + 2 * 2 ^ Snd.T4.mLog κ i * c by ring]; exact b1 x hx c hc)
  refine ⟨fun c hc x hx => ?_, fun y hy hy2 => ?_, hM3⟩
  · rw [c1 c hc x hx]
    have hr : c0 + c < (Snd.CKind.lv κ i).rows := by omega
    have hY : (fun s' => lagVal Jl (2 ^ Snd.T4.mLog κ i) s' fun j => rdF s1.M (cb + cs * j + 2 * c0 + 2 * c)) =
        interpF D (firstK (2 ^ (Snd.CKind.lv κ i).logN) (consN4 κ L es i) (2 ^ Snd.T4.mLog κ i))
          (wordN4 κ L es i ⟨c0 + c, hr⟩) := by
      funext x'
      have hv := lagVal_eq hnd (fun j hj => lt_of_lt_of_le (hJmem j hj) (by omega)) (s := x')
        (fun j => rdF s1.M (cb + cs * j + 2 * c0 + 2 * c))
      rw [hlen] at hv
      rw [hv, hfk]
      refine interpF_congr D _ (fun j hj => ?_) x'
      have hjn := hJmem j (List.mem_toFinset.1 hj)
      have hc' : cs * j ≤ cs * (2 ^ (Snd.CKind.lv κ i).logN) := Nat.mul_le_mul_left _ hjn.le
      rw [show cb + cs * j + 2 * c0 + 2 * c = cb + cs * j + 2 * (c0 + c) by ring,
        rdF_eq (k1 _ (by simp only [regs]; omega) (.inr (by omega)))
        (k1 _ (by simp only [regs]; omega) (.inr (by omega)))]
      rw [show cb + cs * j + 2 * (c0 + c) = cb + cs * j + 2 * ((⟨c0 + c, hr⟩ : Fin _) : ℕ) from rfl,
        hW j hjn ⟨c0 + c, hr⟩]
      simp only [wordN4, hjn, dite_true]
    rw [hY]
    exact level_decode4 hi hfar hA ⟨c0 + c, hr⟩ ⟨x, hx⟩
  · rw [c2 y hy (by omega), b2 y hy (by omega), k1 y hy (by omega)]

/-! ## Controls and the level-0 cost at `m = 32` -/

/-- (+) **A level-0 memory map at `m = 32` fits** (`n = 2^20` positions, `k = 2^19`, rows 4–7):
basis table `2^20`, flags `2^21`, `J` `2^22`, `P` `2^22 + 2^19`, `Y` `2^23`, output `2^23 + 2^22`
(the word's columns may start at `2^23 + 2^22`). -/
theorem backLay4_m32 : BackLay4 (2 ^ 20) (2 ^ 19) 4 (2 ^ 20) (2 ^ 21) (2 ^ 22) (2 ^ 22 + 2 ^ 19) (2 ^ 23)
    (2 ^ 23 + 2 ^ 22) := by
  unfold BackLay4; norm_num [regs]

/-- (−) **`BackLay4` rejects overlapping regions**: the output on top of `Y` fails. -/
theorem not_backLay4_overlap : ¬ BackLay4 (2 ^ 20) (2 ^ 19) 4 (2 ^ 20) (2 ^ 21) (2 ^ 22)
    (2 ^ 22 + 2 ^ 19) (2 ^ 23) (2 ^ 23) := by
  unfold BackLay4; norm_num [regs]

/-- **Level 0's back half at `m = 32`** (rows 4–7): `7.18 · 10^13` steps, within 3.x's `decBudget`
(`2.11 · 10^14 + 8,176 t`) with room for the other levels (`logs/S-H4/fuel-check4.txt`). -/
theorem cost_back0_m32 (cs cb tb fb jb pb yb ob t : ℕ) :
    cost (decBack4IR (2 ^ 20) 19 4 4 cs cb tb fb jb pb yb ob) t = 71758669416262 := by
  rw [cost_decBack4IR _ _ _ _ _ _ _ _ _ _ _ _ _ (by norm_num) (by norm_num) (by norm_num)]
  norm_num

end FR.X

end G6_FRXDec4Back

section G6_FRXDec4Front

-- New for `flock-recursive` (BLUEPRINT revision 4.2, §6.2 step 4; stage S-H4, pass 2, item 2′).

/-!
# The front half of one level's decode at revision 4.1's kinds, on a parametric memory map

`decFront4IR msg ℓ n R cs cb cbS tb fb eb xb yb` is 3.x's front half
(`eqtIR ; msg ; fwdIR ×2 ; flagIR`) with every base a parameter: the `eq` table of P1.i's `ℓ`
challenges (read at `cbS`) to `eb`, the next message's coordinate rows (`msg`) to `xb`, `yb`,
`Enc` of each, the agreement flags to `fb`.

**The memory map** (`FrontLay4`): the basis table at `tb` (800 words), the flags at `fb` (`n`), the
`eq` table at `eb` (256), `X` at `xb` (`2n`), `Y` at `yb` (`2n`), in this order; the word's column
store at `cb ≥ yb + 2n`; the challenges at `cbS` below `eb` (outside the flags).

**`decFront4_sem`** (3.x's `decFront_sem` over `CKind`): the flag at `fb + j` is nonzero iff
`j ∈ A_c` (`flagV_consSet4`). **`MsgOk4`** is 3.x's `MsgOk` at the map's `eb`, `xb`, `yb`.
-/

namespace FR.X

open RecursionFast FR Finset

-- G2: `entryK`/`storeM`/`runPrims` are never unfolded while unifying states (elaboration time).
attribute [local irreducible] entryK storeM runPrims

/-- **The agreement flag marks `A_c`** at a 4.1 kind (3.x's `flagV_consSet`). -/
theorem flagV_consSet4 {M : Mem} {κ : Snd.CKind} {L es : Log} {i cs cb eb xb yb : ℕ}
    (hW : ∀ j (hj : j < 2 ^ (Snd.CKind.lv κ i).logN) (r : Fin (Snd.CKind.lv κ i).rows),
      rdF M (cb + cs * j + 2 * r) = Snd.T4.wordOf κ L es i r ⟨j, hj⟩)
    (hE : ∀ r < (Snd.CKind.lv κ i).rows,
      rdK M (eb + 4 * r) = eqBits (Snd.T4.sAt es i) (Snd.CKind.lv κ i).ell r)
    (hX : ∀ j < 2 ^ (Snd.CKind.lv κ i).logN,
      rdF M (xb + 2 * j) = encF (Snd.T4.mLog κ i) (fun x => (Snd.T4.nextMsg κ L es i x).f₀) j)
    (hY : ∀ j < 2 ^ (Snd.CKind.lv κ i).logN,
      rdF M (yb + 2 * j) = encF (Snd.T4.mLog κ i) (fun x => (Snd.T4.nextMsg κ L es i x).f₁) j) :
    ∀ j < 2 ^ (Snd.CKind.lv κ i).logN,
      (j ∈ consN4 κ L es i ↔ flagV M (Snd.CKind.lv κ i).rows cs cb eb xb yb j ≠ 0) := by
  intro j hj
  rw [flagV, bW_dec_ne_zero, mem_consN4]
  have s0 : ∑ r ∈ range (Snd.CKind.lv κ i).rows, rdF M (cb + cs * j + 2 * r) * rdF M (eb + 4 * r) =
      ∑ r : Fin (Snd.CKind.lv κ i).rows,
        Snd.T4.wordOf κ L es i r ⟨j, hj⟩ * (eqBits (Snd.T4.sAt es i) (Snd.CKind.lv κ i).ell r).f₀ := by
    rw [← Fin.sum_univ_eq_sum_range]
    refine sum_congr rfl fun r _ => ?_
    rw [hW j hj r, ← hE r r.2]
    rfl
  have s1 : ∑ r ∈ range (Snd.CKind.lv κ i).rows, rdF M (cb + cs * j + 2 * r) * rdF M (eb + 4 * r + 2) =
      ∑ r : Fin (Snd.CKind.lv κ i).rows,
        Snd.T4.wordOf κ L es i r ⟨j, hj⟩ * (eqBits (Snd.T4.sAt es i) (Snd.CKind.lv κ i).ell r).f₁ := by
    rw [← Fin.sum_univ_eq_sum_range]
    refine sum_congr rfl fun r _ => ?_
    rw [hW j hj r, ← hE r r.2]
    rfl
  rw [s0, s1, hX j hj, hY j hj]
  constructor
  · rintro ⟨h, hm⟩; exact (mem_consSet4_iff κ L es i _).1 hm
  · intro h; exact ⟨hj, (mem_consSet4_iff κ L es i ⟨j, hj⟩).2 h⟩

/-- **The front half's memory map** (`n` positions, `ℓ` challenges at `cbS`). -/
def FrontLay4 (n ℓ tb fb eb xb yb cbS : ℕ) : Prop :=
  regs ≤ tb ∧ tb + 800 ≤ fb ∧ fb + n ≤ eb ∧ eb + 256 ≤ xb ∧ xb + 2 * n ≤ yb ∧
    yb + 2 * n + 2 < 2 ^ 64 ∧ regs ≤ cbS ∧ cbS + 8 * ℓ + 4 ≤ eb ∧ (cbS + 8 * ℓ + 4 ≤ fb ∨ fb + n ≤ cbS)

/-- **The front half** at a 4.1 level, on the map `tb fb eb xb yb`. -/
def decFront4IR (msg : XIR) (ℓ n R cs cb cbS tb fb eb xb yb : ℕ) : XIR :=
  .seq (eqtIR ℓ cbS eb) (.seq msg (.seq (setA xb) (.seq (fwdIR n tb) (.seq (setA yb)
    (.seq (fwdIR n tb) (flagIR (2 ^ n) R cs cb eb xb yb fb))))))

/-- What the message step owes (3.x's `MsgOk` at the map's `eb`, `xb`, `yb`, `X`/`Y` of `2^n`
entries). -/
def MsgOk4 (I : Array Word) (msg : XIR) (s : St) (eb xb yb n m : ℕ) (g : ℕ → K) : Prop :=
  ∀ s' : St, Inv s'.M → s'.M.size = s.M.size →
    (∀ y, regs ≤ y → (y < eb ∨ eb + 256 ≤ y) → rd s'.M y = rd s.M y) →
    (∀ j < 2 ^ n, rdF (semXIR I msg s').M (xb + 2 * j) = (if j < 2 ^ m then (g j).f₀ else 0) ∧
      rdF (semXIR I msg s').M (yb + 2 * j) = (if j < 2 ^ m then (g j).f₁ else 0)) ∧
    (∀ y, regs ≤ y → (y < xb ∨ yb + 2 * 2 ^ n ≤ y) → rd (semXIR I msg s').M y = rd s'.M y) ∧
    Inv (semXIR I msg s').M

/-- The level parameters the front half needs (every kind, every level). -/
theorem lv4_front (κ : Snd.CKind) {i : ℕ} (hi : i < 5) :
    (Snd.CKind.lv κ i).ell ≤ 6 ∧ 1 ≤ (Snd.CKind.lv κ i).logN ∧ (Snd.CKind.lv κ i).logN ≤ 20 ∧
      Snd.T4.mLog κ i ≤ (Snd.CKind.lv κ i).logN := by
  rcases κ with (_|_|_) | (_|_|_) <;> interval_cases i <;> decide

/-- **The front half marks `A_c`** at a 4.1 kind (3.x's `decFront_sem` on a parametric map). -/
theorem decFront4_sem (I : Array Word) (s : St) (hM : Inv s.M) {κ : Snd.CKind} {L es : Log}
    {i cs cb cbS tb fb eb xb yb : ℕ} {msg : XIR} (hi : i < 5)
    (hL : FrontLay4 (2 ^ (Snd.CKind.lv κ i).logN) (Snd.CKind.lv κ i).ell tb fb eb xb yb cbS)
    (hsz : yb + 2 * 2 ^ (Snd.CKind.lv κ i).logN ≤ s.M.size)
    (hcs : 2 * (Snd.CKind.lv κ i).rows ≤ cs) (hcb : yb + 2 * 2 ^ (Snd.CKind.lv κ i).logN ≤ cb)
    (hcb2 : cb + cs * 2 ^ (Snd.CKind.lv κ i).logN + 2 < 2 ^ 64)
    (hT : ∀ v < 20, ∀ i < 20, rdF s.M (tb + 40 * v + 2 * i) = (wRow D logNMax v).getD i 0)
    (hW : ∀ j (hj : j < 2 ^ (Snd.CKind.lv κ i).logN) (r : Fin (Snd.CKind.lv κ i).rows),
      rdF s.M (cb + cs * j + 2 * r) = Snd.T4.wordOf κ L es i r ⟨j, hj⟩)
    (hS : ∀ v < (Snd.CKind.lv κ i).ell, rdK s.M (cbS + 8 * v) = Snd.T4.sAt es i v)
    (hmsg : MsgOk4 I msg (semXIR I (eqtIR (Snd.CKind.lv κ i).ell cbS eb) s) eb xb yb
      (Snd.CKind.lv κ i).logN (Snd.T4.mLog κ i) (Snd.T4.nextMsg κ L es i)) :
    (∀ j < 2 ^ (Snd.CKind.lv κ i).logN, (j ∈ consN4 κ L es i ↔
      rd (semXIR I (decFront4IR msg (Snd.CKind.lv κ i).ell (Snd.CKind.lv κ i).logN
        (Snd.CKind.lv κ i).rows cs cb cbS tb fb eb xb yb) s).M (fb + j) ≠ 0)) ∧
    (∀ y, regs ≤ y → (y < fb ∨ (fb + 2 ^ (Snd.CKind.lv κ i).logN ≤ y ∧ y < eb) ∨
        yb + 2 * 2 ^ (Snd.CKind.lv κ i).logN ≤ y) →
      rd (semXIR I (decFront4IR msg (Snd.CKind.lv κ i).ell (Snd.CKind.lv κ i).logN
        (Snd.CKind.lv κ i).rows cs cb cbS tb fb eb xb yb) s).M y = rd s.M y) ∧
    Inv (semXIR I (decFront4IR msg (Snd.CKind.lv κ i).ell (Snd.CKind.lv κ i).logN
        (Snd.CKind.lv κ i).rows cs cb cbS tb fb eb xb yb) s).M := by
  obtain ⟨htb, htf, hfe, hex, hxy, hy2, hcS, hcS2, hcSf⟩ := hL
  obtain ⟨hl6, hn1, hn20, hmn⟩ := lv4_front κ hi
  have hs := hM.1
  simp only [regs] at hs hcS htb
  have hRe : (Snd.CKind.lv κ i).rows = 2 ^ (Snd.CKind.lv κ i).ell := rfl
  have hPl : 2 ^ (Snd.CKind.lv κ i).ell ≤ 2 ^ 6 := Nat.pow_le_pow_right (by norm_num) hl6
  have hP1 : 1 ≤ 2 ^ (Snd.CKind.lv κ i).logN := Nat.one_le_two_pow
  have dX : tb + 800 ≤ xb := by omega
  have dY : tb + 800 ≤ yb := by omega
  -- the `eq` table
  rw [decFront4IR, semXIR_seq]
  obtain ⟨e1, e2, hM1⟩ := eqtIR_sem I s hM (ℓ := (Snd.CKind.lv κ i).ell) (cb := cbS) (eb := eb)
    (S := Snd.T4.sAt es i) (by omega) (by simp only [regs]; omega) (by omega)
    (by simp only [regs]; omega) (by omega) (by omega) (.inl (by omega)) hS
  have z1 := size_sem I (eqtIR (Snd.CKind.lv κ i).ell cbS eb) s
  have h256 : 4 * 2 ^ (Snd.CKind.lv κ i).ell ≤ 256 := by
    have := Nat.mul_le_mul_left 4 hPl; simpa using this
  have e2' : ∀ y, regs ≤ y → (y < eb ∨ eb + 256 ≤ y) →
      rd (semXIR I (eqtIR (Snd.CKind.lv κ i).ell cbS eb) s).M y = rd s.M y := fun y hy h =>
    e2 y hy (h.imp_right fun h' => le_trans (Nat.add_le_add_left h256 _) h')
  have hmsg' := hmsg
  generalize semXIR I (eqtIR (Snd.CKind.lv κ i).ell cbS eb) s = s1 at e1 e2' hM1 z1 hmsg'
  clear e2
  -- the message
  rw [semXIR_seq]
  obtain ⟨m1, m2, hM2⟩ := hmsg' s1 hM1 rfl fun y _ _ => rfl
  have z2 := size_sem I msg s1
  generalize semXIR I msg s1 = s2 at m1 m2 hM2 z2
  -- `Enc` of `X`
  rw [semXIR_seq, semXIR_seq]
  obtain ⟨a1, a2, hM3⟩ := setA_sem I s2 hM2 xb
  have z3 := size_sem I (setA xb) s2
  generalize semXIR I (setA xb) s2 = s3 at a1 a2 hM3 z3
  have h31 : ∀ y, regs ≤ y → (y < xb ∨ yb + 2 * 2 ^ (Snd.CKind.lv κ i).logN ≤ y) →
      (y < eb ∨ eb + 256 ≤ y) → rd s3.M y = rd s.M y := fun y hy h1 h2 => by
    rw [a2 y hy, m2 y hy h1, e2' y hy h2]
  have hT3 : ∀ v < 20, ∀ i' < 20, rdF s3.M (tb + 40 * v + 2 * i') = (wRow D logNMax v).getD i' 0 :=
    fun v hv i' hi' => by
      rw [← hT v hv i' hi']
      exact rdF_eq (h31 _ (by simp only [regs]; omega) (.inl (by omega)) (.inl (by omega)))
        (h31 _ (by simp only [regs]; omega) (.inl (by omega)) (.inl (by omega)))
  have hX3 : ∀ j < 2 ^ (Snd.CKind.lv κ i).logN, rdF s3.M (xb + 2 * j) =
      if h : j < 2 ^ Snd.T4.mLog κ i then
        (fun x : Fin (2 ^ Snd.T4.mLog κ i) => (Snd.T4.nextMsg κ L es i x).f₀) ⟨j, h⟩
      else 0 := fun j hj => by
    rw [rdF_eq (a2 _ (by simp only [regs]; omega)) (a2 _ (by simp only [regs]; omega)), (m1 j hj).1]
    by_cases h : j < 2 ^ Snd.T4.mLog κ i
    · rw [if_pos h, dif_pos h]
    · rw [if_neg h, dif_neg h]
  have f1 := fwdIR_enc I s3 hM3 (A := xb) (tb := tb) hn1 hn20 hmn
    (by simp only [regs]; omega) (by omega) (by omega) (by simp only [regs]; omega)
    (by omega) (.inl dX) a1 hT3
    (fun x : Fin (2 ^ Snd.T4.mLog κ i) => (Snd.T4.nextMsg κ L es i x).f₀) hX3
  obtain ⟨-, f2, hM4⟩ := fwdIR_sem I s3 hM3 (A := xb) (tb := tb) hn1 hn20
    (by simp only [regs]; omega) (by omega) (by omega) (by simp only [regs]; omega)
    (by omega) (.inl dX) a1 hT3 (Y := fun j => if h : j < 2 ^ Snd.T4.mLog κ i then
      (fun x : Fin (2 ^ Snd.T4.mLog κ i) => (Snd.T4.nextMsg κ L es i x).f₀) ⟨j, h⟩ else 0) hX3
  have z4 := size_sem I (fwdIR (Snd.CKind.lv κ i).logN tb) s3
  generalize semXIR I (fwdIR (Snd.CKind.lv κ i).logN tb) s3 = s4 at f1 f2 hM4 z4
  -- `Enc` of `Y`
  rw [semXIR_seq, semXIR_seq]
  obtain ⟨b1, b2, hM5⟩ := setA_sem I s4 hM4 yb
  have z5 := size_sem I (setA yb) s4
  generalize semXIR I (setA yb) s4 = s5 at b1 b2 hM5 z5
  have hT5 : ∀ v < 20, ∀ i' < 20, rdF s5.M (tb + 40 * v + 2 * i') = (wRow D logNMax v).getD i' 0 :=
    fun v hv i' hi' => by
      rw [← hT3 v hv i' hi']
      exact rdF_eq ((b2 _ (by simp only [regs]; omega)).trans
          (f2 _ (by simp only [regs]; omega) (.inl (by omega))))
        ((b2 _ (by simp only [regs]; omega)).trans (f2 _ (by simp only [regs]; omega) (.inl (by omega))))
  have hY5 : ∀ j < 2 ^ (Snd.CKind.lv κ i).logN, rdF s5.M (yb + 2 * j) =
      if h : j < 2 ^ Snd.T4.mLog κ i then
        (fun x : Fin (2 ^ Snd.T4.mLog κ i) => (Snd.T4.nextMsg κ L es i x).f₁) ⟨j, h⟩
      else 0 := fun j hj => by
    rw [rdF_eq ((b2 _ (by simp only [regs]; omega)).trans
        (f2 _ (by simp only [regs]; omega) (.inr (by omega))))
      ((b2 _ (by simp only [regs]; omega)).trans (f2 _ (by simp only [regs]; omega) (.inr (by omega)))),
      rdF_eq (a2 _ (by simp only [regs]; omega)) (a2 _ (by simp only [regs]; omega)), (m1 j hj).2]
    by_cases h : j < 2 ^ Snd.T4.mLog κ i
    · rw [if_pos h, dif_pos h]
    · rw [if_neg h, dif_neg h]
  have g1 := fwdIR_enc I s5 hM5 (A := yb) (tb := tb) hn1 hn20 hmn
    (by simp only [regs]; omega) (by omega) (by omega) (by simp only [regs]; omega)
    (by omega) (.inl dY) b1 hT5
    (fun x : Fin (2 ^ Snd.T4.mLog κ i) => (Snd.T4.nextMsg κ L es i x).f₁) hY5
  obtain ⟨-, g2, hM6⟩ := fwdIR_sem I s5 hM5 (A := yb) (tb := tb) hn1 hn20
    (by simp only [regs]; omega) (by omega) (by omega) (by simp only [regs]; omega)
    (by omega) (.inl dY) b1 hT5 (Y := fun j => if h : j < 2 ^ Snd.T4.mLog κ i then
      (fun x : Fin (2 ^ Snd.T4.mLog κ i) => (Snd.T4.nextMsg κ L es i x).f₁) ⟨j, h⟩ else 0) hY5
  have z6 := size_sem I (fwdIR (Snd.CKind.lv κ i).logN tb) s5
  generalize semXIR I (fwdIR (Snd.CKind.lv κ i).logN tb) s5 = s6 at g1 g2 hM6 z6
  -- the heap of `s6`
  have h6 : ∀ y, regs ≤ y → (y < xb ∨ yb + 2 * 2 ^ (Snd.CKind.lv κ i).logN ≤ y) →
      (y < eb ∨ eb + 256 ≤ y) → rd s6.M y = rd s.M y := fun y hy h1 h2 => by
    rw [g2 y hy (by omega), b2 y hy, f2 y hy (by omega), h31 y hy h1 h2]
  have hb6 : ∀ y, cb ≤ y → rd s6.M y = rd s.M y := fun y hy =>
    h6 y (by simp only [regs]; omega) (.inr (by omega)) (.inr (by omega))
  have hW6 : ∀ j (hj : j < 2 ^ (Snd.CKind.lv κ i).logN) (r : Fin (Snd.CKind.lv κ i).rows),
      rdF s6.M (cb + cs * j + 2 * r) = Snd.T4.wordOf κ L es i r ⟨j, hj⟩ := fun j hj r => by
    rw [← hW j hj r]
    have l1 : cb ≤ cb + cs * j + 2 * r := (Nat.le_add_right cb _).trans (Nat.le_add_right _ _)
    exact rdF_eq (hb6 _ l1) (hb6 _ (l1.trans (Nat.le_add_right _ _)))
  have hE6 : ∀ r < (Snd.CKind.lv κ i).rows,
      rdK s6.M (eb + 4 * r) = eqBits (Snd.T4.sAt es i) (Snd.CKind.lv κ i).ell r :=
    fun r hr => by
      rw [← e1 r (by rw [← hRe]; exact hr)]
      refine rdK_eq fun t ht => ?_
      have hr64 : r < 64 := lt_of_lt_of_le hr (by rw [hRe]; simpa using hPl)
      rw [g2 _ (by simp only [regs]; omega) (by omega), b2 _ (by simp only [regs]; omega),
        f2 _ (by simp only [regs]; omega) (by omega), a2 _ (by simp only [regs]; omega),
        m2 _ (by simp only [regs]; omega) (.inl (by omega))]
  have hX6 : ∀ j < 2 ^ (Snd.CKind.lv κ i).logN,
      rdF s6.M (xb + 2 * j) = encF (Snd.T4.mLog κ i) (fun x => (Snd.T4.nextMsg κ L es i x).f₀) j :=
    fun j hj => by
      rw [← f1 j hj]
      exact rdF_eq ((g2 _ (by simp only [regs]; omega) (.inl (by omega))).trans
          (b2 _ (by simp only [regs]; omega)))
        ((g2 _ (by simp only [regs]; omega) (.inl (by omega))).trans (b2 _ (by simp only [regs]; omega)))
  -- the flags
  have hR64 : (Snd.CKind.lv κ i).rows ≤ 64 := by rw [hRe]; simpa using hPl
  obtain ⟨k1, k2, hM7⟩ := flagIR_sem I s6 hM6 (n := 2 ^ (Snd.CKind.lv κ i).logN)
    (R := (Snd.CKind.lv κ i).rows) (cs := cs) (cb := cb) (eb := eb) (xb := xb) (yb := yb) (fb := fb)
    (by omega) (by omega) hcs (by simp only [regs]; omega) hcb2 (by simp only [regs]; omega) (by omega)
    (by simp only [regs]; omega) (by omega) (by simp only [regs]; omega) (by omega)
    (by simp only [regs]; omega) (by omega) (by omega) (.inr (by omega)) (.inr (by omega))
    (.inr (by omega)) (.inr (by omega))
  have hc := flagV_consSet4 (M := s6.M) (cs := cs) (cb := cb) (eb := eb) (xb := xb) (yb := yb)
    hW6 hE6 hX6 g1
  refine ⟨fun j hj => by rw [k1 j hj]; exact hc j hj, fun y hy hy2 => ?_, hM7⟩
  rw [k2 y hy (by omega), h6 y hy (by omega) (by omega)]

end FR.X

end G6_FRXDec4Front
