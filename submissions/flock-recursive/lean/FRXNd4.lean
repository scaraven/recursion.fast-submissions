-- G6: this module also holds the former modules `FRXOut4E`, `FRXOut4F`, `FRXOut4K`, `FRXOut4P`, `FRXOut4A`, `FRXOut4O` (one section each, in import order).
import FRXOut4R
import FRXDec4F0

section G6_FRXOut4E

-- New for `flock-recursive` (BLUEPRINT revision 4.1, §6.2 step 5; stage S-H4, pass 11, item 2: the
-- node output's emitters). 3.x analogue: `FRXOut`'s `.shw` case (shift 1 only, no loader).

/-!
# The node output's emitters: shifted pairs, heap words

After the decode the output reads H's message words through the chain loader `ldC` (`FRXOut4R`):
the loader's word `n` is the heap word at `hAddr κ (ldIx cb jL Δ n)` (**`ldG`**). Here:

* **`shwC κ`**: `oX :=` the shifted pair `shWd (ldG …) s n` of the loader's words `n = qN`, `n + 1`
  (`8s` in `qA`, `63 − 8s` in `qB`): a shifted pair of the loader's words, without the store (**`shwC_sem`**);
* **`shwO κ`** emits it and steps `qN`; **`shw4 κ`** emits four (**`shw4_sem`**);
* **`ldA d a`** loads the heap word at the constant address `a`; **`outAs as`** emits the heap words
  at the addresses `as` (**`outAs_sem`**: the children's statement cells);
* **`loopK_emitR`**: `loopK_emit` for a count `k ≤ K` held in a register (the aggregate's segments).

Every emitter keeps the output phase's frame `OF M₀` (no store).
-/

namespace FR.X

open RecursionFast FR.Read FR.Rev4 FR.Snd

attribute [local irreducible] entryK storeM runPrims

/-! ## Registers (below `FRXOut`'s, above `FRXOut4R`'s) -/

/-- The signature's index word. -/ def qIx : ℕ := 121
/-- The path's block pointer. -/ def qP : ℕ := 122
/-- The path bit, times 4. -/ def qBt : ℕ := 123
/-- The aggregate count's `alive` flag. -/ def qAl : ℕ := 124
/-- The ladder flag `30`. -/ def qF0 : ℕ := 125
/-- The ladder flag `31`. -/ def qF1 : ℕ := 126
/-- The signature loops' counter. -/ def qCs : ℕ := 128
/-- The signature loops' count. -/ def qLs : ℕ := 129
/-- The path level `t`. -/ def qTt : ℕ := 130
/-- Selector words. -/ def qS0 : ℕ := 131
/-- Selector words. -/ def qS1 : ℕ := 132
/-- Selector words. -/ def qS2 : ℕ := 133
/-- Selector words. -/ def qS3 : ℕ := 134
/-- Selector words. -/ def qS4 : ℕ := 135
/-- Selector words. -/ def qS5 : ℕ := 136

/-! ## Specification -/

/-- **The loader's word `n`**: the heap word at H word `ldIx cb jL Δ n`. -/
def ldG (κ : NodeKind) (M₀ : Mem) (cb jL Δ : ℕ) (n : ℕ) : Word := rd M₀ (hAddr κ (ldIx cb jL Δ n))

/-- **The shifted pair**: `oX :=` `(C n >>> 8s) + ((C (n+1) <<< 1) <<< (63 − 8s))` of the loader's
words at `n = qN` (`qA = 8s`, `qB = 63 − 8s`). -/
def shwC (κ : NodeKind) : XIR :=
  .seq (.blk [.const oR (toWord (hBase κ)), .op .or qM qN qN]) (.seq (ldC κ)
  (.seq (.blk [.op .shr oY oX qA, .op .add qM qN cOne]) (.seq (ldC κ)
  (.blk [.op .shl oX oX cOne, .op .shl oX oX qB, .op .add oX oY oX]))))

/-- **Emit the shifted pair** and step `qN`. -/
def shwO (κ : NodeKind) : XIR := .seq (shwC κ) (.seq (.out oX) (.blk [.op .add qN qN cOne]))

/-- **Four shifted pairs** from `qN`. -/
def shw4 (κ : NodeKind) : XIR := .seq (shwO κ) (.seq (shwO κ) (.seq (shwO κ) (shwO κ)))

/-- `d :=` the heap word at the constant address `a`. -/
def ldA (d a : ℕ) : XIR := .seq (.blk [.const oAd (toWord a)]) (.load d oAd)

/-- **Emit the heap words** at the constant addresses `as`. -/
def outAs : List ℕ → XIR
  | [] => .blk []
  | a :: as => .seq (ldA oX a) (.seq (.out oX) (outAs as))

/-! ## Proof helpers: frames -/

/-- A register outside a list containing the program's destinations is kept. -/
theorem keepW (I : Array Word) {P : XIR} {s : St} (hw : WF P) (hM : Inv s.M) {W : List ℕ}
    (hW : ∀ x ∈ wrL P, x ∈ W) {r : ℕ} (hr : r < regs) (h : r ∉ W) : rd (semXIR I P s).M r = rd s.M r :=
  keep_of I hw hM hr fun h' => h (hW _ h')

/-- The loader's registers. -/
structure LdR (cb jL Δ : ℕ) (M : Mem) : Prop where
  cb : rd M qCB = toWord cb
  jl : rd M qJ = toWord jL
  dl : rd M qDl = toWord Δ

/-- The shifted pair's registers at `n`, shift `s`. -/
structure SwR (cb jL Δ sh n : ℕ) (M : Mem) : Prop extends LdR cb jL Δ M where
  n : rd M qN = toWord n
  a : rd M qA = toWord (8 * sh)
  b : rd M qB = toWord (63 - 8 * sh)

/-- What `shwC` writes. -/
def wShw : List ℕ := [oR, qM, oK, qT1, oU, oT1, oT2, oT3, oAd, oX, oY]

theorem wf_shwC (κ : NodeKind) : WF (shwC κ) :=
  ⟨by simp [WF, Prim.dst, oR, qM], wf_ldC κ, by simp [WF, Prim.dst, oY, qM], wf_ldC κ,
    by simp [WF, Prim.dst, oX]⟩

theorem loK_shwC (κ : NodeKind) : LoK (shwC κ) :=
  ⟨by simp [LoK, Prim.dst, regs, oR, qM], loK_ldC κ, by simp [LoK, Prim.dst, regs, oY, qM], loK_ldC κ,
    by simp [LoK, Prim.dst, regs, oX]⟩

theorem wr_shwC (κ : NodeKind) : ∀ x ∈ wrL (shwC κ), x ∈ wShw := by
  simp +decide [wrL, shwC, ldC, ldw, ldPs, Prim.dst, wShw]

theorem swR_keep6 {cb jL Δ sh n : ℕ} {M M' : Mem} (h : SwR cb jL Δ sh n M)
    (hk : ∀ r ∈ [qCB, qJ, qDl, qN, qA, qB], rd M' r = rd M r) : SwR cb jL Δ sh n M' :=
  ⟨⟨(hk _ (by simp)).trans h.cb, (hk _ (by simp)).trans h.jl, (hk _ (by simp)).trans h.dl⟩,
    (hk _ (by simp)).trans h.n, (hk _ (by simp)).trans h.a, (hk _ (by simp)).trans h.b⟩

theorem swR_keep {cb jL Δ sh n : ℕ} {M M' : Mem} (h : SwR cb jL Δ sh n M)
    (hk : ∀ r < regs, r ∉ wShw → rd M' r = rd M r) : SwR cb jL Δ sh n M' :=
  ⟨⟨(hk _ (by decide) (by decide)).trans h.cb, (hk _ (by decide) (by decide)).trans h.jl,
    (hk _ (by decide) (by decide)).trans h.dl⟩, (hk _ (by decide) (by decide)).trans h.n,
    (hk _ (by decide) (by decide)).trans h.a, (hk _ (by decide) (by decide)).trans h.b⟩

/-! ## The shifted pair -/

/-- **`shwC` computes the shifted pair** of the loader's words at `n`, `n + 1`; the output and the
frame are kept. -/
theorem shwC_sem (I : Array Word) (κ : NodeKind) {M₀ : Mem} {cb jL Δ sh n : ℕ} (hs8 : sh < 8)
    (hb : n + 1 + cb + Δ < 2 ^ 64) (hjl : jL < 2 ^ 64) (hl0 : hAddr κ (ldIx cb jL Δ n) < bufB)
    (hl1 : hAddr κ (ldIx cb jL Δ (n + 1)) < bufB) {t : St} (hO : OF M₀ t) (hR : SwR cb jL Δ sh n t.M) :
    rd (semXIR I (shwC κ) t).M oX = shWd (ldG κ M₀ cb jL Δ) sh n ∧ (semXIR I (shwC κ) t).o = t.o ∧
      OF M₀ (semXIR I (shwC κ) t) := by
  have hs := hO.inv.1
  simp only [regs] at hs
  refine ⟨?_, ?_, of_loK I (loK_shwC κ) (wf_shwC κ) hO⟩
  · rw [shwC, semXIR_seq, semXIR_blk]
    set M1 := runPrims [.const oR (toWord (hBase κ)), .op .or qM qN qN] t.M with hM1d
    have k1 : ∀ r, r ≠ oR → r ≠ qM → rd M1 r = rd t.M r := fun r h1 h2 => by
      simp only [hM1d, runPrims, List.foldl, Prim.run]; rw [rd_set_ne (Ne.symm h2), rd_set_ne (Ne.symm h1)]
    have r1 : rd M1 oR = toWord (hBase κ) := by
      simp only [hM1d, runPrims, List.foldl, Prim.run]
      simp (disch := (simp only [size_set, oR, qM] at *; omega)) only [rd_set_self, rd_set_ne]
    have m1 : rd M1 qM = toWord n := by
      simp only [hM1d, runPrims, List.foldl, Prim.run]
      simp (disch := (simp only [size_set, oR, qM, qN] at *; omega)) only [rd_set_self, rd_set_ne]
      rw [or_self_eval, hR.n]
    have i1 : Inv M1 := inv_sem I (P := .blk [.const oR (toWord (hBase κ)), .op .or qM qN qN])
      (by simp +decide [WF, Prim.dst, oR, qM]) hO.inv
    have O1 : OF M₀ ⟨M1, t.o⟩ := of_loK I (P := .blk [.const oR (toWord (hBase κ)), .op .or qM qN qN])
      (by simp [LoK, Prim.dst, regs, oR, qM]) (by simp +decide [WF, Prim.dst, oR, qM]) hO
    obtain ⟨x1, -⟩ := ldC_sem I κ ⟨M1, t.o⟩ i1 r1 m1 (by rw [k1 _ (by decide) (by decide)]; exact hR.cb)
      (by rw [k1 _ (by decide) (by decide)]; exact hR.jl) (by rw [k1 _ (by decide) (by decide)]; exact hR.dl)
      (by omega) hjl
    rw [semXIR_seq]
    generalize hs2 : semXIR I (ldC κ) ⟨M1, t.o⟩ = s2 at x1
    have i2 : Inv s2.M := hs2 ▸ inv_sem I (wf_ldC κ) i1
    have O2 : OF M₀ s2 := hs2 ▸ of_loK I (loK_ldC κ) (wf_ldC κ) O1
    have k2 : ∀ r < regs, r ∉ [oK, qT1, oU, oT1, oT2, oT3, oAd, oX] → rd s2.M r = rd M1 r := fun r hr hn =>
      hs2 ▸ keep_ldC I κ i1 hr hn
    have v1 : rd s2.M oX = ldG κ M₀ cb jL Δ n := by rw [x1, O1.low _ (regs_hAddr κ _) hl0]; rfl
    rw [semXIR_seq, semXIR_blk]
    have hs2' := i2.1
    simp only [regs] at hs2'
    set M3 := runPrims [.op .shr oY oX qA, .op .add qM qN cOne] s2.M with hM3d
    have k3 : ∀ r, r ≠ oY → r ≠ qM → rd M3 r = rd s2.M r := fun r h1 h2 => by
      simp only [hM3d, runPrims, List.foldl, Prim.run]; rw [rd_set_ne (Ne.symm h2), rd_set_ne (Ne.symm h1)]
    have y3 : rd M3 oY = ldG κ M₀ cb jL Δ n >>> (8 * sh) := by
      simp only [hM3d, runPrims, List.foldl, Prim.run]
      simp (disch := (simp only [size_set, oY, qM, oX, qA] at *; omega)) only [rd_set_self, rd_set_ne]
      rw [v1, k2 _ (by decide) (by decide), k1 _ (by decide) (by decide), hR.a, shr_8s _ hs8]
    have m3 : rd M3 qM = toWord (n + 1) := by
      simp only [hM3d, runPrims, List.foldl, Prim.run]
      simp (disch := (simp only [size_set, oY, qM, qN, cOne] at *; omega)) only [rd_set_self, rd_set_ne]
      rw [k2 _ (by decide) (by decide), k1 _ (by decide) (by decide), hR.n, one_cOne i2, add_one_toWord]
    have i3 : Inv M3 := inv_sem I (P := .blk [.op .shr oY oX qA, .op .add qM qN cOne])
      (by simp +decide [WF, Prim.dst, oY, qM]) i2
    have O3 : OF M₀ ⟨M3, s2.o⟩ := of_loK I (P := .blk [.op .shr oY oX qA, .op .add qM qN cOne])
      (by simp [LoK, Prim.dst, regs, oY, qM]) (by simp +decide [WF, Prim.dst, oY, qM]) O2
    have k23 : ∀ r < regs, r ∉ [oK, qT1, oU, oT1, oT2, oT3, oAd, oX, oY, qM, oR] →
        rd M3 r = rd t.M r := fun r hr hn => by
      simp only [List.mem_cons, List.mem_nil_iff, or_false, not_or] at hn
      rw [k3 r hn.2.2.2.2.2.2.2.2.1 hn.2.2.2.2.2.2.2.2.2.1, k2 r hr (by simp [hn.1, hn.2.1, hn.2.2.1,
        hn.2.2.2.1, hn.2.2.2.2.1, hn.2.2.2.2.2.1, hn.2.2.2.2.2.2.1, hn.2.2.2.2.2.2.2.1]),
        k1 r hn.2.2.2.2.2.2.2.2.2.2 hn.2.2.2.2.2.2.2.2.2.1]
    obtain ⟨x2, -⟩ := ldC_sem I κ ⟨M3, s2.o⟩ i3
      (by rw [k3 _ (by decide) (by decide), k2 _ (by decide) (by decide)]; exact r1) m3
      (by rw [k23 _ (by decide) (by decide)]; exact hR.cb) (by rw [k23 _ (by decide) (by decide)]; exact hR.jl)
      (by rw [k23 _ (by decide) (by decide)]; exact hR.dl) (by omega) hjl
    rw [semXIR_seq]
    generalize hs4 : semXIR I (ldC κ) ⟨M3, s2.o⟩ = s4 at x2
    have i4 : Inv s4.M := hs4 ▸ inv_sem I (wf_ldC κ) i3
    have k4 : ∀ r < regs, r ∉ [oK, qT1, oU, oT1, oT2, oT3, oAd, oX] → rd s4.M r = rd M3 r := fun r hr hn =>
      hs4 ▸ keep_ldC I κ i3 hr hn
    have v2 : rd s4.M oX = ldG κ M₀ cb jL Δ (n + 1) := by rw [x2, O3.low _ (regs_hAddr κ _) hl1]; rfl
    rw [semXIR_blk]
    have hs4' := i4.1
    simp only [regs] at hs4'
    simp only [runPrims, List.foldl, Prim.run]
    simp (disch := (simp only [size_set, oX, oY, qB, cOne] at *; omega)) only [rd_set_self, rd_set_ne]
    rw [v2, one_cOne i4, k4 qB (by decide) (by decide), k23 qB (by decide) (by decide), hR.b, shl_shl_one _ hs8,
      k4 oY (by decide) (by decide), y3, shWd]
    rfl
  · rfl

theorem of_mk {M₀ : Mem} {s : St} (h : OF M₀ s) (o : Array Word) : OF M₀ ⟨s.M, o⟩ := ⟨h.inv, h.size, h.low⟩

/-- `qN += 1`. -/
theorem stepN {M : Mem} (hM : Inv M) {n : ℕ} (hn : rd M qN = toWord n) :
    rd (runPrims [.op .add qN qN cOne] M) qN = toWord (n + 1) ∧
      ∀ r, r ≠ qN → rd (runPrims [.op .add qN qN cOne] M) r = rd M r := by
  have hs := hM.1
  simp only [regs] at hs
  refine ⟨?_, fun r hr => ?_⟩
  · simp only [runPrims, List.foldl, Prim.run]
    rw [rd_set_self (by simp only [qN]; omega), hn, one_cOne hM, add_one_toWord]
  · simp only [runPrims, List.foldl, Prim.run]; rw [rd_set_ne (Ne.symm hr)]

/-- **One shifted pair emitted**: the word, `qN := n + 1`, every register outside `qN :: wShw` kept. -/
theorem shwO_sem (I : Array Word) (κ : NodeKind) {M₀ : Mem} {cb jL Δ sh n : ℕ} (hs8 : sh < 8)
    (hb : n + 1 + cb + Δ < 2 ^ 64) (hjl : jL < 2 ^ 64) (hl0 : hAddr κ (ldIx cb jL Δ n) < bufB)
    (hl1 : hAddr κ (ldIx cb jL Δ (n + 1)) < bufB) {t : St} (hO : OF M₀ t) (hR : SwR cb jL Δ sh n t.M) :
    (semXIR I (shwO κ) t).o.toList = t.o.toList ++ [shWd (ldG κ M₀ cb jL Δ) sh n] ∧
      OF M₀ (semXIR I (shwO κ) t) ∧ SwR cb jL Δ sh (n + 1) (semXIR I (shwO κ) t).M ∧
      ∀ r < regs, r ∉ qN :: wShw → rd (semXIR I (shwO κ) t).M r = rd t.M r := by
  obtain ⟨x, o, O⟩ := shwC_sem I κ hs8 hb hjl hl0 hl1 hO hR
  have kC : ∀ r < regs, r ∉ wShw → rd (semXIR I (shwC κ) t).M r = rd t.M r := fun r hr h =>
    keepW I (wf_shwC κ) hO.inv (wr_shwC κ) hr h
  have R1 := swR_keep hR kC
  rw [shwO, semXIR_seq]
  generalize semXIR I (shwC κ) t = t1 at x o O kC R1
  rw [show semXIR I (.seq (.out oX) (.blk [.op .add qN qN cOne])) t1 =
    ⟨runPrims [.op .add qN qN cOne] t1.M, t1.o.push (rd t1.M oX)⟩ from rfl]
  obtain ⟨n1, k1⟩ := stepN O.inv R1.n
  refine ⟨by simp [o, x], of_loK I (P := .blk [.op .add qN qN cOne]) (by simp [LoK, Prim.dst, qN, regs])
    (by simp [WF, Prim.dst, qN]) (of_mk O (t1.o.push (rd t1.M oX))), ⟨⟨?_, ?_, ?_⟩, n1, ?_, ?_⟩, fun r hr h => ?_⟩
  · rw [k1 _ (by decide)]; exact R1.cb
  · rw [k1 _ (by decide)]; exact R1.jl
  · rw [k1 _ (by decide)]; exact R1.dl
  · rw [k1 _ (by decide)]; exact R1.a
  · rw [k1 _ (by decide)]; exact R1.b
  · simp only [List.mem_cons, not_or] at h
    rw [k1 _ h.1]; exact kC r hr (by simpa [wShw] using h.2)

/-- **Four shifted pairs emitted** from `n`. -/
theorem shw4_sem (I : Array Word) (κ : NodeKind) {M₀ : Mem} {cb jL Δ sh n : ℕ} (hs8 : sh < 8)
    (hb : n + 5 + cb + Δ < 2 ^ 64) (hjl : jL < 2 ^ 64) (hl : ∀ j ≤ 4, hAddr κ (ldIx cb jL Δ (n + j)) < bufB)
    {t : St} (hO : OF M₀ t) (hR : SwR cb jL Δ sh n t.M) :
    (semXIR I (shw4 κ) t).o.toList = t.o.toList ++ (List.range 4).map (fun j => shWd (ldG κ M₀ cb jL Δ) sh (n + j)) ∧
      OF M₀ (semXIR I (shw4 κ) t) ∧ SwR cb jL Δ sh (n + 4) (semXIR I (shw4 κ) t).M ∧
      ∀ r < regs, r ∉ qN :: wShw → rd (semXIR I (shw4 κ) t).M r = rd t.M r := by
  obtain ⟨a1, b1, c1, d1⟩ := shwO_sem I κ hs8 (by omega) hjl (by simpa using hl 0 (by omega))
    (by simpa using hl 1 (by omega)) hO hR
  rw [shw4, semXIR_seq]
  generalize semXIR I (shwO κ) t = t1 at a1 b1 c1 d1
  obtain ⟨a2, b2, c2, d2⟩ := shwO_sem I κ hs8 (by omega) hjl (by simpa using hl 1 (by omega))
    (by simpa [Nat.add_assoc] using hl 2 (by omega)) b1 c1
  rw [semXIR_seq]
  generalize semXIR I (shwO κ) t1 = t2 at a2 b2 c2 d2
  obtain ⟨a3, b3, c3, d3⟩ := shwO_sem I κ hs8 (by omega) hjl (by simpa [Nat.add_assoc] using hl 2 (by omega))
    (by simpa [Nat.add_assoc] using hl 3 (by omega)) b2 c2
  rw [semXIR_seq]
  generalize semXIR I (shwO κ) t2 = t3 at a3 b3 c3 d3
  obtain ⟨a4, b4, c4, d4⟩ := shwO_sem I κ hs8 (by omega) hjl (by simpa [Nat.add_assoc] using hl 3 (by omega))
    (by simpa [Nat.add_assoc] using hl 4 (by omega)) b3 c3
  refine ⟨?_, b4, by simpa [Nat.add_assoc] using c4, fun r hr h => (d4 r hr h).trans ((d3 r hr h).trans
    ((d2 r hr h).trans (d1 r hr h)))⟩
  rw [a4, a3, a2, a1]
  simp [List.range_succ, Nat.add_assoc]

/-! ## Heap words at constant addresses -/

theorem ldA_sem (I : Array Word) {d a : ℕ} (hd : 4 ≤ d) (hdr : d < regs) (hda : d ≠ oAd) (ha : regs ≤ a)
    (ha2 : a < 2 ^ 64) {M₀ : Mem} {t : St} (hO : OF M₀ t) :
    rd (semXIR I (ldA d a) t).M d = rd t.M a ∧ (semXIR I (ldA d a) t).o = t.o ∧ OF M₀ (semXIR I (ldA d a) t) ∧
      ∀ r, r ≠ d → r ≠ oAd → rd (semXIR I (ldA d a) t).M r = rd t.M r := by
  have hs := hO.inv.1
  simp only [regs] at hs hdr ha
  have e : semXIR I (ldA d a) t = ⟨(t.M.setIfInBounds oAd (toWord a)).setIfInBounds d
      (rd (t.M.setIfInBounds oAd (toWord a)) (rd (t.M.setIfInBounds oAd (toWord a)) oAd).toNat), t.o⟩ := by
    simp only [ldA, semXIR_seq, semXIR_blk]
    unfold runPrims
    rfl
  have r1 : rd (t.M.setIfInBounds oAd (toWord a)) oAd = toWord a := rd_set_self (by simp only [oAd]; omega)
  refine ⟨?_, by rw [e], of_loK I (P := ldA d a) ⟨by simp [LoK, Prim.dst, oAd, regs], show d < regs from hdr⟩
    ⟨by simp [WF, Prim.dst, oAd], hd⟩ hO, fun r h1 h2 => ?_⟩
  · rw [e]
    simp only
    rw [rd_set_self (by simp only [size_set]; omega), r1, toNat_toWord ha2,
      rd_set_ne (show oAd ≠ a by simp only [oAd]; omega)]
  · rw [e]
    simp only
    rw [rd_set_ne (Ne.symm h1), rd_set_ne (Ne.symm h2)]

/-- **The heap words at `as` are emitted** (registers `oAd`, `oX` written). -/
theorem outAs_sem (I : Array Word) {M₀ : Mem} : ∀ (as : List ℕ) (t : St), (∀ a ∈ as, regs ≤ a ∧ a < bufB) →
    OF M₀ t → (semXIR I (outAs as) t).o.toList = t.o.toList ++ as.map (rd M₀) ∧ OF M₀ (semXIR I (outAs as) t) ∧
      ∀ r, r ≠ oX → r ≠ oAd → rd (semXIR I (outAs as) t).M r = rd t.M r
  | [], t, _, hO => ⟨by simp [outAs, semXIR_blk, runPrims], by simpa [outAs, semXIR_blk, runPrims] using hO,
      fun r _ _ => by simp [outAs, semXIR_blk, runPrims]⟩
  | a :: as, t, ha, hO => by
    have h1 := ha a (by simp)
    obtain ⟨x1, o1, O1, k1⟩ := ldA_sem I (d := oX) (a := a) (by decide) (by decide) (by decide) h1.1
      (by simp only [bufB] at h1; omega) hO
    rw [outAs, semXIR_seq]
    generalize semXIR I (ldA oX a) t = t1 at x1 o1 O1 k1
    rw [semXIR_seq]
    have e2 : semXIR I (.out oX) t1 = ⟨t1.M, t1.o.push (rd t1.M oX)⟩ := rfl
    rw [e2]
    obtain ⟨a2, b2, c2⟩ := outAs_sem I as ⟨t1.M, t1.o.push (rd t1.M oX)⟩ (fun b hb => ha b (by simp [hb]))
      (of_mk O1 _)
    refine ⟨?_, b2, fun r h1' h2' => (c2 r h1' h2').trans (k1 r h1' h2')⟩
    rw [a2, x1, hO.low a h1.1 h1.2, o1]
    simp

/-! ## A counted loop with its count in a register -/

theorem entryK_countR {c n : ℕ} {K : ℕ} {M : Mem} (hM : Inv M) (hc : 4 < c) (hcr : c < regs)
    (hn : n ≠ c) (hnt : n ≠ cTmp) {k : ℕ} (hk : k ≤ K) (hK : K < 2 ^ 64) (hN : rd M n = toWord k) :
    rd (entryK c n (toWord K) M) c = toWord k := by
  have hs := hM.1
  unfold entryK
  dsimp only
  have h1 : rd (M.setIfInBounds c (toWord K)) n = toWord k := by rw [rd_set_ne (Ne.symm hn), hN]
  have h2 : rd (M.setIfInBounds c (toWord K)) c = toWord K := rd_set_self (lt_of_lt_of_le hcr hs)
  rw [h1, h2, rd_set_self (by simp only [size_set, cTmp, regs] at *; omega)]
  rcases Nat.lt_or_eq_of_le hk with hlt | rfl
  · have : XOp.ltu.eval (toWord k) (toWord K) = 1 := by
      simp only [XOp.eval]; rw [if_pos]; rw [BitVec.lt_def, toNat_toWord (by omega), toNat_toWord hK]; exact hlt
    rw [this, if_neg (by decide), rd_set_self (by simp only [size_set]; exact lt_of_lt_of_le hcr hs),
      or_self_eval, rd_set_ne (Ne.symm hnt), h1]
  · have : XOp.ltu.eval (toWord k) (toWord k) = 0 := by simp [XOp.eval]
    rw [this, if_pos rfl, rd_set_ne (by simp only [cTmp]; omega), h2]

/-- **A counted loop that emits**, its count `k ≤ K` in register `n`. -/
theorem loopK_emitR (I : Array Word) {c n K : ℕ} {b : XIR} (Q : ℕ → St → Prop) (out : ℕ → List Word)
    (s : St) (hM : Inv s.M) (hc : 4 < c) (hcr : c < regs) (hn : n ≠ c) (hnt : n ≠ cTmp) (hK : K < 2 ^ 64)
    {k : ℕ} (hk : k ≤ K)
    (hN : rd s.M n = toWord k) (h0 : Q 0 ⟨entryK c n (toWord K) s.M, s.o⟩)
    (hf : ∀ j s, j < k → Q j s → (semXIR I b s).o.toList = s.o.toList ++ out j ∧
      Q (j + 1) (decS c (semXIR I b s))) :
    (semXIR I (.loopK c n (toWord K) b) s).o.toList = s.o.toList ++ (List.range k).flatMap out ∧
      Q k (semXIR I (.loopK c n (toWord K) b) s) := by
  have e : (rd (entryK c n (toWord K) s.M) c).toNat = k := by
    rw [entryK_countR hM hc hcr hn hnt hk hK hN, toNat_toWord (by omega)]
  have := iterL_emit I Q out hf k 0 _ (by omega) h0
  simp only [Nat.zero_add] at this
  have e2 : semXIR I (.loopK c n (toWord K) b) s =
      iterL (semXIR I b) c k ⟨entryK c n (toWord K) s.M, s.o⟩ := by
    simp only [semXIR]; rw [e]
  rw [e2]; exact this

/-! ## The signature -/

/-- One chain: four shift-3 pairs, then `qN += 20` (the next chain's block). -/
def otsB (κ : NodeKind) : XIR := .seq (shw4 κ) (.blk [.const oK (toWord 20), .op .add qN qN oK])

/-- One path level `t`: `qN := qP + 4 − 4·bit_t(idx)`, four shift-1 pairs, `qP += 16`, `t += 1`. -/
def pathB (κ : NodeKind) : XIR :=
  .seq (.blk [.op .shr qBt qIx qTt, .op .and qBt qBt cOne, .const oK (toWord 2), .op .shl qBt qBt oK,
      .const oK (toWord 4), .op .sub qN oK qBt, .op .add qN qN qP])
    (.seq (shw4 κ) (.blk [.const oK (toWord 16), .op .add qP qP oK, .op .add qTt qTt cOne]))

/-- The index word: the H loader (`cb = jL = Δ = 0`), shift 1 at WOTS block `399`; kept in `qIx`. -/
def sigHd (κ : NodeKind) (σ : ℕ) : XIR :=
  .seq (.blk [.const qCB 0, .const qJ 0, .const qDl 0, .const qA (toWord 8), .const qB (toWord 55),
      .const qN (toWord (8 * W4.wb κ σ 399))])
  (.seq (shwC κ) (.seq (.blk [.op .or qIx oX oX]) (.out oX)))

/-- The 133 chains' first `x` fields (shift 3). -/
def otsIR (κ : NodeKind) (σ : ℕ) : XIR :=
  .seq (.blk [.const qA (toWord 24), .const qB (toWord 39), .const qN (toWord (8 * W4.wb κ σ 0 + 1)),
      .const qLs (toWord wotsLen)])
    (.loopK qCs qLs (toWord wotsLen) (otsB κ))

/-- The 16 path siblings (shift 1, offset by the index bit). -/
def pathIR (κ : NodeKind) (σ : ℕ) : XIR :=
  .seq (.blk [.const qA (toWord 8), .const qB (toWord 55), .const qP (toWord (8 * W4.wb κ σ 466)),
      .const qTt 0, .const qLs (toWord sigHeight)])
    (.loopK qCs qLs (toWord sigHeight) (pathB κ))

/-- **Signed child `σ`'s signature** from H's message words (`sigWords_sigH`): the index, the chains,
the path. -/
def sigIR (κ : NodeKind) (σ : ℕ) : XIR := .seq (sigHd κ σ) (.seq (otsIR κ σ) (pathIR κ σ))

/-- The path's offset at level `t` of the index word `X`. -/
def offB (X : Word) (t : ℕ) : ℕ := if X.toNat / 2 ^ t % 2 = 1 then 0 else 4

/-- **The signature's words over a word stream `G`** from WOTS block `b` (`sigWords_sigH`'s shape). -/
def sigL (G : ℕ → Word) (b : ℕ) : List Word :=
  shWd G 1 (8 * b + 3192) :: ((List.range wotsLen).flatMap fun i => (List.range 4).map fun j =>
    shWd G 3 (8 * b + 1 + 24 * i + j)) ++
  (List.range sigHeight).flatMap fun t => (List.range 4).map fun j =>
    shWd G 1 (8 * b + 3728 + 16 * t + offB (shWd G 1 (8 * b + 3192)) t + j)

theorem ldIx_zero (jL m : ℕ) : ldIx 0 jL 0 m = m := by unfold ldIx; split_ifs <;> rfl

/-- The offset as the machine computes it: `4 − ((X >>> t) &&& 1) <<< 2`. -/
theorem offB_eval (X : Word) {t : ℕ} (ht : t < 64) :
    XOp.sub.eval (toWord 4) (XOp.shl.eval (XOp.and.eval (XOp.shr.eval X (toWord t)) 1) (toWord 2)) =
      toWord (offB X t) := by
  rw [shr_c _ _ ht, offB, show XOp.and.eval (X >>> t) 1 = X >>> t &&& 1 from rfl]
  have hb : (X >>> t &&& 1).toNat = X.toNat / 2 ^ t % 2 := by
    rw [BitVec.toNat_and, BitVec.toNat_ushiftRight, show (1 : Word).toNat = 2 ^ 1 - 1 from rfl,
      Nat.and_two_pow_sub_one_eq_mod, Nat.shiftRight_eq_div_pow, pow_one]
  rcases Nat.mod_two_eq_zero_or_one (X.toNat / 2 ^ t) with h | h
  · have : X >>> t &&& 1 = 0 := BitVec.eq_of_toNat_eq (by rw [hb, h]; rfl)
    rw [this, if_neg (by omega)]; decide
  · have : X >>> t &&& 1 = 1 := BitVec.eq_of_toNat_eq (by rw [hb, h]; rfl)
    rw [this, if_pos h]; decide

theorem wf_shwO (κ : NodeKind) : WF (shwO κ) := ⟨wf_shwC κ, trivial, by simp [WF, Prim.dst, qN]⟩

theorem wf_shw4 (κ : NodeKind) : WF (shw4 κ) := ⟨wf_shwO κ, wf_shwO κ, wf_shwO κ, wf_shwO κ⟩

theorem loK_shwO (κ : NodeKind) : LoK (shwO κ) := ⟨loK_shwC κ, trivial, by simp [LoK, Prim.dst, qN, regs]⟩

theorem loK_shw4 (κ : NodeKind) : LoK (shw4 κ) := ⟨loK_shwO κ, loK_shwO κ, loK_shwO κ, loK_shwO κ⟩

theorem wf_sigIR (κ : NodeKind) (σ : ℕ) : WF (sigIR κ σ) := by
  refine ⟨⟨by simp [WF, Prim.dst, qCB, qJ, qDl, qA, qB, qN], wf_shwC κ, by simp [WF, Prim.dst, qIx], trivial⟩,
    ⟨by simp [WF, Prim.dst, qA, qB, qN, qLs], ⟨by decide, by decide, fun h => ?_, wf_shw4 κ,
    by simp [WF, Prim.dst, oK, qN]⟩⟩, by simp [WF, Prim.dst, qA, qB, qP, qTt, qLs],
    ⟨by decide, by decide, fun h => ?_, by simp [WF, Prim.dst, qBt, oK, qN], wf_shw4 κ,
    by simp [WF, Prim.dst, oK, qP, qTt]⟩⟩
  · exact absurd (writes_wrL _ _ h) (by cases κ <;> decide)
  · exact absurd (writes_wrL _ _ h) (by cases κ <;> decide)

theorem loK_sigIR (κ : NodeKind) (σ : ℕ) : LoK (sigIR κ σ) :=
  ⟨⟨by simp [LoK, Prim.dst, regs, qCB, qJ, qDl, qA, qB, qN], loK_shwC κ, by simp [LoK, Prim.dst, regs, qIx],
    trivial⟩, ⟨by simp [LoK, Prim.dst, regs, qA, qB, qN, qLs],
    ⟨by decide, loK_shw4 κ, by simp [LoK, Prim.dst, regs, oK, qN]⟩⟩,
    by simp [LoK, Prim.dst, regs, qA, qB, qP, qTt, qLs],
    ⟨by decide, by simp [LoK, Prim.dst, regs, qBt, oK, qN], loK_shw4 κ, by simp [LoK, Prim.dst, regs, oK, qP, qTt]⟩⟩

/-- **The index word**: emitted and kept in `qIx`; the H loader's registers set. -/
theorem sigHd_sem (I : Array Word) (κ : NodeKind) (σ : ℕ) {M₀ : Mem} {s : St} (hO : OF M₀ s)
    (hb : 8 * W4.wb κ σ 399 + 2 < 2 ^ 64) (hl0 : hAddr κ (8 * W4.wb κ σ 399) < bufB)
    (hl1 : hAddr κ (8 * W4.wb κ σ 399 + 1) < bufB) :
    (semXIR I (sigHd κ σ) s).o.toList = s.o.toList ++ [shWd (ldG κ M₀ 0 0 0) 1 (8 * W4.wb κ σ 399)] ∧
      OF M₀ (semXIR I (sigHd κ σ) s) ∧ LdR 0 0 0 (semXIR I (sigHd κ σ) s).M ∧
      rd (semXIR I (sigHd κ σ) s).M qIx = shWd (ldG κ M₀ 0 0 0) 1 (8 * W4.wb κ σ 399) := by
  have hs := hO.inv.1
  simp only [regs] at hs
  rw [sigHd, semXIR_seq, semXIR_blk]
  set ps1 : List Prim := [.const qCB 0, .const qJ 0, .const qDl 0, .const qA (toWord 8), .const qB (toWord 55),
      .const qN (toWord (8 * W4.wb κ σ 399))] with hps1
  have O1 : OF M₀ ⟨runPrims ps1 s.M, s.o⟩ := of_loK I (P := .blk ps1)
    (by simp [hps1, LoK, Prim.dst, regs, qCB, qJ, qDl, qA, qB, qN])
    (by simp [hps1, WF, Prim.dst, qCB, qJ, qDl, qA, qB, qN]) hO
  have R1 : SwR 0 0 0 1 (8 * W4.wb κ σ 399) (runPrims ps1 s.M) := by
    simp only [hps1, runPrims, List.foldl, Prim.run]
    refine ⟨⟨?_, ?_, ?_⟩, ?_, ?_, ?_⟩ <;>
    simp (disch := (simp only [size_set, qCB, qJ, qDl, qA, qB, qN] at *; omega)) only [rd_set_self, rd_set_ne] <;>
    rfl
  have hl0' : hAddr κ (ldIx 0 0 0 (8 * W4.wb κ σ 399)) < bufB := by rw [ldIx_zero]; exact hl0
  have hl1' : hAddr κ (ldIx 0 0 0 (8 * W4.wb κ σ 399 + 1)) < bufB := by rw [ldIx_zero]; exact hl1
  obtain ⟨x2, o2, O2⟩ := shwC_sem I κ (by norm_num) (by omega) (by norm_num) hl0' hl1' O1 R1
  have k2 : ∀ r < regs, r ∉ wShw → rd (semXIR I (shwC κ) ⟨runPrims ps1 s.M, s.o⟩).M r = rd (runPrims ps1 s.M) r :=
    fun r hr h => keepW I (wf_shwC κ) O1.inv (wr_shwC κ) hr h
  rw [semXIR_seq]
  generalize semXIR I (shwC κ) ⟨runPrims ps1 s.M, s.o⟩ = s2 at x2 o2 O2 k2
  have hs2 := O2.inv.1
  simp only [regs] at hs2
  rw [semXIR_seq, semXIR_blk]
  rw [show semXIR I (.out oX) ⟨runPrims [.op .or qIx oX oX] s2.M, s2.o⟩ =
    ⟨runPrims [.op .or qIx oX oX] s2.M, s2.o.push (rd (runPrims [.op .or qIx oX oX] s2.M) oX)⟩ from rfl]
  have k3 : ∀ r, r ≠ qIx → rd (runPrims [.op .or qIx oX oX] s2.M) r = rd s2.M r := fun r hr => by
    simp only [runPrims, List.foldl, Prim.run]; rw [rd_set_ne (Ne.symm hr)]
  refine ⟨?_, of_mk (of_loK I (P := .blk [.op .or qIx oX oX]) (by simp [LoK, Prim.dst, qIx, regs])
    (by simp [WF, Prim.dst, qIx]) O2) _, ⟨?_, ?_, ?_⟩, ?_⟩
  · rw [k3 _ (by decide), x2]; simp [o2]
  · rw [k3 _ (by decide), k2 _ (by decide) (by decide)]; exact R1.cb
  · rw [k3 _ (by decide), k2 _ (by decide) (by decide)]; exact R1.jl
  · rw [k3 _ (by decide), k2 _ (by decide) (by decide)]; exact R1.dl
  · simp only [runPrims, List.foldl, Prim.run]; rw [rd_set_self (by simp only [qIx]; omega), or_self_eval, x2]

/-- **The chains' words** (shift 3 from word `8b + 1`, `24` words a chain). -/
theorem otsIR_sem (I : Array Word) (κ : NodeKind) (σ : ℕ) {M₀ : Mem} {X : Word} {b : ℕ}
    (hbd : W4.wb κ σ 0 = b) (hb : b < 2 ^ 50) (hl : ∀ m ≤ 8 * b + 4000, hAddr κ m < bufB) {t : St} (hO : OF M₀ t)
    (hR : LdR 0 0 0 t.M) (hx : rd t.M qIx = X) :
    (semXIR I (otsIR κ σ) t).o.toList = t.o.toList ++ (List.range wotsLen).flatMap
      (fun j => (List.range 4).map fun jj => shWd (ldG κ M₀ 0 0 0) 3 (8 * b + 1 + 24 * j + jj)) ∧
      OF M₀ (semXIR I (otsIR κ σ) t) ∧ LdR 0 0 0 (semXIR I (otsIR κ σ) t).M ∧
      rd (semXIR I (otsIR κ σ) t).M qIx = X := by
  have hs := hO.inv.1
  simp only [regs] at hs
  have hl' : ∀ m ≤ 8 * b + 4000, hAddr κ (ldIx 0 0 0 m) < bufB := fun m hm => by rw [ldIx_zero]; exact hl m hm
  rw [otsIR, semXIR_seq, semXIR_blk]
  set ps4 : List Prim := [.const qA (toWord 24), .const qB (toWord 39), .const qN (toWord (8 * W4.wb κ σ 0 + 1)),
      .const qLs (toWord wotsLen)] with hps4
  have k4 : ∀ r, r ∉ [qA, qB, qN, qLs] → rd (runPrims ps4 t.M) r = rd t.M r := fun r hr =>
    rd_runPrims_of_not_writes (fun p hp he => by
      simp only [hps4, List.mem_cons, List.mem_nil_iff, or_false] at hp
      rcases hp with rfl | rfl | rfl | rfl <;> simp only [Prim.dst] at he <;> subst he <;> simp at hr) _
  have R4 : SwR 0 0 0 3 (8 * b + 1) (runPrims ps4 t.M) := by
    refine ⟨⟨?_, ?_, ?_⟩, ?_, ?_, ?_⟩
    · rw [k4 _ (by decide)]; exact hR.cb
    · rw [k4 _ (by decide)]; exact hR.jl
    · rw [k4 _ (by decide)]; exact hR.dl
    all_goals simp only [hps4, runPrims, List.foldl, Prim.run]
    all_goals simp (disch := (simp only [size_set, qA, qB, qN, qLs] at *; omega)) only [rd_set_self, rd_set_ne]
    all_goals first | rw [hbd] | rfl
  have l4 : rd (runPrims ps4 t.M) qLs = toWord wotsLen := by
    simp only [hps4, runPrims, List.foldl, Prim.run]
    simp (disch := (simp only [size_set, qA, qB, qN, qLs] at *; omega)) only [rd_set_self, rd_set_ne]
  have ix4 : rd (runPrims ps4 t.M) qIx = X := by rw [k4 _ (by decide)]; exact hx
  have O4 : OF M₀ ⟨runPrims ps4 t.M, t.o⟩ := of_loK I (P := .blk ps4)
    (by simp [hps4, LoK, Prim.dst, regs, qA, qB, qN, qLs]) (by simp [hps4, WF, Prim.dst, qA, qB, qN, qLs]) hO
  generalize runPrims ps4 t.M = M4 at R4 l4 ix4 O4
  have L5 := loopK_emit I (c := qCs) (n := qLs) (K := wotsLen) (b := otsB κ)
    (fun j t => OF M₀ t ∧ SwR 0 0 0 3 (8 * b + 1 + 24 * j) t.M ∧ rd t.M qIx = X)
    (fun j => (List.range 4).map fun jj => shWd (ldG κ M₀ 0 0 0) 3 (8 * b + 1 + 24 * j + jj)) ⟨M4, t.o⟩ O4.inv
    (by decide) (by decide) (by decide) (by decide) l4
    ⟨of_entryK (by decide) (by decide) O4, swR_keep6 R4 fun r hr => by
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> exact entryK_frame _ (by decide) (by decide), by
      rw [entryK_frame _ (by decide) (by decide)]; exact ix4⟩
    (fun j t hj ⟨hO', hR', hx'⟩ => by
      have hjw : j < 133 := hj
      obtain ⟨a1, b1, c1, d1⟩ := shw4_sem I κ (sh := 3) (by norm_num) (by omega) (by norm_num)
        (fun jj hjj => hl' _ (by omega)) hO' hR'
      rw [otsB, semXIR_seq]
      generalize semXIR I (shw4 κ) t = t1 at a1 b1 c1 d1
      have hs1 := b1.inv.1
      simp only [regs] at hs1
      refine ⟨by rw [semXIR_blk]; exact a1, ?_, ?_, ?_⟩
      · exact ⟨inv_decS (inv_runPrims (by simp [Prim.dst, oK, qN]) b1.inv) (by decide), by simp [semXIR_blk, b1.size],
          fun y h1 h2 => by
            rw [rd_decS (by simp only [qCs, regs] at *; omega), semXIR_blk,
              rd_runPrims_of_not_writes (by simp only [regs] at h1; simp [Prim.dst, oK, qN]; omega), b1.low y h1 h2]⟩
      · have e : ∀ r, r ≠ qCs → r ≠ qN → r ≠ oK →
            rd (decS qCs (semXIR I (.blk [.const oK (toWord 20), .op .add qN qN oK]) t1)).M r = rd t1.M r :=
          fun r h1 h2 h3 => by
            rw [rd_decS (Ne.symm h1), semXIR_blk, rd_runPrims_of_not_writes (by simp [Prim.dst, Ne.symm h2, Ne.symm h3])]
        refine ⟨⟨by rw [e _ (by decide) (by decide) (by decide)]; exact c1.cb,
          by rw [e _ (by decide) (by decide) (by decide)]; exact c1.jl,
          by rw [e _ (by decide) (by decide) (by decide)]; exact c1.dl⟩, ?_,
          by rw [e _ (by decide) (by decide) (by decide)]; exact c1.a,
          by rw [e _ (by decide) (by decide) (by decide)]; exact c1.b⟩
        rw [rd_decS (by decide), semXIR_blk]
        simp only [runPrims, List.foldl, Prim.run]
        simp (disch := (simp only [size_set, oK, qN] at *; omega)) only [rd_set_self, rd_set_ne]
        rw [c1.n, add_toWord, show 8 * b + 1 + 24 * j + 4 + 20 = 8 * b + 1 + 24 * (j + 1) by ring]
      · rw [rd_decS (by decide), semXIR_blk, rd_runPrims_of_not_writes (by simp [Prim.dst, oK, qN, qIx]),
          d1 _ (by decide) (by decide), hx'])
  exact ⟨L5.1, L5.2.1, L5.2.2.1.toLdR, L5.2.2.2⟩

/-- **The path's words** (shift 1 from word `8b + 3728 + 16t`, offset `offB X t`). -/
theorem pathIR_sem (I : Array Word) (κ : NodeKind) (σ : ℕ) {M₀ : Mem} {X : Word} {b : ℕ}
    (hbd : W4.wb κ σ 0 = b) (hb : b < 2 ^ 50) (hl : ∀ m ≤ 8 * b + 4000, hAddr κ m < bufB) {t : St} (hO : OF M₀ t)
    (hR : LdR 0 0 0 t.M) (hx : rd t.M qIx = X) :
    (semXIR I (pathIR κ σ) t).o.toList = t.o.toList ++ (List.range sigHeight).flatMap
      (fun t => (List.range 4).map fun j => shWd (ldG κ M₀ 0 0 0) 1 (8 * b + 3728 + 16 * t + offB X t + j)) ∧
      OF M₀ (semXIR I (pathIR κ σ) t) := by
  have hs := hO.inv.1
  simp only [regs] at hs
  have hl' : ∀ m ≤ 8 * b + 4000, hAddr κ (ldIx 0 0 0 m) < bufB := fun m hm => by rw [ldIx_zero]; exact hl m hm
  have h466 : 8 * W4.wb κ σ 466 = 8 * b + 3728 := by rw [← hbd]; simp only [W4.wb]; ring
  rw [pathIR, semXIR_seq, semXIR_blk]
  set ps6 : List Prim := [.const qA (toWord 8), .const qB (toWord 55), .const qP (toWord (8 * W4.wb κ σ 466)),
      .const qTt 0, .const qLs (toWord sigHeight)] with hps6
  have k6 : ∀ r, r ∉ [qA, qB, qP, qTt, qLs] → rd (runPrims ps6 t.M) r = rd t.M r := fun r hr =>
    rd_runPrims_of_not_writes (fun p hp he => by
      simp only [hps6, List.mem_cons, List.mem_nil_iff, or_false] at hp
      rcases hp with rfl | rfl | rfl | rfl | rfl <;> simp only [Prim.dst] at he <;> subst he <;> simp at hr) _
  have v6 : rd (runPrims ps6 t.M) qA = toWord 8 ∧ rd (runPrims ps6 t.M) qB = toWord 55 ∧
      rd (runPrims ps6 t.M) qP = toWord (8 * b + 3728) ∧ rd (runPrims ps6 t.M) qTt = toWord 0 ∧
      rd (runPrims ps6 t.M) qLs = toWord sigHeight := by
    simp only [hps6, runPrims, List.foldl, Prim.run]
    simp (disch := (simp only [size_set, qA, qB, qP, qTt, qLs] at *; omega)) only [rd_set_self, rd_set_ne]
    refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> first | rw [h466] | exact True.intro | rfl
  have O6 : OF M₀ ⟨runPrims ps6 t.M, t.o⟩ := of_loK I (P := .blk ps6)
    (by simp [hps6, LoK, Prim.dst, regs, qA, qB, qP, qTt, qLs]) (by simp [hps6, WF, Prim.dst, qA, qB, qP, qTt, qLs]) hO
  have L6 := loopK_emit I (c := qCs) (n := qLs) (K := sigHeight) (b := pathB κ)
    (fun t st => OF M₀ st ∧ LdR 0 0 0 st.M ∧ rd st.M qA = toWord 8 ∧ rd st.M qB = toWord 55 ∧
      rd st.M qP = toWord (8 * b + 3728 + 16 * t) ∧ rd st.M qTt = toWord t ∧ rd st.M qIx = X)
    (fun t => (List.range 4).map fun j => shWd (ldG κ M₀ 0 0 0) 1 (8 * b + 3728 + 16 * t + offB X t + j))
    ⟨runPrims ps6 t.M, t.o⟩ O6.inv (by decide) (by decide) (by decide) (by decide) v6.2.2.2.2
    (by
      have e : ∀ r, r ≠ qCs → r ≠ cTmp → r ∉ [qA, qB, qP, qTt, qLs] →
          rd (entryK qCs qLs (toWord sigHeight) (runPrims ps6 t.M)) r = rd t.M r := fun r h1 h2 h3 => by
        rw [entryK_frame _ (Ne.symm h1) (Ne.symm h2), k6 r h3]
      exact ⟨of_entryK (by decide) (by decide) O6, ⟨by rw [e _ (by decide) (by decide) (by decide)]; exact hR.cb,
        by rw [e _ (by decide) (by decide) (by decide)]; exact hR.jl,
        by rw [e _ (by decide) (by decide) (by decide)]; exact hR.dl⟩,
        by rw [entryK_frame _ (by decide) (by decide)]; exact v6.1,
        by rw [entryK_frame _ (by decide) (by decide)]; exact v6.2.1,
        by rw [entryK_frame _ (by decide) (by decide)]; simpa using v6.2.2.1,
        by rw [entryK_frame _ (by decide) (by decide)]; exact v6.2.2.2.1,
        by rw [e _ (by decide) (by decide) (by decide)]; exact hx⟩)
    (fun t st ht ⟨hO', hR', ha', hb', hp', ht', hx'⟩ => by
      have ht16 : t < 16 := ht
      rw [pathB, semXIR_seq, semXIR_blk]
      have hsS := hO'.inv.1
      simp only [regs] at hsS
      set ps7 : List Prim := [.op .shr qBt qIx qTt, .op .and qBt qBt cOne, .const oK (toWord 2), .op .shl qBt qBt oK,
          .const oK (toWord 4), .op .sub qN oK qBt, .op .add qN qN qP] with hps7
      have k7 : ∀ r, r ∉ [qBt, oK, qN] → rd (runPrims ps7 st.M) r = rd st.M r := fun r hr =>
        rd_runPrims_of_not_writes (fun p hp he => by
          simp only [hps7, List.mem_cons, List.mem_nil_iff, or_false] at hp
          rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp only [Prim.dst] at he <;> subst he <;>
            simp at hr) _
      have n7 : rd (runPrims ps7 st.M) qN = toWord (8 * b + 3728 + 16 * t + offB X t) := by
        simp only [hps7, runPrims, List.foldl, Prim.run]
        simp (disch := (simp only [size_set, qBt, oK, qN, qIx, qTt, qP, cOne] at *; omega)) only
          [rd_set_self, rd_set_ne]
        rw [hx', ht', one_cOne hO'.inv, offB_eval X (by omega), hp', add_toWord]
        congr 1; ring
      have O7 : OF M₀ ⟨runPrims ps7 st.M, st.o⟩ := of_loK I (P := .blk ps7)
        (by simp [hps7, LoK, Prim.dst, regs, qBt, oK, qN]) (by simp [hps7, WF, Prim.dst, qBt, oK, qN]) hO'
      have R7 : SwR 0 0 0 1 (8 * b + 3728 + 16 * t + offB X t) (runPrims ps7 st.M) :=
        ⟨⟨by rw [k7 _ (by decide)]; exact hR'.cb, by rw [k7 _ (by decide)]; exact hR'.jl,
          by rw [k7 _ (by decide)]; exact hR'.dl⟩, n7, by rw [k7 _ (by decide)]; exact ha',
          by rw [k7 _ (by decide)]; exact hb'⟩
      have hof : offB X t ≤ 4 := by unfold offB; split_ifs <;> omega
      obtain ⟨a1, b1, c1, d1⟩ := shw4_sem I κ (sh := 1) (by norm_num) (by omega) (by norm_num)
        (fun jj hjj => hl' _ (by omega)) O7 R7
      rw [semXIR_seq]
      generalize semXIR I (shw4 κ) ⟨runPrims ps7 st.M, st.o⟩ = t1 at a1 b1 c1 d1
      have hs1 := b1.inv.1
      simp only [regs] at hs1
      have kk : ∀ r < regs, r ∉ [qBt, oK, qN] ++ wShw → rd t1.M r = rd st.M r := fun r hr h => by
        simp only [List.mem_append, List.mem_cons, List.mem_nil_iff, or_false, not_or] at h
        rw [d1 r hr (by simp only [List.mem_cons, not_or]; exact ⟨h.1.2.2, h.2⟩),
          k7 r (by simp [h.1.1, h.1.2.1, h.1.2.2])]
      have e : ∀ r, r ≠ qCs → r ≠ oK → r ≠ qP → r ≠ qTt →
          rd (decS qCs (semXIR I (.blk [.const oK (toWord 16), .op .add qP qP oK, .op .add qTt qTt cOne]) t1)).M r =
            rd t1.M r := fun r h1 h2 h3 h4 => by
        rw [rd_decS (Ne.symm h1), semXIR_blk, rd_runPrims_of_not_writes (by simp [Prim.dst, Ne.symm h2,
          Ne.symm h3, Ne.symm h4])]
      refine ⟨by rw [semXIR_blk]; simpa using a1, ⟨inv_decS (inv_runPrims (by simp [Prim.dst, oK, qP, qTt]) b1.inv)
          (by decide), by simp [semXIR_blk, b1.size], fun y h1 h2 => by
            rw [rd_decS (by simp only [qCs, regs] at *; omega), semXIR_blk,
              rd_runPrims_of_not_writes (by simp only [regs] at h1; simp [Prim.dst, oK, qP, qTt]; omega),
              b1.low y h1 h2]⟩,
        ⟨by rw [e _ (by decide) (by decide) (by decide) (by decide)]; exact c1.cb,
          by rw [e _ (by decide) (by decide) (by decide) (by decide)]; exact c1.jl,
          by rw [e _ (by decide) (by decide) (by decide) (by decide)]; exact c1.dl⟩,
        by rw [e _ (by decide) (by decide) (by decide) (by decide)]; exact c1.a,
        by rw [e _ (by decide) (by decide) (by decide) (by decide)]; exact c1.b, ?_, ?_,
        by rw [e _ (by decide) (by decide) (by decide) (by decide), kk _ (by decide) (by decide)]; exact hx'⟩
      · rw [rd_decS (by decide), semXIR_blk]
        simp only [runPrims, List.foldl, Prim.run]
        simp (disch := (simp only [size_set, oK, qP, qTt] at *; omega)) only [rd_set_self, rd_set_ne]
        rw [kk _ (by decide) (by decide), hp', add_toWord, show 8 * b + 3728 + 16 * t + 16 = 8 * b + 3728 + 16 * (t + 1)
          by ring]
      · rw [rd_decS (by decide), semXIR_blk]
        simp only [runPrims, List.foldl, Prim.run]
        simp (disch := (simp only [size_set, oK, qP, qTt, cOne] at *; omega)) only [rd_set_self, rd_set_ne]
        rw [kk _ (by decide) (by decide), ht', one_cOne b1.inv, add_one_toWord])
  exact ⟨L6.1, L6.2.1⟩

/-- **The signature's words are emitted** (`sigL` over the heap's H words from WOTS block `b`), the
frame kept. -/
theorem sigIR_sem (I : Array Word) (κ : NodeKind) (σ : ℕ) {M₀ : Mem} {s : St} (hO : OF M₀ s)
    (hb : W4.wb κ σ 0 < 2 ^ 50) (hl : ∀ m ≤ 8 * W4.wb κ σ 0 + 4000, hAddr κ m < bufB) :
    (semXIR I (sigIR κ σ) s).o.toList = s.o.toList ++ sigL (fun m => rd M₀ (hAddr κ m)) (W4.wb κ σ 0) ∧
      OF M₀ (semXIR I (sigIR κ σ) s) := by
  obtain ⟨b, hbd⟩ : ∃ b, W4.wb κ σ 0 = b := ⟨_, rfl⟩
  have h399 : 8 * W4.wb κ σ 399 = 8 * b + 3192 := by rw [← hbd]; simp only [W4.wb]; ring
  rw [hbd] at hb hl ⊢
  have hGe : ldG κ M₀ 0 0 0 = fun m => rd M₀ (hAddr κ m) := funext fun m => by rw [ldG, ldIx_zero]
  rw [← hGe]
  obtain ⟨o1, O1, R1, x1⟩ := sigHd_sem I κ σ hO (by omega) (by rw [h399]; exact hl _ (by omega))
    (by rw [h399]; exact hl _ (by omega))
  rw [sigIR, semXIR_seq]
  generalize semXIR I (sigHd κ σ) s = s1 at o1 O1 R1 x1
  obtain ⟨o2, O2, R2, x2⟩ := otsIR_sem I κ σ hbd hb hl O1 R1 x1
  rw [semXIR_seq]
  generalize semXIR I (otsIR κ σ) s1 = s2 at o2 O2 R2 x2
  obtain ⟨o3, O3⟩ := pathIR_sem I κ σ hbd hb hl O2 R2 x2
  refine ⟨?_, O3⟩
  rw [o3, o2, o1, h399, sigL]
  simp only [List.append_assoc, List.cons_append, List.singleton_append, List.nil_append]

end FR.X

end G6_FRXOut4E

section G6_FRXOut4F

-- New for `flock-recursive` (BLUEPRINT revision 4.1, §6.2 step 5; stage S-H4, pass 11, item 2: the
-- node output's segment emitters and the aggregate's segment count). 3.x analogue: `FRXOutRun`'s
-- `kflagIR`/`slotIR` (one kind flag, no ladder, no count).

/-!
# The segments over the buffer, the ladder, the segment count

After the copy (`FRXOut4R.cpSeg_sem`) segment `i`'s words are the buffer's (`bufB`, shape
`apB`), so 3.x's `segIR` emits them unchanged (`FRXOut.segIR_sem` over `src M apB bufB`):

* **`bufSeg sg`** sets the buffer's context (`setB`) and emits `segOut (src M apB bufB) false 0 sg`;
* **`pfIR`** emits the proof's segment at the ladder of the buffer's word `10` (**`pfIR_sem`**:
  `pSeg4 seq4 (mOfB b)`, `b` the word's low byte; the three ladders are three copies, chosen by
  `b = 'P'` and `b ∈ {'K', 'M'}`, **`mOfB_eq`**);
* **`kSelIR κ a`** computes aggregate `a`'s segment count `kSel κ a w` into `qK` from the
  sub-slots' selector words (**`kSelIR_sem`**: per sub-slot the three selectors' `F` sum is `1`
  iff its low word is `1` and its high word `0`; the count stops at the first sub-slot that fails).
-/

namespace FR.X

open RecursionFast FR.Read FR.Rev4 FR.Snd

attribute [local irreducible] entryK storeM runPrims

/-! ## Specification -/

/-- The buffer's context: `oR := bufB`, depth-0 base `0`, the kind flag `0`. -/
def setB : XIR := .blk [.const oR (toWord bufB), .const (oBd 0) 0, .const oKF 0]

/-- **A segment over the buffer.** -/
def bufSeg (sg : Seg) : XIR := .seq setB (segIR apB 0 sg)

/-- The ladder flags from the buffer's word `10`'s low byte `b`: `qF0 := (b = 'P')`,
`qF1 := (b = 'K') ∨ (b = 'M')`. -/
def ladF : XIR :=
  .seq (.blk [.const oU (toWord 10)]) (.seq (ldw apB)
    (.blk [.const oK (toWord 255), .op .and oX oX oK, .const oK (toWord 0x50), .op .eq qF0 oX oK,
      .const oK (toWord 0x4B), .op .eq qF1 oX oK, .const oK (toWord 0x4D), .op .eq qT1 oX oK,
      .op .or qF1 qF1 qT1]))

/-- The proof's segment at ladder `m`. -/
def pfS (m : ℕ) : XIR := segIR apB 0 (pSeg4 seq4 m)

/-- **The proof over the buffer**, at the ladder of its word `10`. -/
def pfIR : XIR := .seq setB (.seq ladF (.ite qF0 (pfS 30) (.ite qF1 (pfS 31) (pfS 32))))

/-- **The ladder of a low byte**: `'P'` (`L30`) `30`; `'K'` (`L31`), `'M'` (`N2`) `31`; else `32`. -/
theorem mOfB_eq (b : UInt8) : mOfB b = if b = 0x50 then 30 else if b = 0x4B ∨ b = 0x4D then 31 else 32 := by
  unfold mOfB Snd.CKind.ofByte? SegKind.ofByte? NodeKind.ofByte?
  by_cases h1 : b = 0x50 <;> by_cases h2 : b = 0x4B <;> by_cases h3 : b = 0x4C <;> by_cases h4 : b = 0x4D <;>
    by_cases h5 : b = 0x4E <;> by_cases h6 : b = 0x4F <;> simp_all <;> rfl

/-! ## Proof helpers: the buffer's shape -/

theorem hA_B (x : Word) : regs ≤ (addrW apB (toWord bufB) x).toNat := by
  have := addrH_toNat (st := 20) (R := bufB) (u := x.toNat) le_rfl (by decide) x.isLt
  rw [toWord_toNat] at this
  rw [apB, this]; simp only [regs, bufB]; omega

theorem src_bufA (M : Mem) {u : ℕ} (hu : u < 2 ^ 64) : src M apB bufB u = rd M (bufA u) := by
  rw [src, bufA_apB hu]

theorem okSeg_pf : ∀ m ∈ [30, 31, 32], okSeg (pSeg4 seq4 m) = true ∧ depthSeg (pSeg4 seq4 m) ≤ 1 := by
  decide +kernel

theorem okSeg_tr : okSeg (trSeg4 seq4) = true ∧ depthSeg (trSeg4 seq4) ≤ 2 ∧ okSeg (trBody4 seq4) = true ∧
    depthSeg (trBody4 seq4) ≤ 2 := by
  decide +kernel

theorem low_iff (x : Word) {c : ℕ} (hc : c < 256) : x &&& toWord 255 = toWord c ↔ x.toNat.toUInt8 = c.toUInt8 := by
  rw [← BitVec.toNat_inj, ← UInt8.toNat_inj, BitVec.toNat_and, toNat_toWord (by norm_num : 255 < 2 ^ 64),
    toNat_toWord (by omega), show (255 : ℕ) = 2 ^ 8 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]
  simp only [Nat.toUInt8, UInt8.toNat_ofNat']
  omega

/-- The low byte test as the machine computes it. -/
theorem low_eq (x : Word) {c : ℕ} (hc : c < 256) :
    XOp.eq.eval (XOp.and.eval x (toWord 255)) (toWord c) = if x.toNat.toUInt8 = c.toUInt8 then 1 else 0 := by
  simp only [XOp.eval]
  by_cases h : x.toNat.toUInt8 = c.toUInt8
  · have := (low_iff x hc).2 h; simp [this, h]
  · have := mt (low_iff x hc).1 h; simp [this, h]

/-! ## The buffer's segments -/

theorem setB_ctx (I : Array Word) {t : St} (hM : Inv t.M) :
    Ctx t.M bufB false (semXIR I setB t) ∧ rd (semXIR I setB t).M (oBd 0) = toWord 0 := by
  have hs := hM.1
  simp only [regs] at hs
  rw [setB, semXIR_blk]
  refine ⟨⟨inv_runPrims (by simp [Prim.dst, oR, oBd, oKF]) hM, size_runPrims _ _, fun y hy => ?_, ?_, ?_⟩, ?_⟩
  · exact rd_runPrims_of_not_writes (by simp only [regs] at hy; simp [Prim.dst, oR, oBd, oKF]; omega) _
  all_goals simp only [runPrims, List.foldl, Prim.run]
  all_goals simp (disch := (simp only [size_set, oR, oBd, oKF] at *; omega)) only [rd_set_self, rd_set_ne]
  all_goals first | rfl | simp

/-- **A segment over the buffer** emits its words over the heap's buffer; the heap is kept. -/
theorem bufSeg_sem (I : Array Word) (sg : Seg) (hok : okSeg sg = true) (hd : depthSeg sg ≤ 9) {M₀ : Mem}
    {t : St} (hO : OF M₀ t) :
    (semXIR I (bufSeg sg) t).o.toList = t.o.toList ++ segOut (src t.M apB bufB) false 0 sg ∧
      OF M₀ (semXIR I (bufSeg sg) t) ∧ ∀ y, regs ≤ y → rd (semXIR I (bufSeg sg) t).M y = rd t.M y := by
  obtain ⟨c1, b1⟩ := setB_ctx I hO.inv
  rw [bufSeg, semXIR_seq]
  have o1 : (semXIR I setB t).o = t.o := rfl
  generalize semXIR I setB t = t1 at c1 b1 o1
  obtain ⟨o2, c2, -⟩ := seg_step I apB hA_B sg hok hd c1 b1
  refine ⟨by rw [o2, o1], ⟨c2.inv, c2.size.trans hO.size, fun y h1 h2 => (c2.heap y h1).trans (hO.low y h1 h2)⟩,
    c2.heap⟩

theorem ladF_sem (I : Array Word) {M : Mem} {t : St} (hc : Ctx M bufB false t) (hb : rd t.M (oBd 0) = toWord 0) :
    (semXIR I ladF t).o = t.o ∧ Ctx M bufB false (semXIR I ladF t) ∧
      rd (semXIR I ladF t).M (oBd 0) = toWord 0 ∧
      rd (semXIR I ladF t).M qF0 = (if (src M apB bufB 10).toNat.toUInt8 = (0x50 : ℕ).toUInt8 then 1 else 0) ∧
      rd (semXIR I ladF t).M qF1 = (if (src M apB bufB 10).toNat.toUInt8 = (0x4B : ℕ).toUInt8 then 1 else 0) |||
        (if (src M apB bufB 10).toNat.toUInt8 = (0x4D : ℕ).toUInt8 then 1 else 0) := by
  have hs := hc.inv.1
  simp only [regs] at hs
  simp only [ladF, semXIR_seq, semXIR_blk]
  have c1 := ctx_blk (ps := [.const oU (toWord 10)]) (by simp [Prim.dst, oU, oR, oKF, regs]) hc
  have u1 : rd (runPrims [.const oU (toWord 10)] t.M) oU = toWord 10 := by
    simp only [runPrims, List.foldl, Prim.run]; rw [rd_set_self (by simp only [oU]; omega)]
  have b1 : rd (runPrims [.const oU (toWord 10)] t.M) (oBd 0) = toWord 0 := by
    rw [rd_runPrims_of_not_writes (by simp [Prim.dst, oU, oBd])]; exact hb
  obtain ⟨l1, l2⟩ := ldw_src I apB hA_B _ c1 u1
  have c2 := ctx_ldw I apB c1
  have b2 := ldw_keep I apB _ c1.inv (r := oBd 0) (by simp [oBd, regs]) (by simp [oBd, oK, oT1, oT2, oT3, oAd, oX])
  generalize semXIR I (ldw apB) ⟨runPrims [.const oU (toWord 10)] t.M, t.o⟩ = t2 at l1 l2 c2 b2
  have hs2 := c2.inv.1
  simp only [regs] at hs2
  refine ⟨l2, ctx_blk (by simp [Prim.dst, oK, oX, qF0, qF1, qT1, oR, oKF, regs]) c2, ?_, ?_, ?_⟩
  · rw [rd_runPrims_of_not_writes (by simp [Prim.dst, oK, oX, qF0, qF1, qT1, oBd]), b2, b1]
  · simp only [runPrims, List.foldl, Prim.run]
    simp (disch := (simp only [size_set, oK, oX, qF0, qF1, qT1] at *; omega)) only [rd_set_self, rd_set_ne]
    rw [l1, low_eq _ (by norm_num)]
  · simp only [runPrims, List.foldl, Prim.run]
    simp (disch := (simp only [size_set, oK, oX, qF0, qF1, qT1] at *; omega)) only [rd_set_self, rd_set_ne]
    rw [l1]
    have e : ∀ c, c < 256 → XOp.eq.eval (XOp.and.eval (src M apB bufB 10) (toWord 255)) (toWord c) =
        if (src M apB bufB 10).toNat.toUInt8 = c.toUInt8 then 1 else 0 := fun c hc => low_eq _ hc
    rw [e _ (by norm_num), e _ (by norm_num)]
    rfl

theorem mOfB_flags (x : Word) :
    mOfB x.toNat.toUInt8 = if x.toNat.toUInt8 = (0x50 : ℕ).toUInt8 then 30 else
      if x.toNat.toUInt8 = (0x4B : ℕ).toUInt8 ∨ x.toNat.toUInt8 = (0x4D : ℕ).toUInt8 then 31 else 32 := by
  rw [mOfB_eq]; rfl

/-- **The proof's segment over the buffer**, at the ladder of the buffer's word `10`. -/
theorem pfIR_sem (I : Array Word) {M₀ : Mem} {t : St} (hO : OF M₀ t) :
    (semXIR I pfIR t).o.toList = t.o.toList ++
      segOut (src t.M apB bufB) false 0 (pSeg4 seq4 (mOfB (src t.M apB bufB 10).toNat.toUInt8)) ∧
      OF M₀ (semXIR I pfIR t) ∧ ∀ y, regs ≤ y → rd (semXIR I pfIR t).M y = rd t.M y := by
  obtain ⟨c1, b1⟩ := setB_ctx I hO.inv
  rw [pfIR, semXIR_seq]
  have o1 : (semXIR I setB t).o = t.o := rfl
  generalize semXIR I setB t = t1 at c1 b1 o1
  obtain ⟨o2, c2, b2, f0, f1⟩ := ladF_sem I c1 b1
  rw [semXIR_seq]
  generalize semXIR I ladF t1 = t2 at o2 c2 b2 f0 f1
  set x := src t.M apB bufB 10
  have hpf : ∀ m ∈ [30, 31, 32], (semXIR I (pfS m) t2).o.toList = t.o.toList ++
      segOut (src t.M apB bufB) false 0 (pSeg4 seq4 m) ∧ OF M₀ (semXIR I (pfS m) t2) ∧
      ∀ y, regs ≤ y → rd (semXIR I (pfS m) t2).M y = rd t.M y := fun m hm => by
    obtain ⟨g1, g2⟩ := okSeg_pf m hm
    obtain ⟨o3, c3, -⟩ := seg_step I apB hA_B (pSeg4 seq4 m) g1 (by omega) c2 b2
    exact ⟨by rw [pfS, o3, o2, o1], ⟨c3.inv, c3.size.trans hO.size, fun y h1 h2 => (c3.heap y h1).trans
      (hO.low y h1 h2)⟩, c3.heap⟩
  rw [mOfB_flags x, semXIR_ite, f0]
  by_cases h0 : x.toNat.toUInt8 = (0x50 : ℕ).toUInt8
  · simp only [h0, ↓reduceIte]
    first | exact hpf 30 (by simp) | (rw [if_neg (by decide : (1 : Word) ≠ 0)]; exact hpf 30 (by simp))
  · simp only [h0, ↓reduceIte]
    rw [semXIR_ite, f1]
    by_cases h1 : x.toNat.toUInt8 = (0x4B : ℕ).toUInt8 ∨ x.toNat.toUInt8 = (0x4D : ℕ).toUInt8
    · rw [if_pos h1]
      have : ((if x.toNat.toUInt8 = (0x4B : ℕ).toUInt8 then (1 : Word) else 0) |||
          if x.toNat.toUInt8 = (0x4D : ℕ).toUInt8 then 1 else 0) ≠ 0 := by
        rcases h1 with h | h <;> simp [h]
      rw [if_neg this]; exact hpf 31 (by simp)
    · rw [if_neg h1]
      have : ((if x.toNat.toUInt8 = (0x4B : ℕ).toUInt8 then (1 : Word) else 0) |||
          if x.toNat.toUInt8 = (0x4D : ℕ).toUInt8 then 1 else 0) = 0 := by
        rw [not_or] at h1; rw [if_neg h1.1, if_neg h1.2]; rfl
      rw [if_pos this]; exact hpf 32 (by simp)

end FR.X

end G6_FRXOut4F

section G6_FRXOut4K

-- New for `flock-recursive` (BLUEPRINT revision 4.1, §6.2 step 5, A.7; stage S-H4, pass 11, item 2: the
-- aggregate's segment count on the machine). 3.x has no aggregate.

/-!
# The aggregate's segment count on the machine (`kSelIR`)

Aggregate `a`'s segment count is `kSel κ a w` (`FRXOut4`): the first sub-slot `i < maxK` whose three
activity selectors do not sum to `1`, else `maxK`. The selectors are decoded cells (rows 1–3), so
after the decode each is two heap words at `wAddr`. `F` addition is coefficientwise XOR, so the
sum is `1` iff the XOR of the low words is `1` and that of the high words `0` (**`sum3_one`**).

**`kSelIR κ a maxK`** keeps a flag `alive` (all sub-slots so far selected) and adds it to the count
`qK` per sub-slot (**`kSelIR_sem`**: `qK = kSel κ a w`; **`kc_find`**: the running count is the
first failing index).
-/

namespace FR.X

open RecursionFast FR.Read FR.Rev4 FR.Snd

attribute [local irreducible] entryK storeM runPrims

/-! ## Specification -/

/-- Selector `ι` of aggregate `a`'s sub-slot `i`: its cell's heap address. -/
def selA (κ : NodeKind) (a i : ℕ) (ι : Kind) : ℕ := wAddr κ (κ.oneCell + selR (N4c.sub κ a i) ι)

/-- The flag and the count: `qS0 := (Σ low = 1) ∧ (Σ high = 0)`, `alive &&= qS0`, `qK += alive`. -/
def kPs : List Prim :=
  [.op .xor qS0 qS0 qS2, .op .xor qS0 qS0 qS4, .op .xor qS1 qS1 qS3, .op .xor qS1 qS1 qS5,
   .op .eq qS0 qS0 cOne, .const oK 0, .op .eq qS1 qS1 oK, .op .and qS0 qS0 qS1, .op .and qAl qAl qS0,
   .op .add qK qK qAl]

/-- **Sub-slot `i`'s step**: the three selectors' six words, then `kPs`. -/
def kStep (κ : NodeKind) (a i : ℕ) : XIR :=
  .seq (ldA qS0 (selA κ a i .L32)) (.seq (ldA qS1 (selA κ a i .L32 + 1))
  (.seq (ldA qS2 (selA κ a i .P30)) (.seq (ldA qS3 (selA κ a i .P30 + 1))
  (.seq (ldA qS4 (selA κ a i .N30)) (.seq (ldA qS5 (selA κ a i .N30 + 1)) (.blk kPs))))))

/-- **The segment count over the first `n` sub-slots** (`alive := 1`, `qK := 0`, then the steps). -/
def kSelIR (κ : NodeKind) (a : ℕ) : ℕ → XIR
  | 0 => .blk [.const qAl 1, .const qK 0]
  | i + 1 => .seq (kSelIR κ a i) (kStep κ a i)

/-- The running count: per index, `1` while every flag so far holds. -/
def kc (p : ℕ → Bool) : ℕ → ℕ
  | 0 => 0
  | i + 1 => kc p i + if (List.range (i + 1)).all p then 1 else 0

/-! ## The count, purely -/

theorem kc_find (p : ℕ → Bool) : ∀ n, kc p n = ((List.range n).find? fun i => !p i).getD n
  | 0 => rfl
  | n + 1 => by
    rw [kc, kc_find p n, List.range_succ, List.find?_append, List.all_append]
    cases h : (List.range n).find? fun i => !p i with
    | some j =>
      have hj := List.find?_some h
      have hjm := List.mem_range.1 (List.mem_of_find?_eq_some h)
      have ha : (List.range n).all p = false := by
        rw [List.all_eq_false]; exact ⟨j, List.mem_range.2 hjm, by simpa using hj⟩
      simp [ha]
    | none =>
      have ha : (List.range n).all p = true := by
        rw [List.all_eq_true]; intro x hx
        have := List.find?_eq_none.1 h x hx
        simpa using this
      cases hp : p n <;> simp [ha, hp]

/-! ## Proof helpers: words -/

theorem F_one_iff (u v : Word) : (⟨wB u, wB v⟩ : F) = 1 ↔ u = 1 ∧ v = 0 := by
  constructor
  · intro h
    have h1 := congrArg (fun x : F => x.c₀.val.toBitVec) h
    have h2 := congrArg (fun x : F => x.c₁.val.toBitVec) h
    exact ⟨h1, h2⟩
  · rintro ⟨rfl, rfl⟩; rfl

/-- **Three selectors sum to `1`** iff the low words XOR to `1` and the high words to `0`. -/
theorem sum3_one (M : Mem) (a b c : ℕ) :
    rdF M a + rdF M b + rdF M c = 1 ↔
      (rd M a ^^^ rd M b ^^^ rd M c = 1 ∧ rd M (a + 1) ^^^ rd M (b + 1) ^^^ rd M (c + 1) = 0) :=
  F_one_iff _ _

theorem ite_and_w (A B : Prop) [Decidable A] [Decidable B] :
    XOp.and.eval (if A then (1 : Word) else 0) (if B then 1 else 0) = if A ∧ B then 1 else 0 := by
  by_cases a : A <;> by_cases b : B <;> simp [a, b, XOp.eval]

theorem eq_w (x y : Word) : XOp.eq.eval x y = if x = y then 1 else 0 := rfl

/-! ## The step -/

/-- The step's invariant after `i` sub-slots. -/
structure KInv (M₀ : Mem) (p : ℕ → Bool) (i : ℕ) (t : St) : Prop where
  of : OF M₀ t
  al : rd t.M qAl = if (List.range i).all p then 1 else 0
  k : rd t.M qK = toWord (kc p i)

/-- **One sub-slot**: its flag is `p i` when the heap's selector words are the cells'. -/
theorem kStep_sem (I : Array Word) (κ : NodeKind) (a i : ℕ) {M₀ : Mem} {p : ℕ → Bool}
    (hA : ∀ ι, regs ≤ selA κ a i ι ∧ selA κ a i ι + 1 < bufB)
    (hp : p i = decide (rdF M₀ (selA κ a i .L32) + rdF M₀ (selA κ a i .P30) + rdF M₀ (selA κ a i .N30) = 1))
    (hi : kc p i < 2 ^ 32) {t : St} (h : KInv M₀ p i t) :
    (semXIR I (kStep κ a i) t).o = t.o ∧ KInv M₀ p (i + 1) (semXIR I (kStep κ a i) t) := by
  have hs := h.of.inv.1
  simp only [regs] at hs
  have hA' : ∀ ι, regs ≤ selA κ a i ι + 1 ∧ selA κ a i ι + 1 < 2 ^ 64 ∧ selA κ a i ι < 2 ^ 64 :=
    fun ι => ⟨by have := (hA ι).1; omega, by have := (hA ι).2; simp only [bufB] at this; omega,
      by have := (hA ι).2; simp only [bufB] at this; omega⟩
  have L := fun (d : ℕ) (adr : ℕ) (t : St) (h1 : 4 ≤ d) (h2 : d < regs) (h3 : d ≠ oAd) (h4 : regs ≤ adr)
    (h5 : adr < 2 ^ 64) (hO : OF M₀ t) => ldA_sem I (a := adr) h1 h2 h3 h4 h5 hO
  rw [kStep, semXIR_seq]
  obtain ⟨x0, o0, O0, k0⟩ := L qS0 _ t (by decide) (by decide) (by decide) (hA .L32).1 (hA' .L32).2.2 h.of
  generalize semXIR I (ldA qS0 (selA κ a i .L32)) t = t0 at x0 o0 O0 k0
  rw [semXIR_seq]
  obtain ⟨x1, o1, O1, k1⟩ := L qS1 _ t0 (by decide) (by decide) (by decide) (hA' .L32).1 (hA' .L32).2.1 O0
  generalize semXIR I (ldA qS1 (selA κ a i .L32 + 1)) t0 = t1 at x1 o1 O1 k1
  rw [semXIR_seq]
  obtain ⟨x2, o2, O2, k2⟩ := L qS2 _ t1 (by decide) (by decide) (by decide) (hA .P30).1 (hA' .P30).2.2 O1
  generalize semXIR I (ldA qS2 (selA κ a i .P30)) t1 = t2 at x2 o2 O2 k2
  rw [semXIR_seq]
  obtain ⟨x3, o3, O3, k3⟩ := L qS3 _ t2 (by decide) (by decide) (by decide) (hA' .P30).1 (hA' .P30).2.1 O2
  generalize semXIR I (ldA qS3 (selA κ a i .P30 + 1)) t2 = t3 at x3 o3 O3 k3
  rw [semXIR_seq]
  obtain ⟨x4, o4, O4, k4⟩ := L qS4 _ t3 (by decide) (by decide) (by decide) (hA .N30).1 (hA' .N30).2.2 O3
  generalize semXIR I (ldA qS4 (selA κ a i .N30)) t3 = t4 at x4 o4 O4 k4
  rw [semXIR_seq]
  obtain ⟨x5, o5, O5, k5⟩ := L qS5 _ t4 (by decide) (by decide) (by decide) (hA' .N30).1 (hA' .N30).2.1 O4
  generalize semXIR I (ldA qS5 (selA κ a i .N30 + 1)) t4 = t5 at x5 o5 O5 k5
  -- the six words
  have w0 : rd t5.M qS0 = rd M₀ (selA κ a i .L32) := by
    rw [k5 _ (by decide) (by decide), k4 _ (by decide) (by decide), k3 _ (by decide) (by decide),
      k2 _ (by decide) (by decide), k1 _ (by decide) (by decide), x0,
      h.of.low _ (hA .L32).1 (by have := (hA .L32).2; omega)]
  have w1 : rd t5.M qS1 = rd M₀ (selA κ a i .L32 + 1) := by
    rw [k5 _ (by decide) (by decide), k4 _ (by decide) (by decide), k3 _ (by decide) (by decide),
      k2 _ (by decide) (by decide), x1, O0.low _ (hA' .L32).1 (hA .L32).2]
  have w2 : rd t5.M qS2 = rd M₀ (selA κ a i .P30) := by
    rw [k5 _ (by decide) (by decide), k4 _ (by decide) (by decide), k3 _ (by decide) (by decide), x2,
      O1.low _ (hA .P30).1 (by have := (hA .P30).2; omega)]
  have w3 : rd t5.M qS3 = rd M₀ (selA κ a i .P30 + 1) := by
    rw [k5 _ (by decide) (by decide), k4 _ (by decide) (by decide), x3, O2.low _ (hA' .P30).1 (hA .P30).2]
  have w4 : rd t5.M qS4 = rd M₀ (selA κ a i .N30) := by
    rw [k5 _ (by decide) (by decide), x4, O3.low _ (hA .N30).1 (by have := (hA .N30).2; omega)]
  have w5 : rd t5.M qS5 = rd M₀ (selA κ a i .N30 + 1) := by
    rw [x5, O4.low _ (hA' .N30).1 (hA .N30).2]
  have kt : ∀ r, r ∉ [qS0, qS1, qS2, qS3, qS4, qS5, oAd] → rd t5.M r = rd t.M r := fun r hr => by
    simp only [List.mem_cons, List.mem_nil_iff, or_false, not_or] at hr
    rw [k5 _ hr.2.2.2.2.2.1 hr.2.2.2.2.2.2, k4 _ hr.2.2.2.2.1 hr.2.2.2.2.2.2, k3 _ hr.2.2.2.1 hr.2.2.2.2.2.2,
      k2 _ hr.2.2.1 hr.2.2.2.2.2.2, k1 _ hr.2.1 hr.2.2.2.2.2.2, k0 _ hr.1 hr.2.2.2.2.2.2]
  have al5 : rd t5.M qAl = if (List.range i).all p then 1 else 0 := by rw [kt _ (by decide)]; exact h.al
  have kk5 : rd t5.M qK = toWord (kc p i) := by rw [kt _ (by decide)]; exact h.k
  have hs5 := O5.inv.1
  simp only [regs] at hs5
  rw [semXIR_blk]
  have hall : (List.range (i + 1)).all p = ((List.range i).all p && p i) := by
    rw [List.range_succ, List.all_append]; simp
  have hpi : (p i = true) ↔ (rd M₀ (selA κ a i .L32) ^^^ rd M₀ (selA κ a i .P30) ^^^ rd M₀ (selA κ a i .N30) = 1 ∧
      rd M₀ (selA κ a i .L32 + 1) ^^^ rd M₀ (selA κ a i .P30 + 1) ^^^ rd M₀ (selA κ a i .N30 + 1) = 0) := by
    rw [hp, decide_eq_true_iff]; exact sum3_one M₀ _ _ _
  have av : rd (runPrims kPs t5.M) qAl = if (List.range (i + 1)).all p then 1 else 0 := by
    simp only [kPs, runPrims, List.foldl, Prim.run]
    simp (disch := (simp only [size_set, qS0, qS1, qS2, qS3, qS4, qS5, qAl, qK, oK, cOne]; omega)) only
      [rd_set_self, rd_set_ne]
    rw [w0, w1, w2, w3, w4, w5, al5, one_cOne O5.inv, eq_w, eq_w]
    simp only [XOp.eval]
    rw [hall]
    by_cases ha : (List.range i).all p = true <;> by_cases hq : p i = true
    · have := hpi.1 hq; simp [ha, hq, this.1, this.2]
    · have : ¬ (_ ∧ _) := fun h' => hq (hpi.2 h'); simp only [ha, hq] at *
      by_cases e1 : rd M₀ (selA κ a i .L32) ^^^ rd M₀ (selA κ a i .P30) ^^^ rd M₀ (selA κ a i .N30) = 1 <;>
        by_cases e2 : rd M₀ (selA κ a i .L32 + 1) ^^^ rd M₀ (selA κ a i .P30 + 1) ^^^ rd M₀ (selA κ a i .N30 + 1) = 0 <;>
        simp_all
    · simp [ha]
    · simp [ha]
  refine ⟨by simp only [o5, o4, o3, o2, o1, o0], of_loK I (P := .blk kPs)
    (by simp [kPs, LoK, Prim.dst, regs, qS0, qS1, qAl, qK, oK]) (by simp [kPs, WF, Prim.dst, qS0, qS1, qAl, qK, oK]) O5,
    av, ?_⟩
  have e : rd (runPrims kPs t5.M) qK = XOp.add.eval (rd t5.M qK) (rd (runPrims kPs t5.M) qAl) := by
    simp only [kPs, runPrims, List.foldl, Prim.run]
    simp (disch := (simp only [size_set, qS0, qS1, qS2, qS3, qS4, qS5, qAl, qK, oK, cOne]; omega)) only
      [rd_set_self, rd_set_ne]
  rw [e, av, kk5, kc]
  split_ifs
  · rw [add_one_toWord]
  · simp [XOp.eval]

/-- **The count after `n` sub-slots** is `kc` of the flags (`alive` its running conjunction). -/
theorem kSelIR_run (I : Array Word) (κ : NodeKind) (a : ℕ) {M₀ : Mem} {p : ℕ → Bool} {N : ℕ} (hN : N < 2 ^ 32)
    (hA : ∀ i < N, ∀ ι, regs ≤ selA κ a i ι ∧ selA κ a i ι + 1 < bufB)
    (hp : ∀ i < N, p i = decide (rdF M₀ (selA κ a i .L32) + rdF M₀ (selA κ a i .P30) + rdF M₀ (selA κ a i .N30) = 1)) :
    ∀ n, n ≤ N → ∀ {t : St}, OF M₀ t →
      (semXIR I (kSelIR κ a n) t).o = t.o ∧ KInv M₀ p n (semXIR I (kSelIR κ a n) t)
  | 0, _, t, hO => by
    have hs := hO.inv.1
    simp only [regs] at hs
    refine ⟨rfl, of_loK I (P := .blk [.const qAl 1, .const qK 0]) (by simp [LoK, Prim.dst, regs, qAl, qK])
      (by simp [WF, Prim.dst, qAl, qK]) hO, ?_, ?_⟩
    all_goals simp only [kSelIR, semXIR_blk, runPrims, List.foldl, Prim.run]
    all_goals simp (disch := (simp only [size_set, qAl, qK]; omega)) only [rd_set_self, rd_set_ne]
    all_goals first | rfl | (simp [kc]; done) | (simp [kc]; rfl)
  | n + 1, hn, t, hO => by
    obtain ⟨o1, h1⟩ := kSelIR_run I κ a hN hA hp n (by omega) hO
    have hkc : kc p n ≤ n := by
      clear o1 h1 hO
      induction n with
      | zero => simp [kc]
      | succ m ih => rw [kc]; split_ifs <;> omega
    rw [kSelIR, semXIR_seq]
    obtain ⟨o2, h2⟩ := kStep_sem I κ a n (hA n (by omega)) (hp n (by omega)) (by omega) h1
    exact ⟨o2.trans o1, h2⟩

/-- **`kSelIR` computes `kSel`**: on a heap whose selector words are the witness's cells, after
`kSelIR κ a maxK` register `qK` holds aggregate `a`'s segment count. -/
theorem kSelIR_sem (I : Array Word) (κ : NodeKind) (a : ℕ) {M₀ : Mem} {w : Circ.Asg}
    (hA : ∀ i < κ.maxK, ∀ ι, regs ≤ selA κ a i ι ∧ selA κ a i ι + 1 < bufB)
    (hw : ∀ i < κ.maxK, ∀ ι, rdF M₀ (selA κ a i ι) = w (κ.oneCell + selR (N4c.sub κ a i) ι)) {t : St}
    (hO : OF M₀ t) :
    (semXIR I (kSelIR κ a κ.maxK) t).o = t.o ∧ OF M₀ (semXIR I (kSelIR κ a κ.maxK) t) ∧
      rd (semXIR I (kSelIR κ a κ.maxK) t).M qK = toWord (kSel κ a w) := by
  have hm : κ.maxK < 2 ^ 32 := by cases κ <;> decide
  obtain ⟨o, h⟩ := kSelIR_run I κ a (p := fun i => decide ((selSum κ (N4c.sub κ a i)).ev w = 1)) hm hA
    (fun i hi => by rw [selSum_ev, ← hw i hi, ← hw i hi, ← hw i hi]) κ.maxK le_rfl hO
  refine ⟨o, h.of, ?_⟩
  rw [h.k, kc_find, kSel]
  simp only [decide_not]

end FR.X

end G6_FRXOut4K

section G6_FRXOut4P

-- New for `flock-recursive` (BLUEPRINT revision 4.1, §6.2 step 5, A.5, A.7; stage S-H4, pass 11, item 3:
-- a segment's words in the buffer, the previous node's child program). 3.x analogue: `FRXOutRun.slot_step`.

/-!
# A segment in the buffer; the previous node's signed child

The heap after the decode holds `f⁽⁰⁾`'s decoded cells (**`HeapW κ M₀ w`**: cell `e` with `Dec0 e`,
`e < 2^(m − 7)`, at `wAddr κ e`), so H's message word `n` of a block below `hEnd κ` is the heap word at
`hAddr κ n` (**`hMW_heapW`**). The chain loader's registers for signed child `σ` with `k` segments
(**`ChR`**) make the loader's word `n` the chain word `chW κ σ k w n`: H word
`ldIx cb jL Δ n = 8·blkOf κ σ k ⌊n/8⌋ + n mod 8` of a block below `hEnd κ`. Then

* **`cp_vS`**: after `cpSeg κ` with `qI = i`, the buffer's words are segment `i`'s virtual words
  `vS κ σ k i w` (`cpSeg_sem`, `vS_get`);
* **`prevIR κ`** emits a previous node's signed child (`κ.hasPrev`, child `0`): `|π|`, the proof at
  the ladder of word 10, the trace, the signature (**`prevIR_sem`**: `signedWords (sgnX sigH κ 0 w)`).
-/

namespace FR.X

open RecursionFast FR.Read FR.Rev4 FR.Snd

attribute [local irreducible] entryK storeM runPrims

/-! ## The heap after the decode -/

/-- **The decoded cells on the heap**: cell `e` of `w` at `wAddr κ e` (`decF04_wF`'s conclusion). -/
def HeapW (κ : NodeKind) (M₀ : Mem) (w : Circ.Asg) : Prop :=
  ∀ e, Dec0 e → e < 2 ^ (κ.m - 7) → rdF M₀ (wAddr κ e) = w e

/-- `hEnd κ` blocks fit `f`'s cells (`128` cells a block). -/
theorem hEnd_fit (κ : NodeKind) : N4c.hEnd κ * 128 + 128 ≤ 2 ^ (κ.m - 7) := by cases κ <;> decide

theorem hMW_heapW {κ : NodeKind} {M₀ : Mem} {w : Circ.Asg} (hH : HeapW κ M₀ w) {n : ℕ}
    (hn : n / 8 < N4c.hEnd κ) : rd M₀ (hAddr κ n) = hMW w n := by
  have hf := hEnd_fit κ
  have h := hH (W4.hc (n / 8) (4 + n % 8 / 2)) (by unfold Dec0 W4.hc; omega) (by unfold W4.hc; omega)
  rw [hMW, ← h]
  unfold hAddr
  rcases Nat.mod_two_eq_zero_or_one n with h2 | h2 <;> rw [h2] <;> rfl

theorem hAddr_lt' {κ : NodeKind} {n : ℕ} (hn : n / 8 < N4c.hEnd κ) : hAddr κ n < bufB :=
  hAddr_lt κ (by have := hEnd_fit κ; omega)

/-! ## The chain loader's registers -/

/-- **The chain loader for signed child `σ` with `k` segments**: the loader's H word for chain word
`n` is block `blkOf κ σ k ⌊n/8⌋`'s word `n mod 8`, a block below `hEnd κ` for `n ≤ nB`. -/
structure ChR (κ : NodeKind) (σ k cb jL Δ nB : ℕ) : Prop where
  ld : ∀ n, ldIx cb jL Δ n = 8 * N4c.blkOf κ σ k (n / 8) + n % 8
  blk : ∀ n ≤ nB, N4c.blkOf κ σ k (n / 8) < N4c.hEnd κ
  big : 2 ^ 23 + nW + 1 + cb + Δ < 2 ^ 64
  jl : jL < 2 ^ 64

/-- **After `cpSeg κ` with `qI = i`, the buffer holds segment `i`'s virtual words.** -/
theorem cp_vS (I : Array Word) (κ : NodeKind) {σ k i cb jL Δ nB : ℕ} {w : Circ.Asg} {M₀ : Mem} {t : St}
    (hO : OF M₀ t) (hsz : bufB + 2 ^ 22 ≤ M₀.size) (hH : HeapW κ M₀ w) (hC : ChR κ σ k cb jL Δ nB) (hi4 : i ≤ 4)
    (hnB : i * (N4c.strideB / 8) + nW ≤ nB) (hD : i * N4c.strideB + N4c.segB ≤ N4c.streamB κ σ k)
    (hi : rd t.M qI = toWord i) (hcb : rd t.M qCB = toWord cb) (hjr : rd t.M qJ = toWord jL)
    (hd : rd t.M qDl = toWord Δ) :
    OF M₀ (semXIR I (cpSeg κ) t) ∧ (semXIR I (cpSeg κ) t).o = t.o ∧
      ∀ u (hu : u < (vS κ σ k i w).length), (vS κ σ k i w)[u] = src (semXIR I (cpSeg κ) t).M apB bufB u := by
  have hG : ∀ n ≤ nB, rd M₀ (hAddr κ (ldIx cb jL Δ n)) = chW κ σ k w n ∧ hAddr κ (ldIx cb jL Δ n) < bufB :=
    fun n hn => by
      have hb := hC.blk n hn
      have e : ldIx cb jL Δ n / 8 = N4c.blkOf κ σ k (n / 8) := by rw [hC.ld]; omega
      refine ⟨?_, hAddr_lt' (by rw [e]; exact hb)⟩
      rw [hMW_heapW hH (n := ldIx cb jL Δ n) (by rw [e]; exact hb), hC.ld, chW]
  obtain ⟨O1, o1, b1⟩ := cpSeg_sem I κ hO hsz hi4 hi hcb hjr hd hC.big hC.jl
    (fun n hn => (hG n (by omega)).2)
  refine ⟨O1, o1, fun u hu => ?_⟩
  have hl := vS_length κ σ k i w hD
  have huW : u < nW := by rw [hl] at hu; simp only [nW, N4c.segB] at hu ⊢; omega
  rw [vS_get κ σ k i w hD hu, src_bufA _ (by simp only [nW] at huW; omega), b1 u huW, (hG _ (by omega)).1]

/-! ## The previous node's signed child -/

/-- A previous node's chain registers: base `0`, last block `cLen − 1`, no redirect, segment `0`. -/
def prevRegs (κ : NodeKind) : XIR :=
  .blk [.const qCB (toWord (8 * N4c.chBase κ 0)), .const qJ (toWord (N4c.cLen - 1)), .const qDl 0, .const qI 0]

/-- **A previous node's signed child** (child `0`): `|π|`, the proof, the trace, the signature. -/
def prevIR (κ : NodeKind) : XIR :=
  .seq (.blk [.const oX (toWord (piSizeOf seq4))]) (.seq (.out oX)
  (.seq (prevRegs κ) (.seq (cpSeg κ) (.seq pfIR (.seq (bufSeg (trSeg4 seq4)) (sigIR κ 0))))))

theorem chR_prev (κ : NodeKind) (hκ : κ.hasPrev = true) :
    ChR κ 0 0 (8 * N4c.chBase κ 0) (N4c.cLen - 1) 0 nW := by
  have hl : N4c.streamL κ 0 0 = N4c.cLen := by simp [N4c.streamL, N4c.isAgg, hκ]
  have hf : N4c.finBlk κ 0 0 = N4c.cLen - 1 := by
    simp [N4c.finBlk, N4c.isAgg, hκ, N4c.chBase, N4c.chLen]
  have hb : ∀ i, N4c.blkOf κ 0 0 i = i := fun i => by
    unfold N4c.blkOf; rw [hl, hf]; simp only [N4c.chBase, Nat.zero_mul, Nat.zero_add]; split_ifs <;> omega
  refine ⟨fun n => ?_, fun n hn => ?_, by simp [N4c.chBase, nW], by simp [N4c.cLen]⟩
  · rw [hb]; unfold ldIx; simp only [N4c.chBase, Nat.zero_mul, Nat.mul_zero]; split_ifs <;> omega
  · rw [hb]
    have : 24236 < N4c.hEnd κ := by cases κ <;> decide
    simp only [nW] at hn; omega

/-- The signature's WOTS blocks lie below `hEnd κ`. -/
theorem wb_fit (κ : NodeKind) {σ : ℕ} (hσ : σ < 2) : W4.wb κ σ 0 + 500 < N4c.hEnd κ ∧ W4.wb κ σ 0 < 2 ^ 50 := by
  interval_cases σ <;> cases κ <;> decide

/-- The index word is the shift-1 pair at WOTS block `399` (`sigWords_sigH`'s first word). -/
theorem idx_word (κ : NodeKind) (σ : ℕ) (w : Circ.Asg) :
    toWord (idxH κ σ w) = shWd (hMW w) 1 (8 * W4.wb κ σ 399) := by
  show wOf (fun k => hMB w (W4.wb κ σ 399) (1 + k)) = _
  rw [← wOf_hMBs w (by norm_num) (by norm_num)]
  exact wOf_congr fun k hk => by
    rw [show 8 * (8 * W4.wb κ σ 399) + 1 + k = 64 * W4.wb κ σ 399 + (1 + k) by ring, hMBs_blk _ _ (by omega)]

theorem sigL_eq (κ : NodeKind) {σ : ℕ} (hσ : σ < 2) {M₀ : Mem} {w : Circ.Asg} (hH : HeapW κ M₀ w) :
    sigL (fun m => rd M₀ (hAddr κ m)) (W4.wb κ σ 0) = sigWords (sigH κ σ w) := by
  have hf := wb_fit κ hσ
  have hG : ∀ m ≤ 8 * W4.wb κ σ 0 + 4000, rd M₀ (hAddr κ m) = hMW w m := fun m hm =>
    hMW_heapW hH (by omega)
  have sh : ∀ s n, n + 1 ≤ 8 * W4.wb κ σ 0 + 4000 →
      shWd (fun m => rd M₀ (hAddr κ m)) s n = shWd (hMW w) s n := fun s n hn => by
    simp only [shWd]; rw [hG n (by omega), hG (n + 1) hn]
  have hw : ∀ o, W4.wb κ σ o = W4.wb κ σ 0 + o := fun o => by simp only [W4.wb]; omega
  have h399 : 8 * W4.wb κ σ 0 + 3192 = 8 * W4.wb κ σ 399 := by simp only [W4.wb]; omega
  have hidx : (shWd (hMW w) 1 (8 * W4.wb κ σ 0 + 3192)).toNat = idxH κ σ w := by
    rw [h399, ← idx_word, toNat_toWord (show idxH κ σ w < 2 ^ 64 from ofLE_lt64 (by simp))]
  have hX : shWd (fun m => rd M₀ (hAddr κ m)) 1 (8 * W4.wb κ σ 0 + 3192) = shWd (hMW w) 1 (8 * W4.wb κ σ 0 + 3192) :=
    sh _ _ (by omega)
  simp only [sigL, sigWords_sigH]
  refine congrArg₂ (· ++ ·) (congrArg₂ List.cons (by rw [hX, h399]) ?_) ?_
  · refine List.flatMap_congr fun i hi => List.map_congr_left fun j hj => ?_
    have := List.mem_range.1 hi; have := List.mem_range.1 hj
    rw [sh _ _ (by simp only [wotsLen] at *; omega), show 8 * W4.wb κ σ 0 + 1 + 24 * i + j =
      8 * W4.wb κ σ (3 * i) + 1 + j by simp only [W4.wb]; ring]
  · refine List.flatMap_congr fun t ht => List.map_congr_left fun j hj => ?_
    have := List.mem_range.1 ht; have := List.mem_range.1 hj
    have hof : offB (shWd (fun m => rd M₀ (hAddr κ m)) 1 (8 * W4.wb κ σ 0 + 3192)) t =
        if idxH κ σ w / 2 ^ t % 2 = 1 then 0 else 4 := by
      rw [hX, offB, hidx]
    rw [hof, sh _ _ (by simp only [sigHeight] at *; split_ifs <;> omega),
      show 8 * W4.wb κ σ 0 + 3728 + 16 * t = 8 * W4.wb κ σ (466 + 2 * t) by simp only [W4.wb]; ring]

/-- A heap word above the registers is kept: the buffer's source is too. -/
theorem src_congr {M M' : Mem} (h : ∀ y, regs ≤ y → rd M' y = rd M y) : src M' apB bufB = src M apB bufB :=
  funext fun u => h _ (hA_B _)

/-- **A previous node's signed child is emitted** (`signedWords_prev`). -/
theorem prevIR_sem (I : Array Word) (κ : NodeKind) (hκ : κ.hasPrev = true) {M₀ : Mem} {w : Circ.Asg} {s : St}
    (hO : OF M₀ s) (hsz : bufB + 2 ^ 22 ≤ M₀.size) (hH : HeapW κ M₀ w) :
    (semXIR I (prevIR κ) s).o.toList = s.o.toList ++ signedWords (sgnX sigH κ 0 w) ∧
      OF M₀ (semXIR I (prevIR κ) s) := by
  have hs := hO.inv.1
  simp only [regs] at hs
  rw [prevIR, semXIR_seq, semXIR_blk, semXIR_seq]
  rw [show semXIR I (.out oX) ⟨runPrims [.const oX (toWord (piSizeOf seq4))] s.M, s.o⟩ =
    ⟨runPrims [.const oX (toWord (piSizeOf seq4))] s.M,
      s.o.push (rd (runPrims [.const oX (toWord (piSizeOf seq4))] s.M) oX)⟩ from rfl]
  have x1 : rd (runPrims [.const oX (toWord (piSizeOf seq4))] s.M) oX = toWord (piSizeOf seq4) := by
    simp only [runPrims, List.foldl, Prim.run]; rw [rd_set_self (by simp only [oX]; omega)]
  rw [x1]
  have O1 : OF M₀ ⟨runPrims [.const oX (toWord (piSizeOf seq4))] s.M, s.o.push (toWord (piSizeOf seq4))⟩ :=
    of_mk (of_loK I (P := .blk [.const oX (toWord (piSizeOf seq4))]) (by simp [LoK, Prim.dst, oX, regs])
      (by simp [WF, Prim.dst, oX]) hO) _
  have o1 : (⟨runPrims [.const oX (toWord (piSizeOf seq4))] s.M, s.o.push (toWord (piSizeOf seq4))⟩ : St).o =
    s.o.push (toWord (piSizeOf seq4)) := rfl
  generalize (⟨runPrims [.const oX (toWord (piSizeOf seq4))] s.M, s.o.push (toWord (piSizeOf seq4))⟩ : St) = s1 at O1 o1
  have hs1 := O1.inv.1
  simp only [regs] at hs1
  rw [semXIR_seq, prevRegs, semXIR_blk]
  set ps : List Prim := [.const qCB (toWord (8 * N4c.chBase κ 0)), .const qJ (toWord (N4c.cLen - 1)), .const qDl 0,
    .const qI 0] with hps
  have v : rd (runPrims ps s1.M) qI = toWord 0 ∧ rd (runPrims ps s1.M) qCB = toWord (8 * N4c.chBase κ 0) ∧
      rd (runPrims ps s1.M) qJ = toWord (N4c.cLen - 1) ∧ rd (runPrims ps s1.M) qDl = toWord 0 := by
    simp only [hps, runPrims, List.foldl, Prim.run]
    simp (disch := (simp only [size_set, qCB, qJ, qDl, qI] at *; omega)) only [rd_set_self, rd_set_ne]
    refine ⟨?_, ?_, ?_, ?_⟩ <;> first | exact True.intro | rfl
  have O2 : OF M₀ ⟨runPrims ps s1.M, s1.o⟩ := of_loK I (P := .blk ps)
    (by simp [hps, LoK, Prim.dst, regs, qCB, qJ, qDl, qI]) (by simp [hps, WF, Prim.dst, qCB, qJ, qDl, qI]) O1
  rw [semXIR_seq]
  obtain ⟨O3, o3, hV⟩ := cp_vS I κ (σ := 0) (k := 0) (i := 0) (w := w) O2 hsz hH (chR_prev κ hκ) (by norm_num)
    (by simp) (by simp [N4c.streamB, N4c.isAgg, hκ]) v.1 v.2.1 v.2.2.1 v.2.2.2
  generalize semXIR I (cpSeg κ) ⟨runPrims ps s1.M, s1.o⟩ = s3 at O3 o3 hV
  rw [semXIR_seq]
  obtain ⟨o4, O4, h4⟩ := pfIR_sem I O3
  generalize semXIR I pfIR s3 = s4 at o4 O4 h4
  rw [semXIR_seq]
  obtain ⟨o5, O5, h5⟩ := bufSeg_sem I (trSeg4 seq4) okSeg_tr.1 (le_trans okSeg_tr.2.1 (by norm_num)) O4
  generalize semXIR I (bufSeg (trSeg4 seq4)) s4 = s5 at o5 O5 h5
  have hf := wb_fit κ (σ := 0) (by norm_num)
  obtain ⟨o6, O6⟩ := sigIR_sem I κ 0 O5 hf.2 (fun m hm => hAddr_lt' (by omega))
  refine ⟨?_, O6⟩
  rw [o6, o5, o4, src_congr h4, sigL_eq κ (by norm_num) hH, signedWords_prev κ hκ w (src s3.M apB bufB) hV]
  rw [o3]
  simp only [o1, Array.toList_push, List.append_assoc, List.cons_append, List.singleton_append, List.nil_append]

end FR.X

end G6_FRXOut4P

section G6_FRXOut4A

-- New for `flock-recursive` (BLUEPRINT revision 4.1, §6.2 step 5, A.5, A.7; stage S-H4, pass 11, item 3:
-- an aggregate's signed child on the machine). 3.x has no aggregate.

/-!
# An aggregate's signed child (`aggIR4`)

Aggregate `a` (signed child `σ = aggChild κ a`, `k = kSel κ a w` segments) emits (`signedWords_agg`)
`|π_A| = 48 + k·piSize`, the header (`hdrWords`: `'A' ‖ k`, then `n` and `e` as shift-1 pairs of the
`c_A` block's message words), the `k` proofs, the count `k·|items| + (k − 1)`, the `k` traces' bodies
each after its spacer entry (`i ≥ 1`: the constant query words `spW`, then the answer as four shift-1
pairs of chain words, **`spPre`**), the signature. The two segment loops run `k ≤ maxK` times (the count
in `qK`, `loopK_emitR`); each iteration runs its prefix, copies segment `i` into the buffer (`cp_vS`) and
emits over it (**`segLoop_sem`**).

The chain loader's registers (**`aggRegs`**, `ChR` by **`chR_agg`**): base `8·chBase σ`, last block
`jL = k·sBlk − 3 = aggL k − 1` (revision 4.4.1), and the redirect
`Δ = [k < maxK]·8·(finB κ a − 1 − chBase σ + k − jL)`, so the stream's last block is read from the
candidate final block `finB κ a + k − 1`.
-/

namespace FR.X

open RecursionFast FR.Read FR.Rev4 FR.Snd

attribute [local irreducible] entryK storeM runPrims

/-! ## Specification -/

/-- `oX := c + qK·m`. -/
def lenW (c m : ℕ) : List Prim := [.const oK (toWord m), .op .mul oX qK oK, .const oK (toWord c), .op .add oX oX oK]

/-- **The length word and the header**: `48 + k·piSize`, `0x41 + 256k`, then `n` (shift 1 at word
`8·c_A + 4`) and `e` (four shift-1 pairs from word `8·c_A`). -/
def aggHd (κ : NodeKind) (a : ℕ) : XIR :=
  .seq (.blk (lenW 48 (piSizeOf seq4))) (.seq (.out oX)
  (.seq (.blk (lenW 0x41 256)) (.seq (.out oX)
  (.seq (.blk [.const qCB 0, .const qJ 0, .const qDl 0, .const qA (toWord 8), .const qB (toWord 55),
      .const qN (toWord (8 * N4c.cAB κ a + 4))])
  (.seq (shwO κ) (.seq (.blk [.const qN (toWord (8 * N4c.cAB κ a))]) (shw4 κ)))))))

/-- The redirect's constant `finB κ a − 1 − chBase σ`. -/
def dC (κ : NodeKind) (a : ℕ) : ℕ := N4c.finB κ a - 1 - N4c.chBase κ (N4c.aggChild κ a)

/-- **The chain loader's registers** for aggregate `a` with `k = qK` segments, and `qI := 0`:
`qJ := k·sBlk − 3·[0 < k]` (the stream's last block), the redirect `qDl`. -/
def aggRegs (κ : NodeKind) (a : ℕ) : XIR :=
  .seq (.blk [.const qCB (toWord (8 * N4c.chBase κ (N4c.aggChild κ a))), .const oK (toWord N4c.sBlk),
    .op .mul qJ qK oK, .const oK 0, .op .ltu qT1 oK qK, .const oK (toWord 3), .op .mul qT1 qT1 oK,
    .op .sub qJ qJ qT1, .const qI 0])
  (.blk [.const oK (toWord κ.maxK), .op .ltu qT1 qK oK, .const oK (toWord (dC κ a)), .op .add qDl qK oK,
    .op .sub qDl qDl qJ, .const oK (toWord 3), .op .shl qDl qDl oK, .op .mul qDl qT1 qDl])

/-- **A segment loop**: per segment `i < qK`, the prefix `P`, copy segment `i`, run `E` over the buffer,
`i += 1`. -/
def segLoop (κ : NodeKind) (P E : XIR) : XIR :=
  .loopK qSc qK (toWord κ.maxK) (.seq P (.seq (cpSeg κ) (.seq E (.blk [.op .add qI qI cOne]))))

/-- The spacer entry's query words as a segment of constants. -/
def spSeg : Seg := catL (spW.map .wd)

/-- **Spacer `qI`'s entry**: its query's words (constants), then its answer, four shift-1 pairs of chain
words from `qI·(strideB/8) − 4`. -/
def spIR (κ : NodeKind) : XIR :=
  .seq (bufSeg spSeg) (.seq (.blk [.const oK (toWord (N4c.strideB / 8)), .op .mul qN qI oK, .const oK (toWord 4),
    .op .sub qN qN oK, .const qA (toWord 8), .const qB (toWord 55)]) (shw4 κ))

/-- **The traces' prefix**: the spacer entry before segment `qI ≥ 1`. -/
def spPre (κ : NodeKind) : XIR := .ite qI (spIR κ) (.blk [])

/-- `oX := qK·(|items| + 1) − [0 < qK]`: the aggregate trace's length `k·|items| + (k − 1)`. -/
def cntW : List Prim :=
  lenW 0 ((itemsOf seq4).length + 1) ++ [.const oK 0, .op .ltu qT1 oK qK, .op .sub oX oX qT1]

/-- The traces: the count word, `qI := 0`, per segment its spacer entry (`i ≥ 1`) and its body. -/
def aggTr (κ : NodeKind) : XIR :=
  .seq (.blk cntW) (.seq (.out oX) (.seq (.blk [.const qI 0])
    (segLoop κ (spPre κ) (bufSeg (trBody4 seq4)))))

/-- **Aggregate `a`'s signed child.** -/
def aggIR4 (κ : NodeKind) (a : ℕ) : XIR :=
  .seq (kSelIR κ a κ.maxK) (.seq (aggHd κ a) (.seq (aggRegs κ a) (.seq (segLoop κ (.blk []) pfIR)
    (.seq (aggTr κ) (sigIR κ (N4c.aggChild κ a))))))

/-! ## Proof helpers: what the emitters write -/

theorem noW_lo (ap : AP) (sg : Seg) (d : ℕ) {r : ℕ} (hr : r < 200) (hc : r ≠ cTmp) : ¬ Writes (segIR ap d sg) r :=
  fun h => by
    rcases ow_segIR ap sg d r h with h1 | ⟨e, -, h2⟩
    · rcases h1 with h1 | h1
      · exact hc h1
      · omega
    · omega

theorem wf_setB : WF setB := by simp [setB, WF, Prim.dst, oR, oBd, oKF]

theorem wf_ladF : WF ladF :=
  ⟨by simp [WF, Prim.dst, oU], wf_ldw apB, by simp [WF, Prim.dst, oK, oX, qF0, qF1, qT1]⟩

theorem wf_pfS {m : ℕ} (hm : m ∈ [30, 31, 32]) : WF (pfS m) :=
  wf_segIR apB _ 0 (by have := (okSeg_pf m hm).2; omega)

theorem wf_pfIR : WF pfIR :=
  ⟨wf_setB, wf_ladF, wf_pfS (by simp), wf_pfS (by simp), wf_pfS (by simp)⟩

theorem wf_bufSeg {sg : Seg} (hd : depthSeg sg ≤ 9) : WF (bufSeg sg) := ⟨wf_setB, wf_segIR apB sg 0 (by omega)⟩

theorem noW_pfIR {r : ℕ} (hr : r < 200) (hc : r ≠ cTmp) (h : r ∉ [qF0, qF1, qT1, oU, oK, oX]) :
    ¬ Writes pfIR r := by
  simp only [List.mem_cons, List.mem_nil_iff, or_false, not_or] at h
  rintro (h1 | h1 | h1 | h1 | h1)
  · obtain ⟨p, hp, he⟩ := h1
    simp only [setB, List.mem_cons, List.mem_nil_iff, or_false] at hp
    rcases hp with rfl | rfl | rfl <;> simp only [Prim.dst, oR, oBd, oKF] at he <;> omega
  · rcases h1 with ⟨p, hp, he⟩ | h1 | ⟨p, hp, he⟩
    · simp only [List.mem_cons, List.mem_nil_iff, or_false] at hp; subst hp; exact h.2.2.2.1 he.symm
    · have := writes_wrL _ _ h1
      simp only [wrL, ldw, ldPs, List.map_cons, List.map_nil, Prim.dst, List.cons_append, List.nil_append,
        List.mem_cons, List.mem_nil_iff, or_false, List.append_nil] at this
      simp only [oK, oT1, oT2, oT3, oAd, oX] at this; omega
    · simp only [List.mem_cons, List.mem_nil_iff, or_false] at hp
      rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp only [Prim.dst] at he <;>
        subst he <;> simp_all [oK, oX, qF0, qF1, qT1]
  all_goals exact noW_lo apB _ 0 hr hc h1

theorem pfIR_keep (I : Array Word) {t : St} (hM : Inv t.M) {r : ℕ} (hr : r < 200) (hc : r ≠ cTmp)
    (h : r ∉ [qF0, qF1, qT1, oU, oK, oX]) : rd (semXIR I pfIR t).M r = rd t.M r :=
  frame I pfIR t wf_pfIR hM r (by simp only [regs]; omega) (noW_pfIR hr hc h)

theorem noW_bufSeg {sg : Seg} {r : ℕ} (hr : r < 200) (hc : r ≠ cTmp) : ¬ Writes (bufSeg sg) r := by
  rintro (⟨p, hp, he⟩ | h1)
  · simp only [setB, List.mem_cons, List.mem_nil_iff, or_false] at hp
    rcases hp with rfl | rfl | rfl <;> simp only [Prim.dst, oR, oBd, oKF] at he <;> omega
  · exact noW_lo apB _ 0 hr hc h1

theorem bufSeg_keep (I : Array Word) {sg : Seg} (hd : depthSeg sg ≤ 9) {t : St} (hM : Inv t.M) {r : ℕ}
    (hr : r < 200) (hc : r ≠ cTmp) : rd (semXIR I (bufSeg sg) t).M r = rd t.M r :=
  frame I (bufSeg sg) t (wf_bufSeg hd) hM r (by simp only [regs]; omega) (noW_bufSeg hr hc)

theorem cpSeg_keep (I : Array Word) (κ : NodeKind) {t : St} (hM : Inv t.M) {r : ℕ}
    (h : r ∈ [qI, qCB, qJ, qDl, qK, qSc]) : rd (semXIR I (cpSeg κ) t).M r = rd t.M r := by
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl <;>
    exact keep_of I (wf_cpSeg κ) hM (by decide) (by cases κ <;> decide)

/-! ## The segment loops -/

/-- The segment loops' registers at segment `i`. -/
structure AgR (cb jL Δ k i : ℕ) (M : Mem) : Prop where
  i : rd M qI = toWord i
  cb : rd M qCB = toWord cb
  jl : rd M qJ = toWord jL
  dl : rd M qDl = toWord Δ
  k : rd M qK = toWord k

theorem agR_keep {cb jL Δ k i : ℕ} {M M' : Mem} (h : AgR cb jL Δ k i M)
    (hk : ∀ r ∈ [qI, qCB, qJ, qDl, qK], rd M' r = rd M r) : AgR cb jL Δ k i M' :=
  ⟨(hk _ (by simp)).trans h.i, (hk _ (by simp)).trans h.cb, (hk _ (by simp)).trans h.jl,
    (hk _ (by simp)).trans h.dl, (hk _ (by simp)).trans h.k⟩

/-- **A segment loop emits `pre i ++ out i` per segment `i < k`**, when the prefix `P` emits `pre i` at
segment `i`, `E` emits `F` of the buffer's words and `F` of segment `i`'s virtual words is `out i`. -/
theorem segLoop_sem (I : Array Word) (κ : NodeKind) {P E : XIR} {F : (ℕ → Word) → List Word}
    {pre out : ℕ → List Word} {M₀ : Mem} {σ k cb jL Δ nB : ℕ} {w : Circ.Asg}
    (hP : ∀ j < k, ∀ t, OF M₀ t → AgR cb jL Δ k j t.M → (semXIR I P t).o.toList = t.o.toList ++ pre j ∧
      OF M₀ (semXIR I P t) ∧ ∀ r ∈ [qI, qCB, qJ, qDl, qK, qSc], rd (semXIR I P t).M r = rd t.M r)
    (hE : ∀ t, OF M₀ t → (semXIR I E t).o.toList = t.o.toList ++ F (src t.M apB bufB) ∧ OF M₀ (semXIR I E t) ∧
      ∀ r ∈ [qI, qCB, qJ, qDl, qK, qSc], rd (semXIR I E t).M r = rd t.M r)
    (hF : ∀ i < k, ∀ V : ℕ → Word, (∀ u (hu : u < (vS κ σ k i w).length), (vS κ σ k i w)[u] = V u) → F V = out i)
    {t : St} (hO : OF M₀ t) (hsz : bufB + 2 ^ 22 ≤ M₀.size) (hH : HeapW κ M₀ w) (hC : 0 < k → ChR κ σ k cb jL Δ nB)
    (hk : k ≤ κ.maxK) (hk4 : κ.maxK ≤ 4) (hnB : ∀ i < k, i * (N4c.strideB / 8) + nW ≤ nB)
    (hD : ∀ i < k, i * N4c.strideB + N4c.segB ≤ N4c.streamB κ σ k) (hR : AgR cb jL Δ k 0 t.M) :
    (semXIR I (segLoop κ P E) t).o.toList = t.o.toList ++ (List.range k).flatMap (fun i => pre i ++ out i) ∧
      OF M₀ (semXIR I (segLoop κ P E) t) ∧ AgR cb jL Δ k k (semXIR I (segLoop κ P E) t).M := by
  have L := loopK_emitR I (c := qSc) (n := qK) (K := κ.maxK)
    (b := .seq P (.seq (cpSeg κ) (.seq E (.blk [.op .add qI qI cOne]))))
    (fun j st => OF M₀ st ∧ AgR cb jL Δ k j st.M) (fun i => pre i ++ out i) t hO.inv (by decide) (by decide)
    (by decide) (by decide) (by omega) hk hR.k
    ⟨of_entryK (by decide) (by decide) hO, agR_keep hR fun r hr => by
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl <;> exact entryK_frame _ (by decide) (by decide)⟩
    (fun j st hj ⟨hO', hR'⟩ => by
      obtain ⟨p0, P0, kP⟩ := hP j hj st hO' hR'
      rw [semXIR_seq]
      generalize semXIR I P st = s0 at p0 P0 kP
      have hR0 : AgR cb jL Δ k j s0.M := agR_keep hR' fun r hr => kP r (by
        simp only [List.mem_cons, List.mem_nil_iff, or_false] at hr ⊢; tauto)
      obtain ⟨O1, o1, hV⟩ := cp_vS I κ P0 hsz hH (hC (by omega)) (by omega) (hnB j hj) (hD j hj) hR0.i hR0.cb
        hR0.jl hR0.dl
      have k1 : ∀ r ∈ [qI, qCB, qJ, qDl, qK, qSc], rd (semXIR I (cpSeg κ) s0).M r = rd st.M r :=
        fun r hr => (cpSeg_keep I κ P0.inv hr).trans (kP r hr)
      rw [semXIR_seq]
      generalize semXIR I (cpSeg κ) s0 = s1 at O1 o1 hV k1
      obtain ⟨o2, O2, k2⟩ := hE s1 O1
      rw [semXIR_seq]
      generalize semXIR I E s1 = s2 at o2 O2 k2
      have hs2 := O2.inv.1
      simp only [regs] at hs2
      have e : ∀ r ∈ [qCB, qJ, qDl, qK],
          rd (decS qSc (semXIR I (.blk [.op .add qI qI cOne]) s2)).M r = rd st.M r := fun r hr => by
        simp only [List.mem_cons, List.mem_nil_iff, or_false] at hr
        rw [rd_decS (by rcases hr with rfl | rfl | rfl | rfl <;> decide), semXIR_blk,
          rd_runPrims_of_not_writes (by rcases hr with rfl | rfl | rfl | rfl <;> simp [Prim.dst, qI, qCB, qJ, qDl, qK]),
          k2 _ (by simp at hr ⊢; tauto), k1 _ (by simp at hr ⊢; tauto)]
      refine ⟨by rw [semXIR_blk]; simp only [o2, o1, p0, hF j hj _ hV, List.append_assoc],
        ⟨inv_decS (inv_runPrims (by simp [Prim.dst, qI])
        O2.inv) (by decide), by simp [semXIR_blk, O2.size], fun y h1 h2 => by
          rw [rd_decS (by simp only [qSc, regs] at *; omega), semXIR_blk,
            rd_runPrims_of_not_writes (by simp only [regs] at h1; simp [Prim.dst, qI]; omega), O2.low y h1 h2]⟩,
        ⟨?_, by rw [e _ (by simp)]; exact hR'.cb, by rw [e _ (by simp)]; exact hR'.jl, by rw [e _ (by simp)]; exact hR'.dl,
          by rw [e _ (by simp)]; exact hR'.k⟩⟩
      rw [rd_decS (by decide), semXIR_blk]
      simp only [runPrims, List.foldl, Prim.run]
      rw [rd_set_self (by simp only [qI]; omega), k2 _ (by simp), k1 _ (by simp), hR'.i, one_cOne O2.inv,
        add_one_toWord])
  exact ⟨L.1, L.2.1, L.2.2⟩

theorem rd_const_self {M : Mem} {d : ℕ} {v : Word} (h : d < M.size) : rd (runPrims [.const d v] M) d = v := by
  simp only [runPrims, List.foldl, Prim.run]; exact rd_set_self h

/-! ## An aggregate's numbers -/

/-- The stream's last block at `k` segments (`aggL k − 1 = k·sBlk − 3`, `k ≥ 1`). -/
def jLv (k : ℕ) : ℕ := k * N4c.sBlk - 3

theorem aggL_eq' {k : ℕ} (hk : 1 ≤ k) : N4c.aggL k = jLv k + 1 := by
  rw [(N4c.aggB_blocks hk).2.1, jLv, N4c.sBlk]; omega

/-- **The layout facts an aggregate's output uses** (decided per kind). -/
structure AggN (κ : NodeKind) (a : ℕ) : Prop where
  agg : N4c.isAgg κ (N4c.aggChild κ a) = true
  of : N4c.aggOf κ (N4c.aggChild κ a) = a
  len : N4c.chLen κ (N4c.aggChild κ a) = N4c.aggL κ.maxK
  fb : N4c.chBase κ (N4c.aggChild κ a) + N4c.aggL κ.maxK < N4c.finB κ a
  fe : N4c.finB κ a + κ.maxK ≤ N4c.hEnd κ
  nb : N4c.chBase κ (N4c.aggChild κ a) + ((κ.maxK - 1) * (N4c.strideB / 8) + nW) / 8 < N4c.hEnd κ
  mk1 : 1 ≤ κ.maxK
  mk4 : κ.maxK ≤ 4
  cab : N4c.cAB κ a < N4c.hEnd κ
  σ2 : N4c.aggChild κ a < 2
  he : N4c.hEnd κ < 2 ^ 20

theorem aggN (κ : NodeKind) {a : ℕ} (ha : a < N4c.nAgg κ) : AggN κ a := by
  have hn : N4c.nAgg κ ≤ 2 := by cases κ <;> decide
  have h : a = 0 ∨ a = 1 := by omega
  rcases h with rfl | rfl
  · cases κ <;> exact ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide,
      by decide, by decide, by decide⟩
  · cases κ
    · exact absurd ha (by decide)
    · exact absurd ha (by decide)
    · exact ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide,
        by decide, by decide, by decide⟩

/-- The redirect's value at `k` segments (`aggRegs`' `qDl`). -/
def dV (κ : NodeKind) (a k : ℕ) : ℕ := if k < κ.maxK then (k + dC κ a - jLv k) * 2 ^ 3 else 0

/-- **The aggregate's chain loader** (`k ≥ 1` segments): the loader's words are the chain words. -/
theorem chR_agg (κ : NodeKind) {a k : ℕ} (ha : a < N4c.nAgg κ) (hk1 : 0 < k) (hk : k ≤ κ.maxK) :
    ChR κ (N4c.aggChild κ a) k (8 * N4c.chBase κ (N4c.aggChild κ a)) (jLv k) (dV κ a k)
      ((κ.maxK - 1) * (N4c.strideB / 8) + nW) := by
  have N := aggN κ ha
  have hL : N4c.streamL κ (N4c.aggChild κ a) k = jLv k + 1 := by
    simp only [N4c.streamL, N.agg, if_true, aggL_eq' hk1]
  have hLm := aggL_eq' N.mk1
  have hF : N4c.finBlk κ (N4c.aggChild κ a) k = if k < κ.maxK then N4c.finB κ a + (k - 1) else
      N4c.chBase κ (N4c.aggChild κ a) + N4c.aggL κ.maxK - 1 := by
    simp only [N4c.finBlk, N.agg, true_and, N.of, N.len]
  have hb : ∀ i, N4c.blkOf κ (N4c.aggChild κ a) k i = if i = jLv k then
      N4c.finBlk κ (N4c.aggChild κ a) k else N4c.chBase κ (N4c.aggChild κ a) + i := by
    intro i; unfold N4c.blkOf; rw [hL]; split_ifs <;> omega
  have fb := N.fb; have fe := N.fe; have nb := N.nb; have he := N.he; have m4 := N.mk4
  have hc : N4c.chBase κ (N4c.aggChild κ a) < N4c.hEnd κ := by omega
  have hmono : jLv k ≤ jLv κ.maxK := by unfold jLv; have := Nat.mul_le_mul_right N4c.sBlk hk; omega
  have e3 : (2 : ℕ) ^ 3 = 8 := rfl
  have es : N4c.strideB / 8 = 193904 := rfl
  have hj : jLv k = k * 24238 - 3 := rfl
  have hjm : jLv κ.maxK = κ.maxK * 24238 - 3 := rfl
  rw [es] at nb ⊢
  refine ⟨fun n => ?_, fun n hn => ?_, ?_, ?_⟩
  · rw [hb, hF]; unfold ldIx dV dC; simp only [e3]
    by_cases h1 : n / 8 = jLv k <;> by_cases h2 : k < κ.maxK <;> simp only [h1, h2, ↓reduceIte] <;> omega
  · rw [hb, hF]
    by_cases h1 : n / 8 = jLv k <;> by_cases h2 : k < κ.maxK <;> simp only [h1, h2, ↓reduceIte] <;> omega
  · unfold dV dC; simp only [e3]; split_ifs <;> omega
  · unfold jLv; simp only [N4c.sBlk]; omega

/-! ## The header and the registers -/

theorem ltu_toWord {a b : ℕ} (ha : a < 2 ^ 64) (hb : b < 2 ^ 64) :
    XOp.ltu.eval (toWord a) (toWord b) = if a < b then 1 else 0 := by
  simp only [XOp.eval, BitVec.lt_def, toNat_toWord ha, toNat_toWord hb]

theorem lenW_val {M : Mem} (hM : Inv M) {k : ℕ} (hK : rd M qK = toWord k) (c m : ℕ) :
    rd (runPrims (lenW c m) M) oX = toWord (c + k * m) ∧ ∀ r, r ≠ oK → r ≠ oX → rd (runPrims (lenW c m) M) r = rd M r := by
  have hs := hM.1
  simp only [regs] at hs
  refine ⟨?_, fun r h1 h2 => rd_runPrims_of_not_writes (by simp [lenW, Prim.dst, Ne.symm h1, Ne.symm h2]) _⟩
  simp only [lenW, runPrims, List.foldl, Prim.run]
  simp (disch := (simp only [size_set, oK, oX, qK]; omega)) only [rd_set_self, rd_set_ne]
  rw [hK, mul_toWord, add_toWord, Nat.add_comm]

/-- **The length word and the header are emitted** (`hdrWords`), `qK` kept. -/
theorem aggHd_sem (I : Array Word) (κ : NodeKind) (a : ℕ) {M₀ : Mem} {w : Circ.Asg} (hH : HeapW κ M₀ w)
    (hc : N4c.cAB κ a < N4c.hEnd κ) (he : N4c.hEnd κ < 2 ^ 20) {k : ℕ} {t : St} (hO : OF M₀ t)
    (hK : rd t.M qK = toWord k) :
    (semXIR I (aggHd κ a) t).o.toList = t.o.toList ++
      (toWord (48 + k * piSizeOf seq4) :: hdrWords k (N4s.hAn κ a w) (N4s.hAe κ a w)) ∧
      OF M₀ (semXIR I (aggHd κ a) t) ∧ rd (semXIR I (aggHd κ a) t).M qK = toWord k := by
  have hs := hO.inv.1
  simp only [regs] at hs
  have hG : ∀ m ≤ 8 * N4c.cAB κ a + 7, ldG κ M₀ 0 0 0 m = hMW w m := fun m hm => by
    rw [ldG, ldIx_zero, hMW_heapW hH (by omega)]
  have hl : ∀ m ≤ 8 * N4c.cAB κ a + 7, hAddr κ (ldIx 0 0 0 m) < bufB := fun m hm => by
    rw [ldIx_zero]; exact hAddr_lt' (by omega)
  obtain ⟨x1, k1⟩ := lenW_val hO.inv hK 48 (piSizeOf seq4)
  rw [aggHd, semXIR_seq, semXIR_blk, semXIR_seq]
  rw [show semXIR I (.out oX) ⟨runPrims (lenW 48 (piSizeOf seq4)) t.M, t.o⟩ = ⟨runPrims (lenW 48 (piSizeOf seq4)) t.M,
    t.o.push (rd (runPrims (lenW 48 (piSizeOf seq4)) t.M) oX)⟩ from rfl, x1]
  have O1 : OF M₀ ⟨runPrims (lenW 48 (piSizeOf seq4)) t.M, t.o.push (toWord (48 + k * piSizeOf seq4))⟩ :=
    of_mk (of_loK I (P := .blk (lenW 48 (piSizeOf seq4))) (by simp [lenW, LoK, Prim.dst, oK, oX, regs])
      (by simp [lenW, WF, Prim.dst, oK, oX]) hO) _
  have K1 : rd (⟨runPrims (lenW 48 (piSizeOf seq4)) t.M, t.o.push (toWord (48 + k * piSizeOf seq4))⟩ : St).M qK =
      toWord k := by show rd (runPrims (lenW 48 (piSizeOf seq4)) t.M) qK = _; rw [k1 _ (by decide) (by decide)]; exact hK
  have o1 : (⟨runPrims (lenW 48 (piSizeOf seq4)) t.M, t.o.push (toWord (48 + k * piSizeOf seq4))⟩ : St).o =
    t.o.push (toWord (48 + k * piSizeOf seq4)) := rfl
  generalize (⟨runPrims (lenW 48 (piSizeOf seq4)) t.M, t.o.push (toWord (48 + k * piSizeOf seq4))⟩ : St) = t1 at O1 K1 o1
  have hs1 := O1.inv.1
  simp only [regs] at hs1
  rw [semXIR_seq, semXIR_blk, semXIR_seq]
  obtain ⟨x2, k2⟩ := lenW_val O1.inv K1 0x41 256
  rw [show semXIR I (.out oX) ⟨runPrims (lenW 0x41 256) t1.M, t1.o⟩ = ⟨runPrims (lenW 0x41 256) t1.M,
    t1.o.push (rd (runPrims (lenW 0x41 256) t1.M) oX)⟩ from rfl, x2]
  have O2 : OF M₀ ⟨runPrims (lenW 0x41 256) t1.M, t1.o.push (toWord (0x41 + k * 256))⟩ :=
    of_mk (of_loK I (P := .blk (lenW 0x41 256)) (by simp [lenW, LoK, Prim.dst, oK, oX, regs])
      (by simp [lenW, WF, Prim.dst, oK, oX]) O1) _
  have K2 : rd (⟨runPrims (lenW 0x41 256) t1.M, t1.o.push (toWord (0x41 + k * 256))⟩ : St).M qK = toWord k := by
    show rd (runPrims (lenW 0x41 256) t1.M) qK = _; rw [k2 _ (by decide) (by decide)]; exact K1
  have o2 : (⟨runPrims (lenW 0x41 256) t1.M, t1.o.push (toWord (0x41 + k * 256))⟩ : St).o =
    t1.o.push (toWord (0x41 + k * 256)) := rfl
  generalize (⟨runPrims (lenW 0x41 256) t1.M, t1.o.push (toWord (0x41 + k * 256))⟩ : St) = t2 at O2 K2 o2
  have hs2 := O2.inv.1
  simp only [regs] at hs2
  rw [semXIR_seq, semXIR_blk]
  set ps : List Prim := [.const qCB 0, .const qJ 0, .const qDl 0, .const qA (toWord 8), .const qB (toWord 55),
      .const qN (toWord (8 * N4c.cAB κ a + 4))] with hps
  have R3 : SwR 0 0 0 1 (8 * N4c.cAB κ a + 4) (runPrims ps t2.M) := by
    simp only [hps, runPrims, List.foldl, Prim.run]
    refine ⟨⟨?_, ?_, ?_⟩, ?_, ?_, ?_⟩ <;>
    simp (disch := (simp only [size_set, qCB, qJ, qDl, qA, qB, qN]; omega)) only [rd_set_self, rd_set_ne] <;>
    first | exact True.intro | rfl
  have K3 : rd (runPrims ps t2.M) qK = toWord k := by
    rw [rd_runPrims_of_not_writes (by simp [hps, Prim.dst, qCB, qJ, qDl, qA, qB, qN, qK])]; exact K2
  have O3 : OF M₀ ⟨runPrims ps t2.M, t2.o⟩ := of_loK I (P := .blk ps)
    (by simp [hps, LoK, Prim.dst, regs, qCB, qJ, qDl, qA, qB, qN]) (by simp [hps, WF, Prim.dst, qCB, qJ, qDl, qA, qB, qN]) O2
  rw [semXIR_seq]
  obtain ⟨a4, b4, c4, d4⟩ := shwO_sem I κ (sh := 1) (by norm_num) (by omega) (by norm_num) (hl _ (by omega))
    (hl _ (by omega)) O3 R3
  generalize semXIR I (shwO κ) ⟨runPrims ps t2.M, t2.o⟩ = t4 at a4 b4 c4 d4
  have K4 : rd t4.M qK = toWord k := by rw [d4 _ (by decide) (by decide)]; exact K3
  have hs4 := b4.inv.1
  simp only [regs] at hs4
  rw [semXIR_seq, semXIR_blk]
  have k5 : ∀ r, r ≠ qN → rd (runPrims [.const qN (toWord (8 * N4c.cAB κ a))] t4.M) r = rd t4.M r := fun r hr =>
    rd_runPrims_of_not_writes (by simp [Prim.dst, Ne.symm hr]) _
  have R5 : SwR 0 0 0 1 (8 * N4c.cAB κ a) (runPrims [.const qN (toWord (8 * N4c.cAB κ a))] t4.M) :=
    ⟨⟨by rw [k5 _ (by decide)]; exact c4.cb, by rw [k5 _ (by decide)]; exact c4.jl, by rw [k5 _ (by decide)]; exact c4.dl⟩,
      by simp only [runPrims, List.foldl, Prim.run]; rw [rd_set_self (by simp only [qN]; omega)],
      by rw [k5 _ (by decide)]; exact c4.a, by rw [k5 _ (by decide)]; exact c4.b⟩
  have O5 : OF M₀ ⟨runPrims [.const qN (toWord (8 * N4c.cAB κ a))] t4.M, t4.o⟩ :=
    of_loK I (P := .blk [.const qN (toWord (8 * N4c.cAB κ a))]) (by simp [LoK, Prim.dst, regs, qN])
      (by simp [WF, Prim.dst, qN]) b4
  obtain ⟨a6, b6, c6, d6⟩ := shw4_sem I κ (sh := 1) (by norm_num) (by omega) (by norm_num)
    (fun j hj => hl _ (by omega)) O5 R5
  refine ⟨?_, b6, by rw [d6 _ (by decide) (by decide), k5 _ (by decide)]; exact K4⟩
  rw [a6, a4, o2, o1]
  have sh : ∀ n ≤ 8 * N4c.cAB κ a + 6, shWd (ldG κ M₀ 0 0 0) 1 n = shWd (hMW w) 1 n := fun n hn => by
    simp only [shWd]; rw [hG n (by omega), hG (n + 1) (by omega)]
  rw [hdrWords, hAe_words, hAn_word, sh _ (by omega), List.map_congr_left fun j hj => sh _ (by
    have := List.mem_range.1 hj; omega), Nat.mul_comm k 256]
  simp only [Array.toList_push, List.append_assoc, List.cons_append, List.singleton_append, List.nil_append]


theorem aggRegs_sem (I : Array Word) (κ : NodeKind) {a : ℕ} (ha : a < N4c.nAgg κ) {M₀ : Mem} {t : St} (hO : OF M₀ t)
    {k : ℕ} (hk : k ≤ κ.maxK) (hK : rd t.M qK = toWord k) :
    (semXIR I (aggRegs κ a) t).o = t.o ∧ OF M₀ (semXIR I (aggRegs κ a) t) ∧
      AgR (8 * N4c.chBase κ (N4c.aggChild κ a)) (jLv k) (dV κ a k) k 0 (semXIR I (aggRegs κ a) t).M := by
  have N := aggN κ ha
  have hs := hO.inv.1
  simp only [regs] at hs
  have hLm := aggL_eq' N.mk1
  have fb := N.fb; have m4 := N.mk4; have he := N.he; have fe := N.fe
  have hmono : jLv k ≤ jLv κ.maxK := by unfold jLv; have := Nat.mul_le_mul_right N4c.sBlk hk; omega
  have hjd : jLv k ≤ k + dC κ a := by unfold dC; omega
  have hk4 : k ≤ 4 := le_trans hk m4
  rw [aggRegs, semXIR_seq, semXIR_blk]
  set ps : List Prim := [.const qCB (toWord (8 * N4c.chBase κ (N4c.aggChild κ a))), .const oK (toWord N4c.sBlk),
    .op .mul qJ qK oK, .const oK 0, .op .ltu qT1 oK qK, .const oK (toWord 3), .op .mul qT1 qT1 oK,
    .op .sub qJ qJ qT1, .const qI 0] with hps
  have O1 : OF M₀ ⟨runPrims ps t.M, t.o⟩ := of_loK I (P := .blk ps)
    (by simp [hps, LoK, Prim.dst, regs, qCB, oK, qJ, qT1, qI]) (by simp [hps, WF, Prim.dst, qCB, oK, qJ, qT1, qI]) hO
  have v1 : rd (runPrims ps t.M) qCB = toWord (8 * N4c.chBase κ (N4c.aggChild κ a)) ∧
      rd (runPrims ps t.M) qJ = toWord (jLv k) ∧ rd (runPrims ps t.M) qI = toWord 0 ∧
      rd (runPrims ps t.M) qK = toWord k := by
    simp only [hps, runPrims, List.foldl, Prim.run]
    simp (disch := (simp only [size_set, qCB, oK, qJ, qT1, qDl, qI, qK]; omega)) only [rd_set_self, rd_set_ne]
    refine ⟨by first | exact True.intro | rfl, ?_, by first | exact True.intro | rfl, by first | exact True.intro | exact hK⟩
    rw [hK, mul_toWord, show (0 : Word) = toWord 0 from rfl, ltu_toWord (by norm_num) (by omega), ite_mul_toWord,
      sub_toWord (by simp only [N4c.sBlk]; omega) (by split_ifs <;> simp only [N4c.sBlk] <;> omega)]
    congr 1; unfold jLv; simp only [N4c.sBlk]; split_ifs <;> omega
  obtain ⟨c1, j1, i1, k1⟩ := v1
  have hs1 := O1.inv.1
  simp only [regs] at hs1
  obtain ⟨M1, hM1⟩ : ∃ M1, runPrims ps t.M = M1 := ⟨_, rfl⟩
  rw [hM1] at O1 c1 j1 i1 k1 hs1
  rw [semXIR_blk, hM1]
  refine ⟨rfl, of_loK I (P := .blk _) (by simp [LoK, Prim.dst, regs, oK, qT1, qDl])
    (by simp [WF, Prim.dst, oK, qT1, qDl]) O1, ?_, ?_, ?_, ?_, ?_⟩
  all_goals simp only [runPrims, List.foldl, Prim.run]
  all_goals simp (disch := (simp only [size_set, qCB, oK, qJ, qT1, qDl, qI, qK] at *; omega)) only
    [rd_set_self, rd_set_ne]
  · exact i1
  · exact c1
  · exact j1
  · rw [k1, j1, add_toWord, sub_toWord (by unfold dC; omega) hjd,
      shl_toWord (by norm_num) (by unfold dC; omega), ltu_toWord (by omega) (by omega), ite_mul_toWord]; rfl
  · exact k1

theorem segOut_wds (W : ℕ → Word) (κ : Bool) (b : ℕ) : ∀ l : List Word, segOut W κ b (catL (l.map .wd)) = l
  | [] => rfl
  | x :: l => by simp only [List.map_cons, catL, segOut, segOut_wds W κ b l]; rfl

theorem okSeg_sp : okSeg spSeg = true ∧ depthSeg spSeg ≤ 9 := by decide

/-- **The traces' prefix at segment `j`**: nothing at `j = 0`; spacer `j`'s entry words (`spW` and its
answer) at `j ≥ 1`. -/
theorem spPre_sem (I : Array Word) (κ : NodeKind) {a k j : ℕ} (ha : a < N4c.nAgg κ) (hk : k ≤ κ.maxK) (hj : j < k)
    {M₀ : Mem} {w : Circ.Asg} (hH : HeapW κ M₀ w) {t : St} (hO : OF M₀ t)
    (hR : AgR (8 * N4c.chBase κ (N4c.aggChild κ a)) (jLv k) (dV κ a k) k j t.M) :
    (semXIR I (spPre κ) t).o.toList = t.o.toList ++
      (if j = 0 then [] else spW ++ packBytes (N4s.spAns κ (N4c.aggChild κ a) k w j).toList) ∧
      OF M₀ (semXIR I (spPre κ) t) ∧ ∀ r ∈ [qI, qCB, qJ, qDl, qK, qSc], rd (semXIR I (spPre κ) t).M r = rd t.M r := by
  have N := aggN κ ha
  have hk4 : k ≤ 4 := le_trans hk N.mk4
  have hC := chR_agg κ ha (by omega) hk
  rw [spPre, semXIR_ite, hR.i]
  by_cases hj0 : j = 0
  · subst hj0
    have e0 : (toWord 0 : Word) = 0 := rfl
    simp only [e0, if_true, semXIR_blk, List.append_nil]
    exact ⟨by first | exact True.intro | simp, by simpa [runPrims] using hO, fun _ _ => by simp only [runPrims, List.foldl]⟩
  rw [if_neg (show toWord j ≠ (0 : Word) from fun h =>
      hj0 ((toWord_eq_iff (a := j) (b := 0) (by omega) (by norm_num)).1 h)), if_neg hj0, spIR, semXIR_seq]
  -- the query's words
  obtain ⟨o1, O1, k1⟩ := bufSeg_sem I spSeg okSeg_sp.1 okSeg_sp.2 hO
  have kb : ∀ r < 200, r ≠ cTmp → rd (semXIR I (bufSeg spSeg) t).M r = rd t.M r := fun r hr hc =>
    bufSeg_keep I okSeg_sp.2 hO.inv hr hc
  rw [show segOut (src t.M apB bufB) false 0 spSeg = spW by rw [spSeg]; exact segOut_wds _ _ _ _] at o1
  generalize semXIR I (bufSeg spSeg) t = t1 at o1 O1 k1 kb
  have hs1 := O1.inv.1
  simp only [regs] at hs1
  -- the answer's registers
  have hQ : 4 ≤ j * (N4c.strideB / 8) := by
    have : N4c.strideB / 8 ≤ j * (N4c.strideB / 8) := Nat.le_mul_of_pos_left _ (by omega)
    have : 4 ≤ N4c.strideB / 8 := by decide
    omega
  have hQ' : j * (N4c.strideB / 8) < 2 ^ 23 := by
    have : j * (N4c.strideB / 8) ≤ 4 * (N4c.strideB / 8) := Nat.mul_le_mul_right _ (by omega)
    have : 4 * (N4c.strideB / 8) < 2 ^ 23 := by decide
    omega
  rw [semXIR_seq, semXIR_blk]
  set ps : List Prim := [.const oK (toWord (N4c.strideB / 8)), .op .mul qN qI oK, .const oK (toWord 4),
    .op .sub qN qN oK, .const qA (toWord 8), .const qB (toWord 55)] with hps
  have kp : ∀ r, r ∉ [oK, qN, qA, qB] → rd (runPrims ps t1.M) r = rd t1.M r := fun r hr =>
    rd_runPrims_of_not_writes (fun p hp he => by
      simp only [hps, List.mem_cons, List.mem_nil_iff, or_false] at hp
      simp only [List.mem_cons, List.mem_nil_iff, or_false, not_or] at hr
      rcases hp with rfl | rfl | rfl | rfl | rfl | rfl <;> simp only [Prim.dst] at he <;> subst he <;> simp_all) _
  have R2 : SwR (8 * N4c.chBase κ (N4c.aggChild κ a)) (jLv k) (dV κ a k) 1 (j * (N4c.strideB / 8) - 4)
      (runPrims ps t1.M) := by
    refine ⟨⟨?_, ?_, ?_⟩, ?_, ?_, ?_⟩
    · rw [kp _ (by decide), kb _ (by decide) (by decide)]; exact hR.cb
    · rw [kp _ (by decide), kb _ (by decide) (by decide)]; exact hR.jl
    · rw [kp _ (by decide), kb _ (by decide) (by decide)]; exact hR.dl
    all_goals simp only [hps, runPrims, List.foldl, Prim.run]
    all_goals simp (disch := (simp only [size_set, oK, qN, qA, qB, qI] at *; omega)) only [rd_set_self, rd_set_ne]
    all_goals first
      | (rw [kb _ (by decide) (by decide), hR.i, mul_toWord, sub_toWord (by omega) hQ]; done)
      | rfl
  have O2 : OF M₀ ⟨runPrims ps t1.M, t1.o⟩ := of_loK I (P := .blk ps)
    (by simp [hps, LoK, Prim.dst, regs, oK, qN, qA, qB]) (by simp [hps, WF, Prim.dst, oK, qN, qA, qB]) O1
  -- the answer's words
  have hG : ∀ n ≤ (κ.maxK - 1) * (N4c.strideB / 8) + nW,
      rd M₀ (hAddr κ (ldIx (8 * N4c.chBase κ (N4c.aggChild κ a)) (jLv k) (dV κ a k) n)) =
        chW κ (N4c.aggChild κ a) k w n ∧
      hAddr κ (ldIx (8 * N4c.chBase κ (N4c.aggChild κ a)) (jLv k) (dV κ a k) n) < bufB := fun n hn => by
    have hb := hC.blk n hn
    have e : ldIx (8 * N4c.chBase κ (N4c.aggChild κ a)) (jLv k) (dV κ a k) n / 8 =
        N4c.blkOf κ (N4c.aggChild κ a) k (n / 8) := by rw [hC.ld]; omega
    refine ⟨?_, hAddr_lt' (by rw [e]; exact hb)⟩
    rw [hMW_heapW hH (by rw [e]; exact hb), hC.ld, chW]
  have hnB : j * (N4c.strideB / 8) ≤ (κ.maxK - 1) * (N4c.strideB / 8) :=
    Nat.mul_le_mul_right _ (by omega)
  obtain ⟨a3, b3, -, d3⟩ := shw4_sem I κ (sh := 1) (by norm_num) (by have := hC.big; omega) hC.jl
    (fun i hi => (hG _ (by omega)).2) O2 R2
  refine ⟨?_, b3, fun r hr => ?_⟩
  · rw [a3, show ({ M := runPrims ps t1.M, o := t1.o } : St).o = t1.o from rfl, o1, List.append_assoc]
    have hD : j * N4c.strideB < N4c.streamB κ (N4c.aggChild κ a) k := by
      simp only [N4c.streamB, N.agg, if_true]
      have hb := (N4c.aggB_blocks (Nat.lt_of_le_of_lt (Nat.zero_le _) hj)).2.2
      have h1 : (j + 1) * N4c.strideB ≤ k * N4c.strideB := Nat.mul_le_mul_right _ (by omega)
      have h2 : 128 < N4c.strideB := by decide
      rw [Nat.add_one_mul] at h1; omega
    rw [spAns_words κ _ k w (by omega) hD]
    refine congrArg (fun l => t.o.toList ++ (spW ++ l)) (List.map_congr_left fun i hi => ?_)
    have hi4 := List.mem_range.1 hi
    simp only [ldG, shWd]
    rw [(hG _ (by omega)).1, (hG _ (by omega)).1]
  · simp only [List.mem_cons, List.mem_nil_iff, or_false] at hr
    rw [d3 r (by rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> decide)
      (by rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> decide), kp r (by
        rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> decide),
      kb r (by rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> decide)
      (by rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> decide)]

/-- Every selector the count reads is a decoded cell inside `f`, on the heap below the buffer. -/
theorem sel_ok (κ : NodeKind) {a i : ℕ} (ha : a < N4c.nAgg κ) (hi : i < κ.maxK) (ι : Kind) :
    κ.oneCell + selR (N4c.sub κ a i) ι < 2 ^ (κ.m - 7) ∧ regs ≤ selA κ a i ι ∧ selA κ a i ι + 1 < bufB := by
  have hn : N4c.nAgg κ ≤ 2 := by cases κ <;> decide
  have hm : κ.maxK ≤ 4 := by cases κ <;> decide
  have h : a = 0 ∨ a = 1 := by omega
  have hi' : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
  rcases h with rfl | rfl <;> rcases hi' with rfl | rfl | rfl | rfl <;> cases κ <;> cases ι <;>
    first | exact absurd hi (by decide) | exact absurd ha (by decide) | decide

theorem cntW_val {M : Mem} (hM : Inv M) {k : ℕ} (hk : k ≤ 4) (hK : rd M qK = toWord k) :
    rd (runPrims cntW M) oX = toWord (k * (itemsOf seq4).length + (k - 1)) ∧
      ∀ r, r ≠ oK → r ≠ oX → r ≠ qT1 → rd (runPrims cntW M) r = rd M r := by
  have hs := hM.1
  simp only [regs] at hs
  refine ⟨?_, fun r h1 h2 h3 => rd_runPrims_of_not_writes (by
    simp [cntW, lenW, Prim.dst, Ne.symm h1, Ne.symm h2, Ne.symm h3]) _⟩
  have hl : (itemsOf seq4).length = 8783 := itemsOf_seq4_len
  simp only [cntW, lenW, List.cons_append, List.nil_append, runPrims, List.foldl, Prim.run]
  simp (disch := (simp only [size_set, oK, oX, qK, qT1]; omega)) only [rd_set_self, rd_set_ne]
  rw [hK, mul_toWord, add_toWord, show (0 : Word) = toWord 0 from rfl, ltu_toWord (by norm_num) (by omega),
    hl]
  rcases Nat.eq_zero_or_pos k with rfl | hk0
  · rfl
  · rw [if_pos hk0, show (1 : Word) = toWord 1 from rfl, sub_toWord (by omega) (by omega)]
    congr 1; omega

/-- **Aggregate `a`'s signed child is emitted** (`signedWords_agg`). -/
theorem aggIR4_sem (I : Array Word) (κ : NodeKind) {a : ℕ} (ha : a < N4c.nAgg κ) {M₀ : Mem} {w : Circ.Asg}
    {s : St} (hO : OF M₀ s) (hsz : bufB + 2 ^ 22 ≤ M₀.size) (hH : HeapW κ M₀ w) :
    (semXIR I (aggIR4 κ a) s).o.toList = s.o.toList ++ signedWords (sgnX sigH κ (N4c.aggChild κ a) w) ∧
      OF M₀ (semXIR I (aggIR4 κ a) s) := by
  have N := aggN κ ha
  -- the count
  obtain ⟨o1, O1, K1⟩ := kSelIR_sem I κ a (w := w) (fun i hi ι => (sel_ok κ ha hi ι).2) (fun i hi ι =>
    hH _ ((out_cells_dec0 κ).1 _ ι) (sel_ok κ ha hi ι).1) hO
  rw [aggIR4, semXIR_seq]
  generalize semXIR I (kSelIR κ a κ.maxK) s = s1 at o1 O1 K1
  set k := kSel κ a w with hkd
  have hk : k ≤ κ.maxK := (kSel_ctl κ a w).2
  have hk4 : k ≤ 4 := le_trans hk N.mk4
  -- the header
  obtain ⟨o2, O2, K2⟩ := aggHd_sem I κ a hH N.cab N.he O1 K1
  rw [semXIR_seq]
  generalize semXIR I (aggHd κ a) s1 = s2 at o2 O2 K2
  -- the registers
  obtain ⟨o3, O3, R3⟩ := aggRegs_sem I κ ha O2 hk K2
  rw [semXIR_seq]
  generalize semXIR I (aggRegs κ a) s2 = s3 at o3 O3 R3
  have hD : ∀ i < k, i * N4c.strideB + N4c.segB ≤ N4c.streamB κ (N4c.aggChild κ a) k := fun i hi => by
    simp only [N4c.streamB, N.agg, if_true]
    have hb := (N4c.aggB_blocks (Nat.lt_of_le_of_lt (Nat.zero_le _) hi)).2.2
    have h1 : (i + 1) * N4c.strideB ≤ k * N4c.strideB := Nat.mul_le_mul_right _ (by omega)
    have h2 : N4c.strideB = N4c.segB + 128 := by decide
    rw [Nat.add_one_mul] at h1; omega
  have hnB : ∀ i < k, i * (N4c.strideB / 8) + nW ≤ (κ.maxK - 1) * (N4c.strideB / 8) + nW := fun i hi =>
    Nat.add_le_add_right (Nat.mul_le_mul_right _ (by omega)) _
  have hC : 0 < k → ChR κ (N4c.aggChild κ a) k (8 * N4c.chBase κ (N4c.aggChild κ a)) (jLv k) (dV κ a k)
      ((κ.maxK - 1) * (N4c.strideB / 8) + nW) := fun h => chR_agg κ ha h hk
  -- the proofs
  have L4 := segLoop_sem I κ (P := .blk []) (E := pfIR)
    (F := fun V => segOut V false 0 (pSeg4 seq4 (mOfB (V 10).toNat.toUInt8))) (pre := fun _ => [])
    (out := fun i => packBytes (bl (pf4 (N4s.segTr κ (N4c.aggChild κ a) k i w))))
    (fun j _ t ht _ => ⟨by simp [semXIR_blk, runPrims], by simpa [semXIR_blk, runPrims] using ht,
      fun r _ => by simp [semXIR_blk, runPrims]⟩)
    (fun t ht => by
      obtain ⟨g1, g2, -⟩ := pfIR_sem I ht
      exact ⟨g1, g2, fun r hr => by
        simp only [List.mem_cons, List.mem_nil_iff, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> exact pfIR_keep I ht.inv (by decide) (by decide) (by decide)⟩)
    (fun i hi V hV => by rw [pf4_words κ (N4c.aggChild κ a) k i w (hD i hi) V hV false, packBytes_wordsBytes])
    O3 hsz hH hC hk N.mk4 hnB hD R3
  rw [semXIR_seq]
  generalize semXIR I (segLoop κ (.blk []) pfIR) s3 = s4 at L4
  obtain ⟨o4, O4, R4⟩ := L4
  -- (a `rw` with the theorem, not `simp`'s definitional `nil_append`: the kernel would otherwise unfold
  -- `packBytes` of a whole proof to see `[] ++ x ≡ x`)
  rw [List.flatMap_congr (l := List.range k) (fun i _ => List.nil_append
    (packBytes (bl (pf4 (N4s.segTr κ (N4c.aggChild κ a) k i w)))))] at o4
  -- the traces
  have hs4 := O4.inv.1
  simp only [regs] at hs4
  obtain ⟨x5, k5⟩ := cntW_val O4.inv hk4 R4.k
  rw [semXIR_seq, aggTr, semXIR_seq, semXIR_blk, semXIR_seq]
  rw [show semXIR I (.out oX) ⟨runPrims cntW s4.M, s4.o⟩ =
    ⟨runPrims cntW s4.M, s4.o.push (rd (runPrims cntW s4.M) oX)⟩ from rfl, x5]
  have O5 : OF M₀ ⟨runPrims cntW s4.M, s4.o.push (toWord (k * (itemsOf seq4).length + (k - 1)))⟩ :=
    of_mk (of_loK I (P := .blk cntW) (by simp [cntW, lenW, LoK, Prim.dst, oK, oX, qT1, regs])
      (by simp [cntW, lenW, WF, Prim.dst, oK, oX, qT1]) O4) _
  rw [semXIR_seq, semXIR_blk]
  have k6 : ∀ r, r ≠ qI → r ≠ oK → r ≠ oX → r ≠ qT1 → rd (runPrims [.const qI 0] (runPrims cntW s4.M)) r =
      rd s4.M r := fun r h1 h2 h3 h4 => by
    rw [rd_runPrims_of_not_writes (by simp [Prim.dst, Ne.symm h1]), k5 r h2 h3 h4]
  have R6 : AgR (8 * N4c.chBase κ (N4c.aggChild κ a)) (jLv k) (dV κ a k) k 0
      (runPrims [.const qI 0] (runPrims cntW s4.M)) :=
    ⟨by rw [rd_const_self (by rw [size_runPrims]; simp only [qI]; omega)]; rfl,
      by rw [k6 _ (by decide) (by decide) (by decide) (by decide)]; exact R4.cb,
      by rw [k6 _ (by decide) (by decide) (by decide) (by decide)]; exact R4.jl,
      by rw [k6 _ (by decide) (by decide) (by decide) (by decide)]; exact R4.dl,
      by rw [k6 _ (by decide) (by decide) (by decide) (by decide)]; exact R4.k⟩
  have O6 : OF M₀ ⟨runPrims [.const qI 0] (runPrims cntW s4.M),
      s4.o.push (toWord (k * (itemsOf seq4).length + (k - 1)))⟩ :=
    of_loK I (P := .blk [.const qI 0]) (by simp [LoK, Prim.dst, regs, qI]) (by simp [WF, Prim.dst, qI]) O5
  have hdT := okSeg_tr.2.2.2
  have L7 := segLoop_sem I κ (P := spPre κ) (E := bufSeg (trBody4 seq4)) (F := fun V => segOut V false 0 (trBody4 seq4))
    (pre := fun i => if i = 0 then [] else spW ++ packBytes (N4s.spAns κ (N4c.aggChild κ a) k w i).toList)
    (out := fun i => (N4s.segTr κ (N4c.aggChild κ a) k i w).flatMap entryW)
    (fun j hj t ht hR => spPre_sem I κ ha hk hj hH ht hR)
    (fun t ht => by
      obtain ⟨g1, g2, -⟩ := bufSeg_sem I (trBody4 seq4) okSeg_tr.2.2.1 (le_trans hdT (by norm_num)) ht
      exact ⟨g1, g2, fun r hr => by
        simp only [List.mem_cons, List.mem_nil_iff, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;>
          exact bufSeg_keep I (le_trans hdT (by norm_num)) ht.inv (by decide) (by decide)⟩)
    (fun i hi V hV => (entries_segTr κ (N4c.aggChild κ a) k i w (hD i hi) V hV false).symm)
    O6 hsz hH hC hk N.mk4 hnB hD R6
  dsimp only
  generalize semXIR I (segLoop κ (spPre κ) (bufSeg (trBody4 seq4))) ⟨runPrims [.const qI 0]
    (runPrims cntW s4.M), s4.o.push (toWord (k * (itemsOf seq4).length + (k - 1)))⟩ = s7 at L7
  obtain ⟨o7, O7, -⟩ := L7
  have hf := wb_fit κ N.σ2
  obtain ⟨o8, O8⟩ := sigIR_sem I κ (N4c.aggChild κ a) O7 hf.2 (fun m hm => hAddr_lt' (by omega))
  refine ⟨?_, O8⟩
  obtain ⟨V, hVd⟩ : ∃ V : ℕ → ℕ → Word, V = fun i u => (vS κ (N4c.aggChild κ a) k i w).getD u 0 := ⟨_, rfl⟩
  have hV : ∀ i < k, ∀ u (hu : u < (vS κ (N4c.aggChild κ a) k i w).length),
      (vS κ (N4c.aggChild κ a) k i w)[u] = V i u := fun i _ u hu => by
    rw [hVd]; exact (List.getD_eq_getElem _ _ hu).symm
  have hP : ((List.range k).flatMap fun i => segOut (V i) false 0 (pSeg4 seq4 (mOfB (V i 10).toNat.toUInt8))) =
      (List.range k).flatMap fun i => packBytes (bl (pf4 (N4s.segTr κ (N4c.aggChild κ a) k i w))) :=
    List.flatMap_congr fun i hi => by
      rw [pf4_words κ (N4c.aggChild κ a) k i w (hD i (List.mem_range.1 hi)) (V i) (hV i (List.mem_range.1 hi)) false,
        packBytes_wordsBytes]
  have hT : ((List.range k).flatMap fun i =>
        (if i = 0 then [] else spW ++ packBytes (N4s.spAns κ (N4c.aggChild κ a) k w i).toList) ++
          segOut (V i) false 0 (trBody4 seq4)) =
      (List.range k).flatMap fun i =>
        (if i = 0 then [] else spW ++ packBytes (N4s.spAns κ (N4c.aggChild κ a) k w i).toList) ++
          (N4s.segTr κ (N4c.aggChild κ a) k i w).flatMap entryW :=
    List.flatMap_congr fun i hi => by
      rw [entries_segTr κ (N4c.aggChild κ a) k i w (hD i (List.mem_range.1 hi)) (V i) (hV i (List.mem_range.1 hi)) false]
  rw [o8, o7, sigL_eq κ N.σ2 hH, signedWords_agg κ ha w V hV, ← hkd, hP, hT]
  dsimp only
  rw [Array.toList_push, o4, o3, o2, o1]
  simp only [Array.toList_push, List.append_assoc, List.cons_append, List.singleton_append, List.nil_append]

end FR.X

end G6_FRXOut4A

section G6_FRXOut4O

-- New for `flock-recursive` (BLUEPRINT revision 4.1, §6.2 step 5, A.7; stage S-H4, pass 11, items 3–4: the
-- node output program `outIR4`, its semantics, cost, output count and size). 3.x analogue: `FRXOutRun.outIR`.

/-!
# The node output program `outIR4 κ`

`outIR4 κ` emits the tag `1`, the four statement cells' words (`stC κ σ h`, two words each), then
signed child `0` (a previous node for `N2`/`N4`, `prevIR`; aggregate `0` for `N8`) and signed child `1`
(the aggregate: aggregate `0` for `N2`/`N4`, `1` for `N8`).

* **`outIR4_sem`**: on a heap holding the decoded cells of `w = wF κ L es` (`HeapW`, from
  `decF04_wF`), `outIR4 κ` appends **`witWords (readW4 sigH κ L es)`** (`witWords_readW4`,
  `prevIR_sem`, `aggIR4_sem`);
* `wf_outIR4`, `noLoopT_outIR4`; the cost (an upper bound, `cost_outIR4`), the output count and the
  size are computed from their components (each segment's by `decide +kernel`).
-/

namespace FR.X

open RecursionFast FR.Read FR.Rev4 FR.Snd

attribute [local irreducible] entryK storeM runPrims

/-! ## Specification -/

/-- The statement cells' heap words: per signed child `σ < 2` and half `h < 2`, two words. -/
def stA (κ : NodeKind) : List ℕ :=
  (List.range 2).flatMap fun σ => (List.range 2).flatMap fun h => [wAddr κ (N4c.stC κ σ h), wAddr κ (N4c.stC κ σ h) + 1]

/-- **The node output program** at node kind `κ`. -/
def outIR4 (κ : NodeKind) : XIR :=
  .seq (.blk [.const oX 1]) (.seq (.out oX) (.seq (outAs (stA κ))
    (.seq (if κ.hasPrev then prevIR κ else aggIR4 κ 0) (aggIR4 κ (if κ.hasPrev then 0 else 1)))))

/-! ## The semantics -/

theorem stC_ok (κ : NodeKind) {σ h : ℕ} (hσ : σ < 2) (hh : h < 2) :
    N4c.stC κ σ h < 2 ^ (κ.m - 7) ∧ regs ≤ wAddr κ (N4c.stC κ σ h) ∧ wAddr κ (N4c.stC κ σ h) + 1 < bufB := by
  have e1 : σ = 0 ∨ σ = 1 := by omega
  have e2 : h = 0 ∨ h = 1 := by omega
  rcases e1 with rfl | rfl <;> rcases e2 with rfl | rfl <;> cases κ <;> decide

theorem stA_words (κ : NodeKind) {M₀ : Mem} {w : Circ.Asg} (hH : HeapW κ M₀ w) :
    (stA κ).map (rd M₀) = elemWords (w (N4c.stC κ 0 0)) ++ elemWords (w (N4c.stC κ 0 1)) ++
      (elemWords (w (N4c.stC κ 1 0)) ++ elemWords (w (N4c.stC κ 1 1))) := by
  have e : ∀ σ h, σ < 2 → h < 2 → elemWords (w (N4c.stC κ σ h)) =
      [rd M₀ (wAddr κ (N4c.stC κ σ h)), rd M₀ (wAddr κ (N4c.stC κ σ h) + 1)] := fun σ h hσ hh => by
    rw [← hH _ ((out_cells_dec0 κ).2 σ h hh) (stC_ok κ hσ hh).1, elemWords_rdF]
  rw [e 0 0 (by norm_num) (by norm_num), e 0 1 (by norm_num) (by norm_num), e 1 0 (by norm_num) (by norm_num),
    e 1 1 (by norm_num) (by norm_num)]
  rfl

/-- **The node output**: on a heap holding `wF κ L es`'s decoded cells, `outIR4 κ` appends the node
witness's words `witWords (readW4 sigH κ L es)`. -/
theorem outIR4_sem (I : Array Word) (κ : NodeKind) {L es : Log} {s : St} (hM : Inv s.M)
    (hsz : bufB + 2 ^ 22 ≤ s.M.size) (hH : HeapW κ s.M (wF κ L es)) :
    (semXIR I (outIR4 κ) s).o.toList = s.o.toList ++ witWords (readW4 sigH κ L es) := by
  have hO : OF s.M s := ⟨hM, rfl, fun _ _ _ => rfl⟩
  generalize s.M = M₀ at hO hsz hH
  have hs := hO.inv.1
  simp only [regs] at hs
  rw [witWords_readW4]
  unfold outIR4
  simp only [semXIR_seq, semXIR_blk]
  rw [show semXIR I (.out oX) ⟨runPrims [.const oX 1] s.M, s.o⟩ =
    ⟨runPrims [.const oX 1] s.M, s.o.push (rd (runPrims [.const oX 1] s.M) oX)⟩ from rfl]
  have x1 : rd (runPrims [.const oX 1] s.M) oX = toWord 1 := by
    simp only [runPrims, List.foldl, Prim.run]; rw [rd_set_self (by simp only [oX]; omega)]; rfl
  rw [x1]
  have O1 : OF M₀ ⟨runPrims [.const oX 1] s.M, s.o.push (toWord 1)⟩ :=
    of_mk (of_loK I (P := .blk [.const oX 1]) (by simp [LoK, Prim.dst, oX, regs]) (by simp [WF, Prim.dst, oX]) hO) _
  have o1 : (⟨runPrims [.const oX 1] s.M, s.o.push (toWord 1)⟩ : St).o = s.o.push (toWord 1) := rfl
  generalize (⟨runPrims [.const oX 1] s.M, s.o.push (toWord 1)⟩ : St) = s1 at O1 o1
  obtain ⟨o2, O2, -⟩ := outAs_sem I (stA κ) s1 (fun a ha => by
    simp only [stA, List.mem_flatMap, List.mem_range, List.mem_cons, List.mem_nil_iff, or_false] at ha
    obtain ⟨σ, hσ, h, hh, rfl | rfl⟩ := ha
    · exact ⟨(stC_ok κ hσ hh).2.1, Nat.lt_of_succ_lt (stC_ok κ hσ hh).2.2⟩
    · exact ⟨Nat.le_succ_of_le (stC_ok κ hσ hh).2.1, (stC_ok κ hσ hh).2.2⟩) O1
  generalize semXIR I (outAs (stA κ)) s1 = s2 at o2 O2
  rw [stA_words κ hH] at o2
  have hc : ∀ (P₀ P₁ : XIR) (σ₁ : ℕ), σ₁ = 1 →
      (∀ t, OF M₀ t → (semXIR I P₀ t).o.toList = t.o.toList ++ signedWords (sgnX sigH κ 0 (wF κ L es)) ∧
        OF M₀ (semXIR I P₀ t)) →
      (∀ t, OF M₀ t → (semXIR I P₁ t).o.toList = t.o.toList ++ signedWords (sgnX sigH κ σ₁ (wF κ L es)) ∧
        OF M₀ (semXIR I P₁ t)) →
      (semXIR I P₁ (semXIR I P₀ s2)).o.toList = s.o.toList ++ (toWord 1 ::
        (elemWords (wF κ L es (N4c.stC κ 0 0)) ++ elemWords (wF κ L es (N4c.stC κ 0 1)) ++
          (elemWords (wF κ L es (N4c.stC κ 1 0)) ++ elemWords (wF κ L es (N4c.stC κ 1 1))) ++
          signedWords (sgnX sigH κ 0 (wF κ L es)) ++ signedWords (sgnX sigH κ 1 (wF κ L es)))) := by
    intro P₀ P₁ σ₁ hσ h0 h1
    subst hσ
    obtain ⟨a3, b3⟩ := h0 s2 O2
    obtain ⟨a4, -⟩ := h1 _ b3
    rw [a4, a3, o2, o1]
    simp only [Array.toList_push, List.append_assoc, List.cons_append, List.singleton_append, List.nil_append]
  cases hp : κ.hasPrev
  · simp only [Bool.false_eq_true, if_false]
    have n8 : N4c.aggChild κ 0 = 0 ∧ N4c.aggChild κ 1 = 1 ∧ 1 < N4c.nAgg κ := by
      simp [N4c.aggChild, N4c.nAgg, hp]
    exact hc _ _ 1 rfl (fun t ht => by
        have := aggIR4_sem I κ (a := 0) (by omega) ht hsz hH; rwa [n8.1] at this)
      (fun t ht => by have := aggIR4_sem I κ (a := 1) n8.2.2 ht hsz hH; rwa [n8.2.1] at this)
  · simp only [if_true]
    have n2 : N4c.aggChild κ 0 = 1 ∧ 0 < N4c.nAgg κ := by simp [N4c.aggChild, N4c.nAgg, hp]
    exact hc _ _ 1 rfl (fun t ht => prevIR_sem I κ hp ht hsz hH)
      (fun t ht => by have := aggIR4_sem I κ (a := 0) n2.2 ht hsz hH; rwa [n2.1] at this)

/-! ## Well formed, no tape loop -/

theorem wf_ldA {d a : ℕ} (hd : 4 ≤ d) : WF (ldA d a) := ⟨by simp [WF, Prim.dst, oAd], hd⟩

theorem wf_outAs : ∀ l : List ℕ, WF (outAs l)
  | [] => by simp [outAs, WF]
  | _ :: l => ⟨wf_ldA (by decide), trivial, wf_outAs l⟩

theorem wf_kSelIR (κ : NodeKind) (a : ℕ) : ∀ n, WF (kSelIR κ a n)
  | 0 => by simp [kSelIR, WF, Prim.dst, qAl, qK]
  | n + 1 => ⟨wf_kSelIR κ a n, wf_ldA (by decide), wf_ldA (by decide), wf_ldA (by decide), wf_ldA (by decide),
      wf_ldA (by decide), wf_ldA (by decide), by simp [kPs, WF, Prim.dst, qS0, qS1, oK, qAl, qK]⟩

theorem wf_segLoop (κ : NodeKind) {P E : XIR} (hP : WF P) (hE : WF E) (hnP : ¬ Writes P qSc) (hn : ¬ Writes E qSc) :
    WF (segLoop κ P E) := by
  refine ⟨⟨by decide, by decide, by decide⟩, by decide, ?_, hP, wf_cpSeg κ, hE, by simp [WF, Prim.dst, qI]⟩
  rintro (h | h | h | ⟨p, hp, he⟩)
  · exact hnP h
  · exact absurd (writes_wrL _ _ h) (by cases κ <;> decide)
  · exact hn h
  · simp only [List.mem_cons, List.mem_nil_iff, or_false] at hp; subst hp; simp [Prim.dst, qI, qSc] at he

theorem wf_spPre (κ : NodeKind) : WF (spPre κ) :=
  ⟨⟨wf_bufSeg okSeg_sp.2, by simp [WF, Prim.dst, oK, qN, qA, qB], wf_shw4 κ⟩, by simp [WF]⟩

theorem noW_spPre (κ : NodeKind) : ¬ Writes (spPre κ) qSc := by
  rintro ((h | ⟨p, hp, he⟩ | h) | ⟨p, hp, -⟩)
  · exact noW_bufSeg (by decide) (by decide) h
  · simp only [List.mem_cons, List.mem_nil_iff, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl <;> simp [Prim.dst, oK, qN, qA, qB, qSc] at he
  · exact absurd (writes_wrL _ _ h) (by cases κ <;> decide)
  · simp at hp

theorem wf_aggIR4 (κ : NodeKind) (a : ℕ) : WF (aggIR4 κ a) := by
  have hT := okSeg_tr.2.2.2
  refine ⟨wf_kSelIR κ a _, ⟨by simp [lenW, WF, Prim.dst, oK, oX], trivial, by simp [lenW, WF, Prim.dst, oK, oX],
    trivial, by simp [WF, Prim.dst, qCB, qJ, qDl, qA, qB, qN], wf_shwO κ, by simp [WF, Prim.dst, qN], wf_shw4 κ⟩,
    ⟨by simp [WF, Prim.dst, qCB, oK, qJ, qT1, qI], by simp [WF, Prim.dst, oK, qT1, qDl]⟩,
    wf_segLoop κ (by simp [WF]) wf_pfIR (by simp [Writes]) (noW_pfIR (by decide) (by decide) (by decide)),
    ⟨by simp [cntW, lenW, WF, Prim.dst, oK, oX, qT1], trivial, by simp [WF, Prim.dst, qI],
    wf_segLoop κ (wf_spPre κ) (wf_bufSeg (le_trans hT (by norm_num))) (noW_spPre κ)
      (noW_bufSeg (by decide) (by decide))⟩, wf_sigIR κ _⟩

theorem wf_prevIR (κ : NodeKind) : WF (prevIR κ) :=
  ⟨by simp [WF, Prim.dst, oX], trivial, by simp [prevRegs, WF, Prim.dst, qCB, qJ, qDl, qI], wf_cpSeg κ, wf_pfIR,
    wf_bufSeg (le_trans okSeg_tr.2.1 (by norm_num)), wf_sigIR κ 0⟩

theorem wf_outIR4 (κ : NodeKind) : WF (outIR4 κ) := by
  refine ⟨by simp [WF, Prim.dst, oX], trivial, wf_outAs _, ?_, wf_aggIR4 κ _⟩
  cases κ.hasPrev
  · exact wf_aggIR4 κ 0
  · exact wf_prevIR κ

theorem noLoopT_segIR' (sg : Seg) : NoLoopT (segIR apB 0 sg) := noLoopT_segIR apB sg 0

theorem noLoopT_pfIR : NoLoopT pfIR :=
  ⟨trivial, ⟨trivial, by simp [NoLoopT, ldw], trivial⟩, noLoopT_segIR' _, noLoopT_segIR' _, noLoopT_segIR' _⟩

theorem noLoopT_shwC (κ : NodeKind) : NoLoopT (shwC κ) := by simp [NoLoopT, shwC, ldC, ldw]

theorem noLoopT_shw4 (κ : NodeKind) : NoLoopT (shw4 κ) := by simp [NoLoopT, shw4, shwO, shwC, ldC, ldw]

theorem noLoopT_cpSeg (κ : NodeKind) : NoLoopT (cpSeg κ) := by simp [NoLoopT, cpSeg, cpBody, ldC, ldw]

theorem noLoopT_spPre (κ : NodeKind) : NoLoopT (spPre κ) :=
  ⟨⟨⟨trivial, noLoopT_segIR' _⟩, trivial, noLoopT_shw4 κ⟩, trivial⟩

theorem noLoopT_sigIR (κ : NodeKind) (σ : ℕ) : NoLoopT (sigIR κ σ) := by
  simp [NoLoopT, sigIR, sigHd, otsIR, pathIR, otsB, pathB, shw4, shwO, shwC, ldC, ldw]

theorem noLoopT_outAs : ∀ l : List ℕ, NoLoopT (outAs l)
  | [] => trivial
  | _ :: l => ⟨⟨trivial, trivial⟩, trivial, noLoopT_outAs l⟩

theorem noLoopT_kSelIR (κ : NodeKind) (a : ℕ) : ∀ n, NoLoopT (kSelIR κ a n)
  | 0 => trivial
  | n + 1 => ⟨noLoopT_kSelIR κ a n, by simp [NoLoopT, kStep, ldA]⟩

theorem noLoopT_aggIR4 (κ : NodeKind) (a : ℕ) : NoLoopT (aggIR4 κ a) :=
  ⟨noLoopT_kSelIR κ a _, ⟨trivial, trivial, trivial, trivial, trivial, by simp [NoLoopT, shwO, shwC, ldC, ldw], trivial,
    noLoopT_shw4 κ⟩, ⟨trivial, trivial⟩, ⟨trivial, noLoopT_cpSeg κ, noLoopT_pfIR, trivial⟩,
    ⟨trivial, trivial, trivial, noLoopT_spPre κ, noLoopT_cpSeg κ, ⟨trivial, noLoopT_segIR' _⟩, trivial⟩, noLoopT_sigIR κ _⟩

theorem noLoopT_prevIR (κ : NodeKind) : NoLoopT (prevIR κ) :=
  ⟨trivial, trivial, trivial, noLoopT_cpSeg κ, noLoopT_pfIR, ⟨trivial, noLoopT_segIR' _⟩, noLoopT_sigIR κ 0⟩

theorem noLoopT_outIR4 (κ : NodeKind) : NoLoopT (outIR4 κ) := by
  refine ⟨trivial, trivial, noLoopT_outAs _, ?_, noLoopT_aggIR4 κ _⟩
  cases κ.hasPrev
  · exact noLoopT_aggIR4 κ 0
  · exact noLoopT_prevIR κ

/-! ## Cost, output count, size (from the components') -/

theorem cso_pfIR : cost pfIR 0 = 4529999 ∧ outs pfIR 0 = 109538 ∧ sizeIR pfIR = 16288 := by decide +kernel

theorem cso_trS : cost (bufSeg (trSeg4 seq4)) 0 = 6912071 ∧ outs (bufSeg (trSeg4 seq4)) 0 = 193889 ∧
    sizeIR (bufSeg (trSeg4 seq4)) = 5176 := by decide +kernel

theorem cso_trB : cost (bufSeg (trBody4 seq4)) 0 = 6912067 ∧ outs (bufSeg (trBody4 seq4)) 0 = 193888 ∧
    sizeIR (bufSeg (trBody4 seq4)) = 5172 := by decide +kernel

theorem cso_cpSeg (κ : NodeKind) : cost (cpSeg κ) 0 = 17256048 ∧ outs (cpSeg κ) 0 = 0 ∧
    sizeIR (cpSeg κ) = 106 := by cases κ <;> exact ⟨rfl, rfl, rfl⟩

theorem cso_spPre (κ : NodeKind) : cost (spPre κ) 0 = 480 ∧ outs (spPre κ) 0 = 17 ∧ sizeIR (spPre κ) = 481 := by
  cases κ <;> decide +kernel

theorem cso_sigIR (κ : NodeKind) {σ : ℕ} (hσ : σ < 2) : cost (sigIR κ σ) 0 = 62091 ∧ outs (sigIR κ σ) 0 = 597 ∧
    sizeIR (sigIR κ σ) = 993 := by interval_cases σ <;> cases κ <;> decide +kernel

theorem cso_aggHd (κ : NodeKind) {a : ℕ} (ha : a < 2) : cost (aggHd κ a) 0 = 543 ∧ outs (aggHd κ a) 0 = 7 ∧
    sizeIR (aggHd κ a) = 543 := by interval_cases a <;> cases κ <;> decide +kernel

theorem cso_kSel (κ : NodeKind) {a : ℕ} (ha : a < 2) : cost (kSelIR κ a κ.maxK) 0 ≤ 179 ∧
    outs (kSelIR κ a κ.maxK) 0 = 0 ∧ sizeIR (kSelIR κ a κ.maxK) ≤ 179 := by
  interval_cases a <;> cases κ <;> decide +kernel

theorem cso_outAs (κ : NodeKind) : cost (outAs (stA κ)) 0 = 49 ∧ outs (outAs (stA κ)) 0 = 8 ∧
    sizeIR (outAs (stA κ)) = 49 := by cases κ <;> decide +kernel

/-- **The node output's cost, output count and size** (upper bounds; exact values: cost `120,732,390`,
`212,641,792`, `367,763,081`; outputs `911,525`, `1,518,411`, `2,428,763`; size `46,500`, `46,588`,
`47,965` at `N2`, `N4`, `N8`). -/
theorem cso_outIR4 (κ : NodeKind) : cost (outIR4 κ) 0 ≤ 600000000 ∧ outs (outIR4 κ) 0 ≤ 2500000 ∧
    sizeIR (outIR4 κ) ≤ 48000 := by
  -- κ stays a variable and the closed programs are opaque (`PF`, `PS`, `PB`): the kernel never
  -- evaluates a closed cost or size while checking the `simp` steps (G5)
  obtain ⟨r1, r2, r3⟩ := cso_cpSeg κ
  obtain ⟨q1, q2, q3⟩ := cso_spPre κ
  obtain ⟨s1, s2, s3⟩ := cso_sigIR κ (σ := 0) (by norm_num)
  obtain ⟨u1, u2, u3⟩ := cso_sigIR κ (σ := N4c.aggChild κ 0) (by cases κ <;> decide)
  obtain ⟨v1, v2, v3⟩ := cso_sigIR κ (σ := N4c.aggChild κ 1) (by cases κ <;> decide)
  obtain ⟨h1, h2, h3⟩ := cso_aggHd κ (a := 0) (by norm_num)
  obtain ⟨g1, g2, g3⟩ := cso_aggHd κ (a := 1) (by norm_num)
  obtain ⟨k1, k2, k3⟩ := cso_kSel κ (a := 0) (by norm_num)
  obtain ⟨l1, l2, l3⟩ := cso_kSel κ (a := 1) (by norm_num)
  obtain ⟨o1, o2, o3⟩ := cso_outAs κ
  have hm : BitVec.toNat (toWord κ.maxK) ≤ 4 := by cases κ <;> decide
  obtain ⟨PF, hF⟩ : ∃ P, pfIR = P := ⟨_, rfl⟩
  obtain ⟨PS, hS⟩ : ∃ P, bufSeg (trSeg4 seq4) = P := ⟨_, rfl⟩
  obtain ⟨PB, hB⟩ : ∃ P, bufSeg (trBody4 seq4) = P := ⟨_, rfl⟩
  obtain ⟨p1, p2, p3⟩ := hF ▸ cso_pfIR
  obtain ⟨a1, a2, a3⟩ := hS ▸ cso_trS
  obtain ⟨b1, b2, b3⟩ := hB ▸ cso_trB
  simp only [outIR4, prevIR, aggIR4, aggTr, segLoop, prevRegs, aggRegs, hF, hS, hB]
  cases κ.hasPrev <;>
  simp [cost, outs, sizeIR, blkSteps, lenW, cntW, p1, p2, p3, r1, r2, r3, q1, q2, q3, a1, a2, a3, b1, b2, b3, s1, s2,
    s3, u1, u2, u3, v1, v2, v3, h1, h2, h3, g1, g2, g3, k2, l2, o1, o2, o3] <;>
  omega

end FR.X

end G6_FRXOut4O

section G6_FRXNd4

-- New for `flock-recursive` (BLUEPRINT revision 4.1, §6.2 steps 1–5, B-14; stage S-H4, pass 11, item 5: the
-- node branch `nd` and its decode law). 3.x analogue: `FRXNode.decNode`, `FRXNodeRun.ext_node`.

/-!
# The revision 4.1 node branch `nd`

**`nd`** dispatches on the node byte (`ndK4`) and runs, at node kind `κ`, the decode `decF04 κ`
(index, level 0's read, the chain, the five levels: `f⁽⁰⁾`'s rows `1 … 7` on the heap) and then the
output `outIR4 κ` (the node witness's words).

* **`decOk4_nd`**: `DecOk4 nd` — well formed, the loop bounds on every domain tape of a proof of
  `piSizeOf seq4` bytes (`safe_decF04`; the output has no tape loop), the cost within `decBudget4`
  (`cost_le_decF04` and `cso_outIR4`), at most `outCap` output words, at most `2^19` statements.
* **`nodeDec4_nd`**: the decode law `NodeDec4 nd` with links **`LinksD4`** (exactly `decF04_sem`'s
  hypotheses on the log and its transcript) and witness **`readW4 sigH`**: on a node proof in the
  domain whose links hold, `nd` outputs `witWords (readW4 sigH κ L es)` (`decF04_wF`, `outIR4_sem`),
  and the witness fits the output format (`readW4_fits`).

S-L4's `links4_sigH` discharges `Links4 nd nodeDec4_nd` from `Gaps4`.
-/

namespace FR.X.X4

open RecursionFast FR.X FR.Rev4 FR.Snd

/-! ## The node branch -/

/-- **The revision 4.1 node branch**: per node kind, the decode then the output. -/
def nd : XIR :=
  ndK4 (.seq (decF04 .N2) (outIR4 .N2)) (.seq (decF04 .N4) (outIR4 .N4)) (.seq (decF04 .N8) (outIR4 .N8))

/-! ## `DecOk4 nd` -/

theorem noLoopT_kindNd4 : NoLoopT kindNd4 := by simp [NoLoopT, kindNd4, readAt]

theorem cost_kindNd4 (t : ℕ) : cost kindNd4 t = 15 := by
  rw [cost_noLoopT _ noLoopT_kindNd4 t]; decide

theorem outs_kindNd4 (t : ℕ) : outs kindNd4 t = 0 := by
  rw [outs_noLoopT _ noLoopT_kindNd4 t]; decide

/-- `sizeIR` of a sequence, structurally (`rw` with it keeps the kernel from evaluating closed sizes). -/
theorem sizeIR_seq (P Q : XIR) : sizeIR (.seq P Q) = sizeIR P + sizeIR Q + 1 := rfl

/-- `sizeIR` of the dispatch, structurally. -/
theorem sizeIR_ndK4 (P2 P4 P8 : XIR) :
    sizeIR (ndK4 P2 P4 P8) = sizeIR kindNd4 + (sizeIR P2 + (sizeIR P4 + sizeIR P8 + 1) + 1) + 1 := rfl

theorem sizeIR_decF04 : sizeIR (decF04 .N2) = 57067 ∧ sizeIR (decF04 .N4) = 57067 ∧ sizeIR (decF04 .N8) = 57067 := by
  -- the chain's size from its table's length (`chTab4`'s words are not evaluated)
  have hc : sizeIR (chainIR pL4 nRep4 (chTab4 seq4 nRep4) seedIR) = 18943 := by
    rw [sizeIR_chainIR, chTab4_length]; decide +kernel
  refine ⟨?_, ?_, ?_⟩ <;> rw [decF04, sizeIR_seq, sizeIR_seq, sizeIR_seq, hc] <;> decide +kernel

theorem cost_outIR4 (κ : NodeKind) (t : ℕ) : cost (outIR4 κ) t ≤ 600000000 := by
  rw [cost_noLoopT _ (noLoopT_outIR4 κ) t]; exact (cso_outIR4 κ).1

theorem outs_outIR4 (κ : NodeKind) (t : ℕ) : outs (outIR4 κ) t ≤ 2500000 := by
  rw [outs_noLoopT _ (noLoopT_outIR4 κ) t]; exact (cso_outIR4 κ).2.1

/-- **The node branch meets `DecOk4`.** -/
theorem decOk4_nd : DecOk4 nd where
  wf := ⟨wf_kindNd4, ⟨wf_decF04 .N2, wf_outIR4 .N2⟩, ⟨wf_decF04 .N4, wf_outIR4 .N4⟩, ⟨wf_decF04 .N8, wf_outIR4 .N8⟩⟩
  safe := fun c π L hs hq ht => .seq (safe_of_noLoopT noLoopT_kindNd4)
    (.ite (.seq (safe_decF04 .N2 c π L hs hq ht) (safe_of_noLoopT (noLoopT_outIR4 _)))
      (.ite (.seq (safe_decF04 .N4 c π L hs hq ht) (safe_of_noLoopT (noLoopT_outIR4 _)))
        (.seq (safe_decF04 .N8 c π L hs hq ht) (safe_of_noLoopT (noLoopT_outIR4 _)))))
  cost := fun t => by
    obtain ⟨d2, d4, d8⟩ := cost_le_decF04 t
    have o2 := cost_outIR4 .N2 t
    have o4 := cost_outIR4 .N4 t
    have o8 := cost_outIR4 .N8 t
    simp only [nd, ndK4, cost, cost_kindNd4, decBudget4, fuelBase, fuelPerWord]
    omega
  outs := fun t => by
    have o2 := outs_outIR4 .N2 t
    have o4 := outs_outIR4 .N4 t
    have o8 := outs_outIR4 .N8 t
    simp only [nd, ndK4, outs, outs_kindNd4, outs_decF04, outCap]
    omega
  size := by
    obtain ⟨z2, z4, z8⟩ := sizeIR_decF04
    have o2 := (cso_outIR4 .N2).2.2
    have o4 := (cso_outIR4 .N4).2.2
    have o8 := (cso_outIR4 .N8).2.2
    have k : sizeIR kindNd4 = 15 := by decide
    rw [nd, sizeIR_ndK4, sizeIR_seq, sizeIR_seq, sizeIR_seq, z2, z4, z8, k]
    generalize sizeIR (outIR4 .N2) = a2 at o2 ⊢
    generalize sizeIR (outIR4 .N4) = a4 at o4 ⊢
    generalize sizeIR (outIR4 .N8) = a8 at o8 ⊢
    omega

/-! ## The decode law -/

theorem pickNd_eq (κ : NodeKind) :
    pickNd κ (.seq (decF04 .N2) (outIR4 .N2)) (.seq (decF04 .N4) (outIR4 .N4)) (.seq (decF04 .N8) (outIR4 .N8)) =
      .seq (decF04 κ) (outIR4 κ) := by cases κ <;> rfl

/-- **The node branch outputs the node witness** read off `f⁽⁰⁾` (`readW4 sigH`), on a node proof in
the domain whose log and transcript meet the links `LinksD4`. -/
theorem nd_out {κ : NodeKind} {c : Digest} {π : Proof} {L es : Log} (hN : kindOf4 π = .node κ) (hD : InDomE c π L)
    (hl : LinksD4 κ L es π c) :
    (semXIR (extractorInput c π L).toArray nd (st1 c π L)).o.toList = witWords (readW4 sigH κ L es) := by
  obtain ⟨hb, hz⟩ := kindOf4_node hN
  obtain ⟨hS, ⟨st₀, hfm⟩, hcap, hfin, hfar, hA⟩ := hl
  have hps : π.size = piSizeOf seq4 := hz.trans piSizeOf_seq4.symm
  have hpL : pL4 = 109543 := fmt4_vals.1
  have hD4 : Dom4 pL4 c π L := ⟨by rw [hz, hpL], hD.2.1, hD.2.2⟩
  have hM := inv_st1 c π L
  have hsz0 : (st1 c π L).M.size = memX4 + mpwX * (extractorInput c π L).length := by
    simp [st1, initSt]
  have hlen : memX4 + L.length + L.length ≤ memX4 + mpwX * (extractorInput c π L).length := by
    have h1 := tape_entries_end4 c π L hD4.hs
    have h2 := len_entries L
    simp only [mpwX]; omega
  have hπ : 0 < π.size := by omega
  rw [nd, ndK4_sem c π L hb hπ _ _ _ _ hM, pickNd_eq, semXIR_seq]
  obtain ⟨-, -, -, hM1, ho1, hz1⟩ := kindNd4_sem c π L hπ (st1 c π L) hM
  generalize semXIR (tp c π L) kindNd4 (st1 c π L) = s1 at hM1 ho1 hz1
  have hsz1 : memX4 + L.length + L.length ≤ s1.M.size := by rw [hz1, hsz0]; exact hlen
  have hW := decF04_wF κ c π L hD4 hps hS st₀ hfm hcap hfin hfar hA s1 hM1 hsz1
  have hB : BoundsOk (tp c π L) (extractorInput c π L).length (decF04 κ) s1 :=
    boundsOk_of_safe (safe_decF04 κ c π L hps hD.2.1 hD.2.2) (wf_decF04 κ) _ hM1
  have ho := outs_le (extractorInput c π L).length (decF04 κ) s1 (wf_decF04 κ) hM1 hB
  rw [outs_decF04, ho1, st1_o] at ho
  have hM2 := inv_sem (tp c π L) (wf_decF04 κ) hM1
  have hz2 := size_sem (tp c π L) (decF04 κ) s1
  generalize semXIR (tp c π L) (decF04 κ) s1 = s2 at hW ho hM2 hz2
  have ho2 : s2.o = #[] := by simpa using ho
  rw [outIR4_sem (tp c π L) κ hM2 (by rw [hz2, hz1, hsz0]; simp only [memX4, bufB]; omega) hW, ho2,
    Array.toList_empty, List.nil_append]

/-- **The revision 4.1 decode law** of `nd`: links `LinksD4`, witness `readW4 sigH`. -/
noncomputable def nodeDec4_nd : NodeDec4 nd :=
  ⟨LinksD4, readW4 sigH, fun _ _ _ _ _ hN hD hl => ⟨nd_out hN hD hl, readW4_fits _ _ _⟩⟩

/-! ## Controls -/

/-- (+) `nd` is a different branch from `ndNone` (it outputs on a node proof), and (−) its size is not
`ndNone`'s. -/
theorem nd_ne_ndNone : nd ≠ ndNone := fun h => by
  have := congrArg sizeIR h
  rw [nd, sizeIR_ndK4] at this
  exact Nat.add_one_ne_zero _ (Nat.add_eq_zero_iff.mp (Nat.add_right_cancel (m := 1) (k := 0) this)).2

end FR.X.X4

end G6_FRXNd4
