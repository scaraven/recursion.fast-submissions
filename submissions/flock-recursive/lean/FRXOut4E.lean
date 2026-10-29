-- New for `flock-recursive` (BLUEPRINT revision 4.1, §6.2 step 5; stage S-H4, pass 11, item 2: the
-- node output's emitters). 3.x analogue: `FRXOut`'s `.shw` case (shift 1 only, no loader).
import FRXOut4R

/-!
# The node output's emitters: shifted pairs, heap words

After the decode the output reads H's message words through the chain loader `ldC` (`FRXOut4R`):
the loader's word `n` is the heap word at `hAddr κ (ldIx cb jL Δ n)` (**`ldG`**). Here:

* **`shwC κ`**: `oX :=` the shifted pair `shWd (ldG …) s n` of the loader's words `n = qN`, `n + 1`
  (`8s` in `qA`, `63 − 8s` in `qB`): the realign loop's word, without the store (**`shwC_sem`**);
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
