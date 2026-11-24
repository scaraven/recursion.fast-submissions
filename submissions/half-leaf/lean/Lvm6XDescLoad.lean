-- lvm6 X6b (X4 §6 item 1): loaders that read the rows. X4's `LoadOk` fixes the lane's values for every state, which
-- a loader reading the heap cannot meet; `LoadOkB` takes them as a function of the heap below the scratch `B` (the
-- rows `read6IR` left), and the round's semantics is re-proved with it (`lanesIR_semB`, `roundIR_semB`,
-- `roundX_semB`). The loader of the round on the committed word (`ldRow`: one strided copy) meets it (`ldRow_ok`),
-- and its words are W1's `E2` lane components (`coord_laneVal`). New.
import Lvm6XDescProg
import Lvm6XDescW
import Lvm6WhirLanes

/-!
# Loaders from the rows

* **`LoadOkB I ld ℓ B M₀ y`**: from any state whose heap below `B` is `M₀`'s (and `fdEnd B ℓ` words), the loader
  writes `y` at `yA B ℓ` and no other heap word, keeps `Inv` and the output. `LoadOk → LoadOkB`.
* **`lanesIR_semB`**, **`roundIR_semB`**: X4's `lanesIR_sem`/`roundIR_sem` with `LoadOkB` (the round keeps the heap
  below `B`, so every lane's loader sees `M₀`). **`roundX_semB`**: after the agreement-set builder (`SbOk`).
* **`ldRow wB occ w B ℓ`** `= mcpIR (2^ℓ) (wB + w) occ (yA B ℓ)`: word `w` of every row (`read6IR`'s layout
  `wB + occ·p + w`). **`ldRow_ok`**: `LoadOkB … (fun p ↦ rdK M₀ (wB + occ·p + w))` when the rows lie below `B`.
* **`coord_laneVal`**: the `K`-components (`basisE2`) of W1's `E2` lane `s` of a row at levels `≥ 1` are the row's
  words `2s` and `2s + 1`: the round on the committed word loads lane `s`'s component `i` with `ldRow … (2s + i)`.
-/

set_option autoImplicit false

namespace Lvm6.X

open RecursionFast Lvm.X Lvm.Nb Lvm6.FD Finset

/-- **A loader reading the heap below `B`.** -/
def LoadOkB (I : Array Word) (ld : XIR) (ℓ B : ℕ) (M₀ : Mem) (y : ℕ → BF64) : Prop :=
  ∀ s : St, Inv s.M → fdEnd B ℓ ≤ s.M.size → (∀ x, regs ≤ x → x < B → rd s.M x = rd M₀ x) →
    (∀ j < 2 ^ ℓ, rdK (semXIR I ld s).M (yA B ℓ + j) = y j) ∧ Inv (semXIR I ld s).M ∧ (semXIR I ld s).o = s.o ∧
    ∀ x, regs ≤ x → (x < yA B ℓ ∨ yA B ℓ + 2 ^ ℓ ≤ x) → rd (semXIR I ld s).M x = rd s.M x

theorem LoadOk.loadOkB {I : Array Word} {ld : XIR} {ℓ B : ℕ} {y : ℕ → BF64} (h : LoadOk I ld ℓ B y) (M₀ : Mem) :
    LoadOkB I ld ℓ B M₀ y :=
  fun s hM _ _ ↦ h s hM

/-- **The lanes on the machine**, with loaders reading the heap below `B`. -/
theorem lanesIR_semB (I : Array Word) {N ℓ B colB str : ℕ} {S : List ℕ} (ld : ℕ → XIR) (M₀ : Mem)
    (ys : ℕ → ℕ → BF64) (hN : ℓ + 1 ≤ N) (hN64 : N ≤ 64) (hB : regs ≤ B) (hm : S.length ≤ 2 ^ ℓ)
    (hSn : ∀ j ∈ S, j < 2 ^ ℓ) (hcol : fdEnd B ℓ ≤ colB) (hstr : 2 ^ ℓ ≤ str) :
    ∀ (n l : ℕ) (s : St), Inv s.M → LamOk N ℓ B S s.M → (∀ x, regs ≤ x → x < B → rd s.M x = rd M₀ x) →
      colB + str * (l + n) < 2 ^ 64 →
      colB + str * (l + n) ≤ s.M.size → (∀ i < n, LoadOkB I (ld (l + i)) ℓ B M₀ (ys (l + i))) →
      (∀ i < n, ∀ x < 2 ^ ℓ, rdK (semXIR I (lanesIR N ℓ S.length B colB str ld n l) s).M
          (colB + str * (l + i) + x) = fd1 N ℓ S (ys (l + i)) x) ∧
      Inv (semXIR I (lanesIR N ℓ S.length B colB str ld n l) s).M ∧
      (semXIR I (lanesIR N ℓ S.length B colB str ld n l) s).o = s.o ∧
      LamOk N ℓ B S (semXIR I (lanesIR N ℓ S.length B colB str ld n l) s).M ∧
      ∀ r, regs ≤ r → (r < B ∨ (fdEnd B ℓ ≤ r ∧ r < colB + str * l) ∨ colB + str * (l + n) ≤ r) →
        rd (semXIR I (lanesIR N ℓ S.length B colB str ld n l) s).M r = rd s.M r
  | 0, _, _, hM, hL, _, _, _, _ => ⟨fun _ hi ↦ absurd hi (Nat.not_lt_zero _), hM, rfl, hL, fun _ _ _ ↦ rfl⟩
  | n + 1, l, s, hM, hL, h0, h64, hsz, hld => by
    have hB' : 256 ≤ B := hB
    have eY : yA B ℓ = B + 4096 + 2 ^ ℓ := rfl
    have eG : gA B ℓ = B + 4096 + 2 * 2 ^ ℓ := rfl
    have eO : outA B ℓ = B + 4096 + 3 * 2 ^ ℓ := rfl
    have eT : tA B ℓ = B + 4096 + 4 * 2 ^ ℓ := rfl
    have eE : fdEnd B ℓ = B + 4096 + 11 * 2 ^ ℓ := rfl
    have e1 : str * (l + 1) = str * l + str := by ring
    have e2 : str * (l + (n + 1)) = str * l + str + str * n := by ring
    have e3 : str * (l + 1 + n) = str * l + str + str * n := by ring
    rw [e2] at h64 hsz
    simp only [lanesIR, semXIR_seq]
    -- the loader
    obtain ⟨a1, a2, a3, a4⟩ := (by simpa using hld 0 (by omega) : LoadOkB I (ld l) ℓ B M₀ (ys l)) s hM
      (by omega) h0
    have z1 := size_sem I (ld l) s
    have L1 : LamOk N ℓ B S (semXIR I (ld l) s).M := lamOk_of_frame' hN64 hL
      (fun x hx _ hx' ↦ a4 x hx (by omega)) hB hm
    have h01 : ∀ x, regs ≤ x → x < B → rd (semXIR I (ld l) s).M x = rd M₀ x := fun x hx hxB ↦ by
      rw [a4 x hx (by omega), h0 x hx hxB]
    generalize semXIR I (ld l) s = s1 at a1 a2 a3 a4 z1 L1 h01
    -- the lane
    obtain ⟨b1, b2, b3, b4⟩ := laneIR_sem I s1 a2 (y := ys l) hN hN64 hB (by omega) (by omega) hm hSn L1 a1
    have z2 := size_sem I (laneIR N ℓ S.length B) s1
    have h02 : ∀ x, regs ≤ x → x < B → rd (semXIR I (laneIR N ℓ S.length B) s1).M x = rd M₀ x := fun x hx hxB ↦ by
      rw [b4 x hx (by omega), h01 x hx hxB]
    generalize semXIR I (laneIR N ℓ S.length B) s1 = s2 at b1 b2 b3 b4 z2 h02
    -- the copy
    obtain ⟨c1, c2, c3⟩ := mcpIR_sem I s2 b2 (n := 2 ^ ℓ) (src := outA B ℓ) (str := 1)
      (dst := colB + str * l) (by omega) (by omega) (by norm_num) (by simp only [regs]; omega)
      (by omega) (by omega) (fun i hi ↦ Or.inl (by omega)) (fun i _ ↦ by simp only [regs]; omega)
    have c4 := sem_o I (mcpIR (2 ^ ℓ) (outA B ℓ) 1 (colB + str * l)) s2 (hasOut_mcpIR _ _ _ _)
    have z3 := size_sem I (mcpIR (2 ^ ℓ) (outA B ℓ) 1 (colB + str * l)) s2
    have h03 : ∀ x, regs ≤ x → x < B →
        rd (semXIR I (mcpIR (2 ^ ℓ) (outA B ℓ) 1 (colB + str * l)) s2).M x = rd M₀ x := fun x hx hxB ↦ by
      rw [c2 x hx (Or.inl (by omega)), h02 x hx hxB]
    generalize semXIR I (mcpIR (2 ^ ℓ) (outA B ℓ) 1 (colB + str * l)) s2 = s3 at c1 c2 c3 c4 z3 h03
    have L3 : LamOk N ℓ B S s3.M := lamOk_of_frame' hN64 L1 (fun x hx hxE hx' ↦ by
      rw [c2 x hx (Or.inl (by omega)), b4 x hx (by omega)]) hB hm
    -- the remaining lanes
    obtain ⟨d1, d2, d3, d4, d5⟩ := lanesIR_semB I ld M₀ ys hN hN64 hB hm hSn hcol hstr n (l + 1) s3 c3 L3 h03
      (by rw [e3]; omega) (by rw [e3]; omega)
      (fun i hi ↦ by have := hld (i + 1) (by omega); rwa [show l + (i + 1) = l + 1 + i by omega] at this)
    refine ⟨fun i hi x hx ↦ ?_, d2, d3.trans (c4.trans (b3.trans a3)), d4, fun r hr hr' ↦ ?_⟩
    · rcases i with _ | i
      · simp only [Nat.add_zero]
        rw [← b1 x hx]
        refine rdK_eq ((d5 _ (by simp only [regs]; omega) (Or.inr (Or.inl ⟨by omega, by omega⟩))).trans ?_)
        rw [c1 x hx, Nat.one_mul]
      · have := d1 i (by omega) x hx
        rwa [show l + 1 + i = l + (i + 1) by omega] at this
    · rw [d5 r hr (by omega), c2 r hr (by omega), b4 r hr (by omega), a4 r hr (by omega)]

/-- **One descent round on the machine**, with loaders reading the heap below `B`. -/
theorem roundIR_semB (I : Array Word) (s : St) (hM : Inv s.M) {N ℓ B colB str n : ℕ} {S : List ℕ}
    (ld : ℕ → XIR) (M₀ : Mem) (ys : ℕ → ℕ → BF64) (hN : ℓ + 1 ≤ N) (hN64 : N ≤ 64) (hB : regs ≤ B)
    (hm : S.length ≤ 2 ^ ℓ) (hSn : ∀ j ∈ S, j < 2 ^ ℓ)
    (hS : ∀ i < S.length, rd s.M (sA B + i) = toWord (S.getD i 0)) (hcol : fdEnd B ℓ ≤ colB)
    (hstr : 2 ^ ℓ ≤ str) (h64 : colB + str * n < 2 ^ 64) (hsz : colB + str * n ≤ s.M.size)
    (h0 : ∀ x, regs ≤ x → x < B → rd s.M x = rd M₀ x) (hld : ∀ q < n, LoadOkB I (ld q) ℓ B M₀ (ys q)) :
    (∀ q < n, ∀ x < 2 ^ ℓ, rdK (semXIR I (roundIR N ℓ S.length B colB str ld n) s).M (colB + str * q + x) =
        fd1 N ℓ S (ys q) x) ∧
      Inv (semXIR I (roundIR N ℓ S.length B colB str ld n) s).M ∧
      (semXIR I (roundIR N ℓ S.length B colB str ld n) s).o = s.o ∧
      ∀ r, regs ≤ r → (r < B ∨ (fdEnd B ℓ ≤ r ∧ r < colB) ∨ colB + str * n ≤ r) →
        rd (semXIR I (roundIR N ℓ S.length B colB str ld n) s).M r = rd s.M r := by
  have hB' : 256 ≤ B := hB
  have eE : fdEnd B ℓ = B + 4096 + 11 * 2 ^ ℓ := rfl
  have eS : sA B = B + 4096 := rfl
  have eT : tA B ℓ = B + 4096 + 4 * 2 ^ ℓ := rfl
  rw [roundIR, semXIR_seq]
  obtain ⟨a1, a2, a3, a4⟩ := lamIR_sem I s hM hN hN64 hB (by omega) (by omega) hm hSn hS
  have z1 := size_sem I (lamIR N ℓ S.length B) s
  have h01 : ∀ x, regs ≤ x → x < B → rd (semXIR I (lamIR N ℓ S.length B) s).M x = rd M₀ x := fun x hx hxB ↦ by
    rw [a4 x hx (Or.inl hxB), h0 x hx hxB]
  generalize semXIR I (lamIR N ℓ S.length B) s = s1 at a1 a2 a3 a4 z1 h01
  obtain ⟨d1, d2, d3, -, d5⟩ := lanesIR_semB I ld M₀ ys hN hN64 hB hm hSn hcol hstr n 0 s1 a2 a1 h01
    (by simpa using h64) (by simpa [z1] using hsz) (fun i hi ↦ by simpa using hld i hi)
  refine ⟨fun q hq x hx ↦ by simpa using d1 q hq x hx, d2, d3.trans a3, fun r hr hr' ↦ ?_⟩
  rw [d5 r hr (by rw [Nat.mul_zero, Nat.add_zero, Nat.zero_add]; exact hr'), a4 r hr (by omega)]

/-- **A round of `descX6` on the machine**: the builder (`SbOk`), then `roundIR_semB`. -/
theorem roundX_semB (I : Array Word) (s : St) (hM : Inv s.M) {N ℓ B colB str : ℕ} {r : RoundX} {S : List ℕ}
    {Pre : St → Prop} (hP : Pre s) (hsb : SbOk I r.sb B S Pre) (hmS : S.length = r.m) (M₀ : Mem)
    (ys : ℕ → ℕ → BF64) (hN : ℓ + 1 ≤ N) (hN64 : N ≤ 64) (hB : regs ≤ B) (hm : S.length ≤ 2 ^ ℓ)
    (hSn : ∀ j ∈ S, j < 2 ^ ℓ) (hcol : fdEnd B ℓ ≤ colB) (hstr : 2 ^ ℓ ≤ str) (h64 : colB + str * r.n < 2 ^ 64)
    (hsz : colB + str * r.n ≤ s.M.size) (h0 : ∀ x, regs ≤ x → x < B → rd s.M x = rd M₀ x)
    (hld : ∀ q < r.n, LoadOkB I (r.ld q) ℓ B M₀ (ys q)) :
    (∀ q < r.n, ∀ x < 2 ^ ℓ, rdK (semXIR I (roundX N ℓ B colB str r) s).M (colB + str * q + x) =
        fd1 N ℓ S (ys q) x) ∧
      Inv (semXIR I (roundX N ℓ B colB str r) s).M ∧ (semXIR I (roundX N ℓ B colB str r) s).o = s.o ∧
      ∀ x, regs ≤ x → (x < B ∨ (fdEnd B ℓ ≤ x ∧ x < colB) ∨ colB + str * r.n ≤ x) →
        rd (semXIR I (roundX N ℓ B colB str r) s).M x = rd s.M x := by
  obtain ⟨a1, a2, a3, a4⟩ := hsb s hP hM
  have z1 := size_sem I r.sb s
  have eS : sA B = B + 4096 := rfl
  have eE : fdEnd B ℓ = B + 4096 + 11 * 2 ^ ℓ := rfl
  have h01 : ∀ x, regs ≤ x → x < B → rd (semXIR I r.sb s).M x = rd M₀ x := fun x hx hxB ↦ by
    rw [a4 x hx (Or.inl (by omega)), h0 x hx hxB]
  rw [roundX, semXIR_seq, ← hmS]
  generalize semXIR I r.sb s = s1 at a1 a2 a3 a4 z1 h01
  obtain ⟨b1, b2, b3, b4⟩ := roundIR_semB I s1 a2 r.ld M₀ ys hN hN64 hB hm hSn a1 hcol hstr h64
    (by rw [z1]; exact hsz) h01 hld
  refine ⟨b1, b2, b3.trans a3, fun x hx hx' ↦ ?_⟩
  rw [b4 x hx (by omega), a4 x hx (by omega)]

/-! ## The loader of the committed word -/

/-- **Word `w` of every row** to the lane's values (`read6IR`'s layout: row `p` at `wB + occ·p`). -/
def ldRow (wB occ w B ℓ : ℕ) : XIR := mcpIR (2 ^ ℓ) (wB + w) occ (yA B ℓ)

/-- **`ldRow` is a part within `ldCap`** at every deployed level (`16 + 13·2^ℓ ≤ 2^26` for `ℓ ≤ 21`). -/
theorem ldRow_part (wB occ w B : ℕ) {ℓ : ℕ} (hℓ : ℓ ≤ 21) : PartOk (ldRow wB occ w B ℓ) ldCap where
  wf := wf_mcpIR ..
  noLoopT := noLoopT_mcpIR ..
  outs t := outs_mcpIR _ _ _ _ t
  cost t := by
    have hp : 2 ^ ℓ ≤ 2 ^ 21 := Nat.pow_le_pow_right (by norm_num) hℓ
    rw [ldRow, cost_mcpIR _ _ _ _ t (lt_of_le_of_lt hp (by norm_num)), ldCap]
    omega

/-- **The loader of the committed word meets `LoadOkB`**: lane value `p` is word `w` of row `p` in `M₀`. -/
theorem ldRow_ok (I : Array Word) {wB occ w B ℓ : ℕ} (M₀ : Mem) (hwB : regs ≤ wB) (hw : w < occ)
    (hocc : occ ≤ 4096) (hrows : wB + occ * 2 ^ ℓ ≤ B) (h64 : fdEnd B ℓ < 2 ^ 64) :
    LoadOkB I (ldRow wB occ w B ℓ) ℓ B M₀ (fun p ↦ rdK M₀ (wB + occ * p + w)) := by
  intro s hM hsz h0
  have eY : yA B ℓ = B + 4096 + 2 ^ ℓ := rfl
  have eE : fdEnd B ℓ = B + 4096 + 11 * 2 ^ ℓ := rfl
  have hsrc : ∀ i < 2 ^ ℓ, wB + w + occ * i < B := fun i hi ↦ by
    have : occ * (i + 1) ≤ occ * 2 ^ ℓ := Nat.mul_le_mul_left occ hi
    rw [Nat.mul_succ] at this
    omega
  obtain ⟨c1, c2, c3⟩ := mcpIR_sem I s hM (n := 2 ^ ℓ) (src := wB + w) (str := occ) (dst := yA B ℓ)
    (by omega) (by omega) (by omega) (by simp only [regs] at hwB ⊢; omega) (by omega) (by omega)
    (fun i hi ↦ Or.inl (by have := hsrc i hi; omega)) (fun i _ ↦ by simp only [regs] at hwB ⊢; omega)
  refine ⟨fun j hj ↦ ?_, c3, sem_o I _ s (hasOut_mcpIR _ _ _ _), fun x hx hx' ↦ c2 x hx hx'⟩
  show rdK (semXIR I (mcpIR (2 ^ ℓ) (wB + w) occ (yA B ℓ)) s).M (yA B ℓ + j) = rdK M₀ (wB + occ * j + w)
  unfold rdK
  rw [c1 j hj, h0 _ (by simp only [regs] at hwB ⊢; omega) (hsrc j hj),
    show wB + w + occ * j = wB + occ * j + w by ring]

/-- **W1's `E2` lane `s` of a row (levels `≥ 1`) has `K`-components the row's words `2s`, `2s + 1`.** -/
theorem coord_laneVal (row : List BF64) (s : ℕ) :
    basisE2.coord 0 (Lvm6.Whir.laneVal false row s) = row.getD (2 * s) 0 ∧
      basisE2.coord 1 (Lvm6.Whir.laneVal false row s) = row.getD (2 * s + 1) 0 := by
  simp [basisE2, Lvm6.Whir.laneVal, Module.Basis.coord_apply]

end Lvm6.X
