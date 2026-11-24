-- lvm6 X4 (BLUEPRINT §3 step 2, X2 §4 item 2): one descent round as an extractor program: `lamIR` once,
-- then per lane a loader, `laneIR` and a copy of the decoded coefficients out of `outA` (X1 §5); its
-- semantics, exact cost, and the level cost against X2's `descLvl`. New.
import Lvm6XDesc
import Lvm6FDSem
import Lvm6XCost
import LvmXCopy
import LvmXDecCost

/-!
# One descent round on the machine

* `lanesIR N ℓ m B colB str ld n l`: lanes `l … l + n − 1`; lane `q` runs the loader `ld q` (it writes the
  lane's `K`-values at `yA`, `LoadOk`), `laneIR`, and copies `2^ℓ` words from `outA` to `colB + str·q`.
* `roundIR … = lamIR ; lanesIR … 0`: one fold round of the descent (`Λ` built once, X1 §5).
* **`roundIR_sem`**: lane `q`'s decoded word `fd1 N ℓ S (ys q)` is at `colB + str·q`, `Inv`, the output
  and the heap below `B`, in `[fdEnd, colB)` and above the copies are kept. **`roundIR_correct`**: with
  `OneErr` per lane (from `descend6`'s `oneErr_of_witness`, per `K`-component: `oneErr_coord`) the copies
  hold the novel-basis coefficients.
* **`cost_roundIR`**: `lamCost + Σ loaders + n·(laneCost + 19 + 13·2^ℓ) + 2`; **`cost_rounds_le`**: the
  decoder part of `rds` rounds with `Σ` lanes `≤ lns` is within X2's `descLvl` (`descCost6_mono`).
* The loaders (the level's word folded by the earlier challenges, at every position) are parameters with
  their specification `LoadOk` as a hypothesis.
-/

set_option autoImplicit false

namespace Lvm6.X

open RecursionFast Lvm.X Lvm.Nb Lvm6.FD Finset

/-! ## The programs -/

/-- Lanes `l … l + n − 1` of a round: loader, `laneIR`, copy of `outA` to `colB + str·q`. -/
def lanesIR (N ℓ m B colB str : ℕ) (ld : ℕ → XIR) : ℕ → ℕ → XIR
  | 0, _ => .blk []
  | n + 1, l => .seq (ld l) (.seq (laneIR N ℓ m B)
      (.seq (mcpIR (2 ^ ℓ) (outA B ℓ) 1 (colB + str * l)) (lanesIR N ℓ m B colB str ld n (l + 1))))

/-- **One descent round**: `Λ` once, then `n` lanes. -/
def roundIR (N ℓ m B colB str : ℕ) (ld : ℕ → XIR) (n : ℕ) : XIR :=
  .seq (lamIR N ℓ m B) (lanesIR N ℓ m B colB str ld n 0)

/-- **A lane loader**: writes the lane's values `y` at `yA` and no other heap word; keeps `Inv` and the
output. -/
def LoadOk (I : Array Word) (ld : XIR) (ℓ B : ℕ) (y : ℕ → BF64) : Prop :=
  ∀ s : St, Inv s.M → (∀ j < 2 ^ ℓ, rdK (semXIR I ld s).M (yA B ℓ + j) = y j) ∧
    Inv (semXIR I ld s).M ∧ (semXIR I ld s).o = s.o ∧
    ∀ x, regs ≤ x → (x < yA B ℓ ∨ yA B ℓ + 2 ^ ℓ ≤ x) → rd (semXIR I ld s).M x = rd s.M x

/-! ## Cost -/

theorem cost_lanesIR (N ℓ m B colB str t : ℕ) (ld : ℕ → XIR) (hN : ℓ + 1 ≤ N) (hN63 : N ≤ 63)
    (hm : m < 2 ^ 64) (hℓ : 2 ^ ℓ < 2 ^ 64) : ∀ n l, cost (lanesIR N ℓ m B colB str ld n l) t =
      (∑ i ∈ range n, cost (ld (l + i)) t) + n * (laneCost N ℓ m + 19 + 13 * 2 ^ ℓ) + 1
  | 0, _ => by simp [lanesIR, cost, blkSteps]
  | n + 1, l => by
    have ih := cost_lanesIR N ℓ m B colB str t ld hN hN63 hm hℓ n (l + 1)
    have hs : ∑ i ∈ range (n + 1), cost (ld (l + i)) t =
        (∑ i ∈ range n, cost (ld (l + 1 + i)) t) + cost (ld l) t := by
      rw [Finset.sum_range_succ']
      exact congrArg₂ _ (Finset.sum_congr rfl fun i _ ↦ by rw [show l + (i + 1) = l + 1 + i by omega]) rfl
    simp only [lanesIR, cost, ih, hs, (fd1_cost N ℓ m B t hN hN63 hm).2, cost_mcpIR _ _ _ _ t hℓ]
    ring

/-- **The cost of a round.** -/
theorem cost_roundIR (N ℓ m B colB str t : ℕ) (ld : ℕ → XIR) (n : ℕ) (hN : ℓ + 1 ≤ N) (hN63 : N ≤ 63)
    (hm : m < 2 ^ 64) (hℓ : 2 ^ ℓ < 2 ^ 64) : cost (roundIR N ℓ m B colB str ld n) t =
      lamCost N ℓ m + (∑ i ∈ range n, cost (ld i) t) + n * (laneCost N ℓ m + 19 + 13 * 2 ^ ℓ) + 2 := by
  simp only [roundIR, cost, (fd1_cost N ℓ m B t hN hN63 hm).1,
    cost_lanesIR N ℓ m B colB str t ld hN hN63 hm hℓ n 0, Nat.zero_add]
  ring

/-- The decoder part of a level's rounds: `ns` lists each round's lane count. -/
theorem sum_rounds (lam lane : ℕ) : ∀ ns : List ℕ,
    (ns.map fun n ↦ lam + n * lane).sum = ns.length * lam + ns.sum * lane
  | [] => by simp
  | n :: ns => by
    simp only [List.map_cons, List.sum_cons, List.length_cons, sum_rounds lam lane ns]
    ring

/-- **A level's decoder cost is within X2's `descLvl`**: at most `rds i` rounds, at most `lns i` lanes
in all, `|S| ≤ m'`. -/
theorem cost_rounds_le (i m m' : ℕ) (hmm : m ≤ m') (ns : List ℕ) (hr : ns.length ≤ rds i)
    (hl : ns.sum ≤ lns i) :
    (ns.map fun n ↦ lamCost (ht6 i + 1) (ht6 i) m + n * laneCost (ht6 i + 1) (ht6 i) m).sum ≤
      descLvl i m' := by
  rw [sum_rounds, descLvl]
  exact Nat.add_le_add (Nat.mul_le_mul hr (lamCost_mono hmm)) (Nat.mul_le_mul hl (laneCost_mono hmm))

/-! ## Semantics -/

/-- `LamOk` reads only `[tbA, yA)` and `[tA, fdEnd)`. -/
theorem lamOk_of_frame' {N ℓ B : ℕ} {S : List ℕ} {M M' : Mem} (hN64 : N ≤ 64) (hL : LamOk N ℓ B S M)
    (hf : ∀ x, regs ≤ x → x < fdEnd B ℓ → (x < yA B ℓ ∨ tA B ℓ ≤ x) → rd M' x = rd M x)
    (hB : regs ≤ B) (hm : S.length ≤ 2 ^ ℓ) : LamOk N ℓ B S M' := by
  obtain ⟨l1, l2, l3, l4⟩ := hL
  simp only [regs] at hB
  have hNN : N * N ≤ 4096 := by have := Nat.mul_le_mul hN64 hN64; simpa using this
  have hp : 2 ^ (ℓ + 1) = 2 * 2 ^ ℓ := by rw [pow_succ]; ring
  refine ⟨fun v hv i hi ↦ ?_, fun i hi ↦ ?_, fun i hi ↦ ?_, fun j hj ↦ ?_⟩
  · have : N * v + i < 4096 := by
      have := Nat.mul_le_mul_left N (show v + 1 ≤ N by omega); rw [Nat.mul_succ] at this; omega
    rw [← l1 v hv i hi]
    exact rdK_eq (hf _ (by simp only [regs, tbA]; omega) (by simp only [tbA, fdEnd]; omega)
      (Or.inl (by simp only [tbA, yA]; omega)))
  · rw [← l2 i hi]
    exact hf _ (by simp only [regs, sA]; omega) (by simp only [sA, fdEnd]; omega)
      (Or.inl (by simp only [sA, yA]; omega))
  · rw [← l3 i hi]
    exact rdK_eq (hf _ (by simp only [regs, tA]; omega) (by simp only [tA, fdEnd]; omega)
      (Or.inr (by simp only [tA]; omega)))
  · rw [← l4 j hj]
    exact rdK_eq (hf _ (by simp only [regs, iA]; omega) (by simp only [iA, fdEnd]; omega)
      (Or.inr (by simp only [tA, iA]; omega)))

theorem hasOut_mcpIR (n src str dst : ℕ) : hasOut (mcpIR n src str dst) = false := rfl

/-- **The lanes on the machine.** -/
theorem lanesIR_sem (I : Array Word) {N ℓ B colB str : ℕ} {S : List ℕ} (ld : ℕ → XIR)
    (ys : ℕ → ℕ → BF64) (hN : ℓ + 1 ≤ N) (hN64 : N ≤ 64) (hB : regs ≤ B) (hm : S.length ≤ 2 ^ ℓ)
    (hSn : ∀ j ∈ S, j < 2 ^ ℓ) (hcol : fdEnd B ℓ ≤ colB) (hstr : 2 ^ ℓ ≤ str) :
    ∀ (n l : ℕ) (s : St), Inv s.M → LamOk N ℓ B S s.M → colB + str * (l + n) < 2 ^ 64 →
      colB + str * (l + n) ≤ s.M.size → (∀ i < n, LoadOk I (ld (l + i)) ℓ B (ys (l + i))) →
      (∀ i < n, ∀ x < 2 ^ ℓ, rdK (semXIR I (lanesIR N ℓ S.length B colB str ld n l) s).M
          (colB + str * (l + i) + x) = fd1 N ℓ S (ys (l + i)) x) ∧
      Inv (semXIR I (lanesIR N ℓ S.length B colB str ld n l) s).M ∧
      (semXIR I (lanesIR N ℓ S.length B colB str ld n l) s).o = s.o ∧
      LamOk N ℓ B S (semXIR I (lanesIR N ℓ S.length B colB str ld n l) s).M ∧
      ∀ r, regs ≤ r → (r < B ∨ (fdEnd B ℓ ≤ r ∧ r < colB + str * l) ∨ colB + str * (l + n) ≤ r) →
        rd (semXIR I (lanesIR N ℓ S.length B colB str ld n l) s).M r = rd s.M r
  | 0, _, _, hM, hL, _, _, _ => ⟨fun _ hi ↦ absurd hi (Nat.not_lt_zero _), hM, rfl, hL, fun _ _ _ ↦ rfl⟩
  | n + 1, l, s, hM, hL, h64, hsz, hld => by
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
    obtain ⟨a1, a2, a3, a4⟩ := (by simpa using hld 0 (by omega) : LoadOk I (ld l) ℓ B (ys l)) s hM
    have z1 := size_sem I (ld l) s
    have L1 : LamOk N ℓ B S (semXIR I (ld l) s).M := lamOk_of_frame' hN64 hL
      (fun x hx _ hx' ↦ a4 x hx (by omega)) hB hm
    generalize semXIR I (ld l) s = s1 at a1 a2 a3 a4 z1 L1
    -- the lane
    obtain ⟨b1, b2, b3, b4⟩ := laneIR_sem I s1 a2 (y := ys l) hN hN64 hB (by omega) (by omega) hm hSn L1 a1
    have z2 := size_sem I (laneIR N ℓ S.length B) s1
    generalize semXIR I (laneIR N ℓ S.length B) s1 = s2 at b1 b2 b3 b4 z2
    -- the copy
    obtain ⟨c1, c2, c3⟩ := mcpIR_sem I s2 b2 (n := 2 ^ ℓ) (src := outA B ℓ) (str := 1)
      (dst := colB + str * l) (by omega) (by omega) (by norm_num) (by simp only [regs]; omega)
      (by omega) (by omega) (fun i hi ↦ Or.inl (by omega)) (fun i _ ↦ by simp only [regs]; omega)
    have c4 := sem_o I (mcpIR (2 ^ ℓ) (outA B ℓ) 1 (colB + str * l)) s2 (hasOut_mcpIR _ _ _ _)
    have z3 := size_sem I (mcpIR (2 ^ ℓ) (outA B ℓ) 1 (colB + str * l)) s2
    generalize semXIR I (mcpIR (2 ^ ℓ) (outA B ℓ) 1 (colB + str * l)) s2 = s3 at c1 c2 c3 c4 z3
    have L3 : LamOk N ℓ B S s3.M := lamOk_of_frame' hN64 L1 (fun x hx hxE hx' ↦ by
      rw [c2 x hx (Or.inl (by omega)), b4 x hx (by omega)]) hB hm
    -- the remaining lanes
    obtain ⟨d1, d2, d3, d4, d5⟩ := lanesIR_sem I ld ys hN hN64 hB hm hSn hcol hstr n (l + 1) s3 c3 L3
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

/-- **One descent round on the machine**: lane `q`'s decoded word is at `colB + str·q`. -/
theorem roundIR_sem (I : Array Word) (s : St) (hM : Inv s.M) {N ℓ B colB str n : ℕ} {S : List ℕ}
    (ld : ℕ → XIR) (ys : ℕ → ℕ → BF64) (hN : ℓ + 1 ≤ N) (hN64 : N ≤ 64) (hB : regs ≤ B)
    (hm : S.length ≤ 2 ^ ℓ) (hSn : ∀ j ∈ S, j < 2 ^ ℓ)
    (hS : ∀ i < S.length, rd s.M (sA B + i) = toWord (S.getD i 0)) (hcol : fdEnd B ℓ ≤ colB)
    (hstr : 2 ^ ℓ ≤ str) (h64 : colB + str * n < 2 ^ 64) (hsz : colB + str * n ≤ s.M.size)
    (hld : ∀ q < n, LoadOk I (ld q) ℓ B (ys q)) :
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
  generalize semXIR I (lamIR N ℓ S.length B) s = s1 at a1 a2 a3 a4 z1
  obtain ⟨d1, d2, d3, -, d5⟩ := lanesIR_sem I ld ys hN hN64 hB hm hSn hcol hstr n 0 s1 a2 a1
    (by simpa using h64) (by simpa [z1] using hsz) (fun i hi ↦ by simpa using hld i hi)
  refine ⟨fun q hq x hx ↦ by simpa using d1 q hq x hx, d2, d3.trans a3, fun r hr hr' ↦ ?_⟩
  rw [d5 r hr (by rw [Nat.mul_zero, Nat.add_zero, Nat.zero_add]; exact hr'), a4 r hr (by omega)]

/-- A `K`-component of an `F`-lane with one error on `S` has one error on `S`. -/
theorem oneErr_coord {F : Type} [Field F] [Algebra BF64 F] {ι : Type} [Fintype ι] (b : Module.Basis ι BF64 F)
    (i : ι) {ℓ k : ℕ} {S : List ℕ} {v : ℕ → F} {c : Fin k → F} (hnd : S.Nodup)
    (hlen : S.length = k + 2) (hS : ∀ j ∈ S, j < 2 ^ ℓ)
    (he : ∃ e, ∀ j ∈ S, j ≠ e → v j = encN ptK c j) :
    OneErr ℓ k S (fun j ↦ b.coord i (v j)) (fun x ↦ b.coord i (c x)) := by
  obtain ⟨e, he⟩ := he
  exact ⟨hnd, hlen, hS, e, fun j hj hje ↦ by
    show b.coord i (v j) = _
    rw [he j hj hje, encN_coord]⟩

/-- **The round decodes**: with one error per lane on `S`, the copies hold the coefficients. -/
theorem roundIR_correct (I : Array Word) (s : St) (hM : Inv s.M) {N ℓ k B colB str n : ℕ}
    {S : List ℕ} (ld : ℕ → XIR) (ys : ℕ → ℕ → BF64) (cs : ℕ → Fin k → BF64) (hN : ℓ + 1 ≤ N)
    (hN64 : N ≤ 64) (hB : regs ≤ B) (hone : ∀ q < n, OneErr ℓ k S (ys q) (cs q))
    (hS : ∀ i < S.length, rd s.M (sA B + i) = toWord (S.getD i 0)) (hcol : fdEnd B ℓ ≤ colB)
    (hstr : 2 ^ ℓ ≤ str) (h64 : colB + str * n < 2 ^ 64) (hsz : colB + str * n ≤ s.M.size)
    (hld : ∀ q < n, LoadOk I (ld q) ℓ B (ys q)) (h0 : 0 < n) :
    ∀ q < n, ∀ x < 2 ^ ℓ, rdK (semXIR I (roundIR N ℓ S.length B colB str ld n) s).M (colB + str * q + x) =
      if hx : x < k then cs q ⟨x, hx⟩ else 0 := by
  obtain ⟨hnd, hlen, hSn, -⟩ := hone 0 h0
  have hm : S.length ≤ 2 ^ ℓ := by
    rw [← List.toFinset_card_of_nodup hnd, ← Finset.card_range (2 ^ ℓ)]
    exact Finset.card_le_card fun j hj ↦ Finset.mem_range.2 (hSn j (by simpa using hj))
  intro q hq x hx
  rw [(roundIR_sem I s hM ld ys hN hN64 hB hm hSn hS hcol hstr h64 hsz hld).1 q hq x hx,
    fd1_correct hN hN64 (hone q hq) x hx]

end Lvm6.X
