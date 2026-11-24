-- lvm6 X8a (X7a's open item): a level's groups of rounds chained (`groupsX_sem`): group `k` starts at the level-wide
-- round `r` = the earlier groups' round count, its invariant and obligations are the level's at `r + j`; and a
-- level (`levelX_sem`): the transition, `rRd := 0`, the groups. New.
import Lvm6XDescLoop

/-!
# A level's groups on the machine

* **`GroupSem … sz g r`**: group `g`'s obligations when its first round is the level's round `r` (X7a's
  `groupX_sem` hypotheses at `Ss (r + j)`, `ys (r + j)`, `Q (r + j)`; the copies fit a heap of `sz` words).
  **`GroupsSem`**: every group of the list at its offset (`r`, then `r + nr`, …).
* **`groupsX_sem`**: the groups run in order; the level's invariant `Q` holds at round `r + Σ nr`, `rRd = r + Σ nr`,
  `Inv`, the output, the size and the heap below `B` kept.
* **`levelX_sem`**: `levelX i L` = `L.tr ; rRd := 0 ; groups`: from a transition whose end state satisfies `Q 0`
  (and keeps the heap below `B` equal to `M₀`), the level ends in `Q (Σ nr)`.
-/

set_option autoImplicit false

namespace Lvm6.X

open RecursionFast Lvm.X Lvm.Nb Lvm6.FD Finset

/-- **Group `g`'s obligations** as the level's rounds `r, …, r + nr − 1`, the copies within `sz` words. -/
structure GroupSem (I : Array Word) (N ℓ B colB str : ℕ) (M₀ : Mem) (Ss : ℕ → List ℕ)
    (ys : ℕ → ℕ → ℕ → BF64) (Q : ℕ → St → Prop) (sz : ℕ) (g : GroupX) (r : ℕ) : Prop where
  h64 : colB + str * g.n < 2 ^ 64
  hsz : colB + str * g.n ≤ sz
  hr64 : r + g.nr < 2 ^ 64
  hmS : ∀ j < g.nr, (Ss (r + j)).length = g.m
  hm : g.m ≤ 2 ^ ℓ
  hSn : ∀ j < g.nr, ∀ x ∈ Ss (r + j), x < 2 ^ ℓ
  hsw : WF g.sb
  hsl : AllBelow rRd g.sb
  hw : WF g.ld
  hl : AllBelow rRd g.ld
  hsb : ∀ j < g.nr, SbOkW I g.sb B ℓ (Ss (r + j)) (fun s ↦ Q (r + j) s ∧ rd s.M rRd = toWord (r + j))
  hld : ∀ j < g.nr, ∀ q < g.n,
    LoadOkB I (.seq (.blk [.const rRd (toWord (r + j)), .const rLn (toWord q)]) g.ld) ℓ B M₀ (ys (r + j) q)
  hstep : ∀ j < g.nr, ∀ s s', Q (r + j) s → RoundPost N ℓ B colB str g.n (Ss (r + j)) (ys (r + j)) s s' →
    Q (r + (j + 1)) s'

/-- **Every group's obligations**, group `k` starting at the round count of the groups before it. -/
def GroupsSem (I : Array Word) (N ℓ B colB str : ℕ) (M₀ : Mem) (Ss : ℕ → List ℕ) (ys : ℕ → ℕ → ℕ → BF64)
    (Q : ℕ → St → Prop) (sz : ℕ) : List GroupX → ℕ → Prop
  | [], _ => True
  | g :: gs, r => GroupSem I N ℓ B colB str M₀ Ss ys Q sz g r ∧ GroupsSem I N ℓ B colB str M₀ Ss ys Q sz gs (r + g.nr)

/-- **A level's groups on the machine**, chained: the invariant moves from round `r` to `r + Σ nr`. -/
theorem groupsX_sem (I : Array Word) {N ℓ B colB str : ℕ} (M₀ : Mem) (Ss : ℕ → List ℕ)
    (ys : ℕ → ℕ → ℕ → BF64) (Q : ℕ → St → Prop) (hN : ℓ + 1 ≤ N) (hN64 : N ≤ 64) (hB : regs ≤ B)
    (hcol : fdEnd B ℓ ≤ colB) (hstr : 2 ^ ℓ ≤ str) (hQ : ∀ j, HeapPred (Q j)) :
    ∀ (gs : List GroupX) (r : ℕ) (s : St), GroupsSem I N ℓ B colB str M₀ Ss ys Q s.M.size gs r → Inv s.M →
      Q r s → rd s.M rRd = toWord r → (∀ x, regs ≤ x → x < B → rd s.M x = rd M₀ x) →
      Q (r + (gs.map GroupX.nr).sum) (semXIR I (groupsX N ℓ B colB str gs) s) ∧
        Inv (semXIR I (groupsX N ℓ B colB str gs) s).M ∧ (semXIR I (groupsX N ℓ B colB str gs) s).o = s.o ∧
        (semXIR I (groupsX N ℓ B colB str gs) s).M.size = s.M.size ∧
        rd (semXIR I (groupsX N ℓ B colB str gs) s).M rRd = toWord (r + (gs.map GroupX.nr).sum) ∧
        ∀ x, regs ≤ x → x < B → rd (semXIR I (groupsX N ℓ B colB str gs) s).M x = rd M₀ x
  | [], r, s, _, hM, hQ0, hR, h0 => by
    simp only [List.map_nil, List.sum_nil, Nat.add_zero]
    exact ⟨hQ0, hM, rfl, rfl, hR, h0⟩
  | g :: gs, r, s, ⟨hg, hgs⟩, hM, hQ0, hR, h0 => by
    obtain ⟨a1, a2, a3, a4, a5, a6⟩ := groupX_sem I (N := N) (ℓ := ℓ) (B := B) (colB := colB) (str := str)
      (r0 := r) g M₀ (fun j ↦ Ss (r + j)) (fun j ↦ ys (r + j)) (fun j ↦ Q (r + j)) hN hN64 hB hcol hstr hg.h64
      hg.hr64 hg.hmS hg.hm hg.hSn hg.hsw hg.hsl hg.hw hg.hl (fun j ↦ hQ (r + j)) hg.hsb hg.hld hg.hstep s hM
      (by simpa only [Nat.add_zero] using hQ0) hR h0 hg.hsz
    rw [groupsX, semXIR_seq]
    generalize semXIR I (groupX N ℓ B colB str g) s = s1 at a1 a2 a3 a4 a5 a6
    obtain ⟨b1, b2, b3, b4, b5, b6⟩ := groupsX_sem I M₀ Ss ys Q hN hN64 hB hcol hstr hQ gs (r + g.nr) s1
      (by rw [a4]; exact hgs) a2 a1 a5 a6
    have e : r + g.nr + (gs.map GroupX.nr).sum = r + ((g :: gs).map GroupX.nr).sum := by
      simp only [List.map_cons, List.sum_cons]; omega
    rw [e] at b1 b5
    exact ⟨b1, b2, b3.trans a3, b4.trans a4, b5, b6⟩

/-- **A level on the machine**: the transition `L.tr`, then `rRd := 0`, then the groups; from a transition whose
end state satisfies `Q 0` with the heap below `B` equal to `M₀`, the level ends in `Q (Σ nr)`. -/
theorem levelX_sem (I : Array Word) (i : ℕ) (L : LevelX) (M₀ : Mem) (Ss : ℕ → List ℕ) (ys : ℕ → ℕ → ℕ → BF64)
    (Q : ℕ → St → Prop) (hN64 : ht6 i + 1 ≤ 64) (hB : regs ≤ L.B) (hcol : fdEnd L.B (ht6 i) ≤ L.colB)
    (hstr : 2 ^ ht6 i ≤ L.str) (hQ : ∀ j, HeapPred (Q j)) (s : St)
    (htr : Inv (semXIR I L.tr s).M ∧ Q 0 (semXIR I L.tr s) ∧
      (∀ x, regs ≤ x → x < L.B → rd (semXIR I L.tr s).M x = rd M₀ x))
    (hgs : GroupsSem I (ht6 i + 1) (ht6 i) L.B L.colB L.str M₀ Ss ys Q (semXIR I L.tr s).M.size L.gs 0) :
    Q (L.gs.map GroupX.nr).sum (semXIR I (levelX i L) s) ∧ Inv (semXIR I (levelX i L) s).M ∧
      (semXIR I (levelX i L) s).o = (semXIR I L.tr s).o ∧
      ∀ x, regs ≤ x → x < L.B → rd (semXIR I (levelX i L) s).M x = rd M₀ x := by
  obtain ⟨t1, t2, t3⟩ := htr
  rw [levelX, semXIR_seq, semXIR_seq]
  generalize semXIR I L.tr s = s1 at t1 t2 t3 hgs
  have hs := t1.1
  simp only [regs] at hs
  have w0 : WF (.blk [.const rRd 0]) := by simp +decide [WF, Prim.dst, rRd]
  have hM0 := inv_sem I w0 t1
  have z0 := size_sem I (.blk [.const rRd 0]) s1
  have v0 : rd (semXIR I (.blk [.const rRd 0]) s1).M rRd = toWord 0 := by
    rw [sem_blk']; simp only [runPrims, List.foldl, Prim.run]
    rw [rd_set_self (by simp only [rRd]; omega)]; rfl
  have k0 : ∀ x, regs ≤ x → rd (semXIR I (.blk [.const rRd 0]) s1).M x = rd s1.M x := fun x hx ↦
    rd_blk_of_not_dst I _ s1 (by simp only [List.mem_singleton, forall_eq, Prim.dst]; exact
      (ne_of_regs hx (by decide)).symm)
  have q0 : Q 0 (semXIR I (.blk [.const rRd 0]) s1) := hQ 0 s1 _ z0 rfl k0 t2
  have o0 : (semXIR I (.blk [.const rRd 0]) s1).o = s1.o := rfl
  generalize semXIR I (.blk [.const rRd 0]) s1 = s2 at hM0 z0 v0 k0 q0 o0
  obtain ⟨b1, b2, b3, -, -, b6⟩ := groupsX_sem I M₀ Ss ys Q (Nat.le_refl _) hN64 hB hcol hstr hQ L.gs 0 s2
    (by rw [z0]; exact hgs) hM0 q0 v0 (fun x hx hxB ↦ by rw [k0 x hx, t3 x hx hxB])
  rw [Nat.zero_add] at b1
  exact ⟨b1, b2, b3.trans o0, b6⟩

end Lvm6.X
