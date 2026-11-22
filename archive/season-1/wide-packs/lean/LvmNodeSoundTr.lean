-- WP-14c (NodeSound, O10). New for lvm: WP-13a's trace reader (`readTraceL`, lanes) is WP-11b-QL's
-- (`decode`, bytes at the plan's lengths) on the child's stream lanes (`TrBridge`).
import LvmNodeSoundLeft

-- (GOLF2: 5 declarations that `certified` does not use moved verbatim to `LvmNodeSoundTOff`, outside its import closure.)

/-!
# The trace bridge

`decode P20 (wsOf W)` reads entries off the bytes of the lanes `wsOf W` at the plan's query lengths
(`lens P20 = 7 :: lensL`, XA's `ra_plan_chk`); `readTraceL W` reads them lane by lane along
`walk 6 lensL`. Entry `0` (`q₀`) sits at byte `1` (its query bytes `9 … 15`, answer lanes `2 … 5`);
every later entry starts on a lane (lengths `≡ 0 mod 8`), and the walk ends inside the `17·2^14`
lanes (`walkEnd_le`, from the plan's `Σ (40 + len)`). **`trBridge`**.
-/

set_option autoImplicit false

namespace Lvm.NS

open RecursionFast Lvm Lvm.Replay Lvm.QLink

/-- The number of stream lanes. -/
abbrev nLanes : ℕ := 17 * 2 ^ 14

theorem wsOf_slice (W : ℕ → Word) {a n : ℕ} (h : a + n ≤ nLanes) :
    ((wsOf W).drop a).take n = Lvm.X.wsAt W a n := by
  have h' : a + n ≤ 278528 := h
  refine List.ext_getElem (by simp [wsOf, Lvm.X.wsAt]; (clear * - h'; omega)) fun i h1 h2 => ?_
  simp [wsOf, Lvm.X.wsAt]

theorem bytes_slice (W : ℕ → Word) {a n : ℕ} (h : a + n ≤ nLanes) :
    ((wordsBytes (wsOf W)).drop (8 * a)).take (8 * n) = wordsBytes (Lvm.X.wsAt W a n) := by
  rw [wordsBytes_slice, wsOf_slice W h]

theorem getD_bytes (W : ℕ → Word) {a i : ℕ} (hi : i < 32) (h : a + 4 ≤ nLanes) :
    (wordsBytes (wsOf W)).getD (8 * a + i) 0 = (wordsBytes (Lvm.X.wsAt W a 4)).getD i 0 := by
  rw [← bytes_slice W h]
  simp only [List.getD_eq_getElem?_getD, List.getElem?_take, List.getElem?_drop,
    show i < 8 * 4 from by (clear * - hi; omega), ite_true]

/-- **A lane-aligned entry** read off the bytes is the lane reader's. -/
theorem entryAt_eq (W : ℕ → Word) {u len : ℕ} (h8 : len % 8 = 0) (hr : u + 1 + len / 8 + 4 ≤ nLanes) :
    entryAt (wordsBytes (wsOf W)) (8 * u) len = Lvm.X.entAt W u len := by
  have hdv : 8 * (len / 8) = len := Nat.mul_div_cancel' (Nat.dvd_of_mod_eq_zero h8)
  have hq := bytes_slice W (a := u + 1) (n := len / 8) (by (clear * - hr; omega))
  rw [hdv, show 8 * (u + 1) = 8 * u + 8 by ring] at hq
  unfold entryAt Lvm.X.entAt
  refine Prod.ext ?_ ?_
  · show (⟨((wordsBytes (wsOf W)).drop (8 * u + 8)).take len |>.toArray⟩ : ByteArray) = Lvm.X.bArr _
    rw [hq]; rfl
  · simp only [Lvm.X.digW]
    refine Vector.ext fun i hi => ?_
    simp only [Vector.getElem_ofFn]
    rw [show 8 * u + 8 + len + i = 8 * (u + 1 + len / 8) + i by (clear * - h8; omega)]
    exact getD_bytes W hi (by (clear * - hr; omega))

/-- The entries along a walk. -/
theorem readEntries_walk (W : ℕ → Word) : ∀ (l : List ℕ) (u : ℕ), (∀ len ∈ l, len % 8 = 0) →
    u + (l.map fun len => 5 + len / 8).sum ≤ nLanes →
    readEntries (wordsBytes (wsOf W)) (8 * u) l = (Lvm.X.walk u l).map fun x => Lvm.X.entAt W x.1 x.2
  | [], _, _, _ => rfl
  | len :: r, u, h8, hN => by
    have h0 := h8 len (by simp)
    simp only [List.map_cons, List.sum_cons] at hN
    simp only [readEntries, Lvm.X.walk, List.map_cons]
    rw [entryAt_eq W h0 (by (clear * - hN; omega))]
    congr 1
    rw [show 8 * u + 40 + len = 8 * (u + 5 + len / 8) by (clear * - h0; omega)]
    exact readEntries_walk W r _ (fun l hl => h8 l (by simp [hl])) (by (clear * - hN; omega))

/-- `q₀`'s entry. -/
theorem entryAt_q0 (W : ℕ → Word) : entryAt (wordsBytes (wsOf W)) 1 7 = Lvm.X.q0Ent W := by
  unfold entryAt Lvm.X.q0Ent
  refine Prod.ext ?_ ?_
  · have h1 := bytes_slice W (a := 1) (n := 1) (by norm_num)
    have hw : wordsBytes (Lvm.X.wsAt W 1 1) = wordBytes (W 1) := by
      simp [Lvm.X.wsAt, wordsBytes]
    rw [hw] at h1
    show (⟨((wordsBytes (wsOf W)).drop (1 + 8)).take 7 |>.toArray⟩ : ByteArray) = Lvm.X.bArr _
    rw [← h1, List.drop_take, show 1 + 8 = 8 * 1 + 1 by rfl, List.drop_drop]
    rfl
  · simp only [Lvm.X.digW]
    refine Vector.ext fun i hi => ?_
    simp only [Vector.getElem_ofFn]
    rw [show 1 + 8 + 7 + i = 8 * 2 + i by (clear * -; first | decide | (simp only [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]; done) | ring1 | omega)]
    exact getD_bytes W hi (by norm_num)

end Lvm.NS
