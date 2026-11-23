-- New for lvm2 MP-B (cap pruning, stage S2GB): Q_link's soundness at S2GB (`qlinkB`).
import LvmQCapLink

/-!
# Q_link at S2GB is sound

`open_factsB` (`open_facts`' twin on `openLoopsB`): per position the leaf's length lane is the row length, the path's
top is half `x % 2` of heap-bottom slot `2^(m−1) + x / 2` (`x` the `m` cap bits), and the path's node checks hold;
the heap's slots `2^c ≤ k < 2^(m−1)` take their children's answers, the children's length lanes are 64; and slots
`2^c + i` hold the sent cap's nodes.
-/

set_option autoImplicit false

namespace Lvm.QLink

open RecursionFast Lvm Lvm.Replay Lvm.Loop Lvm.Loop.Build

section
variable {p : Params} {lay : Layout} {ws : List Word} {c : Ctx} {M : Mem}

/-! Pure index arithmetic of the opening and heap facts below, on free variables (small `omega` contexts: each
`omega` call re-proves its whole context in the kernel). -/
private theorem hx_hn {s hL a b M N : Nat} (h1 : a ≤ b) (h2 : hL + 13 * b ≤ M) (h3 : s + M ≤ N) :
    s + hL + 13 * a ≤ N := by omega
private theorem hx_c1 {c m : Nat} (h : c < m) : m = m - 1 + 1 := by omega
private theorem hx_idx {A C n ks : Nat} (hn : n < A - C) (hks : A - 1 - n = ks) :
    n + ks + 1 = A ∧ C ≤ ks ∧ n < A := by omega
private theorem hx_sub {A kk nn : Nat} (h : nn + kk + 1 = A) : A - 1 - kk = nn := by omega
private theorem hx_le {A C kk nn : Nat} (h : nn + kk + 1 = A) (hC : C ≤ kk) : nn < A - C ∧ nn < A := by omega
private theorem hx_kids {A H ks : Nat} (hA : A = 2 * H) (hk : ks < H) :
    A - 1 - 2 * ks + 2 * ks + 1 = A ∧ A - 1 - (2 * ks + 1) + (2 * ks + 1) + 1 = A := by omega
private theorem hx_half {ks C : Nat} (h : C ≤ ks) : C ≤ 2 * ks ∧ C ≤ 2 * ks + 1 := by omega
private theorem hx_bot {H ks b : Nat} (hH : H ≤ ks) (hb : b < 2) :
    (2 * (ks - H) + b) / 2 = ks - H ∧ (2 * (ks - H) + b) % 2 = b ∧ H + (ks - H) = ks := by omega
private theorem hx_cap {C ks : Nat} (h1 : C ≤ ks) (h2 : ks < 2 * C) : ks - C < C ∧ C + (ks - C) = ks := by omega
private theorem hx_len {C ks A n H : Nat} (hA : A = 2 * H) (hnk : n + ks + 1 = A) (h1 : C ≤ ks) (h2 : ¬ ks < 2 * C) :
    C ≤ ks / 2 ∧ ks / 2 < H := by omega
private theorem hx_par (ks : Nat) : 2 * (ks / 2) = ks ∨ 2 * (ks / 2) + 1 = ks := by omega
private theorem hx_add_lt {z m P h : Nat} (hz : z < m) (hc : m + P = h) : P + z < h := by omega
private theorem hx_jx {j t P : Nat} (hj : j < t) : j * (1 + P) + P < t * (1 + P) :=
  Nat.lt_of_lt_of_le (by rw [Nat.succ_mul]; omega) (Nat.mul_le_mul_right _ hj)
private theorem hx_lt1 (P : Nat) : P < 1 + P := by omega
private theorem hx_pos' {i0 X n : Nat} (h2 : 2 ≤ i0) : 1 ≤ i0 + X + n := by omega
private theorem hx_len' {i0 X A C L : Nat} (h : i0 + (X + (A - C)) ≤ L) (hC : 2 * C ≤ A) : i0 + X + A ≤ L + C := by
  omega
private theorem hx_plen {i0 y z X A C L : Nat} (h : y + z < X) (hl : i0 + X + A ≤ L + C) (hC : 2 * C ≤ A) :
    i0 + y + z < L := by omega
private theorem hx_tail {E Lh M l : Nat} (h1 : E + 5 + 64 / 8 ≤ Lh) (h2 : Lh + 17 ≤ M) (hl : l < 4) : E + 9 + l < M := by
  omega
private theorem hx_slot0 {E hL x A M : Nat} (hE : E = hL + 13 * x) (hx : x < A) (hH : hL + 13 * A ≤ M) : E < M := by
  omega
private theorem hx_slot1 {E hL x A M l : Nat} (hE : E = hL + 13 * x) (hx : x < A) (hH : hL + 13 * A ≤ M) (hl : l < 4) :
    E + 1 + l < M := by omega
private theorem hx_slot5 {E hL x A M l : Nat} (hE : E = hL + 13 * x) (hx : x < A) (hH : hL + 13 * A ≤ M) (hl : l < 4) :
    E + 5 + l < M := by omega
private theorem hx_slot9 {E hL x A M l : Nat} (hE : E = hL + 13 * x) (hx : x < A) (hH : hL + 13 * A ≤ M) (hl : l < 4) :
    E + 9 + l < M := by omega
private theorem hx_slotB {E hL x A M b l : Nat} (hE : E = hL + 13 * x) (hx : x < A) (hH : hL + 13 * A ≤ M) (hb : b < 2)
    (hl : l < 4) : E + 1 + 4 * b + l < M := by omega
private theorem hx_capb {X C v l M : Nat} (h : X + 4 * C ≤ M) (hv : v < C) (hl : l < 4) : X + 4 * v + l < M := by omega
private theorem hx_re4 (a E b l : Nat) : a + (E + 1 + 4 * b + l) = a + (E + (1 + 4 * b + l)) := by
  simp only [Nat.add_assoc]
private theorem hx_ylt {y P : Nat} (h : y < 1 + P) : y ≤ P := by omega
private theorem hx_ym1 {y P : Nat} (hy : y < 1 + P) (h0 : y ≠ 0) : y - 1 < P := by omega
private theorem hx_lt0 {E X Lh M : Nat} (h1 : E + 5 + X ≤ Lh) (h2 : Lh + 17 ≤ M) : E < M := by omega
private theorem hx_13 {E Lh : Nat} (h : E + 5 + 64 / 8 ≤ Lh) : E + 13 ≤ Lh := by omega
private theorem hx_ed {E Lh M l d : Nat} (h1 : E + 13 ≤ Lh) (h2 : Lh + 17 ≤ M) (hl : l < 4) (hd : d ≤ 9) :
    E + d + l < M := by omega
private theorem hx_em4 {E Lh M l : Nat} (h1 : E + 13 ≤ Lh) (h2 : Lh + 17 ≤ M) (hl : l < 4) : E - 4 + l < M := by omega
private theorem hx_rm4 {s E a b c l : Nat} (hE : E = a + b + c) (h5 : 5 ≤ c) :
    s + (E - 4 + l) = s + a + b + c - 4 + l := by omega
private theorem hx_rp {s E a b c d l : Nat} (hE : E = a + b + c) : s + (E + d + l) = s + a + b + c + d + l := by omega
private theorem hx_gate {zo K rc jj : Nat} (h1 : rc ≤ K) (h2 : jj < rc) :
    zo + K - rc + jj = zo + (K - rc + jj) ∧ K - rc + jj < K := by omega
private theorem hx_add_lt' {y P h : Nat} (hy : y < h - P) : P + y < h := by omega
private theorem hx_re6 {B hc hj hd P y : Nat} (e : hj = hc + hd) : B + hc + P + y + hd = B + hj + (P + y) := by omega
private theorem hx_re7 {s e a b c : Nat} (h : c = a + b) : s + e + a + b = s + e + c := by omega
private theorem hx_re8 {B hc hj hd P y : Nat} (e : hj = hc + hd) : B + hc + P + y + (hd + 0) = B + hj + P + y + 0 := by
  omega
private theorem hx_re9 {s e a b c d l : Nat} (h : c = a + b) : s + e + a + d + 9 + l + b = s + e + c + d + 9 + l := by
  omega
private theorem hx_jf {a D x X : Nat} (ha : a < D) (hx : x < X) : a + D * x < D * X := by
  have : D * (x + 1) ≤ D * X := Nat.mul_le_mul_left _ hx
  rw [Nat.mul_succ] at this; omega
private theorem hx_sublt {a b D : Nat} (h1 : b ≤ a) (h2 : a < b + D) : a - b < D := by omega
private theorem hx_re10 {B hc hj hd d lvl : Nat} (e : hj = hc + hd) (h : d ≤ lvl) :
    B + hc + d + (lvl - d + hd) = B + hj + lvl := by omega
private theorem hx_re12 {B hc hj hd d lvl : Nat} (e : hj = hc + hd) (h : d ≤ lvl) :
    B + hc + d + (1 * (lvl - d) + hd) = B + hj + lvl := by omega
private theorem hx_sl {r d l : Nat} (h : d ≤ l) : r + 13 * d + 13 * (l - d) = r + 13 * l := by omega
private theorem hx_re11 {s e a b c u v w : Nat} (h1 : c = a + b) (h2 : u + v = w) : s + e + a + u + (v + b) = s + e + c + w := by
  omega
private theorem hx_re13 {s e a b c u v w l : Nat} (h1 : c = a + b) (h2 : u + v = w) (h4 : 5 ≤ u) :
    s + e + a + u - 4 + l + (v + b) = s + e + c + w - 4 + l := by omega
private theorem hx_re14 {s e a b c u v w d l : Nat} (h1 : c = a + b) (h2 : u + v = w) :
    s + e + a + u + d + l + (v + b) = s + e + c + w + d + l := by omega
private theorem hx_hz {zo K W C kk : Nat} (hK : W - C ≤ K) (h1 : C ≤ kk) (h2 : kk < W) :
    zo + K - (W - C) + (W - 1 - kk) = zo + (K - (W - C) + (W - 1 - kk)) ∧ K - (W - C) + (W - 1 - kk) < K := by omega

/-- **One opening's checks at S2GB** (`openLoopsB`), from the step array's ones and the Boolean position bits. -/
theorem open_factsB (hin : QIn p lay ws M) {N : Nat} (hinj : GInj N) (hN : c.cells .K ≤ N)
    {zo : Nat} (hz : ∀ x < 2 ^ lay.K, M.k (zo + x) = 1)
    {k : Nat} (hk : k < (opens p).length) {o : OpenInfo} (hko : (opens p).getD k default = o)
    (hph : o.L.path < o.L.height) (hK : ∀ cc ∈ pchunks o.L.t, cc.2 ≤ lay.K)
    (hcm : p.capSendBits o.L.level o.L.cap < o.L.height - o.L.path)
    (hcK : 2 ^ (o.L.height - o.L.path - 1) - 2 ^ p.capSendBits o.L.level o.L.cap ≤ 2 ^ lay.K)
    (hHN : lay.sb + heapLane p o + 13 * 2 ^ (o.L.height - o.L.path - 1) ≤ N)
    {q : Ptr} (h : SegsHold c M q (openLoopsB p lay zo (bitBase p lay k) o q).2)
    (hA : SegsAssert M q (openLoopsB p lay zo (bitBase p lay k) o q).2) :
    (∀ j < o.L.t,
      M.k (lay.sb + eLane p o.i0 + posStride o.L * j) = kOf o.L.row ∧
      (∀ l < 4, M.k ((lay.sb + eLane p o.i0 + posStride o.L * j) + slotOff o.L o.L.path + 9 + l) =
        M.k (hcell (lay.sb + heapLane p o) (o.L.height - o.L.path)
          (2 ^ (o.L.height - o.L.path - 1) +
            bitSum M (bitBase p lay k + o.L.height * j + o.L.path) [] [] (o.L.height - o.L.path) / 2)
          (1 + 4 * (bitSum M (bitBase p lay k + o.L.height * j + o.L.path) [] [] (o.L.height - o.L.path) % 2) + l))) ∧
      (∀ lvl < o.L.path, M.k ((lay.sb + eLane p o.i0 + posStride o.L * j) + slotOff o.L (lvl + 1)) = kOf 64 ∧
        ∀ l < 4, M.k ((lay.sb + eLane p o.i0 + posStride o.L * j) + slotOff o.L (lvl + 1) - 4 + l) =
          if M.k (bitBase p lay k + o.L.height * j + lvl) = 1
          then M.k ((lay.sb + eLane p o.i0 + posStride o.L * j) + slotOff o.L (lvl + 1) + 5 + l)
          else M.k ((lay.sb + eLane p o.i0 + posStride o.L * j) + slotOff o.L (lvl + 1) + 1 + l))) ∧
    (∀ kk, 2 ^ p.capSendBits o.L.level o.L.cap ≤ kk → kk < 2 ^ (o.L.height - o.L.path - 1) →
      (∀ l < 4, M.k (hcell (lay.sb + heapLane p o) (o.L.height - o.L.path) kk (1 + l)) =
          M.k (hcell (lay.sb + heapLane p o) (o.L.height - o.L.path) (2 * kk) (9 + l)) ∧
        M.k (hcell (lay.sb + heapLane p o) (o.L.height - o.L.path) kk (5 + l)) =
          M.k (hcell (lay.sb + heapLane p o) (o.L.height - o.L.path) (2 * kk + 1) (9 + l))) ∧
      M.k (hcell (lay.sb + heapLane p o) (o.L.height - o.L.path) (2 * kk) 0) = kOf 64 ∧
      M.k (hcell (lay.sb + heapLane p o) (o.L.height - o.L.path) (2 * kk + 1) 0) = kOf 64) ∧
    (∀ i < 2 ^ p.capSendBits o.L.level o.L.cap,
      M.k (hcell (lay.sb + heapLane p o) (o.L.height - o.L.path) (2 ^ p.capSendBits o.L.level o.L.cap + i) 0) =
        kOf 64 ∧
      ∀ l < 4, M.k (hcell (lay.sb + heapLane p o) (o.L.height - o.L.path) (2 ^ p.capSendBits o.L.level o.L.cap + i)
        (9 + l)) = M.k (lay.sb + (eLane p o.ce + 1 + o.co / 8) + 4 * i + l)) := by
  have hbit : ∀ j' < o.L.t, ∀ z < o.L.height, M.k (bitBase p lay k + o.L.height * j' + z) = 0 ∨
      M.k (bitBase p lay k + o.L.height * j' + z) = 1 := by
    intro j' hj' z hz'
    have := hin.bits k hk j' (by rw [hko]; exact hj') z (by rw [hko]; exact hz')
    rw [hko] at this
    rw [this]; split <;> simp
  simp only [openLoopsB] at h hA
  rw [hold_bind] at h; rw [assert_bind] at hA
  have hrest := h.2; have hArest := hA.2
  rw [hold_bind] at hrest; rw [assert_bind] at hArest
  have hm1 : 1 ≤ o.L.height - o.L.path := Nat.sub_pos_of_lt hph
  refine ⟨fun j hj => ?_, fun kk hk1 hk2 => ?_, ?_⟩
  · obtain ⟨cc, hcc, hc1, hc2, hc3⟩ := pchunks_cover hj
    obtain ⟨q1, h1, hA1⟩ := seqAll_both _ _ h.1 hA.1 _ (List.mem_map_of_mem hcc)
    rw [hold_bind] at h1; rw [assert_bind] at hA1
    have hgate : ∀ jj, jj < realCount o.L.t cc.1 cc.2 →
        M.k (zo + 2 ^ lay.K - realCount o.L.t cc.1 cc.2 + jj) = 1 := by
      intro jj hjj
      have hKc : 2 ^ cc.2 ≤ 2 ^ lay.K := Nat.pow_le_pow_right (by decide) (hK cc hcc)
      obtain ⟨g1, g2⟩ := hx_gate (zo := zo) (Nat.le_trans (realCount_le o.L.t cc.1 cc.2) hKc) hjj
      rw [g1]
      exact hz _ g2
    have hjs : j = cc.1 + (j - cc.1) := (Nat.add_sub_cancel' hc1).symm
    have hHj : o.L.height * j = o.L.height * cc.1 + o.L.height * (j - cc.1) := by
      rw [← Nat.mul_add, ← hjs]
    have hSj : posStride o.L * j = posStride o.L * cc.1 + posStride o.L * (j - cc.1) := by
      rw [← Nat.mul_add, ← hjs]
    -- the layer loop
    have hc' := layerLoop_spec h1.1 hA1.1 (jf := j - cc.1) (by simpa using hc3) hm1
      (by simp only [unflat_one' (show j - cc.1 < 2 ^ [cc.2].sum by simpa using hc3), Loop.dot, Nat.add_zero,
            Nat.one_mul]
          exact hgate _ hc2)
      (fun y hy => by
        simp only [unflat_one' (show j - cc.1 < 2 ^ [cc.2].sum by simpa using hc3), Loop.dot, Nat.add_zero]
        have := hbit j hj (o.L.path + y) (hx_add_lt' hy)
        rwa [hx_re6 hHj])
      hinj hN hHN
    simp only [unflat_one' (show j - cc.1 < 2 ^ [cc.2].sum by simpa using hc3), Loop.dot, Nat.add_zero] at hc'
    have hbase : lay.sb + eLane p o.i0 + posStride o.L * cc.1 + posStride o.L * (j - cc.1) =
        (lay.sb + eLane p o.i0 + posStride o.L * j) := hx_re7 hSj
    have hbs := bitSum_congr M (bitBase p lay k + o.L.height * cc.1 + o.L.path)
      (bitBase p lay k + o.L.height * j + o.L.path) [o.L.height] [] [j - cc.1] []
      (o.L.height - o.L.path) (fun y _ => by simp only [Loop.dot]; exact hx_re8 hHj)
    refine ⟨?_, fun l hl => ?_, fun lvl hlvl => ?_⟩
    · rw [← hbase]; exact hc'.1
    · have := hc'.2 l hl
      rw [hx_re9 hSj] at this
      rw [this, hbs]
    · -- the node loop of the level chunk holding lvl
      obtain ⟨dd, hdd, hd1, hd2⟩ := chunks_cover hlvl
      have h1s := h1.2; have hA1s := hA1.2
      rw [hold_bind] at h1s; rw [assert_bind] at hA1s
      obtain ⟨q2, h2, hA2⟩ := seqAll_both _ _ h1s.1 hA1s.1 _ (List.mem_map_of_mem hdd)
      have hdl := hx_sublt hd1 hd2
      have hjf : lvl - dd.1 + 2 ^ dd.2 * (j - cc.1) < 2 ^ [dd.2, cc.2].sum := by
        simp only [List.sum_cons, List.sum_nil, Nat.add_zero, Nat.pow_add]
        exact hx_jf hdl hc3
      have hu := unflat_two' (dc := dd.2) (dx := cc.2) (c := lvl - dd.1) (y := j - cc.1) hdl hc3
      have hn := nodeLoop_spec h2 hA2 hjf
        (by rw [hu]; simp only [Loop.dot, Nat.add_zero, Nat.zero_mul, Nat.zero_add, Nat.one_mul]; exact hgate _ hc2)
        (by rw [hu]; simp only [Loop.dot, Nat.add_zero, Nat.one_mul]
            have := hbit j hj lvl (Nat.lt_trans hlvl hph)
            rwa [hx_re10 hHj hd1])
      rw [hu] at hn
      simp only [Loop.dot, Nat.add_zero] at hn
      have hsl : slotOff o.L (dd.1 + 1) + 13 * (lvl - dd.1) = slotOff o.L (lvl + 1) := by
        simp only [slotOff, Nat.add_one_ne_zero, ite_false, Nat.add_sub_cancel]; exact hx_sl hd1
      have h5 : 5 ≤ slotOff o.L (dd.1 + 1) := by
        simp only [slotOff, Nat.add_one_ne_zero, ite_false]
        exact Nat.le_trans (Nat.le_add_right 5 _) (Nat.le_add_right _ _)
      have hb2 : lay.sb + eLane p o.i0 + posStride o.L * cc.1 + slotOff o.L (dd.1 + 1) +
          (13 * (lvl - dd.1) + posStride o.L * (j - cc.1)) =
            (lay.sb + eLane p o.i0 + posStride o.L * j) + slotOff o.L (lvl + 1) := hx_re11 hSj hsl
      refine ⟨by rw [← hb2]; exact hn.1, fun l hl => ?_⟩
      have := hn.2 l hl
      simp only [hx_re12 hHj hd1, hx_re13 hSj hsl h5, hx_re14 hSj hsl] at this
      exact this
  · -- the heap loop
    have hc0 : 1 ≤ 2 ^ p.capSendBits o.L.level o.L.cap := Nat.one_le_two_pow
    refine heapLoop_spec hrest.1 hArest.1 (Nat.le_trans hc0 hk1) hk2 hm1 ?_
    obtain ⟨g1, g2⟩ := hx_hz (zo := zo) hcK hk1 hk2
    rw [g1]
    exact hz _ g2
  · -- the cap check
    have := capChk_spec hrest.2 hArest.2 hin.flag hcm
    intro i hi
    obtain ⟨h1, h2⟩ := this i hi
    exact ⟨h1, fun l hl => by rw [h2 l hl, ← Nat.add_assoc]⟩

end

/-! ## The plan's static stream facts at S2GB (RE-FREEZE R2) -/

/-- **`entryOk`'s S2GB twin**: a heap entry (slot `k` of an opening's heap, at entry `i0 + t·(1 + path) + (2^m − 1 − k)`,
after the opening's `t` paths) is a 64-byte query whose positions lie before the opening; a heap entry with the sent
cap reads `2^c` nodes of the cap entry, before the opening. Every other entry: `entryOk`. -/
def entryOkB (P : List PE) (e : PE) (i : Nat) : Bool :=
  match e.k with
  | .heap pe h t path i0 m k cap =>
    e.len == 64 && decide (2 ≤ i0) && decide (1 ≤ t) && decide (1 ≤ path) && decide (path + m = h) &&
      decide (h ≤ 24) && decide (1 ≤ pe) && decide (pe + (t - 1) / 8 < i0) && decide (1 ≤ k) && decide (k < 2 ^ m) &&
      decide (i = i0 + t * (1 + path) + (2 ^ m - 1 - k)) &&
      (match cap with
       | none => true
       | some (ce, co, c) => co % 8 == 0 && decide (32 ≤ co) && decide (2 ^ c ≤ k) && decide (k < 2 ^ (c + 1)) &&
           decide (co + 32 * 2 ^ c ≤ (P.getD ce default).len) && decide (1 ≤ ce) && decide (ce < i0))
  | _ => entryOk P e i

/-- Every entry of the plan passes `entryOkB`, and every length after `q₀` is a whole number of lanes. -/
def streamOkLB (P : List PE) : Bool :=
  (P.tail.all fun e => e.len % 8 == 0) && P.zipIdx.all fun x => entryOkB P x.1 x.2

/-- **The plan's static stream facts at S2GB** (`StreamOk`'s twin; heap entries pass `entryOkB`). -/
def StreamOkB (p : Params) : Prop := streamOkLB (plan p) = true ∧ hashedLen p = 1 + slenS (lens p)

theorem streamOkB_entry {P : List PE} (h : streamOkLB P = true) {i : Nat} (hi : i < P.length) :
    entryOkB P (P.getD i default) i = true := by
  simp only [streamOkLB, Bool.and_eq_true, List.all_eq_true] at h
  have := h.2 (P[i], i) (List.mem_zipIdx_iff_getElem?.mpr (by simp [List.getElem?_eq_getElem hi]))
  simpa [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi] using this

theorem streamOkB_len {P : List PE} (h : streamOkLB P = true) {i : Nat} (h1 : 1 ≤ i) (hi : i < P.length) :
    (P.getD i default).len % 8 = 0 := by
  simp only [streamOkLB, Bool.and_eq_true, List.all_eq_true] at h
  have hm : P.getD i default ∈ P.tail := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, Option.getD_some]
    rcases P with _ | ⟨x, P⟩
    · simp at hi
    · obtain ⟨k, rfl⟩ : ∃ k, i = k + 1 := ⟨i - 1, by omega⟩
      simp
  simpa using h.1 _ hm

section
variable {p : Params}

theorem bOff_modB (hS : streamOkLB (plan p) = true) : ∀ i, 1 ≤ i → i ≤ (plan p).length → bOff p i % 8 = 0
  | 0, h, _ => absurd h (by omega)
  | 1, _, _ => by rw [bOff_one]
  | i + 2, _, hi => by
    rw [bOff_succ p (by omega)]
    have := bOff_modB hS (i + 1) (by omega) (by omega)
    have := streamOkB_len hS (i := i + 1) (by omega) (by omega)
    omega

theorem bOff_eqB (hS : streamOkLB (plan p) = true) {i : Nat} (h1 : 1 ≤ i) (hi : i ≤ (plan p).length) :
    bOff p i = 8 * eLane p i := by
  have := bOff_modB hS i h1 hi; simp only [eLane]; omega

theorem eLane_succB (hS : streamOkLB (plan p) = true) {i : Nat} (h1 : 1 ≤ i) (hi : i < (plan p).length) :
    eLane p (i + 1) = eLane p i + 5 + ((plan p).getD i default).len / 8 := by
  have h8 := streamOkB_len hS h1 hi
  have e1 := bOff_eqB hS (i := i + 1) (by omega) (by omega)
  have e2 := bOff_eqB hS h1 (by omega)
  rw [bOff_succ p hi] at e1
  omega

theorem lanes_inB (hS : StreamOkB p) {i : Nat} (h1 : 1 ≤ i) (hi : i < (plan p).length) :
    eLane p i + 5 + ((plan p).getD i default).len / 8 ≤ hashedLen p / 8 := by
  have e := entry_end p hi
  rw [← hS.2, bOff_eqB hS.1 h1 (by omega)] at e
  have := streamOkB_len hS.1 h1 hi
  omega

end

/-! ## The openings of the plan at S2GB -/

/-- An entry is a leaf, a node or a heap node. -/
def _root_.Lvm.Replay.EK.isOpenB : EK → Bool
  | .leaf => true
  | .node .. => true
  | .heap .. => true
  | _ => false

/-- **The entries of opening `o` at S2GB**: its paths (no cap on the last level), then its heap (the cap sent at
`capSendBits lv`). -/
def openPlanB (p : Params) (lv : Nat) (o : OpenInfo) : List PE :=
  openPlanN o.L o.pe ++ heapPlan o.L o.pe o.i0 (p.capSendBits lv o.L.cap) o.ce o.co

theorem planItem_openB (p : Params) (hcp : p.capPrune = true) (w : WS) (it : Item) {x : Nat}
    (hx : x < (planItem p w it).1.length) (he : ((planItem p w it).1.getD x default).k.isOpenB = true) :
    ∃ o ∈ openItem p w it, ∃ r : Ref, o.L = p.level r ∧ o.i0 = w.i ∧ (planItem p w it).1 = openPlanB p r.lv o := by
  cases it with
  | read m => simp [planItem] at hx
  | readW m wd => simp [planItem] at hx
  | cap c r => simp [planItem] at hx
  | sample =>
    simp only [planItem, List.length_singleton, Nat.lt_one_iff] at hx
    subst hx; simp [planItem, EK.isOpenB] at he
  | positions r =>
    simp only [planItem, List.length_map, List.length_range] at hx
    simp only [planItem, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hx,
      Option.map_some, Option.getD_some] at he
    split_ifs at he <;> simp [EK.isOpenB] at he
  | opening r =>
    rcases hf : w.caps.find? (·.1 == r) with _ | ⟨r', ce, co, nb⟩
    · simp [planItem, hf] at hx
    · exact ⟨⟨w.i, p.level r, w.pe, ce, co⟩, by simp [openItem, hf], r, rfl, rfl,
        by simp [planItem, hf, hcp, openPlanB]⟩

theorem openItems_openB (p : Params) (hcp : p.capPrune = true) : ∀ (its : List Item) (w : WS) {x : Nat},
    x < (planItems p w its).1.length → ((planItems p w its).1.getD x default).k.isOpenB = true →
    ∃ o ∈ openItems p w its, ∃ r : Ref, o.L = p.level r ∧ o.i0 ≤ w.i + x ∧
      w.i + x < o.i0 + (openPlanB p r.lv o).length ∧
      (planItems p w its).1.getD x default = (openPlanB p r.lv o).getD (w.i + x - o.i0) default
  | [], _, _, hx, _ => by simp [planItems] at hx
  | it :: its, w, x, hx, he => by
    simp only [planItems, List.length_append] at hx he ⊢
    by_cases h1 : x < (planItem p w it).1.length
    · rw [List.getD_append _ _ _ _ h1] at he ⊢
      obtain ⟨o, ho, r, hr, hi, hp⟩ := planItem_openB p hcp w it h1 he
      refine ⟨o, by simp [openItems, ho], r, hr, by omega, by rw [← hp, hi]; omega, ?_⟩
      rw [hi, show w.i + x - w.i = x by omega, hp]
    · rw [List.getD_append_right _ _ _ _ (by omega)] at he ⊢
      obtain ⟨o, ho, r, hr, h2, h3, h4⟩ := openItems_openB p hcp its (planItem p w it).2
        (x := x - (planItem p w it).1.length) (by omega) he
      rw [planItem_i] at h2 h3 h4
      refine ⟨o, by simp [openItems, ho], r, hr, by omega, by omega, ?_⟩
      rw [h4]; congr 1; omega

/-- **Every leaf, node or heap entry lies in an opening** at S2GB. -/
theorem open_of_entryB (p : Params) (hcp : p.capPrune = true) {i : Nat} (hi : i < (plan p).length)
    (he : ((plan p).getD i default).k.isOpenB = true) :
    ∃ o ∈ opens p, ∃ r : Ref, o.L = p.level r ∧ o.i0 ≤ i ∧ i < o.i0 + (openPlanB p r.lv o).length ∧
      (plan p).getD i default = (openPlanB p r.lv o).getD (i - o.i0) default := by
  have h2 : 2 ≤ i := by
    rcases i with _ | _ | i
    · rw [plan_zero] at he; simp [EK.isOpenB] at he
    · rw [plan_one] at he; simp [EK.isOpenB] at he
    · omega
  have hpl : (plan p).getD i default = (planAll p).1.getD (i - 2) default := by
    obtain ⟨k, rfl⟩ : ∃ k, i = k + 2 := ⟨i - 2, by omega⟩
    simp [plan, List.getD_eq_getElem?_getD]
  rw [hpl] at he ⊢
  have := openItems_openB p hcp (schedule p) w0 (x := i - 2)
    (by rw [plan_length] at hi; simp [planAll] at hi ⊢; omega) he
  simp only [w0] at this
  rw [show 2 + (i - 2) = i by omega] at this
  exact this

theorem openItems_alB (p : Params) (hcp : p.capPrune = true) {P : List PE} : ∀ (its : List Item) (w : WS),
    Al P w.i (planItems p w its).1 → ∀ o ∈ openItems p w its, ∃ r : Ref, o.L = p.level r ∧
      Al P o.i0 (openPlanB p r.lv o)
  | [], _, _, o, ho => by simp [openItems] at ho
  | it :: its, w, hal, o, ho => by
    obtain ⟨h1, h2⟩ := Al_planItems p hal
    simp only [openItems, List.mem_append] at ho
    rcases ho with ho | ho
    · cases it with
      | opening r =>
        rcases hf : w.caps.find? (·.1 == r) with _ | ⟨r', ce, co, nb⟩
        · simp [openItem, hf] at ho
        · simp only [openItem, hf, List.mem_singleton] at ho
          subst ho
          exact ⟨r, rfl, by simpa [planItem, hf, hcp, openPlanB] using h1⟩
      | _ => simp [openItem] at ho
    · exact openItems_alB p hcp its _ h2 o ho

/-- Every opening sits in the plan at its first entry (S2GB). -/
theorem opens_alB (p : Params) (hcp : p.capPrune = true) {o : OpenInfo} (ho : o ∈ opens p) :
    ∃ r : Ref, o.L = p.level r ∧ Al (plan p) o.i0 (openPlanB p r.lv o) := by
  refine openItems_alB p hcp (schedule p) w0 ⟨by simp [w0, plan_length, planAll], fun x hx => ?_⟩ o ho
  show (plan p).getD (2 + x) default = _
  simp only [plan, planAll, List.getD_eq_getElem?_getD]
  rw [show 2 + x = x + 1 + 1 by omega]
  simp

/-- A level with a path is at its index (`QOkB.lvIdx`). -/
theorem level_of_ref {p : Params} (hlv : (∀ lv < p.mainLevels.length, (p.mainLevels.getD lv default).level = lv) ∧
    ∀ lv < p.recLevels.length, (p.recLevels.getD lv default).level = lv) {r : Ref} (hp : 1 ≤ (p.level r).path) :
    (p.level r).level = r.lv := by
  rcases r with ⟨com, lv⟩
  cases com with
  | main =>
    simp only [Params.level, Params.levels] at hp ⊢
    by_cases h : lv < p.mainLevels.length
    · exact hlv.1 lv h
    · rw [List.getD_eq_default _ _ (by omega)] at hp; exact absurd hp (by decide)
  | crec =>
    simp only [Params.level, Params.levels] at hp ⊢
    by_cases h : lv < p.recLevels.length
    · exact hlv.2 lv h
    · rw [List.getD_eq_default _ _ (by omega)] at hp; exact absurd hp (by decide)

theorem openPlanN_length (L : Level) (pe : Nat) : (openPlanN L pe).length = L.t * (1 + L.path) := by
  simp [openPlanN, List.length_flatMap]; left; ring

/-- The entry at position `j`, slot `y` of an opening's paths at S2GB. -/
theorem openPlanN_getD (L : Level) (pe : Nat) {j y : Nat} (hj : j < L.t) (hy : y < 1 + L.path) :
    (openPlanN L pe).getD (j * (1 + L.path) + y) default =
      if y = 0 then ⟨.leaf, L.row⟩ else ⟨.node pe L.height j (y - 1) none, 64⟩ := by
  suffices h : ∀ (n k : Nat) (j : Nat), j < n →
      ((List.range' k n).flatMap fun j => (⟨.leaf, L.row⟩ : PE) :: (List.range L.path).map fun lvl =>
        ⟨.node pe L.height j lvl none, 64⟩).getD (j * (1 + L.path) + y) default =
      if y = 0 then ⟨.leaf, L.row⟩ else ⟨.node pe L.height (k + j) (y - 1) none, 64⟩ by
    simpa [openPlanN, List.range_eq_range'] using h L.t 0 j hj
  intro n
  induction n with
  | zero => intro k j hj; omega
  | succ n ih =>
    intro k j hj
    rw [List.range'_succ, List.flatMap_cons]
    rcases j with _ | j
    · simp only [Nat.zero_mul, Nat.zero_add, Nat.add_zero]
      rw [List.getD_append _ _ _ _ (by simp; omega)]
      rcases y with _ | y
      · simp
      · simp only [List.getD_cons_succ, Nat.add_one_ne_zero, ite_false, Nat.add_sub_cancel]
        rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range (by omega)]
        simp
    · rw [List.getD_append_right _ _ _ _ (by simp; nlinarith)]
      have := ih (k + 1) j (by omega)
      rw [show k + (j + 1) = k + 1 + j by omega]
      rw [← this]
      congr 1
      simp only [Nat.succ_mul, List.length_cons, List.length_map, List.length_range]
      ring_nf; omega

theorem heapPlan_length (L : Level) (pe i0 c ce co : Nat) :
    (heapPlan L pe i0 c ce co).length = 2 ^ L.cap - 2 ^ c := by
  simp [heapPlan]

theorem heapPlan_getD (L : Level) (pe i0 c ce co : Nat) {n : Nat} (hn : n < 2 ^ L.cap - 2 ^ c) :
    (heapPlan L pe i0 c ce co).getD n default = ⟨.heap pe L.height L.t L.path i0 L.cap (2 ^ L.cap - 1 - n)
      (if 2 ^ L.cap - 1 - n < 2 ^ (c + 1) then some (ce, co, c) else none), 64⟩ := by
  simp [heapPlan, List.getD_eq_getElem?_getD, List.getElem?_range hn]

theorem openPlanB_length (p : Params) (lv : Nat) (o : OpenInfo) :
    (openPlanB p lv o).length = o.L.t * (1 + o.L.path) + (2 ^ o.L.cap - 2 ^ p.capSendBits lv o.L.cap) := by
  simp only [openPlanB, List.length_append, openPlanN_length, heapPlan_length]

/-- **The lanes inside an opening at S2GB are affine**: its paths as at S2GS, then its heap, 13 lanes a slot from
`heapLane`. -/
theorem eLane_openB {p : Params} (hS : StreamOkB p) {o : OpenInfo} {lv : Nat} (hal : Al (plan p) o.i0 (openPlanB p lv o))
    (h2 : 2 ≤ o.i0) :
    (∀ j < o.L.t, ∀ y ≤ o.L.path,
      eLane p (o.i0 + j * (1 + o.L.path) + y) = eLane p o.i0 + j * posStride o.L + slotOff o.L y) ∧
    ∀ n ≤ 2 ^ o.L.cap - 2 ^ p.capSendBits lv o.L.cap,
      eLane p (o.i0 + o.L.t * (1 + o.L.path) + n) = heapLane p o + 13 * n := by
  have hlen := hal.1
  rw [openPlanB_length] at hlen
  have entry : ∀ j' < o.L.t, ∀ y' < 1 + o.L.path,
      ((plan p).getD (o.i0 + j' * (1 + o.L.path) + y') default).len = if y' = 0 then o.L.row else 64 := by
    intro j' hj' y' hy'
    have hx : j' * (1 + o.L.path) + y' < o.L.t * (1 + o.L.path) := by nlinarith
    rw [Nat.add_assoc, hal.2 _ (by rw [openPlanB_length]; omega), openPlanB,
      List.getD_append _ _ _ _ (by rw [openPlanN_length]; exact hx), openPlanN_getD _ _ hj' hy']
    split <;> rfl
  have hentry : ∀ n < 2 ^ o.L.cap - 2 ^ p.capSendBits lv o.L.cap,
      ((plan p).getD (o.i0 + o.L.t * (1 + o.L.path) + n) default).len = 64 := by
    intro n hn
    rw [Nat.add_assoc, hal.2 _ (by rw [openPlanB_length]; omega), openPlanB,
      List.getD_append_right _ _ _ _ (by rw [openPlanN_length]; omega), openPlanN_length,
      show o.L.t * (1 + o.L.path) + n - o.L.t * (1 + o.L.path) = n by omega, heapPlan_getD _ _ _ _ _ _ hn]
  have within : ∀ j' < o.L.t, ∀ y' ≤ o.L.path, eLane p (o.i0 + j' * (1 + o.L.path) + y') =
      eLane p (o.i0 + j' * (1 + o.L.path)) + slotOff o.L y' := by
    intro j' hj' y'
    induction y' with
    | zero => intro _; simp [slotOff]
    | succ y' ih =>
      intro hy'
      have hx : j' * (1 + o.L.path) + y' < o.L.t * (1 + o.L.path) := by nlinarith
      rw [← Nat.add_assoc, eLane_succB hS.1 (by omega) (by omega), ih (by omega), entry j' hj' y' (by omega)]
      simp only [slotOff, Nat.add_one_ne_zero, ite_false, Nat.add_sub_cancel]
      split
      · next h => subst h; simp; omega
      · next h => omega
  have leaf : ∀ j' ≤ o.L.t, eLane p (o.i0 + j' * (1 + o.L.path)) = eLane p o.i0 + j' * posStride o.L := by
    intro j'
    induction j' with
    | zero => intro _; simp
    | succ j' ih =>
      intro hj'
      have hstep : o.i0 + (j' + 1) * (1 + o.L.path) = o.i0 + j' * (1 + o.L.path) + o.L.path + 1 := by ring
      have hx : j' * (1 + o.L.path) + o.L.path < o.L.t * (1 + o.L.path) := by nlinarith
      rw [hstep, eLane_succB hS.1 (by omega) (by omega), within j' (by omega) o.L.path le_rfl,
        ih (by omega), entry j' (by omega) o.L.path (by omega)]
      simp only [slotOff, posStride]
      split
      · next h => rw [h]; ring_nf
      · next h =>
        have : 13 * o.L.path = 13 * (o.L.path - 1) + 13 := by omega
        rw [Nat.add_mul, this]; ring_nf
  refine ⟨fun j hj y hy => by rw [within j hj y hy, leaf j hj.le], fun n => ?_⟩
  induction n with
  | zero => intro _; rw [Nat.add_zero, leaf _ le_rfl]; rfl
  | succ n ih =>
    intro hn
    rw [← Nat.add_assoc, eLane_succB hS.1 (by omega) (by omega), ih (by omega), hentry n (by omega)]
    ring

/-- **An entry of an opening at S2GB**: its opening, and either its position and slot (a leaf or a node, no
cap) or its heap index `n` (slot `2^cap − 1 − n`). -/
theorem open_posB {p : Params} (hcp : p.capPrune = true)
    (hlv : (∀ lv < p.mainLevels.length, (p.mainLevels.getD lv default).level = lv) ∧
      ∀ lv < p.recLevels.length, (p.recLevels.getD lv default).level = lv)
    (hp1 : ∀ o ∈ opens p, 1 ≤ o.L.path) {i : Nat} (hi : i < (plan p).length)
    (he : ((plan p).getD i default).k.isOpenB = true) :
    ∃ k, k < (opens p).length ∧ ∃ o, (opens p).getD k default = o ∧
      ((∃ jj y, jj < o.L.t ∧ y < 1 + o.L.path ∧ i = o.i0 + jj * (1 + o.L.path) + y ∧
        (plan p).getD i default = if y = 0 then ⟨.leaf, o.L.row⟩ else ⟨.node o.pe o.L.height jj (y - 1) none, 64⟩) ∨
      (∃ n, n < 2 ^ o.L.cap - 2 ^ p.capSendBits o.L.level o.L.cap ∧ i = o.i0 + o.L.t * (1 + o.L.path) + n ∧
        (plan p).getD i default = ⟨.heap o.pe o.L.height o.L.t o.L.path o.i0 o.L.cap (2 ^ o.L.cap - 1 - n)
          (if 2 ^ o.L.cap - 1 - n < 2 ^ (p.capSendBits o.L.level o.L.cap + 1)
           then some (o.ce, o.co, p.capSendBits o.L.level o.L.cap) else none), 64⟩)) := by
  obtain ⟨o, ho, r, hr, h1, h2, h3⟩ := open_of_entryB p hcp hi he
  have hlvr : o.L.level = r.lv := by rw [hr]; exact level_of_ref hlv (by rw [← hr]; exact hp1 o ho)
  rw [← hlvr] at h2 h3
  obtain ⟨k, hk, hko⟩ := List.mem_iff_getElem.mp ho
  refine ⟨k, hk, o, by rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk, Option.getD_some, hko], ?_⟩
  rw [openPlanB_length] at h2
  by_cases hpth : i - o.i0 < o.L.t * (1 + o.L.path)
  · left
    have hP : 0 < 1 + o.L.path := by omega
    have hx : (i - o.i0) / (1 + o.L.path) * (1 + o.L.path) + (i - o.i0) % (1 + o.L.path) = i - o.i0 :=
      Nat.div_add_mod' _ _
    have hjt : (i - o.i0) / (1 + o.L.path) < o.L.t := by
      rw [Nat.div_lt_iff_lt_mul hP]; omega
    have e := openPlanN_getD o.L o.pe hjt (Nat.mod_lt (i - o.i0) hP)
    rw [hx] at e
    refine ⟨(i - o.i0) / (1 + o.L.path), (i - o.i0) % (1 + o.L.path), hjt, Nat.mod_lt _ hP, by omega, ?_⟩
    rw [h3, openPlanB, List.getD_append _ _ _ _ (by rw [openPlanN_length]; exact hpth), e]
  · right
    refine ⟨i - o.i0 - o.L.t * (1 + o.L.path), by omega, by omega, ?_⟩
    rw [h3, openPlanB, List.getD_append_right _ _ _ _ (by rw [openPlanN_length]; omega), openPlanN_length,
      heapPlan_getD _ _ _ _ _ _ (by omega)]

/-- Every opening sits in the plan at its first entry, its heap's cap sent at its level's `capSendBits`. -/
theorem opens_alB' {p : Params} (hcp : p.capPrune = true)
    (hlv : (∀ lv < p.mainLevels.length, (p.mainLevels.getD lv default).level = lv) ∧
      ∀ lv < p.recLevels.length, (p.recLevels.getD lv default).level = lv)
    {o : OpenInfo} (ho : o ∈ opens p) (hp1 : 1 ≤ o.L.path) : Al (plan p) o.i0 (openPlanB p o.L.level o) := by
  obtain ⟨r, hr, hal⟩ := opens_alB p hcp ho
  have : o.L.level = r.lv := by rw [hr]; exact level_of_ref hlv (by rw [← hr]; exact hp1)
  rw [this]; exact hal

/-- The lengths of an opening's entries at S2GB: a leaf its row, a node or a heap node 64. -/
theorem openB_len {p : Params} {o : OpenInfo} {lv : Nat} (hal : Al (plan p) o.i0 (openPlanB p lv o)) :
    (∀ j < o.L.t, ∀ y < 1 + o.L.path,
      ((plan p).getD (o.i0 + j * (1 + o.L.path) + y) default).len = if y = 0 then o.L.row else 64) ∧
    ∀ n < 2 ^ o.L.cap - 2 ^ p.capSendBits lv o.L.cap,
      ((plan p).getD (o.i0 + o.L.t * (1 + o.L.path) + n) default).len = 64 := by
  refine ⟨fun j hj y hy => ?_, fun n hn => ?_⟩
  · have hx : j * (1 + o.L.path) + y < o.L.t * (1 + o.L.path) := by nlinarith
    rw [Nat.add_assoc, hal.2 _ (by rw [openPlanB_length]; omega), openPlanB,
      List.getD_append _ _ _ _ (by rw [openPlanN_length]; exact hx), openPlanN_getD _ _ hj hy]
    split <;> rfl
  · rw [Nat.add_assoc, hal.2 _ (by rw [openPlanB_length]; omega), openPlanB,
      List.getD_append_right _ _ _ _ (by rw [openPlanN_length]; omega), openPlanN_length,
      show o.L.t * (1 + o.L.path) + n - o.L.t * (1 + o.L.path) = n by omega, heapPlan_getD _ _ _ _ _ _ hn]

/-! ## The theorem (CAP-FRZ C, statement first) -/

/-- **Q_link's conditions at S2GB, lane by lane**: `LaneLink`'s (its `cap` field is vacuous: no node entry carries a
cap under `capPrune`), and the heap entries': a bottom slot's halves are the tops of the paths whose top bits select
them, an inner slot's halves are its children's answers, the cap slots' answers are the sent cap's nodes. -/
structure LaneLinkB (p : Params) (ws : List Word) : Prop where
  base : LaneLink p ws
  bot : ∀ i < (plan p).length, ∀ pe h t path i0 m k cap,
    ((plan p).getD i default).k = .heap pe h t path i0 m k cap → 2 ^ (m - 1) ≤ k →
    ∀ b < 2, ∀ j < t, posL p ws (pe + j / 8) (j % 8 * h + path) (h - path) = 2 * (k - 2 ^ (m - 1)) + b →
    ∀ l < 4, lw ws (eLane p i + 1 + 4 * b + l) = lw ws (ansLane p (i0 + j * (1 + path) + path) + l)
  inner : ∀ i < (plan p).length, ∀ pe h t path i0 m k cap,
    ((plan p).getD i default).k = .heap pe h t path i0 m k cap → k < 2 ^ (m - 1) →
    ∀ l < 4, lw ws (eLane p i + 1 + l) = lw ws (ansLane p (i0 + t * (1 + path) + (2 ^ m - 1 - 2 * k)) + l) ∧
      lw ws (eLane p i + 5 + l) = lw ws (ansLane p (i0 + t * (1 + path) + (2 ^ m - 1 - (2 * k + 1))) + l)
  cap : ∀ i < (plan p).length, ∀ pe h t path i0 m k ce co c,
    ((plan p).getD i default).k = .heap pe h t path i0 m k (some (ce, co, c)) →
    ∀ l < 4, lw ws (ansLane p i + l) = lw ws (eLane p ce + 1 + co / 8 + 4 * (k - 2 ^ c) + l)

/-- **Q_link's static conditions at S2GB** (decided per parameter set and layout): `QOk`'s, with `capPrune` and the
openings' heap (`c = capSendBits`, `m = height − path`). -/
structure QOkB (p : Params) (lay : Layout) : Prop where
  qlen : (qltEntries p lay).length ≤ 2 ^ lay.aQ
  qbound : ∀ e ∈ qltEntries p lay, lay.sb ≤ e.1 ∧ lay.sb ≤ e.2.1 ∧ e.1 + 5 ≤ lay.sb + 2 ^ lay.m ∧
    e.2.1 + 4 ≤ lay.sb + 2 ^ lay.m ∧ e.2.2 < 2 ^ 64
  hT : hashedLen p / 8 + 17 ≤ 2 ^ lay.m
  opens : ∀ o ∈ opens p, 1 ≤ o.L.path ∧ o.L.path < o.L.height ∧ (∀ c ∈ pchunks o.L.t, c.2 ≤ lay.K) ∧
    o.L.cap = o.L.height - o.L.path ∧ p.capSendBits o.L.level o.L.cap < o.L.height - o.L.path ∧
    2 ^ (o.L.height - o.L.path - 1) - 2 ^ p.capSendBits o.L.level o.L.cap ≤ 2 ^ lay.K ∧
    heapLane p o + 13 * 2 ^ (o.L.height - o.L.path) ≤ 2 ^ lay.m ∧
    eLane p o.ce + 1 + o.co / 8 + 4 * 2 ^ p.capSendBits o.L.level o.L.cap ≤ 2 ^ lay.m ∧ o.L.row < 2 ^ 64
  pos : ((Lvm.QLink.opens p).map fun o => o.L.t).sum ≤ 2 ^ lay.pa
  cp : p.capPrune = true
  /-- The levels' indices are their places (the plan keys the sent cap on the reference's index, Q_link on
  the level's). -/
  lvIdx : (∀ lv < p.mainLevels.length, (p.mainLevels.getD lv default).level = lv) ∧
    ∀ lv < p.recLevels.length, (p.recLevels.getD lv default).level = lv

/-! ## Q_link's static conditions at S2GB as one Boolean -/

/-- `QOkB`'s conditions, decidable (the QLT bounds follow from `StreamOkB`; `qOkB`'s twin). -/
def qOkCB (p : Params) (lay : Layout) : Bool :=
  decide ((qltEntries p lay).length ≤ 2 ^ lay.aQ) && decide (hashedLen p / 8 + 17 ≤ 2 ^ lay.m) &&
    decide (17 * nBlk (hashedLen p) + 4 ≤ 2 ^ lay.m) && decide (hashedLen p < 2 ^ 64) &&
    ((opens p).all fun o => decide (1 ≤ o.L.path) && decide (o.L.path < o.L.height) &&
      (pchunks o.L.t).all (fun c => decide (c.2 ≤ lay.K)) &&
      decide (o.L.cap = o.L.height - o.L.path) &&
      decide (p.capSendBits o.L.level o.L.cap < o.L.height - o.L.path) &&
      decide (2 ^ (o.L.height - o.L.path - 1) - 2 ^ p.capSendBits o.L.level o.L.cap ≤ 2 ^ lay.K) &&
      decide (heapLane p o + 13 * 2 ^ (o.L.height - o.L.path) ≤ 2 ^ lay.m) &&
      decide (eLane p o.ce + 1 + o.co / 8 + 4 * 2 ^ p.capSendBits o.L.level o.L.cap ≤ 2 ^ lay.m) &&
      decide (o.L.row < 2 ^ 64)) &&
    decide (((opens p).map fun o => o.L.t).sum ≤ 2 ^ lay.pa) && p.capPrune &&
    ((List.range p.mainLevels.length).all fun lv => (p.mainLevels.getD lv default).level == lv) &&
    ((List.range p.recLevels.length).all fun lv => (p.recLevels.getD lv default).level == lv)

theorem lane1C_ltB : lane1C < 2 ^ 64 := lt_of_lt_of_le (ofLE_lt _) (by simp [q0Bytes])

theorem padLane_ltB (L q : Nat) : padLane L q < 2 ^ 64 := lt_of_lt_of_le (ofLE_lt _) (by simp)

section
variable {p : Params} {lay : Layout}

theorem hashedLen_ge48B (hS : StreamOkB p) : 48 ≤ hashedLen p := by
  rw [hS.2]; simp [lens, plan, slenS]; omega

theorem hashedLen_modB (hS : StreamOkB p) : hashedLen p % 8 = 0 := by
  have := bOff_modB hS.1 (plan p).length (by have := plan_length_ge p; omega) le_rfl
  rw [bOff_end, ← hS.2] at this; exact this

/-- **The QLT entries' bounds** at S2GB, from the plan's stream facts (`qbound_of`'s twin). -/
theorem qbound_ofB (hS : StreamOkB p) (hT2 : 17 * nBlk (hashedLen p) + 4 ≤ 2 ^ lay.m) (h64 : hashedLen p < 2 ^ 64) :
    ∀ e ∈ qltEntries p lay, lay.sb ≤ e.1 ∧ lay.sb ≤ e.2.1 ∧ e.1 + 5 ≤ lay.sb + 2 ^ lay.m ∧
      e.2.1 + 4 ≤ lay.sb + 2 ^ lay.m ∧ e.2.2 < 2 ^ 64 := by
  have hL8 := hashedLen_modB hS
  have hL48 := hashedLen_ge48B hS
  have hLb : hashedLen p / 8 + 5 ≤ 2 ^ lay.m := by simp only [nBlk] at hT2; omega
  intro e he
  simp only [qltEntries, List.mem_append] at he
  rcases he with (h01 | hmid) | hpad
  · simp only [List.mem_cons, List.mem_nil_iff, or_false] at h01
    rcases h01 with rfl | rfl <;> dsimp only
    · exact ⟨le_rfl, by omega, by omega, by omega, by simp [lane0C]⟩
    · exact ⟨by omega, by omega, by omega, by omega, lane1C_ltB⟩
  · obtain ⟨⟨pe, i⟩, hx, hf⟩ := List.mem_filterMap.mp hmid
    have hgi := List.mem_zipIdx_iff_getElem?.mp hx
    simp only at hgi hf
    have hi : i < (plan p).length := by
      by_contra hc; rw [List.getElem?_eq_none (by omega)] at hgi; cases hgi
    have hpe : (plan p).getD i default = pe := by
      rw [List.getD_eq_getElem?_getD, hgi, Option.getD_some]
    split at hf
    · next st hk =>
      cases hf
      have hok := streamOkB_entry hS.1 hi
      rw [hpe] at hok
      simp only [entryOkB, entryOk, hk, Bool.and_eq_true, decide_eq_true_eq] at hok
      obtain ⟨⟨h32, hst⟩, h1⟩ := hok
      have hin := lanes_inB hS h1 hi
      rw [hpe] at hin
      have h8 := streamOkB_len hS.1 h1 hi
      rw [hpe] at h8
      have hans : ansLane p st + 4 ≤ hashedLen p / 8 := by
        by_cases h0 : st = 0
        · subst h0; simp only [ansLane, ite_true]; omega
        · have := lanes_inB hS (i := st) (by omega) (by omega)
          simp only [ansLane, h0, ite_false]; omega
      dsimp only
      exact ⟨by omega, by omega, by omega, by omega, by omega⟩
    · cases hf
  · obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hpad
    rw [List.mem_range] at hk
    simp only [nBlk] at hT2 hk ⊢
    exact ⟨by omega, by omega, by omega, by omega, padLane_ltB _ _⟩

/-- **`QOkB` from one Boolean** (`qOk_of`'s twin). -/
theorem qOkB_of (hS : StreamOkB p) (h : qOkCB p lay = true) : QOkB p lay := by
  simp only [qOkCB, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, beq_iff_eq, List.mem_range] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩ := h
  refine ⟨h1, qbound_ofB hS h3 h4, h2, fun o ho => ?_, h6, h7, h8, h9⟩
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨a1, a2⟩, a3⟩, a4⟩, a5⟩, a6⟩, a7⟩, a8⟩, a9⟩ := h5 o ho
  exact ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9⟩

end

section
variable {p : Params} {lay : Layout} {ws : List Word} {c : Ctx} {M : Mem}

/-- **Every QLT entry's checks hold** (`qlt_entry` at S2GB). -/
theorem qlt_entryB (hQ : QOkB p lay) (hin : QIn p lay ws M) {N : Nat} (hinj : GInj N) (hN : c.cells .K ≤ N)
    (hNs : lay.sb + 2 ^ lay.m ≤ N) {pt : Ptr}
    (h : SegsHold c M pt (qltLoop lay.aQ lay.qt lay.sb lay.m (kc lay.fg) pt).2)
    (hA : SegsAssert M pt (qltLoop lay.aQ lay.qt lay.sb lay.m (kc lay.fg) pt).2)
    {e : Nat × Nat × Nat} (he : e ∈ qltEntries p lay) :
    M.k e.1 = kOf e.2.2 ∧ ∀ l < 4, M.k (e.1 + 1 + l) = M.k (e.2.1 + l) := by
  have hmem : e ∈ qltPadded p lay := List.mem_append_left _ he
  obtain ⟨k, hk, hke⟩ := List.mem_iff_getElem.mp hmem
  rw [qltPadded_length p lay hQ.qlen] at hk
  have hkd : (qltPadded p lay).getD k (0, 0, 0) = e := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by rw [qltPadded_length p lay hQ.qlen]; exact hk)]
    simpa using hke
  have hd := tblOf_getD (qltPadded p lay) (k := k) (by rw [qltPadded_length p lay hQ.qlen]; exact hk)
  rw [hkd] at hd
  have hlenD : (qltData p lay).length = 3 * 2 ^ lay.aQ := by
    rw [qltData, tblOf_length, qltPadded_length p lay hQ.qlen]
  have t0 := hin.table (3 * k) (by omega)
  have t1 := hin.table (3 * k + 1) (by omega)
  have t2 := hin.table (3 * k + 2) (by omega)
  simp only [qltData] at t0 t1 t2
  rw [hd.1] at t0; rw [hd.2.1] at t1; rw [hd.2.2] at t2
  obtain ⟨b1, b2, b3, b4, -⟩ := hQ.qbound e he
  have := qltLoop_spec h hA hin.flag hinj hN (jf := k) (e₁ := e.1) (e₂ := e.2.1) hk (by omega) (by omega)
    t0 (by rw [show lay.qt + 1 + 3 * k = lay.qt + (3 * k + 1) by ring]; exact t1)
  rw [show lay.qt + 2 + 3 * k = lay.qt + (3 * k + 2) by ring, t2] at this
  exact this

/-- **A path entry of an opening at S2GB**: its length lane, and a node's selection (`qlinkCoreB_sound`'s part). -/
theorem open_entryB (hS : StreamOkB p) (hQ : QOkB p lay) (hin : QIn p lay ws M)
    {N : Nat} (hinj : GInj N) (hN : c.cells .K ≤ N) (hNs : lay.sb + 2 ^ lay.m ≤ N)
    {zo : Nat} (hz : ∀ x < 2 ^ lay.K, M.k (zo + x) = 1)
    {k : Nat} (hk : k < (opens p).length) {o : OpenInfo} (hko : (opens p).getD k default = o) {q : Ptr}
    (hq1 : SegsHold c M q (openLoopsB p lay zo (bitBase p lay k) o q).2)
    (hq2 : SegsAssert M q (openLoopsB p lay zo (bitBase p lay k) o q).2)
    {jj y : Nat} (hjj : jj < o.L.t) (hy : y < 1 + o.L.path) {i : Nat} (hieq : i = o.i0 + jj * (1 + o.L.path) + y)
    (hi : i < (plan p).length)
    (hpe : (plan p).getD i default =
      (if y = 0 then ⟨.leaf, o.L.row⟩ else ⟨.node o.pe o.L.height jj (y - 1) none, 64⟩)) :
    lw ws (eLane p i) = ((plan p).getD i default).len ∧
    (y ≠ 0 → ∀ l < 4, lw ws ((if ansBit p ws (o.pe + jj / 8) (jj % 8 * o.L.height + (y - 1))
      then eLane p i + 5 else eLane p i + 1) + l) = lw ws (eLane p i - 4 + l)) := by
  have hT := hQ.hT
  have LE : ∀ a b, a < 2 ^ lay.m → b < 2 ^ lay.m → M.k (lay.sb + a) = M.k (lay.sb + b) → lw ws a = lw ws b :=
    fun a b ha hb e => lw_of_laneK (by rw [← hin.stream a ha, ← hin.stream b hb, e])
  have LV : ∀ a v, a < 2 ^ lay.m → v < 2 ^ 64 → M.k (lay.sb + a) = kOf v → lw ws a = v :=
    fun a v ha hv e => lw_of_kOf hv (by rw [← hin.stream a ha, e])
  have ho : o ∈ opens p := by
    rw [← hko, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk]; exact List.getElem_mem hk
  obtain ⟨hp1', hph, hK, -, hcm, hcK, hHl, -, hrow⟩ := hQ.opens o ho
  obtain ⟨f1, -, -⟩ := open_factsB hin hinj hN hz hk hko hph hK hcm hcK
    (hx_hn (Nat.pow_le_pow_right (by decide) (Nat.sub_le _ _)) hHl hNs) hq1 hq2
  obtain ⟨-, -, f3⟩ := f1 jj hjj
  have fl := (f1 jj hjj).1
  have hal := opens_alB' (p := p) hQ.cp hQ.lvIdx ho hp1'
  have h2 := opens_i0 p ho
  have hEL : eLane p i = eLane p o.i0 + posStride o.L * jj + slotOff o.L y := by
    rw [hieq, (eLane_openB hS hal h2).1 jj hjj y (hx_ylt hy), Nat.mul_comm]
  have hi1 : 1 ≤ i := by rw [hieq]; exact hx_pos' h2
  have hin_ := lanes_inB hS hi1 hi
  have hbits : ∀ z < o.L.height, M.k (bitBase p lay k + o.L.height * jj + z) =
      if ansBit p ws (o.pe + jj / 8) (jj % 8 * o.L.height + z) then 1 else 0 := by
    intro z hz
    have := hin.bits k hk jj (by rw [hko]; exact hjj) z (by rw [hko]; exact hz)
    rw [hko] at this; exact this
  refine ⟨?_, ?_⟩
  · by_cases hy0 : y = 0
    · subst hy0
      rw [hpe, if_pos rfl]
      rw [hpe, if_pos rfl] at hin_
      refine LV _ _ (hx_lt0 hin_ hT) hrow ?_
      rw [hEL, show slotOff o.L 0 = 0 from if_pos rfl, Nat.add_zero, ← Nat.add_assoc]
      exact fl
    · rw [hpe, if_neg hy0]
      rw [hpe, if_neg hy0] at hin_
      have := (f3 (y - 1) (hx_ym1 hy hy0)).1
      rw [Nat.sub_add_cancel (Nat.pos_iff_ne_zero.mpr hy0)] at this
      refine LV _ _ (hx_lt0 hin_ hT) (show 64 < 2 ^ 64 by decide) ?_
      rw [hEL]; simp only [Nat.add_assoc] at this ⊢; exact this
  · intro hy0 l hl
    have e := (f3 (y - 1) (hx_ym1 hy hy0)).2 l hl
    rw [Nat.sub_add_cancel (Nat.pos_iff_ne_zero.mpr hy0)] at e
    have hs5 : 5 ≤ slotOff o.L y := by
      simp only [slotOff, if_neg hy0]; exact Nat.le_trans (Nat.le_add_right 5 _) (Nat.le_add_right _ _)
    have hb := hbits (y - 1) (Nat.lt_trans (hx_ym1 hy hy0) hph)
    rw [hpe, if_neg hy0] at hin_
    have h13 : eLane p i + 13 ≤ hashedLen p / 8 := hx_13 hin_
    by_cases hab : ansBit p ws (o.pe + jj / 8) (jj % 8 * o.L.height + (y - 1)) = true
    · rw [if_pos hab] at hb ⊢; rw [if_pos hb] at e
      refine (LE _ _ (hx_em4 h13 hT hl) (hx_ed h13 hT hl (by decide)) ?_).symm
      rw [hx_rm4 hEL hs5, hx_rp hEL]
      exact e
    · rw [if_neg hab] at hb ⊢; rw [hb, if_neg fk01] at e
      refine (LE _ _ (hx_em4 h13 hT hl) (hx_ed h13 hT hl (by decide)) ?_).symm
      rw [hx_rm4 hEL hs5, hx_rp hEL]
      exact e

/-- **A heap entry of an opening at S2GB**: its length lane is 64; a bottom slot's halves are the tops of the paths
its top bits select, an inner slot's halves its children's answers, a cap slot's answer the sent cap's node. -/
theorem heap_entryB (hS : StreamOkB p) (hQ : QOkB p lay) (hin : QIn p lay ws M)
    {N : Nat} (hinj : GInj N) (hN : c.cells .K ≤ N) (hNs : lay.sb + 2 ^ lay.m ≤ N)
    {zo : Nat} (hz : ∀ x < 2 ^ lay.K, M.k (zo + x) = 1)
    {k : Nat} (hk : k < (opens p).length) {o : OpenInfo} (hko : (opens p).getD k default = o) {q : Ptr}
    (hq1 : SegsHold c M q (openLoopsB p lay zo (bitBase p lay k) o q).2)
    (hq2 : SegsAssert M q (openLoopsB p lay zo (bitBase p lay k) o q).2)
    {n : Nat} (hn : n < 2 ^ o.L.cap - 2 ^ p.capSendBits o.L.level o.L.cap) {i : Nat}
    (hieq : i = o.i0 + o.L.t * (1 + o.L.path) + n) :
      lw ws (eLane p i) = 64 ∧
      (2 ^ (o.L.cap - 1) ≤ 2 ^ o.L.cap - 1 - n → ∀ b < 2, ∀ j < o.L.t,
        posL p ws (o.pe + j / 8) (j % 8 * o.L.height + o.L.path) (o.L.height - o.L.path) =
          2 * (2 ^ o.L.cap - 1 - n - 2 ^ (o.L.cap - 1)) + b →
        ∀ l < 4, lw ws (eLane p i + 1 + 4 * b + l) = lw ws (ansLane p (o.i0 + j * (1 + o.L.path) + o.L.path) + l)) ∧
      (2 ^ o.L.cap - 1 - n < 2 ^ (o.L.cap - 1) → ∀ l < 4,
        lw ws (eLane p i + 1 + l) = lw ws (ansLane p (o.i0 + o.L.t * (1 + o.L.path) +
          (2 ^ o.L.cap - 1 - 2 * (2 ^ o.L.cap - 1 - n))) + l) ∧
        lw ws (eLane p i + 5 + l) = lw ws (ansLane p (o.i0 + o.L.t * (1 + o.L.path) +
          (2 ^ o.L.cap - 1 - (2 * (2 ^ o.L.cap - 1 - n) + 1))) + l)) ∧
      (2 ^ o.L.cap - 1 - n < 2 ^ (p.capSendBits o.L.level o.L.cap + 1) → ∀ l < 4,
        lw ws (ansLane p i + l) = lw ws (eLane p o.ce + 1 + o.co / 8 +
          4 * (2 ^ o.L.cap - 1 - n - 2 ^ p.capSendBits o.L.level o.L.cap) + l)) := by
  have hT := hQ.hT
  have LE : ∀ a b, a < 2 ^ lay.m → b < 2 ^ lay.m → M.k (lay.sb + a) = M.k (lay.sb + b) → lw ws a = lw ws b :=
    fun a b ha hb e => lw_of_laneK (by rw [← hin.stream a ha, ← hin.stream b hb, e])
  have LV : ∀ a v, a < 2 ^ lay.m → v < 2 ^ 64 → M.k (lay.sb + a) = kOf v → lw ws a = v :=
    fun a v ha hv e => lw_of_kOf hv (by rw [← hin.stream a ha, e])
  have AL : ∀ x, 1 ≤ x → ((plan p).getD x default).len = 64 → ansLane p x = eLane p x + 9 := by
    intro x h1 hl
    simp only [ansLane, if_neg (Nat.pos_iff_ne_zero.mp h1), hl]
  have ho : o ∈ opens p := by
    rw [← hko, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk]; exact List.getElem_mem hk
  obtain ⟨hp1', hph, hK, hcapm, hcm, hcK, hHl, hcapL, hrow⟩ := hQ.opens o ho
  obtain ⟨f1, f2, f3⟩ := open_factsB hin hinj hN hz hk hko hph hK hcm hcK
    (hx_hn (Nat.pow_le_pow_right (by decide) (Nat.sub_le _ _)) hHl hNs) hq1 hq2
  have hbits : ∀ jj < o.L.t, ∀ z < o.L.height, M.k (bitBase p lay k + o.L.height * jj + z) =
      if ansBit p ws (o.pe + jj / 8) (jj % 8 * o.L.height + z) then 1 else 0 := by
    intro jj hjj z hz
    have := hin.bits k hk jj (by rw [hko]; exact hjj) z (by rw [hko]; exact hz)
    rw [hko] at this; exact this
  have hal := opens_alB' (p := p) hQ.cp hQ.lvIdx ho hp1'
  have h2 := opens_i0 p ho
  obtain ⟨lenP, lenH⟩ := openB_len hal
  have eLP := (eLane_openB hS hal h2).1
  have eLH := (eLane_openB hS hal h2).2
  have hlen := hal.1
  rw [openPlanB_length] at hlen
  rw [← hcapm] at hcm hHl f1 f2 f3 ⊢
  have hch : o.L.cap + o.L.path = o.L.height := by rw [hcapm]; exact Nat.sub_add_cancel hph.le
  -- the heap's arithmetic on fresh variables: `A = 2^m`, `H = 2^(m−1)`, `C = 2^c`, `ks = A − 1 − n`
  obtain ⟨A, hA⟩ : ∃ A, 2 ^ o.L.cap = A := ⟨_, rfl⟩
  obtain ⟨H, hH⟩ : ∃ H, 2 ^ (o.L.cap - 1) = H := ⟨_, rfl⟩
  obtain ⟨C, hC⟩ : ∃ C, 2 ^ p.capSendBits o.L.level o.L.cap = C := ⟨_, rfl⟩
  have hAH : A = 2 * H := by
    rw [← hA, ← hH, ← Nat.pow_succ']; exact congrArg (fun x => 2 ^ x) (hx_c1 hcm)
  have hC1 : 2 ^ (p.capSendBits o.L.level o.L.cap + 1) = 2 * C := by rw [Nat.pow_succ', hC]
  have hCA : 2 * C ≤ A := by rw [← hC1, ← hA]; exact Nat.pow_le_pow_right (by decide) hcm
  rw [hA] at hHl
  rw [hC] at hcapL
  rw [hA, hC] at hn hlen eLH lenH
  rw [hH] at f1 f2; rw [hC] at f2 f3
  rw [hA, hH, hC1, hC]
  obtain ⟨ks, hks⟩ : ∃ ks, A - 1 - n = ks := ⟨_, rfl⟩
  rw [hks]
  obtain ⟨hnk, hCk, hnA⟩ := hx_idx hn hks
  have hlen' := hx_len' hlen hCA
  have hEL : eLane p i = heapLane p o + 13 * n := by rw [hieq]; exact eLH n (hx_le hnk hCk).1.le
  have hHc : ∀ kk nn j, nn + kk + 1 = A → C ≤ kk → hcell (lay.sb + heapLane p o) o.L.cap kk j =
      lay.sb + (eLane p (o.i0 + o.L.t * (1 + o.L.path) + nn) + j) := by
    intro kk nn j h1 h2
    rw [eLH nn (hx_le h1 h2).1.le]
    simp only [hcell]; rw [hA, hx_sub h1]; simp only [Nat.add_assoc]
  have hi1 : 1 ≤ i := by rw [hieq]; exact hx_pos' h2
  have hcellI : ∀ j, hcell (lay.sb + heapLane p o) o.L.cap ks j = lay.sb + (eLane p i + j) := by
    intro j; rw [hHc ks n j hnk hCk, ← hieq]
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- the length lane
    by_cases hk2 : ks < 2 * C
    · obtain ⟨hv1, hv2⟩ := hx_cap hCk hk2
      obtain ⟨g1, -⟩ := f3 (ks - C) hv1
      rw [hv2, hcellI, Nat.add_zero] at g1
      exact LV _ _ (hx_slot0 hEL hnA hHl) (by decide) g1
    · obtain ⟨hh1, hh2⟩ := hx_len hAH hnk hCk hk2
      obtain ⟨-, g1, g2⟩ := f2 (ks / 2) hh1 hh2
      rcases hx_par ks with hw | hw
      · rw [hw, hcellI, Nat.add_zero] at g1
        exact LV _ _ (hx_slot0 hEL hnA hHl) (by decide) g1
      · rw [hw, hcellI, Nat.add_zero] at g2
        exact LV _ _ (hx_slot0 hEL hnA hHl) (by decide) g2
  · -- a bottom slot: its halves are the paths' tops
    intro hbot b hb j hj hpos l hl
    obtain ⟨-, ftop, -⟩ := f1 j hj
    have e := ftop l hl
    have hbs : bitSum M (bitBase p lay k + o.L.height * j + o.L.path) [] [] o.L.cap =
        posL p ws (o.pe + j / 8) (j % 8 * o.L.height + o.L.path) o.L.cap :=
      bitSum_posL fun z hz => by
        have := hbits j hj (o.L.path + z) (hx_add_lt hz hch)
        simpa only [Nat.add_assoc] using this
    obtain ⟨d1, d2, d3⟩ := hx_bot hbot hb
    rw [hbs, hpos, d1, d2, d3, hcellI] at e
    have hjx := hx_jx (P := o.L.path) hj
    have hlt := lenP j hj o.L.path (hx_lt1 _)
    rw [if_neg (Nat.pos_iff_ne_zero.mp hp1')] at hlt
    have hEt := eLP j hj o.L.path le_rfl
    have hin_ := lanes_inB hS (i := o.i0 + j * (1 + o.L.path) + o.L.path) (hx_pos' h2) (hx_plen hjx hlen' hCA)
    rw [hlt] at hin_
    rw [AL _ (hx_pos' h2) hlt]
    refine LE _ _ (hx_slotB hEL hnA hHl hb hl) (hx_tail hin_ hT hl) ?_
    rw [hx_re4, ← e, hEt, Nat.mul_comm j]
    simp only [Nat.add_assoc]
  · -- an inner slot: its halves are its children's answers
    intro hinr l hl
    obtain ⟨g, -, -⟩ := f2 ks hCk hinr
    obtain ⟨g1, g2⟩ := g l hl
    obtain ⟨e1, e2⟩ := hx_kids hAH hinr
    obtain ⟨c1, c2⟩ := hx_half hCk
    rw [hcellI, hHc _ _ _ e1 c1] at g1
    rw [hcellI, hHc _ _ _ e2 c2] at g2
    obtain ⟨l1, l1'⟩ := hx_le e1 c1
    obtain ⟨l2, l2'⟩ := hx_le e2 c2
    have hE1 := eLH _ l1.le
    have hE2 := eLH _ l2.le
    rw [AL _ (hx_pos' h2) (lenH _ l1), AL _ (hx_pos' h2) (lenH _ l2)]
    refine ⟨LE _ _ (hx_slot1 hEL hnA hHl hl) (hx_slot9 hE1 l1' hHl hl) ?_,
      LE _ _ (hx_slot5 hEL hnA hHl hl) (hx_slot9 hE2 l2' hHl hl) ?_⟩
    · rw [Nat.add_assoc (eLane p i) 1 l, Nat.add_assoc _ 9 l]; exact g1
    · rw [Nat.add_assoc (eLane p i) 5 l, Nat.add_assoc _ 9 l]; exact g2
  · -- a cap slot: its answer is the sent cap's node
    intro hcp l hl
    obtain ⟨hv1, hv2⟩ := hx_cap hCk hcp
    obtain ⟨-, g⟩ := f3 _ hv1
    have e := g l hl
    rw [hv2, hcellI] at e
    rw [AL _ hi1 (by rw [hieq]; exact lenH n hn)]
    refine LE _ _ (hx_slot9 hEL hnA hHl hl) (hx_capb hcapL hv1 hl) ?_
    rw [Nat.add_assoc (eLane p i) 9 l, e]
    simp only [Nat.add_assoc]


attribute [local irreducible] Lvm.schedule in
/-- **Q_link's checks after the position cells at S2GB** (`qlinkCore_sound`'s twin). -/
theorem qlinkCoreB_sound (hS : StreamOkB p) (hQ : QOkB p lay) (hin : QIn p lay ws M) (hws : 2 ^ lay.m ≤ ws.length)
    {N : Nat} (hinj : GInj N) (hN : c.cells .K ≤ N) (hNs : lay.sb + 2 ^ lay.m ≤ N) {pt : Ptr}
    (h : SegsHold c M pt (qlinkCoreB p lay pt).2) (hA : SegsAssert M pt (qlinkCoreB p lay pt).2) :
    LaneLinkB p ws ∧ PadOkB (wordsBytes ws) (hashedLen p) := by
  simp only [qlinkCoreB] at h hA
  rw [hold_bind] at h; rw [assert_bind] at hA
  obtain ⟨hz1, -⟩ := stepArr_spec h.1
  have hz : ∀ x < 2 ^ lay.K, M.k (pt.k + x) = 1 := fun x hx => by rw [hz1 x hx, hin.flag]
  have h2 := h.2; have hA2 := hA.2
  rw [stepArr_apply] at h2 hA2
  rw [hold_bind] at h2; rw [assert_bind] at hA2
  have QE : ∀ a b v, (a, b, v) ∈ qltEntries p lay → M.k a = kOf v ∧ ∀ l < 4, M.k (a + 1 + l) = M.k (b + l) :=
    fun a b v he => qlt_entryB hQ hin hinj hN hNs h2.1 hA2.1 he
  have QB : ∀ a b v, (a, b, v) ∈ qltEntries p lay → lay.sb ≤ a ∧ lay.sb ≤ b ∧ a + 5 ≤ lay.sb + 2 ^ lay.m ∧
      b + 4 ≤ lay.sb + 2 ^ lay.m ∧ v < 2 ^ 64 := fun a b v he => hQ.qbound _ he
  have h3 := h2.2; have hA3 := hA2.2
  rw [hold_bind] at h3; rw [assert_bind] at hA3
  have hopk : ∀ k, k < (opens p).length → ∀ o, (opens p).getD k default = o →
      ∃ q, SegsHold c M q (openLoopsB p lay pt.k (bitBase p lay k) o q).2 ∧
        SegsAssert M q (openLoopsB p lay pt.k (bitBase p lay k) o q).2 := by
    intro k hk o hko
    obtain ⟨q, hq1, hq2⟩ := seqAll_both _ _ h3.1 hA3.1 _ (List.mem_map_of_mem (List.mem_range.mpr hk))
    subst hko
    exact ⟨q, hq1, hq2⟩
  -- stream lanes
  have hT := hQ.hT
  have hL8 : hashedLen p % 8 = 0 := by
    have := bOff_modB hS.1 (plan p).length (by have := plan_length_ge p; omega) le_rfl
    rw [bOff_end, ← hS.2] at this; exact this
  have LE : ∀ a b, a < 2 ^ lay.m → b < 2 ^ lay.m → M.k (lay.sb + a) = M.k (lay.sb + b) → lw ws a = lw ws b :=
    fun a b ha hb e => lw_of_laneK (by rw [← hin.stream a ha, ← hin.stream b hb, e])
  have LV : ∀ a v, a < 2 ^ lay.m → v < 2 ^ 64 → M.k (lay.sb + a) = kOf v → lw ws a = v :=
    fun a v ha hv e => lw_of_kOf hv (by rw [← hin.stream a ha, e])
  -- FS entries are QLT entries
  have FSM : ∀ i, i < (plan p).length → ∀ st, ((plan p).getD i default).k = .fs st →
      (lay.sb + eLane p i, lay.sb + ansLane p st, ((plan p).getD i default).len) ∈ qltEntries p lay := by
    intro i hi st hk
    have hgi : (plan p).getD i default = (plan p)[i] := by
      simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]
    rw [hgi] at hk ⊢
    apply List.mem_append_left; apply List.mem_append_right
    rw [List.mem_filterMap]
    exact ⟨((plan p)[i], i), List.mem_zipIdx_iff_getElem?.mpr (by simp [List.getElem?_eq_getElem hi]),
      by simp only [hk]⟩
  have hp1 : ∀ o ∈ opens p, 1 ≤ o.L.path := fun o ho => (hQ.opens o ho).1
  have memk : ∀ k, k < (opens p).length → ∀ o, (opens p).getD k default = o → o ∈ opens p := by
    intro k hk o hko
    rw [← hko, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk]; exact List.getElem_mem hk
  have AL : ∀ x, 1 ≤ x → ((plan p).getD x default).len = 64 → ansLane p x = eLane p x + 9 := by
    intro x h1 hl
    simp only [ansLane, if_neg (show x ≠ 0 by omega), hl]
  -- the constant lanes
  have m0 : (lay.sb, lay.sb + 1, lane0C) ∈ qltEntries p lay :=
    List.mem_append_left _ (List.mem_append_left _ (by simp))
  have m1 : (lay.sb + 1, lay.sb + 2, lane1C) ∈ qltEntries p lay :=
    List.mem_append_left _ (List.mem_append_left _ (by simp))
  have POS := fun {i : Nat} (hi : i < (plan p).length) (he : ((plan p).getD i default).k.isOpenB = true) =>
    open_posB hQ.cp hQ.lvIdx hp1 hi he
  refine ⟨⟨⟨by omega, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_⟩, ?_⟩
  · obtain ⟨-, -, b3, -, b5⟩ := QB _ _ _ m0
    exact LV 0 _ (by omega) b5 (by simpa using (QE _ _ _ m0).1)
  · obtain ⟨-, -, b3, -, b5⟩ := QB _ _ _ m1
    exact LV 1 _ (by omega) b5 (QE _ _ _ m1).1
  · -- the length lanes
    intro i h1 hi
    cases hk : ((plan p).getD i default).k with
    | q0 =>
      have := streamOkB_entry hS.1 hi
      simp only [entryOkB, entryOk, hk] at this
      simp at this; omega
    | fs st =>
      have hm := FSM i hi st hk
      obtain ⟨-, -, b3, -, b5⟩ := QB _ _ _ hm
      exact LV _ _ (by omega) b5 (QE _ _ _ hm).1
    | leaf =>
      obtain ⟨k, hk', o, hko, ⟨jj, y, hjj, hy, hieq, hpe⟩ | ⟨n, hn, hieq, hpe⟩⟩ := POS hi (by rw [hk]; rfl)
      · obtain ⟨q, hq1, hq2⟩ := hopk k hk' o hko
        exact (open_entryB hS hQ hin hinj hN hNs hz hk' hko hq1 hq2 hjj hy hieq hi hpe).1
      · rw [hpe] at hk; simp at hk
    | node pe h j lvl cap =>
      obtain ⟨k, hk', o, hko, ⟨jj, y, hjj, hy, hieq, hpe⟩ | ⟨n, hn, hieq, hpe⟩⟩ := POS hi (by rw [hk]; rfl)
      · obtain ⟨q, hq1, hq2⟩ := hopk k hk' o hko
        exact (open_entryB hS hQ hin hinj hN hNs hz hk' hko hq1 hq2 hjj hy hieq hi hpe).1
      · rw [hpe] at hk; simp at hk
    | heap pe h t path i0 m k cap =>
      obtain ⟨k, hk', o, hko, ⟨jj, y, hjj, hy, hieq, hpe⟩ | ⟨n, hn, hieq, hpe⟩⟩ := POS hi (by rw [hk]; rfl)
      · rw [hpe] at hk; by_cases hy0 : y = 0 <;> simp [hy0] at hk
      · obtain ⟨q, hq1, hq2⟩ := hopk k hk' o hko
        rw [(heap_entryB hS hQ hin hinj hN hNs hz hk' hko hq1 hq2 hn hieq).1, hpe]
  · -- FS queries
    intro i hi st hk l hl
    have hm := FSM i hi st hk
    obtain ⟨-, -, b3, b4, -⟩ := QB _ _ _ hm
    have e := (QE _ _ _ hm).2 l hl
    refine LE _ _ (by omega) (by omega) ?_
    rw [show lay.sb + (eLane p i + 1 + l) = lay.sb + eLane p i + 1 + l by omega,
      show lay.sb + (ansLane p st + l) = lay.sb + ansLane p st + l by omega]
    exact e
  · -- node queries
    intro i hi pe h j lvl cap hk l hl
    obtain ⟨k, hk', o, hko, ⟨jj, y, hjj, hy, hieq, hpe⟩ | ⟨n, hn, hieq, hpe⟩⟩ := POS hi (by rw [hk]; rfl)
    · obtain ⟨q, hq1, hq2⟩ := hopk k hk' o hko
      have hnode := (open_entryB hS hQ hin hinj hN hNs hz hk' hko hq1 hq2 hjj hy hieq hi hpe).2
      rw [hpe] at hk
      by_cases hy0 : y = 0
      · rw [if_pos hy0] at hk; cases hk
      · rw [if_neg hy0] at hk
        simp only [EK.node.injEq] at hk
        obtain ⟨rfl, rfl, rfl, rfl, -⟩ := hk
        exact hnode hy0 l hl
    · rw [hpe] at hk; simp at hk
  · -- no node query carries a cap at S2GB
    intro i hi pe h j lvl ce co path hk
    obtain ⟨k, hk', o, hko, ⟨jj, y, hjj, hy, hieq, hpe⟩ | ⟨n, hn, hieq, hpe⟩⟩ := POS hi (by rw [hk]; rfl)
    · rw [hpe] at hk; by_cases hy0 : y = 0 <;> simp [hy0] at hk
    · rw [hpe] at hk; simp at hk
  · -- bottom heap slots
    intro i hi pe h t path i0 m k cap hk hkm b hb j hj hpos l hl
    obtain ⟨kk, hk', o, hko, ⟨jj, y, hjj, hy, hieq, hpe⟩ | ⟨n, hn, hieq, hpe⟩⟩ := POS hi (by rw [hk]; rfl)
    · rw [hpe] at hk; by_cases hy0 : y = 0 <;> simp [hy0] at hk
    · rw [hpe] at hk
      obtain ⟨q, hq1, hq2⟩ := hopk kk hk' o hko
      simp only [EK.heap.injEq] at hk
      obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, -⟩ := hk
      exact (heap_entryB hS hQ hin hinj hN hNs hz hk' hko hq1 hq2 hn hieq).2.1 hkm b hb j hj hpos l hl
  · -- inner heap slots
    intro i hi pe h t path i0 m k cap hk hkm l hl
    obtain ⟨kk, hk', o, hko, ⟨jj, y, hjj, hy, hieq, hpe⟩ | ⟨n, hn, hieq, hpe⟩⟩ := POS hi (by rw [hk]; rfl)
    · rw [hpe] at hk; by_cases hy0 : y = 0 <;> simp [hy0] at hk
    · rw [hpe] at hk
      obtain ⟨q, hq1, hq2⟩ := hopk kk hk' o hko
      simp only [EK.heap.injEq] at hk
      obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, -⟩ := hk
      exact (heap_entryB hS hQ hin hinj hN hNs hz hk' hko hq1 hq2 hn hieq).2.2.1 hkm l hl
  · -- cap heap slots
    intro i hi pe h t path i0 m k ce co cc hk l hl
    obtain ⟨kk, hk', o, hko, ⟨jj, y, hjj, hy, hieq, hpe⟩ | ⟨n, hn, hieq, hpe⟩⟩ := POS hi (by rw [hk]; rfl)
    · rw [hpe] at hk; by_cases hy0 : y = 0 <;> simp [hy0] at hk
    · rw [hpe] at hk
      obtain ⟨q, hq1, hq2⟩ := hopk kk hk' o hko
      simp only [EK.heap.injEq] at hk
      obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, hc⟩ := hk
      by_cases hcc : 2 ^ o.L.cap - 1 - n < 2 ^ (p.capSendBits o.L.level o.L.cap + 1)
      · rw [if_pos hcc] at hc
        simp only [Option.some.injEq, Prod.mk.injEq] at hc
        obtain ⟨rfl, rfl, rfl⟩ := hc
        exact (heap_entryB hS hQ hin hinj hN hNs hz hk' hko hq1 hq2 hn hieq).2.2.2 hcc l hl
      · rw [if_neg hcc] at hc; cases hc
  · -- the padding
    intro q hq1 hq2
    have hk : q / 8 - hashedLen p / 8 < 17 * nBlk (hashedLen p) - hashedLen p / 8 := by omega
    have hm : (lay.sb + q / 8, lay.sb + q / 8 + 1, padLane (hashedLen p) (q / 8)) ∈ qltEntries p lay := by
      apply List.mem_append_right
      rw [List.mem_map]
      exact ⟨q / 8 - hashedLen p / 8, List.mem_range.mpr hk, by
        simp only [show hashedLen p / 8 + (q / 8 - hashedLen p / 8) = q / 8 by omega]⟩
    obtain ⟨-, -, b3, -, b5⟩ := QB _ _ _ hm
    have hv := LV _ _ (by omega) b5 (QE _ _ _ hm).1
    have hb := byte_of_lane ws (q / 8) (q % 8) (by omega)
    rw [show 8 * (q / 8) + q % 8 = q by omega, hv, padLane_byte _ _ _ (by omega),
      show 8 * (q / 8) + q % 8 = q by omega] at hb
    exact hb

/-- **Q_link at S2GB is sound**: its rows and assertions, with its inputs where the layout says, make the stream meet
every lane condition of the S2GB schedule (paths, heap, cap), and pin the trace sponge's padding. -/
theorem qlinkB_sound (hS : StreamOkB p) (hQ : QOkB p lay) (hin : QIn p lay ws M) (hws : 2 ^ lay.m ≤ ws.length)
    {N : Nat} (hinj : GInj N) (hN : c.cells .K ≤ N) (hNs : lay.sb + 2 ^ lay.m ≤ N) {pt : Ptr}
    (h : SegsHold c M pt (qlinkB p lay pt).2) (hA : SegsAssert M pt (qlinkB p lay pt).2) :
    LaneLinkB p ws ∧ PadOkB (wordsBytes ws) (hashedLen p) := by
  simp only [qlinkB] at h hA
  rw [hold_bind] at h; rw [assert_bind] at hA
  exact qlinkCoreB_sound hS hQ hin hws hinj hN hNs h.2 hA.2

end

end Lvm.QLink
