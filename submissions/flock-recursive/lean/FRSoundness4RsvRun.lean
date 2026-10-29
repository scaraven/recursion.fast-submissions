-- New for `flock-recursive` (revision 4.4.2, the reserve; track RSV-S2a): generic run lemmas for the
-- reserve's op blocks (`rsvEOps`, `rsvSOps`, `rsvBOps`), so that `finE`'s and `finB′`'s flags are
-- proved block by block instead of by one `simp` over the whole field.
import FRVerifierC4

/-!
# Runs of op blocks built from `List.range`

* `pureRun_mapRange`: `n` ops, op `i` with one output `v i` and a true flag, each read from a fixed
  base and the outputs before it;
* `run_rsvSOps`: `finE`'s coefficient block `rsvSOps` (36 ops, generic in its registers);
* `run_rsvHorner`, `hornerV_eq_sum`: `finB′`'s Horner chain (`rsvBOps`' first `2n` ops) and its value
  `Σ_{i ≤ n} κ^i w_{N - n + i}`;
* `rd_appAt`: a read at an offset given by an equation (the blocks' bases are `c + k`, not
  `r.size + k`).
-/

namespace FR.Snd.R4
open RecursionFast Rev4

/-- A read at `x ≥ n = R.size` of `R ++ L`. -/
theorem rd_appAt (R : Array Val) (L : List Val) {n : ℕ} (hR : R.size = n) {x : ℕ} (hx : n ≤ x) :
    rd (R ++ L.toArray) x = L.getD (x - n) default := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hx
  subst hR
  rw [Nat.add_sub_cancel_left]
  exact rd_app R L k

section Gen
variable (impl : OpImpl) (κ : Kind) (inp : Input)

/-- **`n` one-output ops**: op `i` gives `v i` with a true flag on any registers extending
`R ++ M` (it reads the base and the outputs before it). -/
theorem pureRun_mapRange (R : Array Val) (g : ℕ → Op) (v : ℕ → Val) (M : List Val) :
    ∀ n, (∀ i < n, ∀ L : List Val, evalOp impl κ inp (R ++ (M ++ L).toArray) (g i) = .vals [v i] true) →
    pureRun impl κ inp ((List.range n).map g) R M = some (M ++ (List.range n).map v, true)
  | 0, _ => by simp [pureRun]
  | n + 1, h => by
    rw [List.range_succ, List.map_append, pureRun_append,
      pureRun_mapRange R g v M n (fun i hi => h i (by omega)), Option.bind_some]
    simp only [List.map_cons, List.map_nil, pureRun]
    rw [h n (by omega) ((List.range n).map v)]
    simp

/-- The reads of a `List.range` map (`getD` at `i < n`). -/
theorem getD_mapRange {α : Type} (v : ℕ → α) (d : α) {n i : ℕ} (hi : i < n) :
    ((List.range n).map v).getD i d = v i := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hi]; rfl

theorem getD_take' {α : Type} (l : List α) (d : α) {n i : ℕ} (hi : i < n) :
    (l.take n).getD i d = l.getD i d := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_take_of_lt hi]

theorem length_mapRange {α : Type} (v : ℕ → α) (n : ℕ) : ((List.range n).map v).length = n := by simp

/-- **`rsvSOps`** (`finE`'s nine coefficients `s^P`, 36 ops), generic in its registers: from a base
`R` of size `d` holding the indicator values `I`, the three `T`, `W`, `O` and the nine `Sv`, the four
blocks give `I(i/3)·T(i%3)`, `W·Sv i`, their sums and `O·` the sums. -/
theorem run_rsvSOps (R : Array Val) (d : ℕ) (hR : R.size = d) (ind t : ℕ → Reg) (w one : Reg)
    (s : ℕ → Reg) (I T Sv : ℕ → F) (W O : F)
    (hI : ∀ k < 3, ind k < d ∧ (rd R (ind k)).toF = I k) (hT : ∀ m < 3, t m < d ∧ (rd R (t m)).toF = T m)
    (hW : w < d ∧ (rd R w).toF = W) (hO : one < d ∧ (rd R one).toF = O)
    (hS : ∀ i < 9, s i < d ∧ (rd R (s i)).toF = Sv i) :
    pureRun impl κ inp (rsvSOps ind t w one s d) R [] =
      some ((List.range 9).map (fun i => Val.f (I (i / 3) * T (i % 3))) ++
        (List.range 9).map (fun i => Val.f (W * Sv i)) ++
        (List.range 9).map (fun i => Val.f (I (i / 3) * T (i % 3) + W * Sv i)) ++
        (List.range 9).map (fun i => Val.f (O * (I (i / 3) * T (i % 3) + W * Sv i))), true) := by
  have hl : ∀ (M L : List Val) (x : ℕ), x < d → rd (R ++ (M ++ L).toArray) x = rd R x :=
    fun M L x hx => rd_app_left R _ (by omega)
  have hm : ∀ (M L : List Val) (x : ℕ), d ≤ x → x - d < M.length →
      rd (R ++ (M ++ L).toArray) x = M.getD (x - d) default := fun M L x hx hk => by
    rw [rd_appAt R _ hR hx, List.getD_append _ _ _ _ hk]
  have h3 : ∀ i, i % 3 < 3 := fun i => Nat.mod_lt _ (by norm_num)
  unfold rsvSOps
  rw [pureRun_append, pureRun_append, pureRun_append]
  rw [pureRun_mapRange impl κ inp R _ (fun i => Val.f (I (i / 3) * T (i % 3))) [] 9 (fun i hi L => by
    have hi3 : i / 3 < 3 := by omega
    simp only [evalOp, hl _ _ _ (hI _ hi3).1, hl _ _ _ (hT _ (h3 i)).1, (hI _ hi3).2, (hT _ (h3 i)).2])]
  simp only [Option.bind_some, List.nil_append]
  rw [pureRun_mapRange impl κ inp R _ (fun i => Val.f (W * Sv i)) _ 9 (fun i hi L => by
    simp only [evalOp, hl _ _ _ hW.1, hl _ _ _ (hS i hi).1, hW.2, (hS i hi).2])]
  simp only [Option.map_some, Option.bind_some, Bool.and_self]
  rw [pureRun_mapRange impl κ inp R _ (fun i => Val.f (I (i / 3) * T (i % 3) + W * Sv i)) _ 9
    (fun i hi L => by
      simp only [evalOp]
      rw [hm _ _ (d + i) (by omega) (by simp; omega), hm _ _ (d + 9 + i) (by omega) (by simp; omega),
        show d + i - d = i by omega, show d + 9 + i - d = 9 + i by omega,
        List.getD_append _ _ _ _ (by simp; omega), getD_mapRange _ _ hi,
        List.getD_append_right _ _ _ _ (by simp), length_mapRange, Nat.add_sub_cancel_left,
        getD_mapRange _ _ hi]; rfl)]
  simp only [Option.map_some, Option.bind_some, Bool.and_self]
  rw [pureRun_mapRange impl κ inp R _ (fun i => Val.f (O * (I (i / 3) * T (i % 3) + W * Sv i))) _ 9
    (fun i hi L => by
      simp only [evalOp]
      rw [hl _ _ _ hO.1, hO.2, hm _ _ (d + 18 + i) (by omega) (by simp; omega),
        show d + 18 + i - d = 18 + i by omega,
        List.getD_append_right _ _ _ _ (by simp), List.length_append, length_mapRange,
        length_mapRange, show 18 + i - (9 + 9) = i by omega, getD_mapRange _ _ hi]; rfl)]
  simp only [Option.map_some, Bool.and_self, List.append_assoc]

/-- **Horner's value**: `H₀ = h₀`, `H_{k+1} = u k + κ·H_k`. -/
def hornerV (kp h0 : F) (u : ℕ → F) : ℕ → F
  | 0 => h0
  | k + 1 => u k + kp * hornerV kp h0 u k

/-- **Horner over `w_N, w_{N-1}, …`**: `H_n = Σ_{i ≤ n} κ^i w_{N - n + i}` (`n ≤ N`). -/
theorem hornerV_eq_sum (kp : F) (w : ℕ → F) (N : ℕ) :
    ∀ n ≤ N, hornerV kp (w N) (fun k => w (N - 1 - k)) n =
      ∑ i ∈ Finset.range (n + 1), kp ^ i * w (N - n + i)
  | 0, _ => by simp [hornerV]
  | n + 1, hn => by
    rw [hornerV, hornerV_eq_sum kp w N n (by omega), Finset.sum_range_succ' _ (n + 1), Finset.mul_sum]
    rw [add_comm]
    congr 1
    · refine Finset.sum_congr rfl fun i _ => ?_
      rw [pow_succ, show N - n + i = N - (n + 1) + (i + 1) by omega]; ring
    · simp only [pow_zero, one_mul, Nat.add_zero]; congr 1; omega

/-- **The Horner chain** (`rsvBOps`' first `2n` ops), generic in its registers: from a base `R` of
size `d` holding `κ` at `kp`, `h₀` at `a0` and `u k` at `src k`, step `k` writes `κ·H_k` at `d + 2k`
and `H_{k+1}` at `d + 2k + 1`. -/
theorem run_rsvHorner (R : Array Val) (d : ℕ) (hR : R.size = d) (kp a0 : Reg) (src : ℕ → Reg)
    (K0 H0 : F) (u : ℕ → F) (hkp : kp < d ∧ (rd R kp).toF = K0) (ha : a0 < d ∧ (rd R a0).toF = H0)
    (hs : ∀ k, src k < d ∧ (rd R (src k)).toF = u k) :
    ∀ n, ∃ M, pureRun impl κ inp ((List.range n).flatMap fun k =>
        [Op.mulF kp (if k = 0 then a0 else d + 2 * k - 1), Op.addF (src k) (d + 2 * k)]) R [] =
      some (M, true) ∧ M.length = 2 * n ∧
      ∀ k < n, rd (R ++ M.toArray) (d + 2 * k + 1) = .f (hornerV K0 H0 u (k + 1))
  | 0 => ⟨[], by simp [pureRun], rfl, fun k hk => absurd hk (Nat.not_lt_zero _)⟩
  | n + 1 => by
    obtain ⟨M, hM, hl, hv⟩ := run_rsvHorner R d hR kp a0 src K0 H0 u hkp ha hs n
    have hsz : (R ++ M.toArray).size = d + 2 * n := by simp [hR, hl]
    have ha1 := ha.1; have hk1 := hkp.1
    have hext : ∀ (L : List Val) x, x < d → rd (R ++ M.toArray ++ L.toArray) x = rd R x :=
      fun L x hx => by rw [rd_app_left _ _ (by rw [hsz]; omega), rd_app_left _ _ (by omega)]
    have hprev : (rd (R ++ M.toArray) (if n = 0 then a0 else d + 2 * n - 1)).toF = hornerV K0 H0 u n := by
      rcases n with _ | n
      · simp only [↓reduceIte, rd_app_left R M (show a0 < R.size from hR ▸ ha.1), hornerV]; exact ha.2
      · rw [if_neg (Nat.succ_ne_zero n), show d + 2 * (n + 1) - 1 = d + 2 * n + 1 by omega,
          hv n (by omega)]; rfl
    have hprevlt : (if n = 0 then a0 else d + 2 * n - 1) < (R ++ M.toArray).size := by
      rcases Nat.eq_zero_or_pos n with h0 | h0
      · subst h0; rw [if_pos rfl, hsz]; exact Nat.lt_of_lt_of_le ha.1 (Nat.le_add_right _ _)
      · rw [if_neg (by omega), hsz]; show (d + 2 * n - 1 : ℕ) < d + 2 * n; omega
    let x := K0 * hornerV K0 H0 u n
    have hB : pureRun impl κ inp [Op.mulF kp (if n = 0 then a0 else d + 2 * n - 1),
        Op.addF (src n) (d + 2 * n)] (R ++ M.toArray) [] =
        some ([.f x, .f (hornerV K0 H0 u (n + 1))], true) := by
      simp only [pureRun, evalOp, List.nil_append]
      rw [rd_app_left _ _ hprevlt, hprev, hext _ _ hkp.1, hkp.2, hext _ _ (hs n).1, (hs n).2,
        ← hsz, rd_app0]
      rfl
    refine ⟨M ++ [.f x, .f (hornerV K0 H0 u (n + 1))], ?_, by simp [hl]; ring, fun k hk => ?_⟩
    · rw [List.range_succ, List.flatMap_append, List.flatMap_singleton]
      exact pureRun_seq impl κ inp hM hB
    · rw [show R ++ (M ++ [Val.f x, Val.f (hornerV K0 H0 u (n + 1))]).toArray =
          R ++ M.toArray ++ [Val.f x, Val.f (hornerV K0 H0 u (n + 1))].toArray by simp [Array.append_assoc]]
      rcases Nat.lt_succ_iff_lt_or_eq.1 hk with hk | rfl
      · rw [rd_app_left _ _ (by rw [hsz]; omega), hv k hk]
      · rw [show d + 2 * k + 1 = (R ++ M.toArray).size + 1 by rw [hsz], rd_app]; rfl

end Gen

end FR.Snd.R4
