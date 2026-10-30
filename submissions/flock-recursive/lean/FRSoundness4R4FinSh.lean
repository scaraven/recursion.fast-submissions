-- G6: this module also holds the former modules `FRSoundness4RsvRun`, `FRSoundness4R4Fin`, `FRSoundness4R4FinLc`, `FRSoundness4R4FinRS` (one section each, in import order).
import FRVerifierC4

section G6_FRSoundness4RsvRun

-- New for `flock-recursive` (revision 4.4.2, the reserve; track RSV-S2a): generic run lemmas for the
-- reserve's op blocks (`rsvEOps`, `rsvSOps`, `rsvBOps`), so that `finE`'s and `finB′`'s flags are
-- proved block by block instead of by one `simp` over the whole field.

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

end G6_FRSoundness4RsvRun

section G6_FRSoundness4R4Fin

-- New for `flock-recursive` (BLUEPRINT revision 4.1, A.9; stage R4c).

/-!
# The finals' flags at `FinP` on the relocated ops (Z, Lr, E, B′)

`finOps4 P` runs `finalsOf P`'s fields relocated to `P.S`'s format (`reloc P.S`): a read of field
`f < 19` at offset `o` becomes the absolute read `fieldOffOf P.S f + o` (`evalOp_reloc`). Each lemma
here is 3.x's `flag_fin*` (`FRVIRFinals`, `FRVIRFinalsSF`) at `P`'s sizes: the relation is 3.x's
with the sizes (`P.S.z3`, `P.lrR`, `P.e2R`, `P.e4R`), the kind tables (`P.kv.m`, `P.kv.node`) and
the proof reads (`pe4 P.S`) made parameters. At 3.x's parameters each is 3.x's relation
(`relZ4_fin3P`, …: the controls).
-/

namespace FR.Snd.R4
open RecursionFast Rev4

/-! ## Relocated reads -/

/-- The F element at byte `o` of field `f` in `S`'s format. -/
def pe4 (S : Seq) (inp : Input) (f o : ℕ) : F := F.ofBytes (bytesAt inp.π (fieldOffOf S f + o) 16)

section Reloc
variable (impl : OpImpl) (κ : Kind) (inp : Input) (regs : Array Val) (S : Seq)

/-- **A relocated read** of field `f < 19` reads `fieldOffOf S f + o` absolutely. -/
theorem evalOp_reloc {f : ℕ} (hf : f < 19) (o len k : ℕ) :
    evalOp impl κ inp regs (reloc S (.piField f o len)) =
      .vals [.b (inp.π.extract (fieldOffOf S f + o) (fieldOffOf S f + o + len))] true ∧
    evalOp impl κ inp regs (reloc S (.piElem f o)) = .vals [.f (pe4 S inp f o)] true ∧
    evalOp impl κ inp regs (reloc S (.piElemK f o)) =
      .vals [.k (K.ofBytes (bytesAt inp.π (fieldOffOf S f + o) 32))] true ∧
    evalOp impl κ inp regs (reloc S (.piDigest f o)) = .vals [.d (digestAt inp.π (fieldOffOf S f + o))] true ∧
    evalOp impl κ inp regs (reloc S (.piDigestAt f o k)) =
      .vals [.d (digestAt inp.π (fieldOffOf S f + o + 32 * (rd regs k).toN))] true := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> simp only [reloc, hf, ite_true, evalOp, absOff_zero, pe4]

/-- `reloc` on a read of field `f < 19` (the simp form). -/
theorem reloc_piElem {f : ℕ} (hf : f < 19) (o : ℕ) :
    reloc S (.piElem f o) = .piElem 0 (fieldOffOf S f + o) := if_pos hf
theorem reloc_piField {f : ℕ} (hf : f < 19) (o len : ℕ) :
    reloc S (.piField f o len) = .piField 0 (fieldOffOf S f + o) len := if_pos hf
theorem reloc_piDigest {f : ℕ} (hf : f < 19) (o : ℕ) :
    reloc S (.piDigest f o) = .piDigest 0 (fieldOffOf S f + o) := if_pos hf

theorem evalOp_piElem0 (x : ℕ) :
    evalOp impl κ inp regs (.piElem 0 x) = .vals [.f (F.ofBytes (bytesAt inp.π x 16))] true := by
  simp only [evalOp, absOff_zero]
theorem evalOp_piField0 (x len : ℕ) :
    evalOp impl κ inp regs (.piField 0 x len) = .vals [.b (inp.π.extract x (x + len))] true := by
  simp only [evalOp, absOff_zero]
theorem evalOp_piDigest0 (x : ℕ) :
    evalOp impl κ inp regs (.piDigest 0 x) = .vals [.d (digestAt inp.π x)] true := by
  simp only [evalOp, absOff_zero]

end Reloc

/-! ## Running the flags on a reversed accumulator

`pureRun` appends each op's outputs to its accumulator, `L ++ vs`. A `simp` that keeps `L` as one
list literal pays `List.cons_append` over the whole of `L` at every op, and `List.getD_cons_succ`
up to the read at every read: quadratic in the program's length (G3 §3). The flag proofs below
keep the accumulator as `M.reverse` (`M` the outputs, newest first): an op's output is consed onto
`M` (`revAcc_app_cons`), and a read is one lookup in the literal `default :: M` (`rd_revAcc`, by
`Array.reduceGetElem?`) at the distance back from the newest output. -/

/-- Entry `k` of `M.reverse` is entry `M.length - k` of `default :: M`; the `default` stands for
every read past the end. -/
theorem getD_revAcc (M : List Val) (k : ℕ) :
    M.reverse.getD k default = (((default : Val) :: M).toArray[M.length - k]?).getD default := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_toArray]
  rcases Nat.lt_or_ge k M.length with h | h
  · rw [List.getElem?_reverse h, show M.length - k = (M.length - 1 - k) + 1 by omega]; rfl
  · rw [List.getElem?_eq_none (by simpa using h), Nat.sub_eq_zero_of_le h]; rfl

/-- A read of `r ++ M.reverse` at `r.size + k`: one lookup in the literal `default :: M`. -/
theorem rd_revAcc (r : Array Val) (M : List Val) (k : ℕ) :
    rd (r ++ M.reverse.toArray) (r.size + k) =
      (((default : Val) :: M).toArray[M.length - k]?).getD default := by
  rw [rd_app, getD_revAcc]

theorem rd_revAcc0 (r : Array Val) (M : List Val) :
    rd (r ++ M.reverse.toArray) r.size =
      (((default : Val) :: M).toArray[M.length]?).getD default := by
  simpa using rd_revAcc r M 0

/-- An op's outputs join a reversed accumulator at its head. -/
theorem revAcc_app_cons (M : List Val) (a : Val) (as : List Val) :
    M.reverse ++ a :: as = (a :: M).reverse ++ as := by simp

/-- A read at `x ≥ n = R.size` of `R ++ M.reverse` (a block's base is `c + k`, not `r.size + k`). -/
theorem rd_revAccAt (R : Array Val) (M : List Val) {n : ℕ} (hR : R.size = n) {x : ℕ} (hx : n ≤ x) :
    rd (R ++ M.reverse.toArray) x = (((default : Val) :: M).toArray[M.length - (x - n)]?).getD default := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hx
  subst hR
  rw [Nat.add_sub_cancel_left]
  exact rd_revAcc R M k

/-- A run from `[]` is a run from the empty reversed accumulator. -/
theorem pureRun_nil_rev (impl : OpImpl) (κ : Kind) (inp : Input) (ops : List Op) (r : Array Val) :
    pureRun impl κ inp ops r [] = pureRun impl κ inp ops r ([] : List Val).reverse := rfl

section Flags
variable (impl : OpImpl) (κ : Kind) (inp : Input) (fi : FinIn) (r : Array Val) (P : FinP)

/-! ## `finZ` -/

/-- **`relZ` at `P`**: (i) `eq((ρ, r), r′)·â·b̂ = c_Z` over the kind's `m`, Z3's `P.S.z3`
challenges and the relocated Z-end reads; (ii) `P^z*(λ) = α_Z`. -/
def relZ4 : Bool :=
  let rr := (List.ofFn pinnedRho ++ ((coordsR fi "Z1").take (P.kv.m κ - 13)).map (fv r)).toArray
  let rr' := (((chals fi "Z3" P.S.z3).take (P.kv.m κ - 6)).map (fv r)).toArray
  (Val.f (eqPoint rr rr' * pe4 P.S inp fZend 0 * pe4 P.S inp fZend 16)).eqv (rd r (claimN fi "Z3")) &&
  (rd r ((outsOf fi "Z2").getD 2 0)).eqv (rd r (fi.zhat.getD 0 0))

theorem flag_gFinZ (hin : ∀ x ∈ coordsR fi "Z1" ++ chals fi "Z3" P.S.z3 ++
      [claimN fi "Z3", (outsOf fi "Z2").getD 2 0, fi.zhat.getD 0 0], x < r.size) :
    ∃ L, pureRun impl κ inp ((gFinZ P fi r.size).1.map (reloc P.S)) r [] =
      some (L, relZ4 κ inp fi r P) := by
  simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hin
  have h1 := fun L => map_rd_app r L ((coordsR fi "Z1").take (P.kv.m κ - 13))
    fun x hx => hin x (.inl (.inl (List.mem_of_mem_take hx)))
  have h2 := fun L => map_rd_app r L ((chals fi "Z3" P.S.z3).take (P.kv.m κ - 6))
    fun x hx => hin x (.inl (.inr (List.mem_of_mem_take hx)))
  have tf : ∀ x, (Val.f x).toF = x := fun _ => rfl
  have taf : ∀ x, (Val.af x).toAF = x := fun _ => rfl
  have hZ : fZend < 19 := by decide
  simp only [gFinZ, relZ4, pinOps, List.ofFn_succ, List.ofFn_zero, List.map_cons, List.map_nil,
    List.cons_append, List.nil_append, reloc_piElem _ hZ]
  generalize claimN fi "Z3" = cz at *
  generalize (outsOf fi "Z2").getD 2 0 = pz at *
  generalize fi.zhat.getD 0 0 = az at *
  have h5 := hin cz (.inr (.inl rfl)); have h6 := hin pz (.inr (.inr (.inl rfl)))
  have h7 := hin az (.inr (.inr (.inr rfl)))
  rw [pureRun_nil_rev]
  simp only [pureRun, reloc, evalOp, absOff_zero, tf, taf, List.map_cons, h1, h2, rd_revAcc,
    rd_revAcc0, revAcc_app_cons, List.append_nil, List.length_cons, List.length_nil, Nat.reduceAdd,
    Nat.reduceSub, Array.reduceGetElem?, Option.getD_some, rd_app_left _ _ h5,
    rd_app_left _ _ h6, rd_app_left _ _ h7, Option.map_some, Val.eqv, allK, Bool.not_true,
    Bool.false_or, Bool.true_and, Bool.and_true]
  exact ⟨_, rfl⟩

/-! ## `finLr` -/

/-- **`relLr` at `P`** (a node's end check over its `P.lrR` real rows, relocated Lr-end reads). -/
def relLr4 : Bool :=
  let rLr := (((coordsR fi "Lr1").take P.lrR).map (fv r)).toArray
  let rr := ((chals fi "Lr2" P.lrR).map (fv r)).toArray
  let a := pe4 P.S inp fLrEnd 0; let bb := pe4 P.S inp fLrEnd 16; let c := pe4 P.S inp fLrEnd 32
  if P.kv.node κ then (Val.f (eqPoint rLr rr * (a * bb + c))).eqv (rd r (claimN fi "Lr2")) else true

/-- `finLr`'s export `v_L` at `P`. -/
def vLv4 : F :=
  let kL := fv r ((outsOf fi "Lr3").headD 0)
  pe4 P.S inp fLrEnd 0 + kL * pe4 P.S inp fLrEnd 16 + kL * kL * pe4 P.S inp fLrEnd 32

theorem flag_gFinLr (hin : ∀ x ∈ (coordsR fi "Lr1").take P.lrR ++ chals fi "Lr2" P.lrR ++
      [(outsOf fi "Lr3").headD 0, claimN fi "Lr2"], x < r.size) :
    ∃ L, pureRun impl κ inp ((gFinLr P fi r.size).1.map (reloc P.S)) r [] =
        some (L, relLr4 κ inp fi r P) ∧
      (rd (r ++ L.toArray) ((gFinLr P fi r.size).2.getD 0 0)).toF = vLv4 inp fi r P ∧
      (rd (r ++ L.toArray) ((gFinLr P fi r.size).2.getD 1 0)).toAF =
        ((chals fi "Lr2" P.lrR).map (fv r)).toArray := by
  simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hin
  have h1 := fun L => map_rd_app r L ((coordsR fi "Lr1").take P.lrR) fun x hx => hin x (.inl (.inl hx))
  have h2 := fun L => map_rd_app r L (chals fi "Lr2" P.lrR) fun x hx => hin x (.inl (.inr hx))
  have tf : ∀ x, (Val.f x).toF = x := fun _ => rfl
  have taf : ∀ x, (Val.af x).toAF = x := fun _ => rfl
  have hL : fLrEnd < 19 := by decide
  simp only [gFinLr, relLr4, vLv4, List.map_cons, List.map_nil, reloc_piElem _ hL]
  generalize (outsOf fi "Lr3").headD 0 = kl at *
  generalize claimN fi "Lr2" = c2 at *
  have hk := hin kl (.inr (.inl rfl)); have hc2 := hin c2 (.inr (.inr rfl))
  rw [pureRun_nil_rev]
  cases hc : P.ck <;> cases hn : P.kv.node κ <;>
  simp only [hc, Bool.cond_true, Bool.cond_false, hn, pureRun, reloc, evalOp, absOff_zero, tf, taf,
    h1, h2, rd_revAcc, rd_revAcc0, revAcc_app_cons, List.append_nil, List.length_cons,
    List.length_nil, Nat.reduceAdd, Nat.reduceSub, Array.reduceGetElem?, Option.getD_some,
    rd_app_left _ _ hk, rd_app_left _ _ hc2,
    Option.map_some, Bool.not_true, Bool.not_false, Bool.false_or, Bool.true_or, Bool.true_and,
    Bool.and_true, ↓reduceIte, Bool.false_eq_true] <;>
  refine ⟨_, rfl, ?_, ?_⟩ <;> simp only [List.getD_cons_succ, List.getD_cons_zero, rd_revAcc,
    List.length_cons, List.length_nil, Nat.reduceAdd, Nat.reduceSub, Array.reduceGetElem?,
    Option.getD_some, tf, taf] <;> rfl

/-! ## `finE` -/

/-- **`relE` at `P` without the reserve** (3.x, the segment group): (ii)–(iv) for a node over its `P.e2R`/`P.e4R` real rounds, (v) (E4 end is
`f̂(r′) ‖ 0^16`, read at `S`'s E4-end offset) for every kind. -/
def relE4o : Bool :=
  let rE := (((coordsR fi "E1").take P.e2R).map (fv r)).toArray
  let r2 := ((chals fi "E2" P.e2R).map (fv r)).toArray
  let r4 := ((chals fi "E4" P.e4R).map (fv r)).toArray
  let kE := fv r ((outsOf fi "E3").headD 0)
  let kL := fv r ((outsOf fi "Lr3").headD 0)
  let a := pe4 P.S inp fEEnd 0; let bb := pe4 P.S inp fEEnd 16; let c := pe4 P.S inp fEEnd 32
  let m := impl.evalM r2 r4
  let l := impl.evalL (rd r (lrEx fi 1)).toAF r4
  let wM := m.1 + kE * m.2.1 + kE * kE * m.2.2
  let wL := l.1 + kL * l.2.1 + kL * kL * l.2.2
  let o := fieldOffOf P.S fE + (gOE4end P.S + 16)
  let e4 := (Val.f (pe4 P.S inp fE (gOE4end P.S))).eqv (rd r (fi.zhat.getD 3 0)) &&
    (inp.π.extract o (o + 16)).data.all (· == 0)
  if P.kv.node κ then
    (Val.f (eqPoint rE r2 * (a * bb + c))).eqv (rd r (claimN fi "E2")) &&
    ((Val.f (a + kE * bb + kE * kE * c + kE * kE * kE * fv r (lrEx fi 0))).eqv
      (rd r (claim0 fi "E4")) &&
    ((Val.f ((wM + kE * kE * kE * wL) * fv r (fi.zhat.getD 3 0))).eqv (rd r (claimN fi "E4")) &&
      e4))
  else e4

/-- **The reserve's child claim on the registers' input** (RSV2 §2.1, revision 4.4.2): `p_x` (23),
`p_y` (25), `s` (9) from `fLrEnd` at `rsvRx`, `rsvRy`, `rsvS`. -/
def rsvPx4 (inp : Input) (P : FinP) : List F :=
  (List.range 23).map fun j => pe4 P.S inp fLrEnd (rsvRx + 16 * j)
def rsvPy4 (inp : Input) (P : FinP) : List F :=
  (List.range 25).map fun j => pe4 P.S inp fLrEnd (rsvRy + 16 * j)
def rsvS4 (inp : Input) (P : FinP) : List F :=
  (List.range 9).map fun j => pe4 P.S inp fLrEnd (rsvS + 16 * j)

/-- **`relE` at `P`**. Without the reserve (`rsvOps` off: 3.x, the segment group): (ii)–(iv) for a
node over its `P.e2R`/`P.e4R` real rounds, (v) (E4 end is `f̂(r′) ‖ 0^16`, read at `S`'s E4-end
offset) for every kind. **With the reserve** (RSV2 §2.2): (v); `fEEnd[64, 112) = 0`; where the
kind's `rsv` is off, `fLrEnd[48, 1008) = 0` and `fEEnd[48, 64) = 0`; `X₃[1] = X₃[2] = 0`; and on a node

* (ii″) `claimN(E2) = eq(τ, r_E2)(âb̂ + ĉ) + eq(p_x, r_E2)·η·(m̂* + X)`;
* (iii″) `claim0(E4) = â + κ_E b̂ + κ_E² ĉ + κ_E³ v_L + κ_E⁴ m̂*`;
* (iv″) `claimN(E4) = X^P + κ_E³·L̃·f̂`, `X^P` the **one** `evalM` at the row point
  `r_E2[<22] ‖ x̂₂₂ ‖ s^P` (32 entries) and the column point `r′[<24] ‖ ŷ₂₄` (25), with
  `s^P_{3k+m} = [k = κ.ix]·f̂·κ_E^m + κ_E⁴·eq(p_y, r′)·s_{3k+m}` and the mixed entries
  `x̂₂₂ = (r_E2 ‖ p_x[e2R, 23))[22]`, `ŷ₂₄ = (r′ ‖ p_y[e4R, 25))[24]`. -/
def relE4 : Bool :=
  let rE := (((coordsR fi "E1").take P.e2R).map (fv r)).toArray
  let r2 := ((chals fi "E2" P.e2R).map (fv r)).toArray
  let r4 := ((chals fi "E4" P.e4R).map (fv r)).toArray
  let kE := fv r ((outsOf fi "E3").headD 0)
  let kL := fv r ((outsOf fi "Lr3").headD 0)
  let a := pe4 P.S inp fEEnd 0; let bb := pe4 P.S inp fEEnd 16; let c := pe4 P.S inp fEEnd 32
  let l := impl.evalL (rd r (lrEx fi 1)).toAF r4
  let wL := l.1 + kL * l.2.1 + kL * kL * l.2.2
  let o := fieldOffOf P.S fE + (gOE4end P.S + 16)
  let e4 := (Val.f (pe4 P.S inp fE (gOE4end P.S))).eqv (rd r (fi.zhat.getD 3 0)) &&
    (inp.π.extract o (o + 16)).data.all (· == 0)
  if P.rsvOps then
    let px := rsvPx4 inp P; let py := rsvPy4 inp P; let s := rsvS4 inp P
    let X0 := pe4 P.S inp fLrEnd rsvX
    let mh := pe4 P.S inp fEEnd 48
    let eta := fv r ((coordsR fi "E1").getD 23 0)
    let fz := fv r (fi.zhat.getD 3 0)
    let w := kE * kE * (kE * kE) * eqPoint (py.take P.e4R).toArray r4
    let ind : ℕ → F := fun k => if P.kix = k then 1 else 0
    let t : ℕ → F := fun m => [fz, fz * kE, fz * (kE * kE)].getD m 0
    let sP := (List.range 9).map fun i => ind (i / 3) * t (i % 3) + w * s.getD i 0
    let x22 := ((chals fi "E2" P.e2R).map (fv r) ++ px.drop P.e2R).getD 22 (fv r 0)
    let y24 := ((chals fi "E4" P.e4R).map (fv r) ++ py.drop P.e4R).getD 24 (fv r 0)
    let XP := (impl.evalM ((((chals fi "E2" P.e2R).map (fv r)).take 22 ++ [x22] ++ sP).toArray)
      ((((chals fi "E4" P.e4R).map (fv r)).take 24 ++ [y24]).toArray)).1
    let oE := fieldOffOf P.S fEEnd; let oL := fieldOffOf P.S fLrEnd
    e4 && ((inp.π.extract (oE + 64) (oE + 64 + 48)).data.all (· == 0) &&
      ((P.rsv || (inp.π.extract (oL + 48) (oL + 48 + 960)).data.all (· == 0)) &&
      ((P.rsv || (inp.π.extract (oE + 48) (oE + 48 + 16)).data.all (· == 0)) &&
      (decide (pe4 P.S inp fLrEnd (rsvX + 16) = 0) && (decide (pe4 P.S inp fLrEnd (rsvX + 32) = 0) &&
      ((!P.kv.node κ || (Val.f (eqPoint rE r2 * (a * bb + c) +
          eqPoint (px.take P.e2R).toArray r2 * (eta * (mh + X0)))).eqv (rd r (claimN fi "E2"))) &&
      ((!P.kv.node κ || (Val.f (a + kE * bb + kE * kE * c + kE * kE * kE * fv r (lrEx fi 0) +
          kE * kE * (kE * kE) * mh)).eqv (rd r (claim0 fi "E4"))) &&
      (!P.kv.node κ || (Val.f (XP + kE * kE * kE * wL * fz)).eqv (rd r (claimN fi "E4"))))))))))
  else relE4o impl κ inp fi r P

/-- A read at a list entry is the entry of the reads (`List.getD_map`). -/
theorem rd_getD_toF (R : Array Val) (l : List Reg) (i d : ℕ) :
    (rd R (l.getD i d)).toF = (l.map fun x => (rd R x).toF).getD i (rd R d).toF := by
  rw [List.getD_map]

theorem flag_gFinE0 (hin : ∀ x ∈ (coordsR fi "E1").take P.e2R ++ chals fi "E2" P.e2R ++
      chals fi "E4" P.e4R ++
      [(outsOf fi "E3").headD 0, claimN fi "E2", claim0 fi "E4", claimN fi "E4",
       fi.zhat.getD 3 0, (outsOf fi "Lr3").headD 0, lrEx fi 0, lrEx fi 1], x < r.size) :
    ∃ L, pureRun impl κ inp ((gFinE0 P fi r.size (fun κ => P.kv.node κ) true).map (reloc P.S)) r [] =
        some (L, relE4o impl κ inp fi r P) ∧
      (rd (r ++ L.toArray) (r.size + 17)).toAF =
        ((chals fi "E4" P.e4R).map (fv r)).toArray := by
  simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hin
  have h1 := fun L => map_rd_app r L ((coordsR fi "E1").take P.e2R)
    fun x hx => hin x (.inl (.inl (.inl hx)))
  have h2 := fun L => map_rd_app r L (chals fi "E2" P.e2R) fun x hx => hin x (.inl (.inl (.inr hx)))
  have h3 := fun L => map_rd_app r L (chals fi "E4" P.e4R) fun x hx => hin x (.inl (.inr hx))
  have tf : ∀ x, (Val.f x).toF = x := fun _ => rfl
  have taf : ∀ x, (Val.af x).toAF = x := fun _ => rfl
  have hEE : fEEnd < 19 := by decide
  have hE : fE < 19 := by decide
  simp only [gFinE0, relE4o, cond_true, List.cons_append, List.nil_append, List.map_append, List.map_cons, List.map_nil, reloc_piElem _ hEE, reloc_piElem _ hE,
    reloc_piField _ hE]
  generalize (outsOf fi "E3").headD 0 = ke at *
  generalize claimN fi "E2" = c2 at *
  generalize claim0 fi "E4" = c40 at *
  generalize claimN fi "E4" = c4 at *
  generalize fi.zhat.getD 3 0 = ze at *
  generalize (outsOf fi "Lr3").headD 0 = kl at *
  generalize lrEx fi 0 = vl at *
  generalize lrEx fi 1 = rl at *
  have hk := hin ke (.inr (.inl rfl)); have hc2 := hin c2 (.inr (.inr (.inl rfl)))
  have hc40 := hin c40 (.inr (.inr (.inr (.inl rfl))))
  have hc4 := hin c4 (.inr (.inr (.inr (.inr (.inl rfl)))))
  have hze := hin ze (.inr (.inr (.inr (.inr (.inr (.inl rfl))))))
  have hkl := hin kl (.inr (.inr (.inr (.inr (.inr (.inr (.inl rfl)))))))
  have hvl := hin vl (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl rfl))))))))
  have hrl := hin rl (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr rfl))))))))
  rw [pureRun_nil_rev]
  cases hc : P.ck <;> cases hn : P.kv.node κ <;>
  simp only [hc, Bool.cond_true, Bool.cond_false, hn, pureRun, reloc, evalOp, absOff_zero, tf, taf,
    h1, h2, h3, rd_revAcc, rd_revAcc0, revAcc_app_cons, List.append_nil, List.length_cons,
    List.length_nil, Nat.reduceAdd, Nat.reduceSub, Array.reduceGetElem?, Option.getD_some,
    rd_app_left _ _ hk, rd_app_left _ _ hc2, rd_app_left _ _ hc40,
    rd_app_left _ _ hc4, rd_app_left _ _ hze, rd_app_left _ _ hkl, rd_app_left _ _ hvl,
    rd_app_left _ _ hrl, allK,
    Option.map_some, Bool.not_true, Bool.not_false, Bool.false_or, Bool.true_or, Bool.true_and,
    Bool.and_true, ↓reduceIte, Bool.false_eq_true, Val.isZero] <;>
  refine ⟨_, rfl, ?_⟩ <;> simp only [List.getD_cons_zero, rd_revAcc,
    List.length_cons, List.length_nil, Nat.reduceAdd, Nat.reduceSub, Array.reduceGetElem?,
    Option.getD_some, taf]

/-- **Block A of the reserve's `finE`**: the own ops with no `evalM` and no assert
(`gFinE0 … (fun _ => false) false`): the flag is (v), and the registers the reserve's block reads. -/
theorem run_gFinE0off (hin : ∀ x ∈ (coordsR fi "E1").take P.e2R ++ chals fi "E2" P.e2R ++
      chals fi "E4" P.e4R ++
      [(outsOf fi "E3").headD 0, claimN fi "E2", claim0 fi "E4", claimN fi "E4",
       fi.zhat.getD 3 0, (outsOf fi "Lr3").headD 0, lrEx fi 0, lrEx fi 1], x < r.size) :
    ∃ L, pureRun impl κ inp ((gFinE0 P fi r.size (fun _ => false) false).map (reloc P.S)) r [] =
        some (L, (Val.f (pe4 P.S inp fE (gOE4end P.S))).eqv (rd r (fi.zhat.getD 3 0)) &&
          (inp.π.extract (fieldOffOf P.S fE + (gOE4end P.S + 16))
            (fieldOffOf P.S fE + (gOE4end P.S + 16) + 16)).data.all (· == 0)) ∧
      L.length = 38 ∧
      rd (r ++ L.toArray) (r.size + 4) = .af ((chals fi "E2" P.e2R).map (fv r)).toArray ∧
      rd (r ++ L.toArray) (r.size + 8) = .f (eqPoint (((coordsR fi "E1").take P.e2R).map (fv r)).toArray
        ((chals fi "E2" P.e2R).map (fv r)).toArray *
        (pe4 P.S inp fEEnd 0 * pe4 P.S inp fEEnd 16 + pe4 P.S inp fEEnd 32)) ∧
      rd (r ++ L.toArray) (r.size + 10) = .f (fv r ((outsOf fi "E3").headD 0) * fv r ((outsOf fi "E3").headD 0)) ∧
      rd (r ++ L.toArray) (r.size + 16) = .f (pe4 P.S inp fEEnd 0 +
        fv r ((outsOf fi "E3").headD 0) * pe4 P.S inp fEEnd 16 +
        fv r ((outsOf fi "E3").headD 0) * fv r ((outsOf fi "E3").headD 0) * pe4 P.S inp fEEnd 32 +
        fv r ((outsOf fi "E3").headD 0) * fv r ((outsOf fi "E3").headD 0) * fv r ((outsOf fi "E3").headD 0) *
          fv r (lrEx fi 0)) ∧
      rd (r ++ L.toArray) (r.size + 17) = .af ((chals fi "E4" P.e4R).map (fv r)).toArray ∧
      rd (r ++ L.toArray) (r.size + 35) = .f (fv r ((outsOf fi "E3").headD 0) * fv r ((outsOf fi "E3").headD 0) *
        fv r ((outsOf fi "E3").headD 0) *
        ((impl.evalL (rd r (lrEx fi 1)).toAF ((chals fi "E4" P.e4R).map (fv r)).toArray).1 +
          fv r ((outsOf fi "Lr3").headD 0) *
            (impl.evalL (rd r (lrEx fi 1)).toAF ((chals fi "E4" P.e4R).map (fv r)).toArray).2.1 +
          fv r ((outsOf fi "Lr3").headD 0) * fv r ((outsOf fi "Lr3").headD 0) *
            (impl.evalL (rd r (lrEx fi 1)).toAF ((chals fi "E4" P.e4R).map (fv r)).toArray).2.2) *
        fv r (fi.zhat.getD 3 0)) := by
  simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hin
  have h1 := fun L => map_rd_app r L ((coordsR fi "E1").take P.e2R)
    fun x hx => hin x (.inl (.inl (.inl hx)))
  have h2 := fun L => map_rd_app r L (chals fi "E2" P.e2R) fun x hx => hin x (.inl (.inl (.inr hx)))
  have h3 := fun L => map_rd_app r L (chals fi "E4" P.e4R) fun x hx => hin x (.inl (.inr hx))
  have tf : ∀ x, (Val.f x).toF = x := fun _ => rfl
  have taf : ∀ x, (Val.af x).toAF = x := fun _ => rfl
  have hEE : fEEnd < 19 := by decide
  have hE : fE < 19 := by decide
  simp only [gFinE0, cond_false, List.cons_append, List.nil_append, List.map_append, List.map_cons,
    List.map_nil, reloc_piElem _ hEE, reloc_piElem _ hE, reloc_piField _ hE]
  generalize (outsOf fi "E3").headD 0 = ke at *
  generalize claimN fi "E2" = c2 at *
  generalize claim0 fi "E4" = c40 at *
  generalize claimN fi "E4" = c4 at *
  generalize fi.zhat.getD 3 0 = ze at *
  generalize (outsOf fi "Lr3").headD 0 = kl at *
  generalize lrEx fi 0 = vl at *
  generalize lrEx fi 1 = rl at *
  have hk := hin ke (.inr (.inl rfl))
  have hze := hin ze (.inr (.inr (.inr (.inr (.inr (.inl rfl))))))
  have hkl := hin kl (.inr (.inr (.inr (.inr (.inr (.inr (.inl rfl)))))))
  have hvl := hin vl (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl rfl))))))))
  have hrl := hin rl (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr rfl))))))))
  rw [pureRun_nil_rev]
  cases hc : P.ck <;>
  simp only [hc, Bool.cond_true, Bool.cond_false, pureRun, reloc, evalOp, absOff_zero, tf, taf,
    h1, h2, h3, rd_revAcc, rd_revAcc0, revAcc_app_cons, List.append_nil, List.length_cons,
    List.length_nil, Nat.reduceAdd, Nat.reduceSub, Array.reduceGetElem?, Option.getD_some,
    rd_app_left _ _ hk, rd_app_left _ _ hze, rd_app_left _ _ hkl, rd_app_left _ _ hvl,
    rd_app_left _ _ hrl, allK,
    Option.map_some, Bool.not_true, Bool.not_false, Bool.false_or, Bool.true_or, Bool.true_and,
    Bool.and_true, ↓reduceIte, Bool.false_eq_true, Val.isZero] <;>
  refine ⟨_, rfl, rfl, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp only [rd_revAcc,
    List.length_cons, List.length_nil, Nat.reduceAdd, Nat.reduceSub, Array.reduceGetElem?,
    Option.getD_some, mul_zero, zero_add, add_zero, pe4, Nat.add_zero, fv]

/-- `rsvEOps`' second block (21 ops, registers `c + 60 … c + 75`): `m̂*`, the zero asserts, the
packed child points and their `eq`s, `κ_E⁴`, `w`, `f̂κ_E`, `f̂κ_E²`, the kind indicators and `1`. -/
def rsvBC (P : FinP) (fi : FinIn) (b c : ℕ) : List Op :=
  let kE := (outsOf fi "E3").headD 0
  let fz := fi.zhat.getD 3 0
  [Op.piElem fEEnd 48,
   Op.piField fEEnd 64 48, Op.assertZero (c + 61) allK,
   Op.piField fLrEnd 48 960, Op.assertZero (c + 62) (fun _ => !P.rsv),
   Op.piField fEEnd 48 16, Op.assertZero (c + 63) (fun _ => !P.rsv),
   Op.assertZero (c + 58) allK, Op.assertZero (c + 59) allK,
   Op.packFK (fun _ => ((List.range 23).map (c + ·)).take P.e2R), Op.eqPt (c + 64) (b + 4),
   Op.packFK (fun _ => ((List.range 25).map (c + 23 + ·)).take P.e4R), Op.eqPt (c + 66) (b + 17),
   Op.mulF (b + 10) (b + 10), Op.mulF (c + 68) (c + 67),
   Op.mulF fz kE, Op.mulF fz (b + 10),
   Op.const (fun _ => .f (if P.kix = 0 then 1 else 0)),
   Op.const (fun _ => .f (if P.kix = 1 then 1 else 0)),
   Op.const (fun _ => .f (if P.kix = 2 then 1 else 0)),
   Op.const (fun _ => .f 1)]

/-- `rsvEOps`' last block (21 ops from `d + 36`, `d = c + 76`): the mixed entries, the stacked call and
the three claim asserts (ii″)–(iv″). -/
def rsvTl (P : FinP) (fi : FinIn) (b c : ℕ) : List Op :=
  let eta := (coordsR fi "E1").getD 23 0
  let node : KC Bool := fun κ => P.kv.node κ
  let rx := (List.range 23).map (c + ·)
  let ry := (List.range 25).map (c + 23 + ·)
  let d := c + 76
  [Op.packFK (fun _ => [(chals fi "E2" P.e2R ++ rx.drop P.e2R).getD 22 0]), Op.getF (d + 36) 0,
   Op.mulF (c + 75) (d + 37),
   Op.packFK (fun _ => [(chals fi "E4" P.e4R ++ ry.drop P.e4R).getD 24 0]), Op.getF (d + 39) 0,
   Op.mulF (c + 75) (d + 40),
   Op.packFK (fun _ => (chals fi "E2" P.e2R).take 22 ++ [d + 38] ++ (List.range 9).map (d + 27 + ·)),
   Op.packFK (fun _ => (chals fi "E4" P.e4R).take 24 ++ [d + 41]),
   Op.evalM (d + 42) (d + 43),
   Op.addF (c + 60) (c + 57), Op.mulF eta (d + 47), Op.mulF (c + 65) (d + 48), Op.addF (b + 8) (d + 49),
   Op.assertEq (d + 50) (claimN fi "E2") node,
   Op.mulF (c + 68) (c + 60), Op.addF (b + 16) (d + 51),
   Op.assertEq (d + 52) (claim0 fi "E4") node,
   Op.addF (d + 44) (b + 35),
   Op.assertEq (d + 53) (claimN fi "E4") node]

/-- **`rsvEOps` in blocks** (fixed kind): the 60 reads of `fLrEnd` (`p_x ‖ p_y ‖ s ‖ X₃` are contiguous
from byte 48), `rsvBC`, `rsvSOps`, `rsvTl`. -/
theorem rsvEOps_split (P : FinP) (fi : FinIn) (b c : ℕ) :
    rsvEOps P fi b c = (List.range 60).map (fun j => Op.piElem fLrEnd (48 + 16 * j)) ++ rsvBC P fi b c ++
      rsvSOps (c + 72 + ·) (fun m => [fi.zhat.getD 3 0, c + 70, c + 71].getD m 0) (c + 69) (c + 75)
        (c + 48 + ·) (c + 76) ++ rsvTl P fi b c := by
  rfl

/-- **Block BC's run**, from a base `R` of size `c + 60` holding the 60 reads at `c …` and block A's
registers below `c`. -/
theorem run_rsvBC (R : Array Val) (b c : ℕ) (hR : R.size = c + 60) (hbc : b + 38 ≤ c)
    (r2 r4 : Array F) (k2 kE fz : F)
    (hb4 : rd R (b + 4) = .af r2) (hb10 : rd R (b + 10) = .f k2) (hb17 : rd R (b + 17) = .af r4)
    (hfz : fi.zhat.getD 3 0 < c ∧ (rd R (fi.zhat.getD 3 0)).toF = fz)
    (hkE : (outsOf fi "E3").headD 0 < c ∧ (rd R ((outsOf fi "E3").headD 0)).toF = kE)
    (hV : ∀ j < 60, rd R (c + j) = .f (pe4 P.S inp fLrEnd (48 + 16 * j))) :
    ∃ L, pureRun impl κ inp ((rsvBC P fi b c).map (reloc P.S)) R [] =
        some (L, (inp.π.extract (fieldOffOf P.S fEEnd + 64) (fieldOffOf P.S fEEnd + 64 + 48)).data.all (· == 0) &&
          ((P.rsv || (inp.π.extract (fieldOffOf P.S fLrEnd + 48) (fieldOffOf P.S fLrEnd + 48 + 960)).data.all
              (· == 0)) &&
          ((P.rsv || (inp.π.extract (fieldOffOf P.S fEEnd + 48) (fieldOffOf P.S fEEnd + 48 + 16)).data.all
              (· == 0)) &&
          (decide (pe4 P.S inp fLrEnd (rsvX + 16) = 0) && decide (pe4 P.S inp fLrEnd (rsvX + 32) = 0))))) ∧
      L.length = 16 ∧
      rd (R ++ L.toArray) (c + 60) = .f (pe4 P.S inp fEEnd 48) ∧
      rd (R ++ L.toArray) (c + 65) = .f (eqPoint ((rsvPx4 inp P).take P.e2R).toArray r2) ∧
      rd (R ++ L.toArray) (c + 68) = .f (k2 * k2) ∧
      rd (R ++ L.toArray) (c + 69) = .f (k2 * k2 * eqPoint ((rsvPy4 inp P).take P.e4R).toArray r4) ∧
      rd (R ++ L.toArray) (c + 70) = .f (fz * kE) ∧
      rd (R ++ L.toArray) (c + 71) = .f (fz * k2) ∧
      rd (R ++ L.toArray) (c + 72) = .f (if P.kix = 0 then 1 else 0) ∧
      rd (R ++ L.toArray) (c + 73) = .f (if P.kix = 1 then 1 else 0) ∧
      rd (R ++ L.toArray) (c + 74) = .f (if P.kix = 2 then 1 else 0) ∧
      rd (R ++ L.toArray) (c + 75) = .f 1 := by
  have hl : ∀ x, x < c + 60 → ∀ L : List Val, rd (R ++ L.toArray) x = rd R x :=
    fun x hx L => rd_app_left _ _ (by omega)
  have hpx : ∀ L : List Val, (((List.range 23).map (c + ·)).take P.e2R).map
      (fun x => (rd (R ++ L.toArray) x).toF) = (rsvPx4 inp P).take P.e2R := fun L => by
    rw [List.map_take, List.map_map]; refine congrArg (List.take P.e2R) ?_; unfold rsvPx4
    refine List.map_congr_left fun j hj => ?_
    rw [List.mem_range] at hj
    simp only [Function.comp_apply]; rw [hl (c + j) (by omega), hV j (by omega)]; rfl
  have hpy : ∀ L : List Val, (((List.range 25).map (c + 23 + ·)).take P.e4R).map
      (fun x => (rd (R ++ L.toArray) x).toF) = (rsvPy4 inp P).take P.e4R := fun L => by
    rw [List.map_take, List.map_map]; refine congrArg (List.take P.e4R) ?_; unfold rsvPy4
    refine List.map_congr_left fun j hj => ?_
    rw [List.mem_range] at hj
    simp only [Function.comp_apply]
    rw [show c + 23 + j = c + (23 + j) by omega, hl (c + (23 + j)) (by omega), hV (23 + j) (by omega)]
    show F.ofBytes (bytesAt inp.π (fieldOffOf P.S fLrEnd + (48 + 16 * (23 + j))) 16) =
      F.ofBytes (bytesAt inp.π (fieldOffOf P.S fLrEnd + (rsvRy + 16 * j)) 16)
    rw [show 48 + 16 * (23 + j) = rsvRy + 16 * j by simp only [rsvRy]; omega]
  have h4 := hl (b + 4) (by omega); have h10 := hl (b + 10) (by omega)
  have h17 := hl (b + 17) (by omega)
  have hz := hl _ (Nat.lt_of_lt_of_le hfz.1 (by omega))
  have hk := hl _ (Nat.lt_of_lt_of_le hkE.1 (by omega))
  have h58 := hl (c + 58) (by omega); have h59 := hl (c + 59) (by omega)
  have v58 := hV 58 (by norm_num); have v59 := hV 59 (by norm_num)
  have hEE : fEEnd < 19 := by decide
  have hL : fLrEnd < 19 := by decide
  have tf : ∀ x, (Val.f x).toF = x := fun _ => rfl
  have taf : ∀ x, (Val.af x).toAF = x := fun _ => rfl
  simp only [rsvBC, List.map_cons, List.map_nil, reloc_piElem _ hEE, reloc_piField _ hEE,
    reloc_piField _ hL]
  rw [pureRun_nil_rev]
  simp only [pureRun, reloc, evalOp, absOff_zero, tf, taf, rd_revAccAt R _ hR, hpx, hpy,
    revAcc_app_cons, List.append_nil, List.length_cons, List.length_nil, Nat.reduceAdd,
    Nat.reduceSub, Nat.reduceMul, Nat.add_sub_add_left, Nat.add_le_add_iff_left, Nat.reduceLeDiff,
    Array.reduceGetElem?, Option.getD_some, h4, h10, h17, hz, hk, h58, h59, v58, v59, hb4, hb10, hb17,
    hfz.2, hkE.2, allK, Option.map_some, Bool.not_true, Bool.not_false, Bool.not_not, Bool.false_or,
    Bool.true_or, Bool.true_and, Bool.and_true, Val.isZero]
  refine ⟨_, rfl, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
  simp only [rd_revAccAt R _ hR, List.length_cons, List.length_nil, Nat.reduceAdd, Nat.reduceSub,
    Nat.add_sub_add_left, Nat.add_le_add_iff_left, Nat.reduceLeDiff, Array.reduceGetElem?,
    Option.getD_some, Nat.le_refl, Nat.sub_self, le_add_iff_nonneg_right, zero_le] <;> rfl

/-- **Block E's run** (`rsvTl`), from a base `R` of size `c + 76 + 36` holding blocks A–D. -/
theorem run_rsvTl (R : Array Val) (b c : ℕ) (hR : R.size = c + 76 + 36) (hbc : b + 38 ≤ c)
    (r2l r4l sPl : List F) (x22 y24 X0 mh eta e65 v8 k4 v16 v35 : F)
    (hE2 : ∀ L : List Val, (chals fi "E2" P.e2R).map (fun x => (rd (R ++ L.toArray) x).toF) = r2l)
    (hE4 : ∀ L : List Val, (chals fi "E4" P.e4R).map (fun x => (rd (R ++ L.toArray) x).toF) = r4l)
    (hsP : ∀ L : List Val, ((List.range 9).map (c + 76 + 27 + ·)).map
      (fun x => (rd (R ++ L.toArray) x).toF) = sPl)
    (hx22 : (chals fi "E2" P.e2R ++ ((List.range 23).map (c + ·)).drop P.e2R).getD 22 0 < R.size ∧
      (rd R ((chals fi "E2" P.e2R ++ ((List.range 23).map (c + ·)).drop P.e2R).getD 22 0)).toF = x22)
    (hy24 : (chals fi "E4" P.e4R ++ ((List.range 25).map (c + 23 + ·)).drop P.e4R).getD 24 0 < R.size ∧
      (rd R ((chals fi "E4" P.e4R ++ ((List.range 25).map (c + 23 + ·)).drop P.e4R).getD 24 0)).toF = y24)
    (heta : (coordsR fi "E1").getD 23 0 < R.size ∧ (rd R ((coordsR fi "E1").getD 23 0)).toF = eta)
    (h75 : rd R (c + 75) = .f 1) (h57 : rd R (c + 57) = .f X0) (h60 : rd R (c + 60) = .f mh)
    (h65 : rd R (c + 65) = .f e65) (h68 : rd R (c + 68) = .f k4) (h8 : rd R (b + 8) = .f v8)
    (h16 : rd R (b + 16) = .f v16) (h35 : rd R (b + 35) = .f v35)
    (hcl : claimN fi "E2" < R.size ∧ claim0 fi "E4" < R.size ∧ claimN fi "E4" < R.size) :
    ∃ L, pureRun impl κ inp ((rsvTl P fi b c).map (reloc P.S)) R [] =
        some (L, (!P.kv.node κ || (Val.f (v8 + e65 * (eta * (mh + X0)))).eqv (rd R (claimN fi "E2"))) &&
          ((!P.kv.node κ || (Val.f (v16 + k4 * mh)).eqv (rd R (claim0 fi "E4"))) &&
          (!P.kv.node κ || (Val.f ((impl.evalM (r2l.take 22 ++ [x22] ++ sPl).toArray
            (r4l.take 24 ++ [y24]).toArray).1 + v35)).eqv (rd R (claimN fi "E4"))))) := by
  have hl : ∀ x, x < c + 76 + 36 → ∀ L : List Val, rd (R ++ L.toArray) x = rd R x :=
    fun x hx L => rd_app_left _ _ (by omega)
  have tf : ∀ x, (Val.f x).toF = x := fun _ => rfl
  have taf : ∀ x, (Val.af x).toAF = x := fun _ => rfl
  have hgd : ∀ a : F, ([a].toArray).getD 0 0 = a := fun _ => rfl
  have g75 := hl (c + 75) (by omega); have g57 := hl (c + 57) (by omega)
  have g60 := hl (c + 60) (by omega); have g65 := hl (c + 65) (by omega)
  have g68 := hl (c + 68) (by omega); have g8 := hl (b + 8) (by omega)
  have g16 := hl (b + 16) (by omega); have g35 := hl (b + 35) (by omega)
  have gx := fun L => rd_app_left R L hx22.1
  have gy := fun L => rd_app_left R L hy24.1
  have ge := fun L => rd_app_left R L heta.1
  have gc1 := fun L => rd_app_left R L hcl.1
  have gc2 := fun L => rd_app_left R L hcl.2.1
  have gc3 := fun L => rd_app_left R L hcl.2.2
  simp only [rsvTl, List.map_cons, List.map_nil]
  rw [pureRun_nil_rev]
  simp only [pureRun, reloc, evalOp, tf, taf, rd_revAccAt R _ hR, List.map_append, List.map_take, hE2, hE4,
    hsP, revAcc_app_cons, List.append_nil, List.length_cons, List.length_nil, Nat.reduceAdd,
    Nat.reduceSub, Nat.add_sub_add_left, Nat.add_le_add_iff_left, Nat.reduceLeDiff,
    Array.reduceGetElem?, Option.getD_some, g75, g57, g60, g65, g68, g8, g16, g35, gx, gy, ge, gc1, gc2,
    gc3, h75, h57, h60, h65, h68, h8, h16, h35, hx22.2, hy24.2, heta.2, hgd, Option.map_some,
    Bool.true_and, Bool.and_true, List.map_cons, List.map_nil, one_mul]
  exact ⟨_, rfl⟩

theorem rsvSOps_reloc (S : Seq) (ind t : ℕ → Reg) (w one : Reg) (s : ℕ → Reg) (d : ℕ) :
    (rsvSOps ind t w one s d).map (reloc S) = rsvSOps ind t w one s d := by
  simp only [rsvSOps, List.map_append, List.map_map]; rfl

theorem getD_lt' {N : ℕ} (hN : 0 < N) {l : List ℕ} (h : ∀ x ∈ l, x < N) (n : ℕ) : l.getD n 0 < N := by
  rw [List.getD_eq_getElem?_getD]
  rcases hl : l[n]? with _ | z
  · exact hN
  · exact h z (List.mem_of_getElem? hl)

/-- **`finE`'s flag with the reserve** (`rsvOps`): blocks A (`run_gFinE0off`), the 60 reads,
`rsvBC`, `rsvSOps`, `rsvTl`, joined by `pureRun_seq`. -/
theorem flag_gFinE1 (hr : P.rsvOps = true) (hin : ∀ x ∈ (coordsR fi "E1").take P.e2R ++ chals fi "E2" P.e2R ++
      chals fi "E4" P.e4R ++
      [(outsOf fi "E3").headD 0, claimN fi "E2", claim0 fi "E4", claimN fi "E4",
       fi.zhat.getD 3 0, (outsOf fi "Lr3").headD 0, lrEx fi 0, lrEx fi 1, (coordsR fi "E1").getD 23 0, 0],
      x < r.size) :
    ∃ L, pureRun impl κ inp ((gFinE P fi r.size).1.map (reloc P.S)) r [] =
        some (L, relE4 impl κ inp fi r P) ∧
      (rd (r ++ L.toArray) ((gFinE P fi r.size).2.getD 0 0)).toAF =
        ((chals fi "E4" P.e4R).map (fv r)).toArray ∧
      ∀ i < rsvN, P.rsvOps = true → rd (r ++ L.toArray) (((gFinE P fi r.size).2.drop 1).getD i 0) =
        .f (pe4 P.S inp fLrEnd (48 + 16 * i)) := by
  simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hin
  obtain ⟨LA, hA, hlA, a4, a8, a10, a16, a17, a35⟩ := run_gFinE0off impl κ inp fi r P fun x hx => hin x (by
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with ((h | h) | h) | h | h | h | h | h | h | h | h
    exacts [.inl (.inl (.inl h)), .inl (.inl (.inr h)), .inl (.inr h), .inr (.inl h),
      .inr (.inr (.inl h)), .inr (.inr (.inr (.inl h))), .inr (.inr (.inr (.inr (.inl h)))),
      .inr (.inr (.inr (.inr (.inr (.inl h))))), .inr (.inr (.inr (.inr (.inr (.inr (.inl h)))))),
      .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl h))))))),
      .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl h))))))))])
  have hpos : 0 < r.size := hin 0 (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr rfl))))))))))
  have hkE := hin _ (.inr (.inl rfl))
  have hfz := hin _ (.inr (.inr (.inr (.inr (.inr (.inl rfl))))))
  have heta := hin _ (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl rfl))))))))))
  have hc2 := hin _ (.inr (.inr (.inl rfl)))
  have hc40 := hin _ (.inr (.inr (.inr (.inl rfl))))
  have hc4 := hin _ (.inr (.inr (.inr (.inr (.inl rfl)))))
  have hE2r : ∀ x ∈ chals fi "E2" P.e2R, x < r.size := fun x hx => hin x (.inl (.inl (.inr hx)))
  have hE4r : ∀ x ∈ chals fi "E4" P.e4R, x < r.size := fun x hx => hin x (.inl (.inr hx))
  -- the bases
  have hEE : fLrEnd < 19 := by decide
  have e1 : ExtA r (r ++ LA.toArray) := ExtA.app r LA
  have s1 : (r ++ LA.toArray).size = r.size + 38 := by simp [hlA]
  -- B1: the 60 reads
  have hB1 : pureRun impl κ inp (((List.range 60).map fun j => Op.piElem fLrEnd (48 + 16 * j)).map
      (reloc P.S)) (r ++ LA.toArray) [] =
      some ((List.range 60).map fun j => Val.f (pe4 P.S inp fLrEnd (48 + 16 * j)), true) := by
    rw [List.map_map]
    have := pureRun_mapRange impl κ inp (r ++ LA.toArray) (reloc P.S ∘ fun j => Op.piElem fLrEnd (48 + 16 * j))
      (fun j => Val.f (pe4 P.S inp fLrEnd (48 + 16 * j))) [] 60 (fun i _ L => by
        simp only [Function.comp_apply, reloc_piElem _ hEE, evalOp, absOff_zero]; rfl)
    simpa using this
  generalize hV60 : ((List.range 60).map fun j => Val.f (pe4 P.S inp fLrEnd (48 + 16 * j))) = V60 at hB1
  have hlV : V60.length = 60 := by rw [← hV60]; simp
  have e2 : ExtA (r ++ LA.toArray) (r ++ LA.toArray ++ V60.toArray) := ExtA.app _ V60
  have s2 : (r ++ LA.toArray ++ V60.toArray).size = r.size + 38 + 60 := by simp [hlA, hlV]
  have e02 := e1.trans e2
  have hV : ∀ j < 60, rd (r ++ LA.toArray ++ V60.toArray) (r.size + 38 + j) =
      .f (pe4 P.S inp fLrEnd (48 + 16 * j)) := fun j hj => by
    rw [← s1, rd_app, ← hV60, getD_mapRange _ _ hj]
  -- BC
  obtain ⟨LBC, hBC, hlBC, f60, f65, f68, f69, f70, f71, f72, f73, f74, f75⟩ :=
    run_rsvBC impl κ inp fi P (r ++ LA.toArray ++ V60.toArray) r.size (r.size + 38) s2 le_rfl
      ((chals fi "E2" P.e2R).map (fv r)).toArray ((chals fi "E4" P.e4R).map (fv r)).toArray
      (fv r ((outsOf fi "E3").headD 0) * fv r ((outsOf fi "E3").headD 0)) (fv r ((outsOf fi "E3").headD 0))
      (fv r (fi.zhat.getD 3 0))
      (by rw [e2.rd (by omega), a4]) (by rw [e2.rd (by omega), a10]) (by rw [e2.rd (by omega), a17])
      ⟨Nat.lt_of_lt_of_le hfz (by omega), by rw [e02.rd (Nat.lt_of_lt_of_le hfz (by omega))]⟩
      ⟨Nat.lt_of_lt_of_le hkE (by omega), by rw [e02.rd (Nat.lt_of_lt_of_le hkE (by omega))]⟩ hV
  generalize hR3 : r ++ LA.toArray ++ V60.toArray ++ LBC.toArray = R3 at *
  have e3 : ExtA (r ++ LA.toArray ++ V60.toArray) R3 := hR3 ▸ ExtA.app _ LBC
  have s3 : R3.size = r.size + 38 + 76 := by rw [← hR3]; simp [hlA, hlV, hlBC]
  have e03 := e02.trans e3
  -- D
  have hD := run_rsvSOps impl κ inp R3 (r.size + 38 + 76) s3 (r.size + 38 + 72 + ·)
    (fun m => [fi.zhat.getD 3 0, r.size + 38 + 70, r.size + 38 + 71].getD m 0) (r.size + 38 + 69) (r.size + 38 + 75)
    (r.size + 38 + 48 + ·) (fun k => if P.kix = k then 1 else 0)
    (fun m => [fv r (fi.zhat.getD 3 0), fv r (fi.zhat.getD 3 0) * fv r ((outsOf fi "E3").headD 0),
      fv r (fi.zhat.getD 3 0) * (fv r ((outsOf fi "E3").headD 0) * fv r ((outsOf fi "E3").headD 0))].getD m 0)
    (fun i => pe4 P.S inp fLrEnd (48 + 16 * (48 + i)))
    (fv r ((outsOf fi "E3").headD 0) * fv r ((outsOf fi "E3").headD 0) *
      (fv r ((outsOf fi "E3").headD 0) * fv r ((outsOf fi "E3").headD 0)) *
      eqPoint ((rsvPy4 inp P).take P.e4R).toArray ((chals fi "E4" P.e4R).map (fv r)).toArray) 1
    (fun k hk => by
      refine ⟨show (r.size + 38 + 72 + k : ℕ) < r.size + 38 + 76 by omega, ?_⟩
      interval_cases k
      · rw [f72]; rfl
      · rw [show r.size + 38 + 72 + 1 = r.size + 38 + 73 by omega, f73]; rfl
      · rw [show r.size + 38 + 72 + 2 = r.size + 38 + 74 by omega, f74]; rfl)
    (fun m hm => by
      interval_cases m
      · exact ⟨Nat.lt_of_lt_of_le hfz (by omega), by
          simp only [List.getD_cons_zero]; rw [e03.rd (Nat.lt_of_lt_of_le hfz (by omega))]⟩
      · exact ⟨show r.size + 38 + 70 < r.size + 38 + 76 by omega, by
          simp only [List.getD_cons_succ, List.getD_cons_zero]; rw [f70]; rfl⟩
      · exact ⟨show r.size + 38 + 71 < r.size + 38 + 76 by omega, by
          simp only [List.getD_cons_succ, List.getD_cons_zero]; rw [f71]; rfl⟩)
    ⟨show (r.size + 38 + 69 : ℕ) < r.size + 38 + 76 by omega, by rw [f69]; rfl⟩
    ⟨show (r.size + 38 + 75 : ℕ) < r.size + 38 + 76 by omega, by rw [f75]; rfl⟩
    (fun i hi => ⟨show (r.size + 38 + 48 + i : ℕ) < r.size + 38 + 76 by omega, by
      rw [e3.rd (by omega), show r.size + 38 + 48 + i = r.size + 38 + (48 + i) by omega, hV _ (by omega)]; rfl⟩)
  generalize hLD : (List.range 9).map _ ++ (List.range 9).map _ ++ (List.range 9).map _ ++
    (List.range 9).map _ = LD at hD
  generalize hR4 : R3 ++ LD.toArray = R4
  have e4 : ExtA R3 R4 := hR4 ▸ ExtA.app _ LD
  have s4 : R4.size = r.size + 38 + 76 + 36 := by
    rw [← hR4, Array.size_append, s3, List.size_toArray, ← hLD]; simp
  have e04 := e03.trans e4
  have e24 := e3.trans e4
  -- reads of the 60 values from any extension of the read block
  have hVx : ∀ R', ExtA (r ++ LA.toArray ++ V60.toArray) R' → ∀ j < 60,
      (rd R' (r.size + 38 + j)).toF = pe4 P.S inp fLrEnd (48 + 16 * j) := fun R' e j hj => by
    rw [e.rd (by rw [s2]; omega), hV j hj]; rfl
  have hfr : ∀ R', ExtA r R' → ∀ l : List Reg, (∀ x ∈ l, x < r.size) →
      l.map (fun x => (rd R' x).toF) = l.map (fv r) := fun R' e l hl =>
    List.map_congr_left fun x hx => by rw [e.rd (hl x hx)]
  let kE := fv r ((outsOf fi "E3").headD 0)
  let fz := fv r (fi.zhat.getD 3 0)
  have hsP : ∀ L : List Val, ((List.range 9).map (r.size + 38 + 76 + 27 + ·)).map
      (fun x => (rd (R4 ++ L.toArray) x).toF) =
      (List.range 9).map fun i => (if P.kix = i / 3 then 1 else 0) *
        [fz, fz * kE, fz * (kE * kE)].getD (i % 3) 0 +
        kE * kE * (kE * kE) * eqPoint ((rsvPy4 inp P).take P.e4R).toArray
          ((chals fi "E4" P.e4R).map (fv r)).toArray * (rsvS4 inp P).getD i 0 := fun L => by
    rw [List.map_map]
    refine List.map_congr_left fun i hi => ?_
    rw [List.mem_range] at hi
    simp only [Function.comp_apply]
    rw [rd_app_left _ _ (show r.size + 38 + 76 + 27 + i < R4.size by omega), ← hR4,
      rd_appAt R3 LD s3 (show r.size + 38 + 76 ≤ r.size + 38 + 76 + 27 + i by omega),
      show r.size + 38 + 76 + 27 + i - (r.size + 38 + 76) = 27 + i by omega, ← hLD,
      List.getD_append_right _ _ _ _ (by simp), List.length_append, List.length_append,
      length_mapRange, length_mapRange, length_mapRange, show 27 + i - (9 + 9 + 9) = i by omega,
      getD_mapRange _ _ hi, rsvS4, getD_mapRange _ _ hi]
    simp only [one_mul, Val.toF]
    rw [show 48 + 16 * (48 + i) = rsvS + 16 * i by simp only [rsvS]; omega]
  have hrx : ∀ R', ExtA (r ++ LA.toArray ++ V60.toArray) R' →
      ((List.range 23).map (r.size + 38 + ·)).map (fun x => (rd R' x).toF) = rsvPx4 inp P := fun R' e => by
    rw [List.map_map]; unfold rsvPx4
    refine List.map_congr_left fun j hj => ?_
    rw [List.mem_range] at hj
    simp only [Function.comp_apply]; rw [hVx R' e j (by omega)]; rfl
  have hry : ∀ R', ExtA (r ++ LA.toArray ++ V60.toArray) R' →
      ((List.range 25).map (r.size + 38 + 23 + ·)).map (fun x => (rd R' x).toF) = rsvPy4 inp P := fun R' e => by
    rw [List.map_map]; unfold rsvPy4
    refine List.map_congr_left fun j hj => ?_
    rw [List.mem_range] at hj
    simp only [Function.comp_apply]
    rw [show r.size + 38 + 23 + j = r.size + 38 + (23 + j) by omega, hVx R' e (23 + j) (by omega),
      show 48 + 16 * (23 + j) = rsvRy + 16 * j by simp only [rsvRy]; omega]
  have hlt4 : ∀ x, x < r.size → x < R4.size := fun x hx => Nat.lt_of_lt_of_le hx e04.1
  have h0 : (rd R4 0).toF = fv r 0 := by rw [e04.rd hpos]
  have e14 : ExtA (r ++ LA.toArray) R4 := e2.trans e24
  obtain ⟨LE, hE⟩ := run_rsvTl impl κ inp fi P R4 r.size (r.size + 38) s4 le_rfl
    ((chals fi "E2" P.e2R).map (fv r)) ((chals fi "E4" P.e4R).map (fv r)) _
    (((chals fi "E2" P.e2R).map (fv r) ++ (rsvPx4 inp P).drop P.e2R).getD 22 (fv r 0))
    (((chals fi "E4" P.e4R).map (fv r) ++ (rsvPy4 inp P).drop P.e4R).getD 24 (fv r 0))
    (pe4 P.S inp fLrEnd rsvX) (pe4 P.S inp fEEnd 48) (fv r ((coordsR fi "E1").getD 23 0))
    (eqPoint ((rsvPx4 inp P).take P.e2R).toArray ((chals fi "E2" P.e2R).map (fv r)).toArray)
    (eqPoint (((coordsR fi "E1").take P.e2R).map (fv r)).toArray ((chals fi "E2" P.e2R).map (fv r)).toArray *
      (pe4 P.S inp fEEnd 0 * pe4 P.S inp fEEnd 16 + pe4 P.S inp fEEnd 32))
    (kE * kE * (kE * kE))
    (pe4 P.S inp fEEnd 0 + kE * pe4 P.S inp fEEnd 16 + kE * kE * pe4 P.S inp fEEnd 32 +
      kE * kE * kE * fv r (lrEx fi 0))
    (kE * kE * kE *
        ((impl.evalL (rd r (lrEx fi 1)).toAF ((chals fi "E4" P.e4R).map (fv r)).toArray).1 +
          fv r ((outsOf fi "Lr3").headD 0) *
            (impl.evalL (rd r (lrEx fi 1)).toAF ((chals fi "E4" P.e4R).map (fv r)).toArray).2.1 +
          fv r ((outsOf fi "Lr3").headD 0) * fv r ((outsOf fi "Lr3").headD 0) *
            (impl.evalL (rd r (lrEx fi 1)).toAF ((chals fi "E4" P.e4R).map (fv r)).toArray).2.2) * fz)
    (fun L => hfr _ (e04.trans (ExtA.app _ L)) _ hE2r) (fun L => hfr _ (e04.trans (ExtA.app _ L)) _ hE4r)
    hsP
    ⟨getD_lt' (Nat.lt_of_lt_of_le hpos e04.1) (fun x hx => by
        rcases List.mem_append.1 hx with hx | hx
        · exact hlt4 x (hE2r x hx)
        · obtain ⟨j, hj, rfl⟩ := List.mem_map.1 (List.mem_of_mem_drop hx)
          rw [List.mem_range] at hj; rw [s4]; omega) 22,
      by rw [rd_getD_toF, List.map_append, hfr _ e04 _ hE2r, List.map_drop, hrx _ e24, h0]⟩
    ⟨getD_lt' (Nat.lt_of_lt_of_le hpos e04.1) (fun x hx => by
        rcases List.mem_append.1 hx with hx | hx
        · exact hlt4 x (hE4r x hx)
        · obtain ⟨j, hj, rfl⟩ := List.mem_map.1 (List.mem_of_mem_drop hx)
          rw [List.mem_range] at hj; rw [s4]; omega) 24,
      by rw [rd_getD_toF, List.map_append, hfr _ e04 _ hE4r, List.map_drop, hry _ e24, h0]⟩
    ⟨hlt4 _ heta, by rw [e04.rd heta]⟩
    (by rw [e4.rd (by rw [s3]; omega), f75])
    (by rw [e24.rd (by rw [s2]; omega), hV 57 (by norm_num)]; rfl)
    (by rw [e4.rd (by rw [s3]; omega), f60]) (by rw [e4.rd (by rw [s3]; omega), f65])
    (by rw [e4.rd (by rw [s3]; omega), f68])
    (by rw [e14.rd (by rw [s1]; omega), a8]) (by rw [e14.rd (by rw [s1]; omega), a16])
    (by rw [e14.rd (by rw [s1]; omega), a35])
    ⟨hlt4 _ hc2, hlt4 _ hc40, hlt4 _ hc4⟩
  subst hR4 hR3
  refine ⟨LA ++ (V60 ++ (LBC ++ (LD ++ LE))), ?_, ?_, ?_⟩
  · simp only [gFinE, hr, Bool.cond_true, List.map_append, rsvEOps_split, rsvSOps_reloc, List.append_assoc]
    rw [pureRun_seq impl κ inp hA (pureRun_seq impl κ inp hB1 (pureRun_seq impl κ inp hBC
      (pureRun_seq impl κ inp hD hE)))]
    rw [e04.rd hc2, e04.rd hc40, e04.rd hc4]
    simp only [relE4, hr, ↓reduceIte, Bool.true_and, Bool.and_assoc]
    rfl
  · simp only [gFinE, hr, Bool.cond_true, List.getD_cons_zero]
    rw [← app_app, rd_app_left _ _ (by rw [s1]; omega), a17]; rfl
  · intro i hi _
    simp only [gFinE, hr, Bool.cond_true, List.drop_succ_cons, List.drop_zero]
    have hi' : i < 60 := hi
    rw [getD_mapRange _ _ hi, ← app_app, ← app_app, rd_app_left _ _ (by rw [s2]; omega), hV i hi']
/-- **`finE`'s flag** (revision 4.4.2): without the reserve it is `relE4o` (`flag_gFinE0`). With the
reserve (`rsvOps`) the op list is `gFinE0 … (fun _ => false) false ++ rsvEOps …` (RSV2 §2.2) and the
flag is `relE4`'s first branch (`flag_gFinE1`, block by block). -/
theorem flag_gFinE (hin : ∀ x ∈ (coordsR fi "E1").take P.e2R ++ chals fi "E2" P.e2R ++
      chals fi "E4" P.e4R ++
      [(outsOf fi "E3").headD 0, claimN fi "E2", claim0 fi "E4", claimN fi "E4",
       fi.zhat.getD 3 0, (outsOf fi "Lr3").headD 0, lrEx fi 0, lrEx fi 1, (coordsR fi "E1").getD 23 0, 0],
      x < r.size) :
    ∃ L, pureRun impl κ inp ((gFinE P fi r.size).1.map (reloc P.S)) r [] =
        some (L, relE4 impl κ inp fi r P) ∧
      (rd (r ++ L.toArray) ((gFinE P fi r.size).2.getD 0 0)).toAF =
        ((chals fi "E4" P.e4R).map (fv r)).toArray ∧
      ∀ i < rsvN, P.rsvOps = true → rd (r ++ L.toArray) (((gFinE P fi r.size).2.drop 1).getD i 0) =
        .f (pe4 P.S inp fLrEnd (48 + 16 * i)) := by
  rcases Bool.eq_false_or_eq_true P.rsvOps with hr | hr
  rotate_left
  · have h := flag_gFinE0 impl κ inp fi r P fun x hx => hin x (by
      simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hx ⊢
      rcases hx with ((h | h) | h) | h | h | h | h | h | h | h | h
      exacts [.inl (.inl (.inl h)), .inl (.inl (.inr h)), .inl (.inr h), .inr (.inl h),
        .inr (.inr (.inl h)), .inr (.inr (.inr (.inl h))), .inr (.inr (.inr (.inr (.inl h)))),
        .inr (.inr (.inr (.inr (.inr (.inl h))))), .inr (.inr (.inr (.inr (.inr (.inr (.inl h)))))),
        .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl h))))))),
        .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl h))))))))])
    simp only [gFinE, relE4, hr, cond_false, Bool.false_eq_true, ↓reduceIte, List.getD_cons_zero]
    obtain ⟨L, h1, h2⟩ := h
    exact ⟨L, h1, h2, fun _ _ h => h.elim⟩
  · exact flag_gFinE1 impl κ inp fi r P hr hin

/-! ## `finB′` -/

/-- `pubH` at `P`: the statement's digests read at `S`'s `stmt` offset. -/
def pubH4 (kp : F) : F :=
  let vl := dLo inp.vk; let vh := dHi inp.vk
  let c₁ := bytesAt inp.π (fieldOffOf P.S fStmt + 1) 32
  let c₂ := bytesAt inp.π (fieldOffOf P.S fStmt + 33) 32
  1 + kp * (vl + kp * (vh + kp * (dLo c₁ + kp * (dHi c₁ + kp * (vl + kp * (vh + kp * (dLo c₂ +
    kp * dHi c₂)))))))

/-- `v*` at `P` without the reserve: `v_RS + [node] κ′²·pubH(κ′)` (`finB′`'s export). -/
def vStar4o : F :=
  let kp := fv r ((outsOf fi "B'").headD 0)
  fv r (fi.zhat.getD nRS 0) + (if P.kv.node κ then kp * kp * pubH4 inp P kp else 0)

/-- **`v*` at `P`** (revision 4.4.2, RSV2 §2.2): with the reserve on the kind (`rsvOps ∧ rsv`), the
child claim's 60 values `v_i` (`finE`'s exports after `r′`) at `κ′^{11} … κ′^{70}`:
`v*₀ + κ′^{11}·Σ_{i<60} κ′^i v_i`. -/
def vStar4 : F :=
  let kp := fv r ((outsOf fi "B'").headD 0)
  if P.rsvOps && P.rsv then
    vStar4o κ inp fi r P + kp ^ 11 * ∑ i ∈ Finset.range rsvN,
      kp ^ i * fv r (((fi.ex.getD exE []).drop 1).getD i 0)
  else vStar4o κ inp fi r P

/-- **`relB` at `P`**: `v*` (in `K`) is P1.0's initial claim. -/
def relB4 : Bool := (Val.k (K.smulF (vStar4 κ inp fi r P) 1)).eqv (rd r (claim0 fi "P1"))

theorem flag_gFinB'o (hr : P.rsvOps = false) (hin : ∀ x ∈ [(outsOf fi "B'").headD 0, fi.zhat.getD nRS 0, claim0 fi "P1"],
      x < r.size) :
    ∃ L, pureRun impl κ inp ((gFinB' P fi r.size).1.map (reloc P.S)) r [] =
        some (L, relB4 κ inp fi r P) ∧
      (rd (r ++ L.toArray) ((gFinB' P fi r.size).2.getD 0 0)).toF = vStar4o κ inp fi r P := by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hin
  have tf : ∀ x, (Val.f x).toF = x := fun _ => rfl
  have td : ∀ x, (Val.d x).toD = x := fun _ => rfl
  have tk : ∀ x, (Val.k x).toK = x := fun _ => rfl
  have hS : fStmt < 19 := by decide
  simp only [gFinB', relB4, vStar4, vStar4o, pubH4, dLo, dHi, List.map_cons, List.map_nil,
    reloc_piDigest _ hS, hr, cond_false, Bool.false_and, Bool.false_eq_true, ↓reduceIte, List.append_nil]
  generalize (outsOf fi "B'").headD 0 = kp at *
  generalize fi.zhat.getD nRS 0 = vR at *
  generalize claim0 fi "P1" = c0 at *
  have hk := hin kp (.inl rfl); have hR := hin vR (.inr (.inl rfl))
  have hc := hin c0 (.inr (.inr rfl))
  rw [pureRun_nil_rev]
  cases hn : P.kv.node κ <;>
  simp only [hn, pureRun, reloc, evalOp, absOff_zero, tf, td, tk, rd_revAcc, rd_revAcc0,
    revAcc_app_cons, List.append_nil, List.length_cons, List.length_nil, Nat.reduceAdd,
    Nat.reduceSub, Array.reduceGetElem?, Option.getD_some, rd_app_left _ _ hk, rd_app_left _ _ hR,
    rd_app_left _ _ hc, Option.map_some, allK, Bool.not_true, Bool.false_or,
    Bool.true_and, Bool.and_true, ↓reduceIte, Bool.false_eq_true, digestAt_eq] <;>
  refine ⟨_, rfl, ?_⟩ <;> simp only [List.getD_cons_zero, rd_revAcc,
    List.length_cons, List.length_nil, Nat.reduceAdd, Nat.reduceSub, Array.reduceGetElem?,
    Option.getD_some, tf]

/-- `finB′`'s own ops (33 outputs from `b`), its assert gated by `g`. -/
def gB0 (P : FinP) (fi : FinIn) (b : ℕ) (g : KC Bool) : List Op :=
  let kp := (outsOf fi "B'").headD 0
  let vRS := fi.zhat.getD nRS 0
  [.input 0, .splitDigest b, .piDigest fStmt 1, .splitDigest (b + 3), .piDigest fStmt 33,
    .splitDigest (b + 6), .const (fun _ => .f 1),
    .mulF kp (b + 8), .addF (b + 7) (b + 10), .mulF kp (b + 11), .addF (b + 2) (b + 12),
    .mulF kp (b + 13), .addF (b + 1) (b + 14), .mulF kp (b + 15), .addF (b + 5) (b + 16),
    .mulF kp (b + 17), .addF (b + 4) (b + 18), .mulF kp (b + 19), .addF (b + 2) (b + 20),
    .mulF kp (b + 21), .addF (b + 1) (b + 22), .mulF kp (b + 23), .addF (b + 9) (b + 24),
    .mulF kp kp, .mulF (b + 26) (b + 25), .const (fun _ => .f 0),
    .keep (fun κ => P.kv.node κ) (b + 27) (b + 28),
    .addF vRS (b + 29),
    .const (fun _ => .k 1), .mulKF (b + 31) (b + 30),
    .assertEq (b + 32) (claim0 fi "P1") g]

/-- `rsvBOps`' tail (9 ops from `e = d + 118`): `κ′^{11}`, the claim, its assert. -/
def rsvBTl (fi : FinIn) (kp k2 s9 vRS one e : ℕ) (rsv : KC Bool) : List Op :=
  [Op.mulF k2 k2, Op.mulF e e, Op.mulF (e + 1) k2, Op.mulF (e + 2) kp,
   Op.mulF (e + 3) (e - 1), Op.addF s9 (e + 4), Op.addF vRS (e + 5), Op.mulKF one (e + 6),
   Op.assertEq (e + 7) (claim0 fi "P1") rsv]

theorem gFinB'_rsv (hr : P.rsvOps = true) (b : ℕ) : (gFinB' P fi b).1 =
    gB0 P fi b (fun _ => !P.rsv) ++
      (((List.range 59).flatMap fun k =>
        [Op.mulF ((outsOf fi "B'").headD 0)
          (if k = 0 then ((fi.ex.getD exE []).drop 1).getD 59 0 else b + 33 + 2 * k - 1),
         Op.addF (((fi.ex.getD exE []).drop 1).getD (58 - k) 0) (b + 33 + 2 * k)]) ++
      rsvBTl fi ((outsOf fi "B'").headD 0) (b + 26) (b + 29) (fi.zhat.getD nRS 0) (b + 31) (b + 33 + 118)
        (fun _ => P.rsv)) := by
  simp only [gFinB', hr, Bool.cond_true]; rfl

/-- **Block A of the reserve's `finB′`**: the own ops with the assert gated `¬rsv`. -/
theorem run_gB0 (hin : ∀ x ∈ [(outsOf fi "B'").headD 0, fi.zhat.getD nRS 0, claim0 fi "P1"], x < r.size) :
    ∃ L, pureRun impl κ inp ((gB0 P fi r.size (fun _ => !P.rsv)).map (reloc P.S)) r [] =
        some (L, P.rsv || (Val.k (K.smulF (vStar4o κ inp fi r P) 1)).eqv (rd r (claim0 fi "P1"))) ∧
      L.length = 33 ∧
      rd (r ++ L.toArray) (r.size + 26) = .f (fv r ((outsOf fi "B'").headD 0) * fv r ((outsOf fi "B'").headD 0)) ∧
      rd (r ++ L.toArray) (r.size + 29) = .f (if P.kv.node κ then
        fv r ((outsOf fi "B'").headD 0) * fv r ((outsOf fi "B'").headD 0) *
          pubH4 inp P (fv r ((outsOf fi "B'").headD 0)) else 0) ∧
      rd (r ++ L.toArray) (r.size + 31) = .k 1 ∧
      (rd (r ++ L.toArray) (r.size + 30)).toF = vStar4o κ inp fi r P := by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hin
  have tf : ∀ x, (Val.f x).toF = x := fun _ => rfl
  have td : ∀ x, (Val.d x).toD = x := fun _ => rfl
  have tk : ∀ x, (Val.k x).toK = x := fun _ => rfl
  have hS : fStmt < 19 := by decide
  simp only [gB0, vStar4o, pubH4, dLo, dHi, List.map_cons, List.map_nil, reloc_piDigest _ hS]
  generalize (outsOf fi "B'").headD 0 = kp at *
  generalize fi.zhat.getD nRS 0 = vR at *
  generalize claim0 fi "P1" = c0 at *
  have hk := hin kp (.inl rfl); have hR := hin vR (.inr (.inl rfl))
  have hc := hin c0 (.inr (.inr rfl))
  rw [pureRun_nil_rev]
  cases hn : P.kv.node κ <;>
  simp only [hn, pureRun, reloc, evalOp, absOff_zero, tf, td, tk, rd_revAcc, rd_revAcc0,
    revAcc_app_cons, List.append_nil, List.length_cons, List.length_nil, Nat.reduceAdd,
    Nat.reduceSub, Array.reduceGetElem?, Option.getD_some, rd_app_left _ _ hk, rd_app_left _ _ hR,
    rd_app_left _ _ hc, Option.map_some, allK, Bool.not_true, Bool.false_or,
    Bool.true_and, Bool.and_true, ↓reduceIte, Bool.false_eq_true, digestAt_eq, Bool.not_not] <;>
  refine ⟨_, rfl, rfl, ?_, ?_, ?_, ?_⟩ <;> simp only [rd_revAcc,
    List.length_cons, List.length_nil, Nat.reduceAdd, Nat.reduceSub, Array.reduceGetElem?,
    Option.getD_some, tf]

/-- **`finB′`'s flag with the reserve** (`rsvOps`): the own block (`run_gB0`), the Horner chain
(`run_rsvHorner`) and the tail. Reads the 60 exports of `finE` (`hex`). -/
theorem flag_gFinB'1 (hr : P.rsvOps = true)
    (hin : ∀ x ∈ [(outsOf fi "B'").headD 0, fi.zhat.getD nRS 0, claim0 fi "P1"], x < r.size)
    (hex : ∀ x ∈ (fi.ex.getD exE []).drop 1, x < r.size) :
    ∃ L, pureRun impl κ inp ((gFinB' P fi r.size).1.map (reloc P.S)) r [] =
        some (L, relB4 κ inp fi r P) ∧
      (rd (r ++ L.toArray) ((gFinB' P fi r.size).2.getD 0 0)).toF = vStar4o κ inp fi r P := by
  obtain ⟨LA, hA, hlA, a26, a29, a31, a30⟩ := run_gB0 impl κ inp fi r P hin
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hin
  have hk := hin _ (.inl rfl); have hR := hin _ (.inr (.inl rfl)); have hc := hin _ (.inr (.inr rfl))
  have hpos : 0 < r.size := Nat.lt_of_le_of_lt (Nat.zero_le _) hk
  have hvs : ∀ j, ((fi.ex.getD exE []).drop 1).getD j 0 < r.size := fun j => getD_lt' hpos hex j
  have s1 : (r ++ LA.toArray).size = r.size + 33 := by simp [hlA]
  have e1 : ExtA r (r ++ LA.toArray) := ExtA.app r LA
  obtain ⟨MH, hH, hlH, hvH⟩ := run_rsvHorner impl κ inp (r ++ LA.toArray) (r.size + 33) s1
    ((outsOf fi "B'").headD 0) (((fi.ex.getD exE []).drop 1).getD 59 0)
    (fun k => ((fi.ex.getD exE []).drop 1).getD (58 - k) 0)
    (fv r ((outsOf fi "B'").headD 0)) (fv r (((fi.ex.getD exE []).drop 1).getD 59 0))
    (fun k => fv r (((fi.ex.getD exE []).drop 1).getD (58 - k) 0))
    ⟨Nat.lt_of_lt_of_le hk (by omega), by rw [e1.rd hk]⟩
    ⟨Nat.lt_of_lt_of_le (hvs 59) (by omega), by rw [e1.rd (hvs 59)]⟩
    (fun k => ⟨Nat.lt_of_lt_of_le (hvs _) (by omega), by rw [e1.rd (hvs _)]⟩) 59
  have s2 : (r ++ LA.toArray ++ MH.toArray).size = r.size + 33 + 118 := by simp [hlA, hlH]
  have e2 : ExtA (r ++ LA.toArray) (r ++ LA.toArray ++ MH.toArray) := ExtA.app _ MH
  have e02 := e1.trans e2
  have g : ∀ x, x < r.size + 33 → ∀ L : List Val,
      rd (r ++ LA.toArray ++ MH.toArray ++ L.toArray) x = rd (r ++ LA.toArray) x := fun x hx L => by
    rw [rd_app_left _ _ (by rw [s2]; omega), e2.rd (by rw [s1]; exact hx)]
  have g0 : ∀ x, x < r.size → ∀ L : List Val,
      rd (r ++ LA.toArray ++ MH.toArray ++ L.toArray) x = rd r x := fun x hx L => by
    rw [g x (by omega) L, e1.rd hx]
  have gH : ∀ L : List Val, rd (r ++ LA.toArray ++ MH.toArray ++ L.toArray) (r.size + 33 + 118 - 1) =
      .f (hornerV (fv r ((outsOf fi "B'").headD 0)) (fv r (((fi.ex.getD exE []).drop 1).getD 59 0))
        (fun k => fv r (((fi.ex.getD exE []).drop 1).getD (58 - k) 0)) 59) := fun L => by
    rw [rd_app_left _ _ (by rw [s2]; omega), show r.size + 33 + 118 - 1 = r.size + 33 + 2 * 58 + 1 by omega,
      hvH 58 (by norm_num)]
  have g26 := g (r.size + 26) (by omega); have g29 := g (r.size + 29) (by omega)
  have g30 := g (r.size + 30) (by omega); have g31 := g (r.size + 31) (by omega)
  have gk := g0 _ hk; have gR := g0 _ hR; have gc := g0 _ hc
  have tf : ∀ x, (Val.f x).toF = x := fun _ => rfl
  have tk : ∀ x, (Val.k x).toK = x := fun _ => rfl
  have hsum := hornerV_eq_sum (fv r ((outsOf fi "B'").headD 0))
    (fun j => fv r (((fi.ex.getD exE []).drop 1).getD j 0)) 59 59 le_rfl
  simp only [Nat.reduceSub, Nat.sub_self, zero_add, Nat.reduceAdd] at hsum
  have hT : ∃ LT fT, pureRun impl κ inp ((rsvBTl fi ((outsOf fi "B'").headD 0) (r.size + 26) (r.size + 29)
      (fi.zhat.getD nRS 0) (r.size + 31) (r.size + 33 + 118) (fun _ => P.rsv)).map (reloc P.S))
      (r ++ LA.toArray ++ MH.toArray) [] = some (LT, fT) ∧ fT = (!P.rsv || (Val.k (K.smulF (vStar4o κ inp fi r P +
        fv r ((outsOf fi "B'").headD 0) ^ 11 * ∑ i ∈ Finset.range rsvN,
          fv r ((outsOf fi "B'").headD 0) ^ i * fv r (((fi.ex.getD exE []).drop 1).getD i 0)) 1)).eqv
        (rd r (claim0 fi "P1"))) := by
    simp only [rsvBTl, List.map_cons, List.map_nil]
    rw [pureRun_nil_rev]
    simp only [pureRun, reloc, evalOp, tf, tk, rd_revAccAt _ _ s2, revAcc_app_cons, List.append_nil,
      List.length_cons, List.length_nil, Nat.reduceAdd, Nat.reduceSub, Nat.add_sub_cancel_left,
      Nat.le_add_right, le_refl, Nat.sub_self, Array.reduceGetElem?, Option.getD_some, g26, g29,
      g31, gk, gR, gc, gH, a26, a29, a31, Option.map_some, Bool.true_and, Bool.and_true, hsum]
    refine ⟨_, _, rfl, ?_⟩
    simp only [vStar4o, rsvN]
    congr 4
    ring

  obtain ⟨LT, fT, hT, rfl⟩ := hT
  refine ⟨LA ++ (MH ++ LT), ?_, ?_⟩
  · rw [gFinB'_rsv (fi := fi) (P := P) hr, List.map_append, List.map_append]
    have hHr : ((List.range 59).flatMap fun k =>
        [Op.mulF ((outsOf fi "B'").headD 0)
          (if k = 0 then ((fi.ex.getD exE []).drop 1).getD 59 0 else r.size + 33 + 2 * k - 1),
         Op.addF (((fi.ex.getD exE []).drop 1).getD (58 - k) 0) (r.size + 33 + 2 * k)]).map (reloc P.S) =
        (List.range 59).flatMap fun k =>
        [Op.mulF ((outsOf fi "B'").headD 0)
          (if k = 0 then ((fi.ex.getD exE []).drop 1).getD 59 0 else r.size + 33 + 2 * k - 1),
         Op.addF (((fi.ex.getD exE []).drop 1).getD (58 - k) 0) (r.size + 33 + 2 * k)] := by
      simp only [List.map_flatMap, List.map_cons, List.map_nil, reloc]
    rw [hHr, pureRun_seq impl κ inp hA (pureRun_seq impl κ inp hH hT)]
    cases hrs : P.rsv <;> simp [relB4, vStar4, hr, hrs]
  · simp only [gFinB', List.getD_cons_zero]
    rw [← app_app, rd_app_left _ _ (by rw [s1]; omega), a30]

/-- **`finB′`'s flag** (revision 4.4.2). Without the reserve, `flag_gFinB'o`. With it, B′'s own
assert is gated `¬rsv` and `rsvBOps` (Horner over the 60 exports, RSV2 §2.2) asserts `v*` where
`rsv` (`flag_gFinB'1`; `hex`: `finE`'s exports are registers of the file). The export is `v*₀`
(`vStar4o`) in both cases. -/
theorem flag_gFinB' (hin : ∀ x ∈ [(outsOf fi "B'").headD 0, fi.zhat.getD nRS 0, claim0 fi "P1"],
      x < r.size) (hex : ∀ x ∈ (fi.ex.getD exE []).drop 1, x < r.size) :
    ∃ L, pureRun impl κ inp ((gFinB' P fi r.size).1.map (reloc P.S)) r [] =
        some (L, relB4 κ inp fi r P) ∧
      (rd (r ++ L.toArray) ((gFinB' P fi r.size).2.getD 0 0)).toF = vStar4o κ inp fi r P := by
  cases hr : P.rsvOps
  · exact flag_gFinB'o impl κ inp fi r P hr hin
  · exact flag_gFinB'1 impl κ inp fi r P hr hin hex

end Flags

end FR.Snd.R4

end G6_FRSoundness4R4Fin

section G6_FRSoundness4R4FinLc

-- New for `flock-recursive` (BLUEPRINT revision 4.1, A.9 `finLc`; stage R4c).

/-!
# `finLc`'s flag at `FinP` on the relocated ops

3.x's `flag_finLc` (`FRVIRFinals`, revision 3.16) for `gFinLc P`: Z3's `P.S.z3` challenges (the
first eight), the kind's node flag `P.kv.node`, and L3's message and the Z-end pair read at `S`'s
offsets (`pe4 P.S`). The 64-term sum (`dotOps`) and the tail (`lcTail`) read no proof byte, so the
relocation leaves them unchanged (`dotOps_reloc`, `lcTail_reloc`).
-/

namespace FR.Snd.R4
open RecursionFast Rev4

theorem dotOps_reloc (S : Seq) (x y z c : ℕ) : ∀ n, (dotOps x y z c n).map (reloc S) = dotOps x y z c n
  | 0 => rfl
  | n + 1 => by rw [dotOps, List.map_append, dotOps_reloc S x y z c n]; rfl

theorem lcTail_reloc (S : Seq) (fi : FinIn) (b d : ℕ) : (lcTail fi b d).map (reloc S) = lcTail fi b d := rfl

section Flags
variable (impl : OpImpl) (κ : Kind) (inp : Input) (fi : FinIn) (r : Array Val) (P : FinP)


/-- `finLc`'s claims `v_0 … v_7` (L3's message). -/
def lcV4 : List F := (List.range 8).map fun i => pe4 P.S inp fL2 (phaseOffOf P.S (phaseIx "L3") fL2 + 16 * i)

/-- `r′_hi`: Z3's first 8 challenges. -/
def lcRhi4 : Array F := (((chals fi "Z3" P.S.z3).take 8).map (fv r)).toArray

/-- **The walk** `Â + α B̂` at `rowW′ = maskRows w rowW` and `eq(r_k, ·)`; `w` = a node's
`nodeKindW v` (`free` weight 0, revision 3.16), a leaf's `v₀ :: 0^8`. -/
def lcWalk4 : F :=
  let α := fv r ((outsOf fi "L1").headD 0)
  let w : List F := if P.kv.node κ then nodeKindW (lcV4 inp P) else (lcV4 inp P).headD 0 :: List.replicate 8 0
  let rw := maskRows w.toArray (impl.rowW (fv r ((outsOf fi "Z2").headD 0)) (lcRhi4 fi r P))
  let cw := eqTab (lcRk fi r).toArray
  (impl.walkAB rw cw).1 + α * (impl.walkAB rw cw).2

/-- `v_free`: a node's `v₇`, a leaf's `0`. -/
def lcVf4 : F := if P.kv.node κ then pe4 P.S inp fL2 (phaseOffOf P.S (phaseIx "L3") fL2 + 16 * 7) else 0

/-- **`free`'s term without `(1 + α)`** (revision 3.16, R-V-M2): `v_free · (Σ_{s<64} L_s(λ)
eq(r_k[0..5], s)) · eq(r′_hi, r_k[6..13])` (`L_s(λ)` = `eqZ(λ, 0)[s]`); its spec is
`FRSpartan.linM_free_mle`, `⟨rowW, eq(r_k, ·)⟩` in closed form. -/
def lcFree4 : F :=
  lcVf4 κ inp P * (dotAcc 0 (impl.eqZ (fv r ((outsOf fi "Z2").headD 0)) 0)
    (eqTab (((chals fi "L2" 14).take 6).map (fv r)).toArray) 64 * eqPoint (lcRhi4 fi r P) (((chals fi "L2" 14).drop 6).map (fv r)).toArray)

/-- (+) **A leaf's `free` term is `0`**: `lcVf` is `0`, so a leaf's (ii) is the 3.15 walk. -/
theorem lcFree4_leaf (h : P.kv.node κ = false) : lcFree4 impl κ inp fi r P = 0 := by
  simp [lcFree4, lcVf4, h]

/-- **A.9's `finLc` relation** over the register values (revision 3.16): (i) `c₀ = â + α b̂`,
(iii) `Σ_{i<8} β^i v_i = α₂`, (ii) `c_Lc = walk + (1 + α)·lcFree` (as `Y + α Y`). -/
def relLc4 : Bool :=
  let α := fv r ((outsOf fi "L1").headD 0); let β := fv r ((outsOf fi "L3β").headD 0)
  let v := lcV4 inp P
  let vβ := (v.reverse.drop 1).foldl (fun acc x => x + β * acc) (v.getD 7 0)
  let y := lcFree4 impl κ inp fi r P
  ((Val.f (pe4 P.S inp fZend 0 + α * pe4 P.S inp fZend 16)).eqv (rd r (claim0 fi "L2")) &&
    (Val.f vβ).eqv (rd r (fi.zhat.getD 1 0))) &&
  (Val.f (lcWalk4 impl κ inp fi r P + (y + α * y))).eqv (rd r (claimN fi "L2"))

set_option maxRecDepth 4096 in
/-- **`flag_finLc` at `P`**: the relocated `gFinLc`'s flag is `relLc4`. -/
theorem flag_gFinLc (hin : ∀ x ∈ (chals fi "Z3" P.S.z3).take 8 ++ chals fi "L2" 14 ++
      [(outsOf fi "L1").headD 0, (outsOf fi "L3β").headD 0, (outsOf fi "Z2").headD 0,
       claim0 fi "L2", claimN fi "L2", fi.zhat.getD 1 0], x < r.size) :
    ∃ L, pureRun impl κ inp ((gFinLc P fi r.size).1.map (reloc P.S)) r [] = some (L, relLc4 impl κ inp fi r P) := by
  simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hin
  have h1 := fun L => map_rd_app r L ((chals fi "Z3" P.S.z3).take 8) fun x hx => hin x (.inl (.inl hx))
  have h2 := fun L => map_rd_app r L (chals fi "L2" 14) fun x hx => hin x (.inl (.inr hx))
  have h2a := fun L => map_rd_app r L ((chals fi "L2" 14).take 6)
    fun x hx => hin x (.inl (.inr (List.mem_of_mem_take hx)))
  have tf : ∀ x, (Val.f x).toF = x := fun _ => rfl
  have taf : ∀ x, (Val.af x).toAF = x := fun _ => rfl
  have hZ : fZend < 19 := by decide
  have hL2 : fL2 < 19 := by decide
  have ha := hin _ (.inr (.inl rfl)); have hb := hin _ (.inr (.inr (.inl rfl)))
  have hl := hin _ (.inr (.inr (.inr (.inl rfl))))
  have hc0 := hin _ (.inr (.inr (.inr (.inr (.inl rfl)))))
  have hcN := hin _ (.inr (.inr (.inr (.inr (.inr (.inl rfl))))))
  have hz := hin _ (.inr (.inr (.inr (.inr (.inr (.inr rfl))))))
  -- the head: registers `b … b + 40`
  obtain ⟨V1, f1, hA, hlen, hf1, g4, g14, g22, g37, g38, g40⟩ : ∃ V1 f1,
      pureRun impl κ inp ((gLcHead P fi r.size).map (reloc P.S)) r [] = some (V1, f1) ∧ V1.length = 41 ∧
      f1 = ((Val.f (pe4 P.S inp fZend 0 + fv r ((outsOf fi "L1").headD 0) * pe4 P.S inp fZend 16)).eqv
          (rd r (claim0 fi "L2")) &&
        (Val.f (((lcV4 inp P).reverse.drop 1).foldl
          (fun acc x => x + fv r ((outsOf fi "L3β").headD 0) * acc) ((lcV4 inp P).getD 7 0))).eqv
          (rd r (fi.zhat.getD 1 0))) ∧
      V1.getD 4 default = .af (lcRhi4 fi r P) ∧ V1.getD 14 default = .f 0 ∧
      V1.getD 22 default = .f (lcWalk4 impl κ inp fi r P) ∧ V1.getD 37 default = .f (lcVf4 κ inp P) ∧
      V1.getD 38 default = .af (impl.eqZ (fv r ((outsOf fi "Z2").headD 0)) 0) ∧
      V1.getD 40 default = .af (eqTab (((chals fi "L2" 14).take 6).map (fv r)).toArray) := by
    cases hk : P.kv.node κ
    all_goals
      apply Exists.intro
      apply Exists.intro
      refine ⟨?run, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      case run =>
        rw [pureRun_nil_rev]
        simp only [gLcHead, hk, List.map_cons, List.map_nil, hZ, hL2, reloc, absOff_zero, pureRun, evalOp, tf, taf, List.nil_append, List.cons_append, h1, h2,
            h2a, hornerOps, rd_revAcc, rd_revAcc0, revAcc_app_cons, List.append_nil,
            List.length_cons, List.length_nil, Array.reduceGetElem?, rd_app_left _ _ ha,
            rd_app_left _ _ hb,
            rd_app_left _ _ hl, rd_app_left _ _ hc0, rd_app_left _ _ hz, List.range_succ,
            List.range_zero, List.map_cons, List.map_nil, List.map_append,
            Option.getD_some, Option.map_some, allK, Bool.not_true, Bool.false_or, Bool.true_and,
            Bool.and_true, List.take_succ_cons, List.take_zero, List.replicate_succ,
            List.replicate_zero, ite_true, ite_false, Bool.false_eq_true, List.flatMap_append,
            List.flatMap_cons, List.flatMap_nil, ↓reduceIte, Nat.reduceEqDiff, Nat.reduceAdd,
            Nat.reduceMul, Nat.reduceSub]
        rfl
      all_goals
        try simp only [List.length_reverse, List.length_cons, List.length_nil, getD_revAcc,
          Nat.reduceAdd, Nat.reduceSub, Array.reduceGetElem?, Option.getD_some]
      all_goals
        try simp only [lcWalk4, lcV4, lcRhi4, lcRk, lcVf4, nodeKindW, hk, ite_true, ite_false,
          Bool.false_eq_true, List.range_succ, List.range_zero, List.map_cons, List.map_nil,
          List.map_append, List.nil_append, List.cons_append, List.getD_cons_succ,
          List.getD_cons_zero, List.take_succ_cons, List.take_zero, List.headD_cons,
          List.replicate_succ, List.replicate_zero, List.reverse_cons, List.reverse_nil,
          List.drop_succ_cons, List.drop_zero,
          List.foldl_cons, List.foldl_nil, List.getD_eq_getElem?_getD, List.getElem?_cons_succ,
          List.getElem?_cons_zero, Option.getD_some, Nat.reduceMul]
      all_goals rfl
  -- the 64-term sum: registers `b + 41 … b + 296`
  have hsz : (r ++ V1.toArray).size = r.size + 41 := by simp [hlen]
  have hD := run_dotOps impl κ inp (r ++ V1.toArray) (r.size + 38) (r.size + 40) (r.size + 14)
    (by rw [hsz]; omega) (by rw [hsz]; omega) (by rw [hsz]; omega) 64
  rw [hsz, rd_app, rd_app, rd_app, g14, g38, g40] at hD
  set dv := dotVals (Val.f 0).toF (Val.af (impl.eqZ (fv r ((outsOf fi "Z2").headD 0)) 0)).toAF
    (Val.af (eqTab (((chals fi "L2" 14).take 6).map (fv r)).toArray)).toAF 64 with hdv
  -- the tail: registers from `b + 297`
  set R2 := r ++ (V1 ++ dv).toArray with hR2def
  have hR2 : R2.size = r.size + 297 := by simp [R2, hlen, hdv, dotVals_length]
  have rr : ∀ i < r.size, ∀ L : List Val, rd (R2 ++ L.toArray) i = rd r i := fun i hi L => by
    rw [rd_app_left R2 L (by omega), hR2def, rd_app_left r _ hi]
  have rv : ∀ k < 41, ∀ L : List Val, rd (R2 ++ L.toArray) (r.size + k) = V1.getD k default :=
    fun k hk L => by
      rw [rd_app_left R2 L (by omega), hR2def, rd_app, List.getD_eq_getElem?_getD,
        List.getElem?_append_left (by omega), ← List.getD_eq_getElem?_getD]
  have rs : ∀ L : List Val, rd (R2 ++ L.toArray) (r.size + 296) =
      .f (dotAcc 0 (impl.eqZ (fv r ((outsOf fi "Z2").headD 0)) 0)
        (eqTab (((chals fi "L2" 14).take 6).map (fv r)).toArray) 64) := fun L => by
    rw [rd_app_left R2 L (by omega), hR2def, rd_app, List.getD_eq_getElem?_getD,
      List.getElem?_append_right (by omega), hlen, ← List.getD_eq_getElem?_getD, hdv,
      show 296 - 41 = 4 * 63 + 3 by norm_num, dotVals_last]
    rfl
  have h2b := fun L => map_rd_app' r R2 rr L ((chals fi "L2" 14).drop 6)
    fun x hx => hin x (.inl (.inr (List.mem_of_mem_drop hx)))
  obtain ⟨V3, hC⟩ : ∃ V3, pureRun impl κ inp (lcTail fi r.size R2.size) R2 [] =
      some (V3, (Val.f (lcWalk4 impl κ inp fi r P + (lcFree4 impl κ inp fi r P +
        fv r ((outsOf fi "L1").headD 0) * lcFree4 impl κ inp fi r P))).eqv (rd r (claimN fi "L2"))) := by
    rw [pureRun_nil_rev]
    simp only [lcTail, pureRun, evalOp, tf, taf, h2b, rd_revAcc, rd_revAcc0, revAcc_app_cons,
      List.append_nil, List.length_cons, List.length_nil, Nat.reduceAdd, Nat.reduceSub,
      Array.reduceGetElem?, Option.getD_some, rv 4 (by norm_num), rv 22 (by norm_num),
      rv 37 (by norm_num), rs, g4, g22, g37, rr _ ha, rr _ hb, rr _ hcN, Option.map_some,
      allK, Bool.not_true, Bool.false_or, Bool.true_and, Bool.and_true]
    exact ⟨_, rfl⟩
  have e : (gFinLc P fi r.size).1.map (reloc P.S) =
      ((gLcHead P fi r.size).map (reloc P.S) ++
        dotOps (r.size + 38) (r.size + 40) (r.size + 14) (r.size + 41) 64) ++
        lcTail fi r.size R2.size := by
    rw [hR2]; simp only [gFinLc, List.map_append, dotOps_reloc, lcTail_reloc, List.append_assoc]
  rw [e, pureRun_seq impl κ inp (pureRun_seq impl κ inp hA hD) hC, hf1]
  exact ⟨_, by simp only [relLc4, Bool.and_true]; rfl⟩



end Flags

end FR.Snd.R4

end G6_FRSoundness4R4FinLc

section G6_FRSoundness4R4FinRS

-- New for `flock-recursive` (BLUEPRINT revision 4.1, A.9 `finRS`; stage R4c).

/-!
# `finRS` at `FinP` on the relocated ops

3.x's `exec_finRS` (`FRVIRFinalsSF`) for `gFinRS P`: the slice values are read at `S`'s RS0 offset
(`sv4`), the Sh point's low part is S2's `P.S.s2` challenges from `P.kv.m κ − 14`, a leaf's fourth
claim's zero check reads `S`'s offset (`rsLeafZero4`) and is gated by `P.kv.node`. The run kit
(`run_elemOps4`, `run_elemsOps4`, `run_claimOps4`, `run_rsTail4`) is 3.x's on the relocated ops.
-/

namespace FR.Snd.R4
open RecursionFast Rev4

/-- Slice value `i` of claim `j` at `S`'s RS0 offset. -/
def sv4 (S : Seq) (inp : Input) (j i : ℕ) : F :=
  F.ofBytes (bytesAt inp.π (fieldOffOf S fRS0 + rsOff j i) 16)

/-- A leaf's fourth claim's slice bytes are zero (at `S`'s RS0 offset). -/
def rsLeafZero4 (S : Seq) (inp : Input) : Bool :=
  (inp.π.extract (fieldOffOf S fRS0 + rsOff 3 0) (fieldOffOf S fRS0 + rsOff 3 0 + 2048)).data.all (· == 0)

section Run
variable (impl : OpImpl) (κ : Kind) (inp : Input) (r : Array Val) (S : Seq)


/-- **One slice value**: the claim value gains `c · s`, the switched claim `bitBasis i · Φ(s)`. -/
theorem run_elemOps4 (j i aA aT R : ℕ) (wop : ℕ → Op) (c A T : F) (rpp : Array F) (L : List Val)
    (hR : R < r.size + L.length) (hRv : (rd (r ++ L.toArray) R).toAF = rpp)
    (hA : aA < r.size + L.length) (hT : aT < r.size + L.length)
    (hAv : (rd (r ++ L.toArray) aA).toF = A) (hTv : (rd (r ++ L.toArray) aT).toF = T)
    (hw : ∀ X : List Val, evalOp impl κ inp (r ++ (L ++ X).toArray) (wop i) = .vals [.f c] true)
    (hwr : reloc S (wop i) = wop i) :
    ∃ M, pureRun impl κ inp ((elemOps j i wop R aA aT (r.size + L.length)).map (reloc S)) r L = some (L ++ M, true) ∧
      M.length = elemW ∧
      (rd (r ++ (L ++ M).toArray) (r.size + L.length + 3)).toF = A + c * sv4 S inp j i ∧
      (rd (r ++ (L ++ M).toArray) (r.size + L.length + elemW - 1)).toF =
        T + bb i * impl.phiRS rpp (sv4 S inp j i) := by
  set s := sv4 S inp j i
  have tf : ∀ x, (Val.f x).toF = x := fun _ => rfl
  have e0 : evalOp impl κ inp (r ++ L.toArray) (.piElem 0 (fieldOffOf S fRS0 + rsOff j i)) =
      .vals [.f s] true := by simp only [evalOp, absOff_zero]; rfl
  have hRS : fRS0 < 19 := by decide
  have e1 : evalOp impl κ inp (r ++ (L ++ [Val.f s]).toArray) (wop i) = .vals [.f c] true := hw _
  set φ := impl.phiRS rpp s
  refine ⟨[.f s, .f c, .f (c * s), .f (A + c * s), .f φ, .f (bb i), .f (bb i * φ),
    .f (T + bb i * φ)], ?_, rfl, ?_, ?_⟩
  · simp only [elemOps, List.map_cons, List.map_nil, hwr]
    simp only [hRS, reloc, ite_true]
    rw [pr_op impl κ inp r e0, pr_op impl κ inp r e1]
    simp only [pureRun, evalOp, List.append_assoc, List.cons_append, List.nil_append, rdX, rdX0,
      List.getD_cons_succ, List.getD_cons_zero, tf, rdL r hA, rdL r hT, rdL r hR, hAv, hTv, hRv,
      Option.map_some, Bool.true_and, Bool.and_true]
    rfl
  · rw [rdX]; rfl
  · rw [show r.size + L.length + elemW - 1 = r.size + L.length + 7 from rfl, rdX]; rfl

/-- **A claim's slice values, `n` of them**: the claim value and the switched claim as sums. -/
theorem run_elemsOps4 (j : ℕ) (wop : ℕ → Op) (R : ℕ) (rpp : Array F) (c : ℕ → F) (L₀ : List Val)
    (hR : R < r.size + L₀.length) (hRv : (rd (r ++ L₀.toArray) R).toAF = rpp)
    (hw : ∀ i (X : List Val), evalOp impl κ inp (r ++ (L₀ ++ X).toArray) (wop i) = .vals [.f (c i)] true)
    (hwr : ∀ i, reloc S (wop i) = wop i) (n : ℕ) : ∀ (i aA aT : ℕ) (A T : F) (X : List Val), aA < r.size + L₀.length + X.length →
    aT < r.size + L₀.length + X.length → (rd (r ++ (L₀ ++ X).toArray) aA).toF = A →
    (rd (r ++ (L₀ ++ X).toArray) aT).toF = T →
    ∃ M, pureRun impl κ inp ((elemsOps j wop R n i aA aT (r.size + L₀.length + X.length)).map (reloc S)) r (L₀ ++ X) =
      some (L₀ ++ X ++ M, true) ∧ M.length = n * elemW ∧
      (0 < n → (rd (r ++ (L₀ ++ X ++ M).toArray) (r.size + L₀.length + X.length + (n - 1) * elemW + 3)).toF =
          A + ∑ k ∈ Finset.range n, c (i + k) * sv4 S inp j (i + k) ∧
        (rd (r ++ (L₀ ++ X ++ M).toArray) (r.size + L₀.length + X.length + n * elemW - 1)).toF =
          T + ∑ k ∈ Finset.range n, bb (i + k) * impl.phiRS rpp (sv4 S inp j (i + k))) := by
  induction n with
  | zero => intro i aA aT A T X _ _ _ _; exact ⟨[], by simp [elemsOps, pureRun], by simp, by simp⟩
  | succ n ih =>
    intro i aA aT A T X hA hT hAv hTv
    have hlen : r.size + (L₀ ++ X).length = r.size + L₀.length + X.length := by simp; omega
    obtain ⟨M₁, h₁, hl₁, hα, hτ⟩ := run_elemOps4 impl κ inp r S j i aA aT R wop (c i) A T rpp (L₀ ++ X)
      (by rw [hlen]; omega) (by rw [rdL r hR, hRv]) (by rw [hlen]; exact hA) (by rw [hlen]; exact hT)
      hAv hTv (fun Y => by rw [List.append_assoc]; exact hw i _) (hwr i)
    rw [hlen] at h₁ hα hτ
    obtain ⟨M₂, h₂, hl₂, hv₂⟩ := ih (i + 1) (r.size + L₀.length + X.length + 3)
      (r.size + L₀.length + X.length + elemW - 1) (A + c i * sv4 S inp j i)
      (T + bb i * impl.phiRS rpp (sv4 S inp j i)) (X ++ M₁)
      (by simp only [List.length_append, hl₁, elemW]; omega)
      (by simp only [List.length_append, hl₁, elemW]; omega)
      (by simpa only [List.append_assoc] using hα) (by simpa only [List.append_assoc] using hτ)
    have hb : r.size + L₀.length + (X ++ M₁).length = r.size + L₀.length + X.length + elemW := by
      simp [hl₁]; omega
    rw [hb] at h₂ hv₂
    refine ⟨M₁ ++ M₂, ?_, by simp [hl₁, hl₂]; ring, fun _ => ?_⟩
    · simp only [elemsOps, List.map_append]
      rw [pr_app impl κ inp r h₁, List.append_assoc L₀ X M₁, h₂]; simp
    · rcases Nat.eq_zero_or_pos n with rfl | hn
      · rw [Nat.zero_mul, List.length_eq_zero_iff] at hl₂; subst hl₂
        simp only [List.append_nil, Nat.zero_add, Finset.sum_range_one, Nat.add_zero, Nat.sub_self,
          Nat.zero_mul, Nat.one_mul]
        exact ⟨hα, hτ⟩
      · obtain ⟨h3, h4⟩ := hv₂ hn
        have hk : ∀ k, i + 1 + k = i + (k + 1) := fun k => by omega
        simp only [List.append_assoc] at h3 h4 ⊢
        refine ⟨?_, ?_⟩
        · rw [show r.size + L₀.length + X.length + (n + 1 - 1) * elemW + 3 =
            r.size + L₀.length + X.length + elemW + (n - 1) * elemW + 3 by
              simp only [elemW]; omega, h3, Finset.sum_range_succ']
          simp only [hk, Nat.add_zero]; ring
        · rw [show r.size + L₀.length + X.length + (n + 1) * elemW - 1 =
            r.size + L₀.length + X.length + elemW + n * elemW - 1 by
              simp only [elemW]; omega, h4, Finset.sum_range_succ']
          simp only [hk, Nat.add_zero]; ring

theorem run_claimOps4 (j : ℕ) (wop : ℕ → Op) (R : ℕ) (rpp : Array F) (c : ℕ → F) (L₀ X : List Val)
    (hR : R < r.size + L₀.length) (hRv : (rd (r ++ L₀.toArray) R).toAF = rpp)
    (hw : ∀ i (X : List Val), evalOp impl κ inp (r ++ (L₀ ++ X).toArray) (wop i) = .vals [.f (c i)] true)
    (hwr : ∀ i, reloc S (wop i) = wop i) :
    ∃ M, pureRun impl κ inp ((claimOps j wop R (r.size + L₀.length + X.length)).map (reloc S)) r (L₀ ++ X) =
      some (L₀ ++ X ++ M, true) ∧ M.length = 1 + 128 * elemW ∧
      (rd (r ++ (L₀ ++ X ++ M).toArray) (r.size + L₀.length + X.length + 127 * elemW + 4)).toF =
        ∑ k ∈ Finset.range 128, c k * sv4 S inp j k ∧
      (rd (r ++ (L₀ ++ X ++ M).toArray) (r.size + L₀.length + X.length + 128 * elemW)).toF =
        ∑ k ∈ Finset.range 128, bb k * impl.phiRS rpp (sv4 S inp j k) := by
  set B := r.size + L₀.length + X.length
  have e0 : evalOp impl κ inp (r ++ (L₀ ++ X).toArray) (.const (fun _ => .f 0)) = .vals [.f 0] true := rfl
  have hz : (rd (r ++ (L₀ ++ (X ++ [Val.f 0])).toArray) B).toF = 0 := by
    rw [← List.append_assoc, show B = r.size + (L₀ ++ X).length by simp [B]; omega, rd_new1]; rfl
  obtain ⟨M, hM, hl, hv⟩ := run_elemsOps4 impl κ inp r S j wop R rpp c L₀ hR hRv hw hwr 128 0 B B 0 0
    (X ++ [Val.f 0]) (by simp [B]) (by simp [B]) hz hz
  have hb : r.size + L₀.length + (X ++ [Val.f 0]).length = B + 1 := by simp [B]; omega
  rw [hb] at hM hv
  obtain ⟨h1, h2⟩ := hv (by decide)
  refine ⟨[Val.f 0] ++ M, ?_, by simp [hl]; omega, ?_, ?_⟩
  · simp only [claimOps, List.map_cons]; rw [show reloc S (.const (fun _ => .f 0)) = .const (fun _ => .f 0) from rfl,
      pr_op impl κ inp r e0]
    simp only [List.append_assoc] at hM ⊢; exact hM
  · simp only [List.append_assoc, zero_add] at h1 ⊢
    rw [show B + 127 * elemW + 4 = B + 1 + (128 - 1) * elemW + 3 from rfl, h1]
  · simp only [List.append_assoc, zero_add] at h2 ⊢
    rw [show B + 128 * elemW = B + 1 + 128 * elemW - 1 from rfl, h2]


end Run

theorem run_rsTail4 (impl : OpImpl) (κ : Kind) (inp : Input) (r : Array Val) (P : FinP) (kap t₀ t₁ t₂ t₃ : ℕ)
    (Lc : List Val) (T₀ T₁ T₂ T₃ kp : F) (hk : kap < r.size) (hkv : (rd r kap).toF = kp)
    (h₀ : t₀ < r.size + Lc.length) (h₁ : t₁ < r.size + Lc.length) (h₂ : t₂ < r.size + Lc.length)
    (h₃ : t₃ < r.size + Lc.length)
    (v₀ : (rd (r ++ Lc.toArray) t₀).toF = T₀) (v₁ : (rd (r ++ Lc.toArray) t₁).toF = T₁)
    (v₂ : (rd (r ++ Lc.toArray) t₂).toF = T₂) (v₃ : (rd (r ++ Lc.toArray) t₃).toF = T₃) :
    ∃ M, pureRun impl κ inp ((gRsTail P kap t₀ t₁ t₂ t₃ (r.size + Lc.length)).map (reloc P.S)) r Lc =
        some (Lc ++ M, P.kv.node κ || rsLeafZero4 P.S inp) ∧
      (rd (r ++ (Lc ++ M).toArray) (r.size + Lc.length + 8)).toF =
        T₀ + kp * (T₁ + kp * (T₂ + kp * (if P.kv.node κ then T₃ else 0))) := by
  have tf : ∀ x, (Val.f x).toF = x := fun _ => rfl
  have hkr : ∀ X : List Val, (rd (r ++ X.toArray) kap).toF = kp := fun X => by rw [rd_app_left r X hk, hkv]
  have rL : ∀ {t T} (X : List Val), t < r.size + Lc.length → (rd (r ++ Lc.toArray) t).toF = T →
      (rd (r ++ (Lc ++ X).toArray) t).toF = T := fun X h v => by rw [rdL r h, v]
  set y := (if P.kv.node κ then T₃ else 0)
  set v' : Val := if P.kv.node κ = true then Val.f (T₃ + 0) else Val.f 0
  have hv' : (if P.kv.node κ = true then Val.f (T₃ + 0) else Val.f 0).toF = y := by
    simp only [y]; split <;> simp [tf]
  set by₁ := inp.π.extract (fieldOffOf P.S fRS0 + rsOff 3 0) (fieldOffOf P.S fRS0 + rsOff 3 0 + 2048)
  have hRS : fRS0 < 19 := by decide
  refine ⟨[.f 0, .f (T₃ + 0), v', .f (kp * y), .f (T₂ + kp * y),
    .f (kp * (T₂ + kp * y)), .f (T₁ + kp * (T₂ + kp * y)), .f (kp * (T₁ + kp * (T₂ + kp * y))),
    .f (T₀ + kp * (T₁ + kp * (T₂ + kp * y))), .b by₁], ?_, ?_⟩
  · simp only [gRsTail, List.map_cons, List.map_nil, hRS, reloc, ite_true, absOff_zero, pureRun, evalOp, List.append_assoc, List.cons_append, List.nil_append,
      rdX, rdX0, List.getD_cons_succ, List.getD_cons_zero, hkr, tf,
      rL _ h₀ v₀, rL _ h₁ v₁, rL _ h₂ v₂, rL _ h₃ v₃, hv', Bool.not_not, Val.isZero,
      Option.map_some, Bool.true_and, Bool.and_true, rsLeafZero4]
    rfl
  · rw [rdX]; rfl

section RS
variable (impl : OpImpl) (κ : Kind) (inp : Input) (fi : FinIn) (r : Array Val) (P : FinP)

/-- **The inner weights** `c_{j,i}` of the four claims (`rs_column`): `eqZ λ ρ₁` for Z; `eq` at the
low 7 coordinates of Lc's (L2) and Sh's (S2's position part) points; the packing basis `bb i` for
E4's `f̂(r′)` (revision 3.13). -/
def rsW4 (j i : ℕ) : F :=
  match j with
  | 0 => (impl.eqZ (fv r ((outsOf fi "Z2").headD 0)) (pinnedRho 0)).getD i 0
  | 1 => (eqTab (ptF r ((chals fi "L2" 14).take 7))).getD i 0
  | 2 => (eqTab (ptF r (((chals fi "S2" P.S.s2).drop (P.kv.m κ - 14)).take 7))).getD i 0
  | _ => bb i

/-- **Claim `j`'s value** `α_j = Σ_i c_{j,i} s_{j,i}`. -/
def rsAlpha4 (j : ℕ) : F := ∑ k ∈ Finset.range 128, rsW4 impl κ fi r P j k * sv4 P.S inp j k

/-- **Claim `j`'s switched claim** `T_j = Σ_i bitBasis i · Φ_{r″}(s_{j,i})` (`rsT`). -/
def rsTv4 (j : ℕ) : F := ∑ k ∈ Finset.range 128, bb k * impl.phiRS (ptF r (rsFsRegs fi)) (sv4 P.S inp j k)

/-- **`v_RS = Σ_j κ^j T_j`** (Horner; a leaf's `T₃` is `0`). -/
def rsV4 : F :=
  let kp := fv r ((coordsR fi "RS1").getD 7 0)
  rsTv4 impl inp fi r P 0 + kp * (rsTv4 impl inp fi r P 1 + kp * (rsTv4 impl inp fi r P 2 +
    kp * (if P.kv.node κ then rsTv4 impl inp fi r P 3 else 0)))

/-- `finRS`'s flag: a leaf's fourth claim has zero slice values. -/
def relRS4 : Bool := P.kv.node κ || rsLeafZero4 P.S inp

/-- The registers `finRS` reads. -/
def rsRefs4 : List Reg :=
  (List.range 8).map (fun p => (coordsR fi "RS1").getD p 0) ++ [(outsOf fi "Z2").headD 0] ++
    (chals fi "L2" 14).take 7 ++ ((chals fi "S2" P.S.s2).drop (P.kv.m κ - 14)).take 7

/-- **`exec_finRS`** (A.9, RS): `finRS` asks nothing; its flag is `relRS` (a leaf's fourth claim is
zero), its exports are the claim values `α_Z, α_Lc, α_Sh, α_E` (`rsAlpha`) and `v_RS` (`rsV`). -/
theorem exec_gFinRS (hin : ∀ x ∈ rsRefs4 κ fi P, x < r.size) :
    ∃ L, pureRun impl κ inp ((gFinRS P fi r.size).1.map (reloc P.S)) r [] = some (L, relRS4 κ inp P) ∧
      (∀ j < 4, (rd (r ++ L.toArray) ((gFinRS P fi r.size).2.getD j 0)).toF = rsAlpha4 impl κ inp fi r P j) ∧
      (rd (r ++ L.toArray) ((gFinRS P fi r.size).2.getD nRS 0)).toF = rsV4 impl κ inp fi r P := by
  simp only [rsRefs4, List.mem_append, List.mem_map, List.mem_range, List.mem_cons,
    List.not_mem_nil, or_false] at hin
  have tf : ∀ x, (Val.f x).toF = x := fun _ => rfl
  have hW : elemW = 8 := rfl
  set kap := (coordsR fi "RS1").getD 7 0 with hkapd
  set lam := (outsOf fi "Z2").headD 0 with hlamd
  have hkap : kap < r.size := hin _ (.inl (.inl (.inl ⟨7, by omega, rfl⟩)))
  have hlam : lam < r.size := hin _ (.inl (.inl (.inr rfl)))
  set x1 := (chals fi "L2" 14).take 7
  set x2 := ((chals fi "S2" P.S.s2).drop (P.kv.m κ - 14)).take 7
  set x4 := rsFsRegs fi
  have hx1 : ∀ x ∈ x1, x < r.size := fun x h => hin x (.inl (.inr h))
  have hx2 : ∀ x ∈ x2, x < r.size := fun x h => hin x (.inr h)
  have hx4 : ∀ x ∈ x4, x < r.size := fun x h => by
    simp only [x4, rsFsRegs, List.mem_map, List.mem_range] at h
    obtain ⟨p, hp, rfl⟩ := h; exact hin _ (.inl (.inl (.inl ⟨p, by omega, rfl⟩)))
  set ρ := pinnedRho 0
  set p1 := ptF r x1; set p2 := ptF r x2; set p4 := ptF r x4
  set ez := impl.eqZ (fv r lam) ρ
  set L₀ : List Val := [.f ρ, .af ez, .af p1, .af (eqTab p1), .af p2, .af (eqTab p2),
    .af p4] with hL₀
  have hpk : ∀ (xs : List Reg), (∀ x ∈ xs, x < r.size) → ∀ X : List Val,
      (xs.map fun x => (rd (r ++ X.toArray) x).toF).toArray = ptF r xs := fun xs h X => by
    rw [ptF, map_rd_app r X xs h]
  have es : ∀ ops, pureRun impl κ inp ([.const (fun _ => .f ρ), .eqZ lam r.size,
      .packF x1, .eqTable (r.size + 2),
      .packFK (fun κ => ((chals fi "S2" P.S.s2).drop (P.kv.m κ - 14)).take 7), .eqTable (r.size + 4),
      .packF x4] ++ ops) r [] = pureRun impl κ inp ops r L₀ := by
    intro ops
    simp only [List.cons_append, List.nil_append]
    rw [pr_op impl κ inp r (v := .f ρ) rfl,
      pr_op impl κ inp r (v := .af ez) (by
        simp only [evalOp, rd_app0, rd_app_left r _ hlam, List.nil_append, List.getD_cons_zero]; rfl),
      pr_op impl κ inp r (v := .af p1) (by simp only [evalOp, hpk x1 hx1]; rfl),
      pr_op impl κ inp r (v := .af (eqTab p1)) (by
        simp only [evalOp, rd_app, List.nil_append, List.append_assoc, List.cons_append,
          List.getD_cons_succ, List.getD_cons_zero]; rfl),
      pr_op impl κ inp r (v := .af p2) (by
        simp only [evalOp]
        rw [show List.take 7 (List.drop (P.kv.m κ - 14) (chals fi "S2" P.S.s2)) = x2 from rfl, hpk x2 hx2]),
      pr_op impl κ inp r (v := .af (eqTab p2)) (by
        simp only [evalOp, rd_app, List.nil_append, List.append_assoc, List.cons_append,
          List.getD_cons_succ, List.getD_cons_zero]; rfl),
      pr_op impl κ inp r (v := .af p4) (by simp only [evalOp, hpk x4 hx4]; rfl)]
    simp [hL₀]
  have e7 : List.map (reloc P.S) ([.const (fun _ => .f ρ), .eqZ lam r.size,
      .packF x1, .eqTable (r.size + 2),
      .packFK (fun κ => ((chals fi "S2" P.S.s2).drop (P.kv.m κ - 14)).take 7), .eqTable (r.size + 4),
      .packF x4] : List Op) = [.const (fun _ => .f ρ), .eqZ lam r.size,
      .packF x1, .eqTable (r.size + 2),
      .packFK (fun κ => ((chals fi "S2" P.S.s2).drop (P.kv.m κ - 14)).take 7), .eqTable (r.size + 4),
      .packF x4] := rfl
  have hL0 : L₀.length = 7 := rfl
  have hrd : ∀ t < 7, ∀ X : List Val, rd (r ++ (L₀ ++ X).toArray) (r.size + t) = L₀.getD t default :=
    fun t ht X => by rw [rd_app, List.getD_append _ _ _ _ (by rw [hL0]; omega)]
  have hwE : ∀ t (ht : t < 7) (p : Array F), L₀.getD t default = .af p → ∀ i (X : List Val),
      evalOp impl κ inp (r ++ (L₀ ++ X).toArray) (.getF (r.size + t) i) =
        .vals [.f (p.getD i 0)] true := fun t ht p hp i X => by
    simp only [evalOp, hrd t ht X, hp]; rfl
  have hR : r.size + 6 < r.size + L₀.length := by rw [hL0]; omega
  have hRv : (rd (r ++ L₀.toArray) (r.size + 6)).toAF = p4 := by
    have h6 := hrd 6 (by decide) []; rw [List.append_nil] at h6; rw [h6]; rfl
  obtain ⟨N₀, c0h, c0l, c0a, c0t⟩ := run_claimOps4 impl κ inp r P.S 0 _ (r.size + 6) p4 (rsW4 impl κ fi r P 0)
    L₀ [] hR hRv (hwE 1 (by decide) ez rfl) (fun _ => rfl)
  obtain ⟨N₁, c1h, c1l, c1a, c1t⟩ := run_claimOps4 impl κ inp r P.S 1 _ (r.size + 6) p4 (rsW4 impl κ fi r P 1)
    L₀ N₀ hR hRv (hwE 3 (by decide) (eqTab p1) rfl) (fun _ => rfl)
  obtain ⟨N₂, c2h, c2l, c2a, c2t⟩ := run_claimOps4 impl κ inp r P.S 2 _ (r.size + 6) p4 (rsW4 impl κ fi r P 2)
    L₀ (N₀ ++ N₁) hR hRv (hwE 5 (by decide) (eqTab p2) rfl) (fun _ => rfl)
  obtain ⟨N₃, c3h, c3l, c3a, c3t⟩ := run_claimOps4 impl κ inp r P.S 3 (fun i => .const (fun _ => .f (bb i)))
    (r.size + 6) p4 (rsW4 impl κ fi r P 3) L₀ (N₀ ++ N₁ ++ N₂) hR hRv (fun _ _ => rfl) (fun _ => rfl)
  simp only [List.length_append, List.length_nil, hL0, c0l, c1l, c2l, Nat.add_zero] at c0h c1h c2h c3h c0a c1a c2a c3a c0t c1t c2t c3t
  simp only [List.append_nil, List.append_assoc] at c0h c1h c2h c3h c0a c1a c2a c3a c0t c1t c2t c3t
  rw [show 1 + 128 * elemW + (1 + 128 * elemW) = 2 * (1 + 128 * elemW) by ring] at c2h
  rw [show 1 + 128 * elemW + (1 + 128 * elemW) + (1 + 128 * elemW) = 3 * (1 + 128 * elemW) by ring] at c3h
  simp only [gFinRS, List.map_append, List.append_assoc]
  rw [e7]
  rw [es, pr_app' impl κ inp r c0h, pr_app' impl κ inp r c1h, pr_app' impl κ inp r c2h,
    pr_app' impl κ inp r c3h]
  set A := 1 + 128 * elemW with hAd
  set Lc := L₀ ++ (N₀ ++ (N₁ ++ (N₂ ++ N₃)))
  have hLc : Lc.length = 7 + 4 * A := by
    simp only [Lc, List.length_append, hL0, c0l, c1l, c2l, c3l]; ring
  have pre : ∀ (P Q : List Val) (t : ℕ), t < r.size + P.length →
      rd (r ++ (P ++ Q).toArray) t = rd (r ++ P.toArray) t := fun P Q t h => rdL r h
  have rT : ∀ (P Q : List Val) (t t' : ℕ) (v : F), Lc = P ++ Q → t' < r.size + P.length → t = t' →
      (rd (r ++ P.toArray) t').toF = v → (rd (r ++ Lc.toArray) t).toF = v := by
    intro P Q t t' v hPQ ht he hv; rw [hPQ, he, pre P Q t' ht, hv]
  obtain ⟨Mt, ht, hvt⟩ := run_rsTail4 impl κ inp r P kap (r.size + 7 + A - 1)
    (r.size + 7 + 2 * A - 1) (r.size + 7 + 3 * A - 1)
    (r.size + Lc.length - 1) Lc (rsTv4 impl inp fi r P 0) (rsTv4 impl inp fi r P 1) (rsTv4 impl inp fi r P 2)
    (rsTv4 impl inp fi r P 3) (fv r kap) hkap rfl
    (by rw [hLc]; omega) (by rw [hLc]; omega) (by rw [hLc]; omega) (by rw [hLc]; omega)
    (rT (L₀ ++ N₀) (N₁ ++ (N₂ ++ N₃)) _ _ _ (by simp [Lc]) (by simp [hL0, c0l]; omega)
      (by omega) c0t)
    (rT (L₀ ++ (N₀ ++ N₁)) (N₂ ++ N₃) _ _ _ (by simp [Lc]) (by simp [hL0, c0l, c1l]; omega)
      (by omega) c1t)
    (rT (L₀ ++ (N₀ ++ (N₁ ++ N₂))) N₃ _ _ _ (by simp [Lc])
      (by simp [hL0, c0l, c1l, c2l]; omega) (by omega) c2t)
    (rT Lc [] _ _ _ (by simp) (by simp [Lc, hL0, c0l, c1l, c2l, c3l]; omega) (by omega) c3t)
  rw [← hkapd, show r.size + 7 + 4 * A = r.size + Lc.length by rw [hLc]; omega, ht]
  refine ⟨Lc ++ Mt, rfl, fun j hj => ?_, ?_⟩
  · have rA : ∀ (P Q : List Val) (t t' : ℕ) (v : F), Lc = P ++ Q → t' < r.size + P.length → t = t' →
        (rd (r ++ P.toArray) t').toF = v → (rd (r ++ (Lc ++ Mt).toArray) t).toF = v := by
      intro P Q t t' v hPQ ht' he hv
      have hlt : t < r.size + Lc.length := by rw [he, hPQ, List.length_append]; omega
      rw [pre Lc Mt t hlt]; exact rT P Q t t' v hPQ ht' he hv
    interval_cases j <;> simp only [List.range_succ, List.range_zero, List.map_append, List.map_cons,
      List.map_nil, List.nil_append, List.cons_append, List.getD_cons_zero, List.getD_cons_succ]
    · exact rA (L₀ ++ N₀) (N₁ ++ (N₂ ++ N₃)) _ _ _ (by simp [Lc]) (by simp [hL0, c0l]; omega)
        (by omega) c0a
    · exact rA (L₀ ++ (N₀ ++ N₁)) (N₂ ++ N₃) _ _ _ (by simp [Lc])
        (by simp [hL0, c0l, c1l]; omega) (by omega) c1a
    · exact rA (L₀ ++ (N₀ ++ (N₁ ++ N₂))) N₃ _ _ _ (by simp [Lc])
        (by simp [hL0, c0l, c1l, c2l]; omega) (by omega) c2a
    · exact rA Lc [] _ _ _ (by simp) (by simp [Lc, hL0, c0l, c1l, c2l, c3l]; omega) (by omega) c3a
  · simp only [nRS, List.range_succ, List.range_zero, List.map_append, List.map_cons, List.map_nil,
      List.nil_append, List.cons_append, List.getD_cons_zero, List.getD_cons_succ]
    rw [hvt]; rfl


end RS

end FR.Snd.R4

end G6_FRSoundness4R4FinRS

section G6_FRSoundness4R4FinSh

-- New for `flock-recursive` (BLUEPRINT revision 4.1, A.9 `finSh`, B-12; stage R4c).

/-!
# `finSh`'s flag at `FinP` on the relocated ops

3.x's `flag_finSh` (`FRVIRFinals`) for `gFinSh P`: the sizes (`P.S.s2`, `nb = P.S.mStar − 14`), the
kind tables and the boundary reads (`pe4 P.S`) are `P`'s; with `P.vn` (a segment, B-12) the masked
shift's operand is `τ ‖ L` (`τ` zero-padded by the statement's zero register, then `L`'s bits) and
the boundary's last block is `L` (`lastRegs`), and `E`, `Sh`, `E₀` are `shiftMask`'s.
-/

namespace FR.Snd.R4
open RecursionFast Rev4

section Flags
variable (impl : OpImpl) (κ : Kind) (inp : Input) (fi : FinIn) (r : Array Val) (P : FinP)

/-- **`relSh` at `P`**: (i) `shiftTarget(κ_s, τ, θ, bnd) = c₀^{S2}`; (ii) `(w_out + w_in)·α_Sh =
c_N^{S2}`, the weights' `E`, `Sh`, `E₀` from `shiftMask` on the masked operand when `P.vn` or a node,
else 3.x's leaf `eq`/`shiftEq`. -/
def relSh4 : Bool :=
  let co := coordsR fi "S1"; let rs := chals fi "S2" P.S.s2
  let m := P.kv.m κ; let nb := P.S.mStar - 14
  let ks := fv r (co.getD (nb + 10) 0)
  let τ := ((co.take (m - 14)).map (fv r) ++ List.replicate (P.S.mStar - m) 0).toArray
  let θ := (((co.drop nb).take 10).map (fv r)).toArray
  let rb := ((rs.take (m - 14)).map (fv r) ++ List.replicate (P.S.mStar - m) 0).toArray
  let rp := (((rs.drop (m - 14)).take 10).map (fv r)).toArray
  let tt := ((co.take (m - 14) ++ (co.drop nb).take 10).map (fv r)).toArray
  let rr := ((rs.take (m - 14) ++ (rs.drop (m - 14)).take 10).map (fv r)).toArray
  let tm : Array F := if P.vn then
      ((co.take (m - 14)).map (fv r) ++ List.replicate (P.S.mStar - m) (fv r (zeroReg fi)) ++
        (lastRegs fi).map (fv r)).toArray
    else τ
  let mk := P.vn || P.kv.node κ
  let sm := impl.shiftMask tm rb
  let e := if mk then sm.1 else eqPoint τ rb
  let sh := if mk then sm.2.1 else impl.shiftEq τ rb
  let e0 := if mk then sm.2.2 else eqPoint (Array.replicate nb 0) rb
  let sIn := if P.kv.node κ then impl.slotW κ 2 θ rp else impl.slotW κ 1 θ rp
  let wout := e * impl.slotW κ 0 θ rp
  let win := linkSum (impl.linkWAll κ tt rr) ks nLinkFam ((sh + ks * e0) * sIn) (ks * ks)
  let bnd : Array F := ((if P.kv.node κ then [0, 0, 0, 0]
    else [pe4 P.S inp fHdr 16, pe4 P.S inp fHdr 32, pe4 P.S inp fStmt 1, pe4 P.S inp fStmt 17]) ++
    (if P.vn then (lastRegs fi).map (fv r)
     else List.replicate (m - 14) 1 ++ List.replicate (P.S.mStar - m) 0)).toArray
  (Val.f (impl.shiftTarget ks τ θ bnd)).eqv (rd r (claim0 fi "S2")) &&
  (Val.f ((wout + win) * fv r (fi.zhat.getD 2 0))).eqv (rd r (claimN fi "S2"))

set_option maxRecDepth 8192 in
theorem flag_gFinSh (hin : ∀ x ∈ coordsR fi "S1" ++ chals fi "S2" P.S.s2 ++ lastRegs fi ++
      [claim0 fi "S2", claimN fi "S2", fi.zhat.getD 2 0, zeroReg fi,
       (coordsR fi "S1").getD (P.S.mStar - 14 + 10) 0], x < r.size) :
    ∃ L, pureRun impl κ inp ((gFinSh P fi r.size).1.map (reloc P.S)) r [] =
      some (L, relSh4 impl κ inp fi r P) := by
  simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hin
  have hco : ∀ x ∈ coordsR fi "S1", x < r.size := fun x hx => hin x (.inl (.inl (.inl hx)))
  have hrs : ∀ x ∈ chals fi "S2" P.S.s2, x < r.size := fun x hx => hin x (.inl (.inl (.inr hx)))
  have hlr : ∀ x ∈ lastRegs fi, x < r.size := fun x hx => hin x (.inl (.inr hx))
  have h1 := fun L => map_rd_app r L ((coordsR fi "S1").take (P.kv.m κ - 14))
    fun x hx => hco x (List.mem_of_mem_take hx)
  have h2 := fun L => map_rd_app r L (((coordsR fi "S1").drop (P.S.mStar - 14)).take 10)
    fun x hx => hco x (List.mem_of_mem_drop (List.mem_of_mem_take hx))
  have h3 := fun L => map_rd_app r L ((chals fi "S2" P.S.s2).take (P.kv.m κ - 14))
    fun x hx => hrs x (List.mem_of_mem_take hx)
  have h4 := fun L => map_rd_app r L (((chals fi "S2" P.S.s2).drop (P.kv.m κ - 14)).take 10)
    fun x hx => hrs x (List.mem_of_mem_drop (List.mem_of_mem_take hx))
  have h5 := fun L => map_rd_app r L ((coordsR fi "S1").take (P.kv.m κ - 14) ++
    ((coordsR fi "S1").drop (P.S.mStar - 14)).take 10) fun x hx => by
      rcases List.mem_append.1 hx with hx | hx
      · exact hco x (List.mem_of_mem_take hx)
      · exact hco x (List.mem_of_mem_drop (List.mem_of_mem_take hx))
  have h6 := fun L => map_rd_app r L ((chals fi "S2" P.S.s2).take (P.kv.m κ - 14) ++
    ((chals fi "S2" P.S.s2).drop (P.kv.m κ - 14)).take 10) fun x hx => by
      rcases List.mem_append.1 hx with hx | hx
      · exact hrs x (List.mem_of_mem_take hx)
      · exact hrs x (List.mem_of_mem_drop (List.mem_of_mem_take hx))
  have h7 := fun L => map_rd_app r L (lastRegs fi) hlr
  have tf : ∀ x, (Val.f x).toF = x := fun _ => rfl
  have taf : ∀ x, (Val.af x).toAF = x := fun _ => rfl
  have hH : fHdr < 19 := by decide
  have hS : fStmt < 19 := by decide
  simp only [gFinSh, gShCore, relSh4, gBndOps, gPadB]
  generalize claim0 fi "S2" = c0 at *
  generalize claimN fi "S2" = cN at *
  generalize fi.zhat.getD 2 0 = zo at *
  generalize zeroReg fi = zr at *
  generalize (coordsR fi "S1").getD (P.S.mStar - 14 + 10) 0 = ks at *
  have hc0 := hin c0 (.inr (.inl rfl)); have hcN := hin cN (.inr (.inr (.inl rfl)))
  have hzo := hin zo (.inr (.inr (.inr (.inl rfl))))
  have hzr := hin zr (.inr (.inr (.inr (.inr (.inl rfl)))))
  have hk := hin ks (.inr (.inr (.inr (.inr (.inr rfl)))))
  rw [pureRun_nil_rev]
  cases hv : P.vn <;> cases hκ : P.kv.node κ <;>
  simp only [hκ, Bool.cond_true, Bool.cond_false, Bool.true_or, Bool.false_or,
    Bool.false_eq_true, Nat.add_assoc, List.map_cons, List.map_nil, List.cons_append,
    List.nil_append, hH, hS, reloc, absOff_zero,
    pureRun, evalOp, tf, taf, h1, h2, h3, h4, h5, h6, h7, linkOps,
    List.map_append, List.map_replicate,
    nLinkFam, linkSum, List.range_succ, List.range_zero, List.flatMap_append, List.flatMap_cons,
    List.flatMap_nil, ↓reduceIte, Nat.reduceEqDiff, Nat.reduceAdd, Nat.reduceMul, Nat.reduceSub,
    rd_revAcc, rd_revAcc0, revAcc_app_cons, List.append_nil, List.length_cons, List.length_nil,
    Array.reduceGetElem?, Option.getD_some, rd_app_left _ _ hc0, rd_app_left _ _ hcN,
    rd_app_left _ _ hzo, rd_app_left _ _ hk, rd_app_left _ _ hzr,
    Option.map_some, allK, Bool.not_true, Bool.false_or, Bool.true_and, Bool.and_true] <;>
  exact ⟨_, rfl⟩

end Flags

end FR.Snd.R4

end G6_FRSoundness4R4FinSh
