-- lvm6 EXF phase 2 (F-EXG-2): the front's cells on the history. The values `fillIR18` copies are the opening's: each
-- request's event is its source (`srcs18`), and W1's runs put the rounds' `(α, β)`, the tails' high parts and the final
-- scalars at those events. `fill_front`, `frontIn18`. New.
import Lvm6XFill18

/-!
# The front, filled, on the history

* `ev_at`, `n0_eq` (the opening starts at `N18`), `req_smp`/`req_rd` (a request's cell holds its event's `E2` lanes).
* `RunMidE`/`RunFinE` (EXI's `RunMid`/`RunFin`, same bodies), `mid_seg`/`fin_seg` (a level's values are events of `h`).
* **`Rows18`**, **`FrontSeg18`**, **`fill_front`**, **`frontIn18`** (see `Lvm6XFill18`'s docstring).
-/

set_option autoImplicit false

namespace Lvm6.X

open RecursionFast Lvm Lvm.X Lvm.FS Lvm6.Whir
open LeanVM.Protocol.Compile (Ev VerifierProgram commits)
open LeanVM.Parameters (E E2 e2OfE)

/-! ## Events and their sources -/

theorem forall₂_getElem? {α β : Type} {R : α → β → Prop} :
    ∀ {l₁ : List α} {l₂ : List β}, List.Forall₂ R l₁ l₂ → ∀ (n : ℕ) (b : β), l₂[n]? = some b →
      ∃ a, l₁[n]? = some a ∧ R a b
  | _, _, .nil, n, b, h => by simp at h
  | _, _, .cons hab hr, 0, b, h => by simp only [List.getElem?_cons_zero, Option.some.injEq] at h; subst h; exact ⟨_, rfl, hab⟩
  | _, _, .cons _ hr, n + 1, b, h => by simpa using forall₂_getElem? hr n b (by simpa using h)

/-- An event of the `P18` replay satisfies its source. -/
theorem ev_at {S : Scheme} {π : Proof} {L : Log} {h : List Ev} (hf : List.Forall₂ (EvSrc S P18 π L) srcs18 h)
    {n : ℕ} {e : Ev} (he : h[n]? = some e) : EvSrc S P18 π L (srcs18.getD n default) e := by
  obtain ⟨a, ha, hR⟩ := forall₂_getElem? hf n e he
  rw [List.getD_eq_getElem?_getD, ha, Option.getD_some]
  exact hR

/-- **The opening starts at `N18`.** -/
theorem n0_eq {S : Scheme} {π : Proof} {L : Log} {h : List Ev} (hf : List.Forall₂ (EvSrc S P18 π L) srcs18 h)
    {cl : StackClaim6} {N₀ : ℕ} {b : Bool} (hN : (whirP18 cl).after (h.drop N₀) = some (.ret b)) : N₀ = N18 := by
  have h1 := after_length _ (whirP18_follows_ops18 cl) hN
  have h2 := hf.length_eq
  obtain ⟨-, -, -, h3, h4, h5, -⟩ := fill18_ok
  rw [List.length_drop] at h1
  unfold N18
  omega

/-! ## The values the cells receive -/

section Values

variable {I : Array Word} {Mf M : Mem} {S : Scheme} {c : Digest} {π : Proof} {L : Log} {h : List Ev}

/-- A request's cell after the fill, from a draw: the challenge's `E2` lanes. -/
theorem req_smp (hI : I = (extractorInput c π L).toArray) (hf : List.Forall₂ (EvSrc S P18 π L) srcs18 h)
    (hfill : ∀ e ∈ fillTab18, rd M e.2.2 = cpV I Mf e)
    (hch : ∀ p < nCh6 P18, ∀ a, fmAns (fsQ6 P18 π) zeroDL L p = some a → ∀ m < 4,
      rd Mf (ansB + 4 * p + m) = (packBytes a.toList).getD m 0)
    {n dst : ℕ} (hr : (n, dst) ∈ reqs18) {cc : E} (he : h[n]? = some (Ev.sample cc)) :
    rdE2 M dst = e2OfE cc := by
  have hev := ev_at hf he
  have hok := List.all_eq_true.1 fill18_ok.2.2.1 _ hr
  unfold reqOK at hok
  simp only at hok
  have hmem : ∀ e ∈ cpOf (srcs18.getD n default) dst, e ∈ fillTab18 := fun e he' =>
    List.mem_flatMap.2 ⟨(n, dst), hr, he'⟩
  revert hev hok hmem
  cases srcs18.getD n default with
  | smp p =>
    intro hev hok hmem
    obtain ⟨a, ha, rfl⟩ := hev
    simp only [decide_eq_true_eq] at hok
    have w0 := hfill _ (hmem (true, ansB + 4 * p, dst) (by simp [cpOf]))
    have w1 := hfill _ (hmem (true, ansB + 4 * p + 1, dst + 1) (by simp [cpOf]))
    simp only [cpV, if_true] at w0 w1
    have hl : (packBytes a.toList).length = 4 := by rw [packBytes_length, Vector.length_toList]
    rw [e2OfE_chalOf]
    unfold rdE2 rdK
    rw [w0, w1]
    have c0 := hch p hok a ha 0 (by norm_num)
    have c1 := hch p hok a ha 1 (by norm_num)
    rw [Nat.add_zero] at c0
    rw [c0, c1, wK_packBytes6 _ (by omega), wK_packBytes6 _ (by omega)]
    rfl
  | rd off w => intro hev; exact hev.elim
  | cap => intro hev; exact hev.elim
  | opn => intro hev; exact hev.elim

theorem eOfBytes_limb (b : List UInt8) (j : Fin 3) :
    (Lvm.FS.eOfBytes b).limb j = Lvm.FS.kOfBytes (b.drop (8 * j)) := by
  simp only [Lvm.FS.eOfBytes, LeanVM.Parameters.E.limb]
  exact congrFun ((CompPoly.Extension.Ext.equivFn BF64.ext3Params).apply_symm_apply _) j

theorem eOfBytes_limb0 (b : List UInt8) : (Lvm.FS.eOfBytes b).limb 0 = Lvm.FS.kOfBytes b := by
  simpa using eOfBytes_limb b 0

theorem eOfBytes_limb1 (b : List UInt8) : (Lvm.FS.eOfBytes b).limb 1 = Lvm.FS.kOfBytes (b.drop 8) := by
  simpa using eOfBytes_limb b 1

/-- A request's cell after the fill, from a read: the scalar's `E2` lanes. -/
theorem req_rd (hI : I = (extractorInput c π L).toArray) (hS : S.decE = Lvm.FS.eOfBytes) (hs : π.size = pz6)
    (hf : List.Forall₂ (EvSrc S P18 π L) srcs18 h) (hfill : ∀ e ∈ fillTab18, rd M e.2.2 = cpV I Mf e)
    {n dst : ℕ} (hr : (n, dst) ∈ reqs18) {x : E} (he : h[n]? = some (Ev.read x)) :
    rdE2 M dst = e2OfE x := by
  have hev := ev_at hf he
  have hok := List.all_eq_true.1 fill18_ok.2.2.1 _ hr
  unfold reqOK at hok
  simp only at hok
  have hmem : ∀ e ∈ cpOf (srcs18.getD n default) dst, e ∈ fillTab18 := fun e he' =>
    List.mem_flatMap.2 ⟨(n, dst), hr, he'⟩
  revert hev hok hmem
  cases srcs18.getD n default with
  | rd off w =>
    intro hev hok hmem
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hok
    obtain ⟨⟨rfl, ho8⟩, hoz⟩ := hok
    have hx : x = Lvm.FS.eOfBytes ((π.data.toList.drop off).take 16) := by rw [← hS]; exact hev
    subst hx
    have w0 := hfill _ (hmem (false, 5 + off / 8, dst) (by simp [cpOf]))
    have w1 := hfill _ (hmem (false, 5 + off / 8 + 1, dst + 1) (by simp [cpOf]))
    simp only [cpV, Bool.false_eq_true, if_false] at w0 w1
    have hpl : (packBytes π.data.toList).length = (π.size + 7) / 8 := by
      rw [packBytes_length, ← WitnessSending.size_eq_length]
    have t0 : I.getD (5 + off / 8) 0 = (packBytes π.data.toList).getD (off / 8) 0 := by
      rw [hI, getD_toArray, tape_getD_proof c π L (by rw [hs]; omega), ← List.getD_eq_getElem _ 0]
    have t1 : I.getD (5 + off / 8 + 1) 0 = (packBytes π.data.toList).getD (off / 8 + 1) 0 := by
      rw [hI, getD_toArray, show 5 + off / 8 + 1 = 5 + (off / 8 + 1) by omega,
        tape_getD_proof c π L (by rw [hs]; omega), ← List.getD_eq_getElem _ 0]
    have k0 : Lvm.FS.kOfBytes ((π.data.toList.drop off).take 16) = Lvm.FS.kOfBytes (π.data.toList.drop off) := by
      rw [kOfBytes_decLE, kOfBytes_decLE, List.take_take]; rfl
    have k1 : Lvm.FS.kOfBytes (((π.data.toList.drop off).take 16).drop 8) =
        Lvm.FS.kOfBytes (π.data.toList.drop (off + 8)) := by
      rw [kOfBytes_decLE, kOfBytes_decLE]
      congr 1
      simp [List.drop_take, List.take_take, List.drop_drop]
    unfold rdE2 rdK e2OfE
    rw [w0, w1, t0, t1, wK_packBytes6 _ (by omega), wK_packBytes6 _ (by omega), eOfBytes_limb0, eOfBytes_limb1,
      k0, k1, show 8 * (off / 8) = off by omega, show 8 * (off / 8 + 1) = off + 8 by omega]
  | smp p => intro hev; exact hev.elim
  | cap => intro hev; exact hev.elim
  | opn => intro hev; exact hev.elim

end Values

/-! ## The opening's runs -/

/-- **A mid level's runs** (EXI's `RunMid`). -/
def RunMidE {n ℓ n' ℓ' : ℕ} (M : MidLv E2 WtE n ℓ n' ℓ') (l : List Ev) (rs : List (Rnd E2))
    (o : TailOut E2 M.L.ko M.L.t n) (l' : List Ev) : Prop :=
  ∃ l₁ l₃, l = l₁ ++ (l₃ ++ l') ∧ (roundsP chalE2 M.g ℓ).after l₁ = some (.ret rs) ∧
    (tailP M.L chalE2 M.ht M.wd M.i M.gO M.gQ (M.vals rs)).after l₃ = some (.ret o)

/-- **The final level's runs** (EXI's `RunFin`). -/
def RunFinE {n ℓ : ℕ} (V : FinLv E2 WtE n ℓ) (l : List Ev) (rs : List (Rnd E2)) (sc : List E2) : Prop :=
  ∃ l₁ l₃ l₄, l = l₁ ++ (l₃ ++ l₄) ∧ (roundsP chalE2 V.g ℓ).after l₁ = some (.ret rs) ∧
    (readFs chalE2 V.Fv.nf).after l₃ = some (.ret sc)

theorem length_rounds (ℓ : ℕ) : ((List.replicate ℓ roundOps).flatten).length = 7 * ℓ := by
  simp [roundOps, List.length_flatten]; ring

/-- **A mid level at offset `N`**: the rest is `h.drop (N + 7ℓ + |tail|)`, the rounds' challenges and the tail's
high parts are events of `h`. -/
theorem mid_seg {n ℓ n' ℓ' : ℕ} (M : MidLv E2 WtE n ℓ n' ℓ') {h : List Ev} {N : ℕ} {rs : List (Rnd E2)}
    {o : TailOut E2 M.L.ko M.L.t n} {l' : List Ev} (hR : RunMidE M (h.drop N) rs o l') :
    l' = h.drop (N + 7 * ℓ + (tailOps M.L.nh M.ht M.wd M.L.ko M.L.kq M.i).length) ∧ rs.length = ℓ ∧
    (∀ k < ℓ, ∃ c c' : E, h[N + 7 * k + 5]? = some (Ev.sample c) ∧ h[N + 7 * k + 6]? = some (Ev.sample c') ∧
      (rs.getD k default).α = e2OfE c ∧ (rs.getD k default).β = e2OfE c') ∧
    (∀ k < M.L.nh, ∃ x, h[N + 7 * ℓ + k]? = some (Ev.read x) ∧ o.hi.getD k 0 = e2OfE x) := by
  obtain ⟨l₁, l₃, hl, h1, h3⟩ := hR
  have a1 : l₁.length = 7 * ℓ := (after_length _ (follows_roundsP M.g ℓ) h1).trans (length_rounds ℓ)
  have a3 := after_length _ (follows_tailP M.L M.ht M.wd M.i M.gO M.gQ (M.vals rs)) h3
  obtain ⟨hlen, hr⟩ := roundsP_run ℓ h1
  have hT := tailP_hi M.L M.ht M.wd M.i M.gO M.gQ (M.vals rs) h3
  have hg : ∀ j, h[N + j]? = (l₁ ++ (l₃ ++ l'))[j]? := fun j => by rw [← hl, List.getElem?_drop]
  refine ⟨?_, hlen, fun k hk => ?_, fun k hk => ?_⟩
  · have e : l' = (h.drop N).drop (l₁.length + l₃.length) := by
      rw [hl, ← List.append_assoc, List.drop_left' (by simp)]
    rw [e, List.drop_drop]
    congr 1
    rw [a1, a3]
    omega
  · obtain ⟨c, c', b1, b2, b3, b4⟩ := hr k hk
    refine ⟨c, c', ?_, ?_, b3, b4⟩
    · rw [show N + 7 * k + 5 = N + (7 * k + 5) by ring, hg, List.getElem?_append_left (by omega)]; exact b1
    · rw [show N + 7 * k + 6 = N + (7 * k + 6) by ring, hg, List.getElem?_append_left (by omega)]; exact b2
  · obtain ⟨x, b1, b2⟩ := hT k hk
    refine ⟨x, ?_, b2⟩
    have hnh : M.L.nh ≤ (tailOps M.L.nh M.ht M.wd M.L.ko M.L.kq M.i).length := by simp [tailOps]
    rw [show N + 7 * ℓ + k = N + (7 * ℓ + k) by ring, hg, List.getElem?_append_right (by omega), a1,
      Nat.add_sub_cancel_left,
      List.getElem?_append_left (by omega)]
    exact b1

theorem length_rounds4 : ((List.replicate 4 roundOps).flatten).length = 28 := by
  rw [length_rounds]

/-- **The final level at offset `N`**: the rounds' challenges and the final scalars are events of `h`. -/
theorem fin_seg {h : List Ev} {N : ℕ} {rs : List (Rnd E2)} {sc : List E2} (hR : RunFinE fin18 (h.drop N) rs sc) :
    rs.length = 4 ∧
    (∀ k < 4, ∃ c c' : E, h[N + 7 * k + 5]? = some (Ev.sample c) ∧ h[N + 7 * k + 6]? = some (Ev.sample c') ∧
      (rs.getD k default).α = e2OfE c ∧ (rs.getD k default).β = e2OfE c') ∧
    (∀ k < 12, ∃ x, h[N + 7 * 4 + k]? = some (Ev.read x) ∧ sc.getD k 0 = e2OfE x) := by
  obtain ⟨l₁, l₃, l₄, hl, h1, h3⟩ := hR
  have a1 : l₁.length = 28 := (after_length _ (follows_roundsP fin18.g 4) h1).trans length_rounds4
  obtain ⟨hlen, hr⟩ := roundsP_run 4 h1
  have hnf : fin18.Fv.nf = 12 := rfl
  rw [hnf] at h3
  obtain ⟨a3, hv⟩ := readFs_run 12 h3
  have hg : ∀ j, h[N + j]? = (l₁ ++ (l₃ ++ l₄))[j]? := fun j => by rw [← hl, List.getElem?_drop]
  refine ⟨hlen, fun k hk => ?_, fun k hk => ?_⟩
  · obtain ⟨c, c', b1, b2, b3, b4⟩ := hr k hk
    refine ⟨c, c', ?_, ?_, b3, b4⟩
    · rw [show N + 7 * k + 5 = N + (7 * k + 5) by ring, hg, List.getElem?_append_left (by omega)]; exact b1
    · rw [show N + 7 * k + 6 = N + (7 * k + 6) by ring, hg, List.getElem?_append_left (by omega)]; exact b2
  · obtain ⟨x, b1, b2⟩ := hv k hk
    refine ⟨x, ?_, b2⟩
    rw [show N + 7 * 4 + k = N + (28 + k) by ring, hg, List.getElem?_append_right (by omega), a1,
      Nat.add_sub_cancel_left, List.getElem?_append_left (by omega)]
    exact b1

/-! ## The cells, as EXG's levels read them -/

/-- Level `i`'s challenge pairs (`trIR_sem`'s `hch`). -/
def ChF (M : Mem) (i : ℕ) (rs : List (Rnd E2)) : Prop :=
  ∀ k < rnd18 i, rdE2 M (F18.ch i k) = ((rs.map fun r ↦ (r.α, r.β)).getD k (0, 0)).1 ∧
    rdE2 M (F18.ch i k + 2) = ((rs.map fun r ↦ (r.α, r.β)).getD k (0, 0)).2

/-- Level `i`'s high parts (`glueIR_cols`' `hhi`). -/
def HiF (M : Mem) (i : ℕ) (hi : List E2) : Prop := ∀ k < rnd18 i, rdE2 M (F18.hi i + 2 * k) = hi.getD k 0

/-- The final scalars (`startIR_cols`' `hs`, `2^3 + 4 = 12`). -/
def SF (M : Mem) (sc : List E2) : Prop := ∀ k < 12, rdE2 M (F18.s + 2 * k) = sc.getD k 0

/-- **The front's cells on every decomposition of the opening's log** `h.drop N18` into the levels' runs. -/
def FrontSeg18 (M : Mem) (h : List Ev) : Prop :=
  ∀ rs0 o0 l1 rs1 o1 l2 rs2 o2 l3 rs3 o3 l4 rs4 sc,
    RunMidE mid0 (h.drop N18) rs0 o0 l1 → RunMidE mid1 l1 rs1 o1 l2 → RunMidE mid2 l2 rs2 o2 l3 →
    RunMidE mid3 l3 rs3 o3 l4 → RunFinE fin18 l4 rs4 sc →
    ChF M 0 rs0 ∧ ChF M 1 rs1 ∧ ChF M 2 rs2 ∧ ChF M 3 rs3 ∧ ChF M 4 rs4 ∧
      HiF M 0 o0.hi ∧ HiF M 1 o1.hi ∧ HiF M 2 o2.hi ∧ HiF M 3 o3.hi ∧ SF M sc

/-- **The committed rows** at `wB6 i` (`front6_heap`'s). -/
def Rows18 (M : Mem) (h : List Ev) : Prop :=
  (commits h).length = 5 ∧
    ∀ i < 5, ((commits h).getD i default).1 = ht6 i ∧ ((commits h).getD i default).2.1 = zp6 i + occ6 i ∧
      (∀ p, ∀ t < zp6 i, (((commits h).getD i default).2.2 p).getD t 0 = 0) ∧
      ∀ p < 2 ^ ht6 i, ∀ t < occ6 i, rdK M (wB6 i + occ6 i * p + t) =
        (((commits h).getD i default).2.2 p).getD (zp6 i + t) 0

theorem mem_ch {i k : ℕ} (hi : i < 5) (hk : k < rnd18 i) :
    (N18 + base18 i + 7 * k + 5, F18.ch i k) ∈ reqs18 ∧ (N18 + base18 i + 7 * k + 6, F18.ch i k + 2) ∈ reqs18 := by
  unfold reqs18
  constructor <;>
  exact List.mem_append.2 (Or.inl (List.mem_append.2 (Or.inl (List.mem_flatMap.2 ⟨i, List.mem_range.2 hi,
    List.mem_flatMap.2 ⟨k, List.mem_range.2 hk, by simp⟩⟩))))

theorem mem_hi {i k : ℕ} (hi : i < 4) (hk : k < rnd18 i) :
    (N18 + base18 i + 7 * rnd18 i + k, F18.hi i + 2 * k) ∈ reqs18 := by
  unfold reqs18
  exact List.mem_append.2 (Or.inl (List.mem_append.2 (Or.inr (List.mem_flatMap.2 ⟨i, List.mem_range.2 hi,
    List.mem_map.2 ⟨k, List.mem_range.2 hk, rfl⟩⟩))))

theorem mem_s {k : ℕ} (hk : k < 12) : (N18 + base18 4 + 7 * 4 + k, F18.s + 2 * k) ∈ reqs18 := by
  unfold reqs18
  exact List.mem_append.2 (Or.inr (List.mem_map.2 ⟨k, List.mem_range.2 hk, rfl⟩))

section Levels

variable {M : Mem} {h : List Ev}
  (hS : ∀ n dst, (n, dst) ∈ reqs18 → ∀ cc, h[n]? = some (Ev.sample cc) → rdE2 M dst = e2OfE cc)
  (hR : ∀ n dst, (n, dst) ∈ reqs18 → ∀ x, h[n]? = some (Ev.read x) → rdE2 M dst = e2OfE x)
include hS

theorem chF_of {i : ℕ} (hi : i < 5) {rs : List (Rnd E2)} (hl : rs.length = rnd18 i)
    (hr : ∀ k < rnd18 i, ∃ c c' : E, h[N18 + base18 i + 7 * k + 5]? = some (Ev.sample c) ∧
      h[N18 + base18 i + 7 * k + 6]? = some (Ev.sample c') ∧
      (rs.getD k default).α = e2OfE c ∧ (rs.getD k default).β = e2OfE c') : ChF M i rs := by
  intro k hk
  obtain ⟨c, c', b1, b2, b3, b4⟩ := hr k hk
  obtain ⟨m1, m2⟩ := mem_ch hi hk
  have e : (rs.map fun r ↦ (r.α, r.β)).getD k (0, 0) = ((rs.getD k default).α, (rs.getD k default).β) := by
    rw [show ((0 : E2), (0 : E2)) = (fun r : Rnd E2 ↦ (r.α, r.β)) default from rfl, List.getD_map]
  rw [e]
  exact ⟨by rw [hS _ _ m1 c b1, b3], by rw [hS _ _ m2 c' b2, b4]⟩

omit hS in
include hR in
theorem hiF_of {i : ℕ} (hi : i < 4) {hs : List E2}
    (hh : ∀ k < rnd18 i, ∃ x, h[N18 + base18 i + 7 * rnd18 i + k]? = some (Ev.read x) ∧ hs.getD k 0 = e2OfE x) :
    HiF M i hs := fun k hk => by
  obtain ⟨x, b1, b2⟩ := hh k hk
  rw [hR _ _ (mem_hi hi hk) x b1, b2]

include hR in
/-- **A mid level**: from its run at `N18 + base18 i`, its cells, and the next level's start. -/
theorem mid_level {n ℓ n' ℓ' : ℕ} (Md : MidLv E2 WtE n ℓ n' ℓ') {i : ℕ} (hi : i < 4) (hℓ : ℓ = rnd18 i)
    (hnh : Md.L.nh = rnd18 i) (hT : (tailOps Md.L.nh Md.ht Md.wd Md.L.ko Md.L.kq Md.i).length = tl18 i)
    {rs : List (Rnd E2)} {o : TailOut E2 Md.L.ko Md.L.t n} {l' : List Ev}
    (hRun : RunMidE Md (h.drop (N18 + base18 i)) rs o l') :
    l' = h.drop (N18 + base18 (i + 1)) ∧ ChF M i rs ∧ HiF M i o.hi := by
  obtain ⟨e1, e2, e3, e4⟩ := mid_seg Md hRun
  subst hℓ
  refine ⟨?_, chF_of hS (by omega) e2 e3, hiF_of hR hi fun k hk => e4 k (by omega)⟩
  rw [e1, hT, show base18 (i + 1) = base18 i + 7 * rnd18 i + tl18 i from rfl, ← Nat.add_assoc, ← Nat.add_assoc]

include hR in
theorem fin_level {rs : List (Rnd E2)} {sc : List E2} (hRun : RunFinE fin18 (h.drop (N18 + base18 4)) rs sc) :
    ChF M 4 rs ∧ SF M sc := by
  obtain ⟨e1, e2, e3⟩ := fin_seg hRun
  refine ⟨chF_of hS (by norm_num) e1 e2, fun k hk => ?_⟩
  obtain ⟨x, b1, b2⟩ := e3 k hk
  rw [hR _ _ (mem_s hk) x b1, b2]

include hR in
/-- **`FrontSeg18`** from the requests' cells. -/
theorem frontSeg18_of : FrontSeg18 M h := by
  intro rs0 o0 l1 rs1 o1 l2 rs2 o2 l3 rs3 o3 l4 rs4 sc r0 r1 r2 r3 r4
  have r0' : RunMidE mid0 (h.drop (N18 + base18 0)) rs0 o0 l1 := by simpa only [base18, Nat.add_zero] using r0
  have n0 : mid0.L.nh = rnd18 0 := rfl
  have n1 : mid1.L.nh = rnd18 1 := rfl
  have n2 : mid2.L.nh = rnd18 2 := rfl
  have n3 : mid3.L.nh = rnd18 3 := rfl
  have t0 : (tailOps mid0.L.nh mid0.ht mid0.wd mid0.L.ko mid0.L.kq mid0.i).length = tl18 0 := rfl
  have t1 : (tailOps mid1.L.nh mid1.ht mid1.wd mid1.L.ko mid1.L.kq mid1.i).length = tl18 1 := rfl
  have t2 : (tailOps mid2.L.nh mid2.ht mid2.wd mid2.L.ko mid2.L.kq mid2.i).length = tl18 2 := rfl
  have t3 : (tailOps mid3.L.nh mid3.ht mid3.wd mid3.L.ko mid3.L.kq mid3.i).length = tl18 3 := rfl
  obtain ⟨q1, c0, h0⟩ := mid_level hS hR mid0 (i := 0) (by norm_num) rfl n0 t0 r0'
  rw [show (0 + 1 : ℕ) = 1 from rfl] at q1
  rw [q1] at r1
  obtain ⟨q2, c1, h1⟩ := mid_level hS hR mid1 (i := 1) (by norm_num) rfl n1 t1 r1
  rw [show (1 + 1 : ℕ) = 2 from rfl] at q2
  rw [q2] at r2
  obtain ⟨q3, c2, h2⟩ := mid_level hS hR mid2 (i := 2) (by norm_num) rfl n2 t2 r2
  rw [show (2 + 1 : ℕ) = 3 from rfl] at q3
  rw [q3] at r3
  obtain ⟨q4, c3, h3⟩ := mid_level hS hR mid3 (i := 3) (by norm_num) rfl n3 t3 r3
  rw [show (3 + 1 : ℕ) = 4 from rfl] at q4
  rw [q4] at r4
  obtain ⟨c4, s4⟩ := fin_level hS hR r4
  exact ⟨c0, c1, c2, c3, c4, h0, h1, h2, h3, s4⟩

end Levels

/-! ## The fill on the front -/

/-- `¬ Bad` gives no state hit (season 1's `notStateHit_of_notBad`, `LvmXSpec`, ported). -/
theorem notStateHit_of_notBad6 {L : Log} (h : ¬ Lvm.FS.Bad L) : ¬ StateHit L := by
  rintro ⟨i, j, hij, hj, hs⟩
  refine h (Or.inr (Or.inr ⟨i, j, hij, hj, ?_⟩))
  unfold stateIn at hs
  split_ifs at hs with hc
  refine ⟨hc.2, 0, hc.1, ?_⟩
  have e := (Option.some.inj hs).symm
  rw [e]
  apply Vector.ext
  intro k hk
  simp [Lvm.FS.win, Lvm.FS.dg, Lvm.FS.qb]

/-- The state after the parse, the front and the fill. -/
def fillSt (c : Digest) (π : Proof) (L : Log) : St :=
  semXIR (extractorInput c π L).toArray fillIR18 (frontSt6 (extractorInput c π L))

theorem notin_dsts {y : ℕ} (hy : y < 33554432 ∨ 67108864 ≤ y) : y ∉ fillTab18.map fun e ↦ e.2.2 := by
  intro hm
  obtain ⟨e, he, rfl⟩ := List.mem_map.1 hm
  have := List.all_eq_true.1 fill18_ok.1 e he
  simp only [cpOK, Bool.and_eq_true, decide_eq_true_eq] at this
  omega

/-- **`fill_front`**: after `parseIR ; frontIR6 ; fillIR18` on the tape of an accepted `S` proof of `pz6` bytes, a log
with no state hit and the tape's size facts: `Inv`, no output, the heap outside `[2^25, 2^26)` as the front left it,
the committed rows, the front's cells on every decomposition of the opening's log, and the opening starts at `N18`. -/
theorem fill_front {Φ : Phases} (hF : PhasesFollow Φ P18) (hW : ∀ cl, QLen tP18 (Φ.whir P18 cl))
    {vk c : Digest} {π : Proof} {L : Log} {x : List UInt8} {h : List Ev}
    (hE : (schemeOf (prog6 Φ) P18 vk).Ex (fun _ x h => (x, h)) c π L = some (x, h)) (hs : π.size = pz6)
    (hq : ∀ e ∈ L, e.1.size < 2 ^ 64) (ht : (extractorInput c π L).length ≤ 2 ^ 64) (hSt : ¬ StateHit L) :
    Inv (fillSt c π L).M ∧ (fillSt c π L).o = #[] ∧
    (∀ y, regs ≤ y → (y < 33554432 ∨ 67108864 ≤ y) →
      rd (fillSt c π L).M y = rd (frontSt6 (extractorInput c π L)).M y) ∧
    Rows18 (fillSt c π L).M h ∧ FrontSeg18 (fillSt c π L).M h ∧
    ∀ (cl : StackClaim6) (N₀ : ℕ) (b : Bool), (whirP18 cl).after (h.drop N₀) = some (.ret b) → N₀ = N18 := by
  obtain ⟨-, -, hfor⟩ := front6_hist hF hW hE
  obtain ⟨m1, m2, -, m4⟩ := front6_sem (c := c) hs hq ht hSt
  obtain ⟨-, -, r1, r2, -⟩ := front6_heap hF hW hE hs hq ht hSt
  have hsz : 67108864 ≤ (frontSt6 (extractorInput c π L)).M.size := by
    rw [frontSt6, size_sem, size_sem, initSt_M, size_runPrims, Array.size_replicate]
    simp only [mem6]; omega
  have hfi : fillIR18 = cpsIR fillTab18 := rfl
  have hfs : fillSt c π L = semXIR (extractorInput c π L).toArray (cpsIR fillTab18)
      (frontSt6 (extractorInput c π L)) := by rw [fillSt, hfi]
  obtain ⟨f1, f2, f3, f4, -⟩ := cpsIR_sem (extractorInput c π L).toArray 33554432 67108864 fillTab18 _ m1 hsz
    fill18_ok.1 fill18_ok.2.1
  rw [hfs]
  have hfr : ∀ y, regs ≤ y → (y < 33554432 ∨ 67108864 ≤ y) →
      rd (semXIR (extractorInput c π L).toArray (cpsIR fillTab18) (frontSt6 (extractorInput c π L))).M y =
        rd (frontSt6 (extractorInput c π L)).M y := fun y hy hy' => f2 y hy (notin_dsts hy')
  refine ⟨f3, f4.trans m2, hfr, ⟨r1, fun i hi => ?_⟩, ?_, fun cl N₀ b hN => n0_eq hfor hN⟩
  · obtain ⟨a1, a2, a3, a4⟩ := r2 i hi
    refine ⟨a1, a2, a3, fun p hp t htt => ?_⟩
    rw [← a4 p hp t htt]
    unfold rdK
    have hw : 134217728 ≤ wB6 i := by
      rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4) with rfl | rfl | rfl | rfl | rfl <;>
        simp only [wB6] <;> omega
    rw [hfr _ (by simp only [regs]; omega) (Or.inr (by omega))]
  · exact frontSeg18_of (fun n dst hr cc he => req_smp rfl hfor f1 m4 hr he)
      (fun n dst hr x he => req_rd rfl rfl hs hfor f1 hr he)

/-- **`frontIn18`**: `fill_front` under `¬ Bad L` (no state hit) for phases with the deployed opening. -/
theorem frontIn18 {Φ : Phases} (hF : PhasesFollow Φ P18) (hw : Φ.whir = whirAt Whir.whirP18)
    {vk c : Digest} {π : Proof} {L : Log} {x : List UInt8} {h : List Ev}
    (hE : (schemeOf (prog6 Φ) P18 vk).Ex (fun _ x h => (x, h)) c π L = some (x, h)) (hs : π.size = pz6)
    (hq : ∀ e ∈ L, e.1.size < 2 ^ 64) (ht : (extractorInput c π L).length ≤ 2 ^ 64) (hB : ¬ Lvm.FS.Bad L) :
    Inv (fillSt c π L).M ∧ (fillSt c π L).o = #[] ∧
    (∀ y, regs ≤ y → (y < 33554432 ∨ 67108864 ≤ y) →
      rd (fillSt c π L).M y = rd (frontSt6 (extractorInput c π L)).M y) ∧
    Rows18 (fillSt c π L).M h ∧ FrontSeg18 (fillSt c π L).M h ∧
    ∀ (cl : StackClaim6) (N₀ : ℕ) (b : Bool), (whirP18 cl).after (h.drop N₀) = some (.ret b) → N₀ = N18 :=
  fill_front hF (qlen_whirAt hw) hE hs hq ht (notStateHit_of_notBad6 hB)

end Lvm6.X
