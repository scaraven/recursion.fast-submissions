-- New for lvm6 (WP ASM, owning WP RS's v2.4 items): FORMAT6 v2.4 §6.5 as a program over WP RS's
-- verifier functions (the bind, one group of a nonce and 33 draws: two ring maps and `λ₀`; the batched
-- stack claim), and its proof against WP S's `Stmt.ringSpec6` (list form, `CAND-decision.md`). The
-- count and the group escape follow RS's `card_stackBad_le`, `card_powOK_outOf_le`, `ringSpec6`.
import Lvm6Ring
import Lvm6AsmProg
import Lvm6MultiaffBase

/-!
# §6.5 at v2.4: two slice sets in one group

WP RS's `ringProg` (`Lvm6Ring`, kept for WP CC) switches one slice set with 17 draws. FORMAT6 v2.4
§6.5 has `B`, then `G(17) D(32)`: the nonce, the tree map `f, g` (the ground draw `f₀` carries the
proof of work), the sponge map `f, g`, then `λ₀` (33 draws).

* **`ringPhase6 sh sl st`**: a static `require` (`ringOK`: the batch row `(J₀ + 3)·L₀` admitted at
  `gRing`, `gRing ≤ 64`, two slice sets with points of `M` coordinates), the bind, the nonce, the 33 draws with
  the proof of work, and the claim `claimOf6`: RS's `batch` by `λ₀` of the stacked claims with the two
  ring claims at FORMAT6's indices 1 and 15 (`placeRing`). A slice claim is a whole-stack point (a
  block's selector bits are Boolean coordinates), so RS's `ringClaim` is taken with `μ = M` and no
  selector (`ringOf`). `ringPhase6_follows`, `ringPhase6_noCommit`.
* **`sdef_ringOf`**: the bridge to WP S's types: the defect of `ringOf c` on a `Stack` is RS's ring
  form of `c`'s true slice values (`zS`) minus the target (`bitsOf`: `Fin (2^M) ≃ (Fin M → Bool)`).
* **`card_bad6_le`**: for one stack whose slice or stack claims are false, at most `(|st| + 3)·|E2|^32`
  of the `|E2|^33` challenge tuples make the batched claim true (`card_ringBad_le` per map).
* **`ringSpec6_asm : Stmt.ringSpec6 ringPhase6`**: S's list form, the group's escape
  `L₀·2^-g·(|st| + 3)/2^128 ≤ εI` from PARAM's admission (`errG_le_εI`), over any candidate map of at
  most `sh.L₀` members fixed on `G` (`listSpec_of`). The batched claim is multiaffine when the
  stacked claims are (W1 F-3): `claimOf6_mle` (`ringOf_mle` per map, RS's `mle_batch`), carried in
  `ringSpec6v24`'s postcondition through its escape computation (`escRet_doomed_stableP`), and
  `multiaffine_iff_mle` (S's `Multiaffine` is RS's `Claim.Mle`).
-/

set_option autoImplicit false

namespace Lvm6

open LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Protocol.EndToEnd.Front LeanVM.Protocol.Whir.Sound Lvm Lvm.E2V Finset
open Lvm6.Ring
open scoped ENNReal

/-! ## The program -/

/-- The 33 draws read as `((tree f, tree g), (sponge f, sponge g)), λ₀`. -/
def ringOut6 (cs : List E) : ((List E2 × List E2) × (List E2 × List E2)) × E2 :=
  ((((cs.take 8).map e2OfE, ((cs.drop 8).take 8).map e2OfE),
    (((cs.drop 16).take 8).map e2OfE, ((cs.drop 24).take 8).map e2OfE)), e2OfE (cs.getD 32 0))

/-- FORMAT6 §6.5's order: claim 0, the tree ring claim, the 13 tree claims, the sponge ring claim,
the rest. -/
def placeRing (rt rs : StackClaim6) (st : List StackClaim6) : List StackClaim6 :=
  st.take 1 ++ rt :: (st.drop 1).take 13 ++ rs :: st.drop 14

/-- RS's ring claim of a whole-stack slice claim (`μ = |pt|`, no selector). -/
def ringOf (c : SliceClaim) (f g : List E2) : StackClaim6 :=
  ringClaim c.pt.length c.pt (List.ofFn c.s) [] f g

/-- The batched claim of the challenges. -/
def claimOf6 (sl : List SliceClaim) (st : List StackClaim6)
    (o : ((List E2 × List E2) × (List E2 × List E2)) × E2) : StackClaim6 :=
  batch o.2 (placeRing (ringOf (sl.getD 0 ⟨[], 0⟩) o.1.1.1 o.1.1.2)
    (ringOf (sl.getD 1 ⟨[], 0⟩) o.1.2.1 o.1.2.2) st)

/-- The static conditions of §6.5 (true at `P18`): the batch row admitted, the grind within a lane,
two slice sets with points of `M` coordinates. -/
def ringOK (sh : Shape) (sl : List SliceClaim) : Prop :=
  Params.admits ((sh.J₀ + 3) * sh.L₀) sh.gRing = true ∧ sh.gRing ≤ 64 ∧
    (∀ c ∈ sl, c.pt.length = sh.M) ∧ sl.length = 2

instance (sh : Shape) (sl : List SliceClaim) : Decidable (ringOK sh sl) := by
  unfold ringOK; infer_instance

/-- The draws, the proof of work and the claim. -/
def ringBody (g : ℕ) (sl : List SliceClaim) (st : List StackClaim6) :
    VerifierProgram StackClaim6 :=
  VerifierProgram.sampleChallenges 33 >>= fun cs ↦
    VerifierProgram.require (powOK g (cs.headD 0)) >>= fun _ ↦ pure (claimOf6 sl st (ringOut6 cs))

/-- **The ring phase of `prog6`** (FORMAT6 v2.4 §6.5). -/
def ringPhase6 (sh : Shape) (sl : List SliceClaim) (st : List StackClaim6) :
    VerifierProgram StackClaim6 :=
  VerifierProgram.require (ringOK sh sl) >>= fun _ ↦ e2Sep >>= fun _ ↦
    VerifierProgram.readScalar >>= fun _ ↦ ringBody sh.gRing sl st

theorem follows_sampleChallenges : ∀ n, Follows (VerifierProgram.sampleChallenges n)
    (List.replicate n .smp)
  | 0 => rfl
  | n + 1 => by
    have h : List.replicate (n + 1) Op.smp = [.smp] ++ (List.replicate n .smp ++ []) := by
      simp [List.replicate_succ]
    rw [h]
    exact Follows.bind' ⟨rfl, fun _ ↦ rfl⟩ fun _ ↦
      Follows.bind' (follows_sampleChallenges n) fun _ ↦ rfl

theorem ringOps (sh : Shape) : opsOf sh.levs sh.ringPart =
    [] ++ ([.smp] ++ ([.rd] ++ (List.replicate 33 .smp ++ ([] ++ [])))) := by
  simp only [opsOf, Shape.ringPart, V.Prims.walk, V.Prims.item, po_rep_draw]
  simp [PO, List.replicate_succ]

theorem ringPhase6_follows (sh : Shape) (sl : List SliceClaim) (st : List StackClaim6) :
    Follows (ringPhase6 sh sl st) (opsOf sh.levs sh.ringPart) := by
  rw [ringOps]
  exact Follows.bind' (follows_require _) fun _ ↦ Follows.bind' ⟨rfl, fun _ ↦ rfl⟩ fun _ ↦
    Follows.bind' ⟨rfl, fun _ ↦ rfl⟩ fun _ ↦ Follows.bind' (follows_sampleChallenges 33) fun _ ↦
      Follows.bind' (follows_require _) fun _ ↦ rfl

/-- A program following operations with no cap commits nothing. -/
theorem Follows.noCommit {α : Type} : ∀ {p : VerifierProgram α} {os : List Op}, Follows p os →
    (∀ ht w, Op.cap ht w ∉ os) → p.NoCommit
  | .ret _, _, _, _ => trivial
  | .fail, _, _, _ => trivial
  | .grind _ _, _, h, _ => h.elim
  | .read _, _, h, hc => fun x ↦ (h.2 x).noCommit fun ht w hm ↦ hc ht w (List.mem_of_mem_tail hm)
  | .sample _, _, h, hc => fun x ↦ (h.2 x).noCommit fun ht w hm ↦ hc ht w (List.mem_of_mem_tail hm)
  | .commit ht w _, _, h, hc => hc ht w (List.mem_of_mem_head? h.1)
  | .query _ _ _, _, h, hc => fun r ↦ (h.2 r).noCommit fun ht w hm ↦
      hc ht w (List.mem_of_mem_tail hm)

/-- **§6.5 commits nothing.** -/
theorem ringPhase6_noCommit (sh : Shape) (sl : List SliceClaim) (st : List StackClaim6) :
    Stmt.noCommit (ringPhase6 sh sl st) := fun _ _ hr ↦
  VerifierProgram.NoCommit.reach_commits ((ringPhase6_follows sh sl st).noCommit fun ht w hm ↦ by
    rw [ringOps] at hm; simp [List.mem_replicate] at hm) hr

/-! ## The bridge to WP S's claims -/

section Bridge

variable (M : ℕ)

instance (M : ℕ) (c : StackClaim6) (q : Stack) : Decidable (c.Holds M q) :=
  inferInstanceAs (Decidable (_ = _))

/-- The defect of a stack claim on a stack. -/
def sdef (c : StackClaim6) (q : Stack) : E2 :=
  ∑ x : Fin (2 ^ M), c.1 (boolPt M x) * algebraMap K E2 (q x) - c.2

theorem holds_iff_sdef (c : StackClaim6) (q : Stack) : c.Holds M q ↔ sdef M c q = 0 := by
  rw [StackClaim6.Holds, sdef, sub_eq_zero]

/-- **The batch's defect is the batch polynomial of the defects.** -/
theorem sdef_batch (lam : E2) (cs : List StackClaim6) (q : Stack) :
    sdef M (batch lam cs) q = polyEvalF (cs.map fun c ↦ sdef M c q) lam := by
  rw [sdef, batch_snd]
  simp only [batch_fst]
  induction cs with
  | nil => simp [polyEvalF]
  | cons c cs ih =>
    have e : ∀ x : Fin (2 ^ M),
        polyEvalF ((c :: cs).map fun c ↦ c.1 (boolPt M x)) lam * algebraMap K E2 (q x) =
          polyEvalF (cs.map fun c ↦ c.1 (boolPt M x)) lam * algebraMap K E2 (q x) * lam +
            c.1 (boolPt M x) * algebraMap K E2 (q x) := fun x ↦ by
      rw [List.map_cons, polyEvalF_cons]; ring
    rw [Finset.sum_congr rfl fun x _ ↦ e x, Finset.sum_add_distrib, ← Finset.sum_mul,
      List.map_cons, List.map_cons, polyEvalF_cons, polyEvalF_cons, ← ih, sdef]
    ring

/-- The bits of an index of the stack, low first. -/
def bitsOf (x : Fin (2 ^ M)) : Fin M → Bool := fun i ↦ (x : ℕ).testBit i

theorem bitsOf_bijective : Function.Bijective (bitsOf M) := by
  refine (Fintype.bijective_iff_injective_and_card _).mpr ⟨fun x y h ↦ ?_, by simp⟩
  apply Fin.ext
  apply Nat.eq_of_testBit_eq
  intro i
  by_cases hi : i < M
  · exact congrFun h ⟨i, hi⟩
  · have hp : 2 ^ M ≤ 2 ^ i := Nat.pow_le_pow_right (by norm_num) (by omega)
    rw [Nat.testBit_eq_false_of_lt (lt_of_lt_of_le x.2 hp),
      Nat.testBit_eq_false_of_lt (lt_of_lt_of_le y.2 hp)]

/-- The stack on the cube. -/
noncomputable def qb (q : Stack) : (Fin M → Bool) → K :=
  fun u ↦ q ((Equiv.ofBijective _ (bitsOf_bijective M)).symm u)

theorem qb_bitsOf (q : Stack) (x : Fin (2 ^ M)) : qb M q (bitsOf M x) = q x := by
  simp only [qb]
  rw [show (Equiv.ofBijective _ (bitsOf_bijective M)).symm (bitsOf M x) = x from
    Equiv.ofBijective_symm_apply_apply _ _ x]

theorem boolPt_eq (x : Fin (2 ^ M)) :
    boolPt M x = List.ofFn (bitV (bitsOf M x) : Fin M → E2) := by
  apply List.ext_getElem (by simp [boolPt])
  intro i h1 h2
  simp only [boolPt, bitV, bitsOf, List.getElem_map, List.getElem_range, List.getElem_ofFn]
  split_ifs <;> simp_all

theorem eqPt_ofFn {n : ℕ} (a b : Fin n → E2) : eqPt (List.ofFn a) (List.ofFn b) = eqP a b := by
  have h2 : (2 : E2) = 0 := CharTwo.two_eq_zero
  unfold eqPt
  rw [show (fun r t : E2 ↦ r * t + (1 + r) * (1 + t)) = (fun r t ↦ 1 + r + t) from
    funext₂ fun r t ↦ by linear_combination (r * t) * h2]
  exact zipWith_prod_ofFn a b

/-- The true slice values of a slice claim's point on the stack. -/
def zS (c : SliceClaim) (q : Stack) (i : Fin 64) : E2 :=
  ∑ x : Fin (2 ^ M), eqPt c.pt (boolPt M x) * bitE (q x) i

theorem sliceHolds_iff (c : SliceClaim) (q : Stack) : c.Holds M q ↔ c.s = zS M c q := by
  constructor
  · intro h; funext i; exact (h i).symm
  · intro h i; rw [h]; rfl

/-- **The ring claim's defect** on a stack: RS's ring form of the true slice values minus the
target. -/
theorem sdef_ringOf (c : SliceClaim) (hc : c.pt.length = M) (f g : Fin 8 → E2) (q : Stack) :
    sdef M (ringOf c (List.ofFn f) (List.ofFn g)) q =
      ∑ i : Fin 64, Ring.ringW i * frobPhi 8 f g (zS M c q i) -
        ringTarget genE2 (List.ofFn c.s) (List.ofFn f) (List.ofFn g) := by
  obtain ⟨r, hpt⟩ : ∃ r : Fin M → E2, c.pt = List.ofFn r :=
    ⟨fun i ↦ c.pt[i.val]'(by rw [hc]; exact i.2),
      List.ext_getElem (by simp [hc]) fun i _ _ ↦ by simp⟩
  have hw : ∀ u : Fin M → Bool, (ringOf c (List.ofFn f) (List.ofFn g)).1
      (List.ofFn (bitV u : Fin M → E2)) = frobPhi 8 f g (eqP r (bitV u)) := by
    intro u
    simp only [ringOf, ringClaim]
    rw [hpt, List.length_ofFn, List.take_of_length_le (by simp), ringWeight_ofFn, frobPhi_eqP]
    simp [eqEvalF]
  have hs : ∀ i, Ring.sliceExt (qb M q) r i = zS M c q i := by
    intro i
    simp only [Ring.sliceExt, zS]
    rw [← (bitsOf_bijective M).sum_comp]
    refine Finset.sum_congr rfl fun x _ ↦ ?_
    rw [qb_bitsOf, boolPt_eq, hpt, eqPt_ofFn]
    rfl
  have hsum : ∑ x : Fin (2 ^ M), (ringOf c (List.ofFn f) (List.ofFn g)).1 (boolPt M x) *
      algebraMap K E2 (q x) = ∑ u, frobPhi 8 f g (eqP r (bitV u)) * ofK2 (qb M q u) := by
    rw [← (bitsOf_bijective M).sum_comp]
    refine Finset.sum_congr rfl fun x _ ↦ ?_
    rw [boolPt_eq, hw, qb_bitsOf]
  rw [sdef, hsum, ring_complete]
  simp only [hs, ringOf, ringClaim]

end Bridge

/-! ## The count -/

section Count

theorem mem_placeRing {rt rs : StackClaim6} {st : List StackClaim6} {x : StackClaim6}
    (hx : x ∈ placeRing rt rs st) : x = rt ∨ x = rs ∨ x ∈ st := by
  simp only [placeRing, List.mem_append, List.mem_cons] at hx
  rcases hx with ((h | h | h) | h | h)
  · exact Or.inr (Or.inr (List.mem_of_mem_take h))
  · exact Or.inl h
  · exact Or.inr (Or.inr (List.mem_of_mem_drop (List.mem_of_mem_take h)))
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr (List.mem_of_mem_drop h))

theorem placeRing_mem {rt rs : StackClaim6} {st : List StackClaim6} {x : StackClaim6}
    (hx : x ∈ st) : x ∈ placeRing rt rs st := by
  have e : st = st.take 1 ++ ((st.drop 1).take 13 ++ st.drop 14) := by
    rw [show st.drop 14 = (st.drop 1).drop 13 by rw [List.drop_drop], List.take_append_drop,
      List.take_append_drop]
  rw [e] at hx
  simp only [placeRing, List.mem_append, List.mem_cons] at hx ⊢
  tauto

theorem rt_mem_placeRing (rt rs : StackClaim6) (st : List StackClaim6) :
    rt ∈ placeRing rt rs st := by
  simp [placeRing]

theorem rs_mem_placeRing (rt rs : StackClaim6) (st : List StackClaim6) :
    rs ∈ placeRing rt rs st := by
  simp [placeRing]

theorem length_placeRing (rt rs : StackClaim6) (st : List StackClaim6) :
    (placeRing rt rs st).length = st.length + 2 := by
  simp only [placeRing, List.length_append, List.length_cons, List.length_take, List.length_drop]
  omega

/-- The challenge tuples: the two maps. -/
abbrev X6 : Type := ((Fin 8 → E2) × (Fin 8 → E2)) × ((Fin 8 → E2) × (Fin 8 → E2))

/-- A tuple with `λ₀` as lists. -/
def outL (y : X6 × E2) : ((List E2 × List E2) × (List E2 × List E2)) × E2 :=
  (((List.ofFn y.1.1.1, List.ofFn y.1.1.2), (List.ofFn y.1.2.1, List.ofFn y.1.2.2)), y.2)

theorem card_filter_prod_fst' {α γ : Type} [Fintype α] [Fintype γ] (P : α × γ → Prop)
    [DecidablePred P] :
    (univ.filter P).card = ∑ x : α, (univ.filter fun y : γ ↦ P (x, y)).card := by
  rw [Finset.card_filter, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun x _ ↦ ?_
  rw [Finset.card_filter]

theorem card_filter_fst {α γ : Type} [Fintype α] [Fintype γ] (P : α → Prop)
    [DecidablePred P] :
    (univ.filter fun z : α × γ ↦ P z.1).card = (univ.filter P).card * Fintype.card γ := by
  rw [show (univ.filter fun z : α × γ ↦ P z.1) = (univ.filter P) ×ˢ (univ : Finset γ) by
    ext z; simp, Finset.card_product, Finset.card_univ]

theorem card_filter_snd {α γ : Type} [Fintype α] [Fintype γ] (P : γ → Prop)
    [DecidablePred P] :
    (univ.filter fun z : α × γ ↦ P z.2).card = Fintype.card α * (univ.filter P).card := by
  rw [show (univ.filter fun z : α × γ ↦ P z.2) = (univ : Finset α) ×ˢ (univ.filter P) by
    ext z; simp, Finset.card_product, Finset.card_univ]

/-- A member of at most two slice sets is the first or the second. -/
theorem mem_two {sl : List SliceClaim} (hsl : sl.length ≤ 2) {c : SliceClaim} (hc : c ∈ sl) :
    c = sl.getD 0 ⟨[], 0⟩ ∨ c = sl.getD 1 ⟨[], 0⟩ := by
  match sl, hsl, hc with
  | [a], _, hc => left; simpa using hc
  | [a, b], _, hc =>
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr rfl

variable (M : ℕ)

/-- One map's bad pairs: at most `2·|E2|^15` when the slice claim is false. -/
theorem card_ringOfBad_le (c : SliceClaim) (hc : c.pt.length = M) (q : Stack)
    (h : ¬ c.Holds M q) :
    (univ.filter fun fg : (Fin 8 → E2) × (Fin 8 → E2) ↦
      sdef M (ringOf c (List.ofFn fg.1) (List.ofFn fg.2)) q = 0).card ≤ 2 * (2 ^ 128) ^ 15 := by
  have hne : c.s ≠ zS M c q := fun e ↦ h ((sliceHolds_iff M c q).mpr e)
  refine (Finset.card_le_card fun fg hfg ↦ ?_).trans (card_ringBad_le hne)
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hfg ⊢
  rw [sdef_ringOf M c hc] at hfg
  exact (sub_eq_zero.mp hfg).symm

/-- **The count behind `ringSpec6_asm`**: for a stack whose slice or stack claims are false, at most
`(|st| + 3)·|E2|^32` challenge tuples make the batched claim true. -/
theorem card_bad6_le (sl : List SliceClaim) (st : List StackClaim6) (hsl : sl.length ≤ 2)
    (hlen : ∀ c ∈ sl, c.pt.length = M) (q : Stack)
    (h : ¬ ((∀ c ∈ sl, c.Holds M q) ∧ ∀ c ∈ st, c.Holds M q)) :
    (univ.filter fun y : X6 × E2 ↦ (claimOf6 sl st (outL y)).Holds M q).card ≤
      (st.length + 3) * (2 ^ 128) ^ 32 := by
  classical
  let s0 : SliceClaim := sl.getD 0 ⟨[], 0⟩
  let s1 : SliceClaim := sl.getD 1 ⟨[], 0⟩
  let D : X6 → List E2 := fun x ↦ (placeRing (ringOf s0 (List.ofFn x.1.1) (List.ofFn x.1.2))
    (ringOf s1 (List.ofFn x.2.1) (List.ofFn x.2.2)) st).map fun c ↦ sdef M c q
  have hDlen : ∀ x, (D x).length = st.length + 2 := fun x ↦ by simp [D, length_placeRing]
  have hcard : (univ.filter fun y : X6 × E2 ↦ (claimOf6 sl st (outL y)).Holds M q) =
      univ.filter fun y : X6 × E2 ↦ polyEvalF (D y.1) y.2 = 0 := by
    ext y
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, holds_iff_sdef, claimOf6, outL,
      sdef_batch, D, s0, s1]
  rw [hcard, card_filter_prod_fst']
  have hE : Fintype.card E2 = 2 ^ 128 := card_E2
  have hx : ∀ x, (univ.filter fun lam ↦ polyEvalF (D x) lam = 0).card ≤
      (st.length + 1) + (if ∀ d ∈ D x, d = 0 then 2 ^ 128 else 0) := by
    intro x
    split_ifs with h0
    · exact (Finset.card_le_univ _).trans (by rw [hE]; omega)
    · have hex : ∃ d ∈ D x, d ≠ 0 := by
        by_contra hall; push_neg at hall; exact h0 hall
      have := card_polyEvalF_zero_le _ hex
      rw [hDlen] at this
      omega
  have hpair : Fintype.card ((Fin 8 → E2) × (Fin 8 → E2)) = (2 ^ 128) ^ 16 := by
    rw [Fintype.card_prod, Fintype.card_fun, Fintype.card_fin, hE, ← pow_add]
  have hZ : (univ.filter fun x : X6 ↦ ∀ d ∈ D x, d = 0).card ≤ 2 * (2 ^ 128) ^ 31 := by
    by_cases hst : ∀ c ∈ st, c.Holds M q
    · have hsl' : ¬ ∀ c ∈ sl, c.Holds M q := fun hs ↦ h ⟨hs, hst⟩
      push_neg at hsl'
      obtain ⟨c, hc, hnc⟩ := hsl'
      rcases mem_two hsl hc with e0 | e1
      · have hsub : (univ.filter fun x : X6 ↦ ∀ d ∈ D x, d = 0) ⊆ univ.filter fun x : X6 ↦
            sdef M (ringOf s0 (List.ofFn x.1.1) (List.ofFn x.1.2)) q = 0 := by
          intro x hx0
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx0 ⊢
          exact hx0 _ (List.mem_map_of_mem (rt_mem_placeRing _ _ _))
        refine (Finset.card_le_card hsub).trans ?_
        rw [card_filter_fst (fun fg : (Fin 8 → E2) × (Fin 8 → E2) ↦
          sdef M (ringOf s0 (List.ofFn fg.1) (List.ofFn fg.2)) q = 0), hpair]
        have hb := card_ringOfBad_le M s0 (by rw [show s0 = c from e0.symm]; exact hlen c hc) q
          (by rw [show s0 = c from e0.symm]; exact hnc)
        calc _ ≤ 2 * (2 ^ 128) ^ 15 * (2 ^ 128) ^ 16 := Nat.mul_le_mul_right _ hb
          _ = 2 * (2 ^ 128) ^ 31 := by ring
      · have hsub : (univ.filter fun x : X6 ↦ ∀ d ∈ D x, d = 0) ⊆ univ.filter fun x : X6 ↦
            sdef M (ringOf s1 (List.ofFn x.2.1) (List.ofFn x.2.2)) q = 0 := by
          intro x hx0
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx0 ⊢
          exact hx0 _ (List.mem_map_of_mem (rs_mem_placeRing _ _ _))
        refine (Finset.card_le_card hsub).trans ?_
        rw [card_filter_snd (fun fg : (Fin 8 → E2) × (Fin 8 → E2) ↦
          sdef M (ringOf s1 (List.ofFn fg.1) (List.ofFn fg.2)) q = 0), hpair]
        have hb := card_ringOfBad_le M s1 (by rw [show s1 = c from e1.symm]; exact hlen c hc) q
          (by rw [show s1 = c from e1.symm]; exact hnc)
        calc _ ≤ (2 ^ 128) ^ 16 * (2 * (2 ^ 128) ^ 15) := Nat.mul_le_mul_left _ hb
          _ = 2 * (2 ^ 128) ^ 31 := by ring
    · have : (univ.filter fun x : X6 ↦ ∀ d ∈ D x, d = 0) = ∅ := by
        ext x
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty, iff_false]
        intro hall
        exact hst fun c hc ↦ (holds_iff_sdef M c q).mpr
          (hall _ (List.mem_map_of_mem (placeRing_mem hc)))
      rw [this, Finset.card_empty]; exact Nat.zero_le _
  have huniv : Fintype.card X6 = (2 ^ 128) ^ 32 := by
    rw [Fintype.card_prod, hpair, ← pow_add]
  calc ∑ x, (univ.filter fun lam ↦ polyEvalF (D x) lam = 0).card
      ≤ ∑ x : X6, ((st.length + 1) + if ∀ d ∈ D x, d = 0 then 2 ^ 128 else 0) :=
        Finset.sum_le_sum fun x _ ↦ hx x
    _ = (2 ^ 128) ^ 32 * (st.length + 1) +
          (univ.filter fun x : X6 ↦ ∀ d ∈ D x, d = 0).card * 2 ^ 128 := by
        rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, huniv, smul_eq_mul,
          ← Finset.sum_filter, Finset.sum_const, smul_eq_mul]
    _ ≤ (2 ^ 128) ^ 32 * (st.length + 1) + 2 * (2 ^ 128) ^ 31 * 2 ^ 128 :=
        Nat.add_le_add_left (Nat.mul_le_mul_right _ hZ) _
    _ = (st.length + 3) * (2 ^ 128) ^ 32 := by ring

end Count

/-! ## The batched weight is multiaffine (W1's F-3) -/

section Mle

variable (M : ℕ)

/-- **A ring claim's weight is multiaffine** (RS's `Claim.Mle`), for any ring map. -/
theorem ringOf_mle (c : SliceClaim) (hc : c.pt.length = M) (f g : List E2) :
    Claim.Mle M (ringOf c f g) := by
  obtain ⟨r, hpt⟩ : ∃ r : Fin M → E2, c.pt = List.ofFn r :=
    ⟨fun i ↦ c.pt[i.val]'(by rw [hc]; exact i.2),
      List.ext_getElem (by simp [hc]) fun i _ _ ↦ by simp⟩
  have hw : ∀ y : Fin M → E2, (ringOf c f g).1 (List.ofFn y) =
      ∑ k ∈ range (ringCoefficients f g).length,
        (ringCoefficients f g).getD k 0 * eqP (frobPt r k) y := by
    intro y
    simp only [ringOf, ringClaim]
    rw [hpt, List.length_ofFn, List.take_of_length_le (by simp), ringWeight_ofFn,
      idxSum_eq_sum_range]
    simp only [eqEvalF, List.zipWith_nil_left, List.foldl_nil, one_mul]
  intro x
  rw [hw x]
  simp only [hw, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  simp only [mul_assoc, ← Finset.mul_sum, sum_eqP_mul_eqP]

/-- **The batched claim's weight is multiaffine** when the stacked claims' weights are. -/
theorem claimOf6_mle (sl : List SliceClaim) (st : List StackClaim6)
    (o : ((List E2 × List E2) × (List E2 × List E2)) × E2) (hlen : ∀ c ∈ sl, c.pt.length = M)
    (h2 : sl.length = 2) (hst : ∀ c ∈ st, Claim.Mle M c) : Claim.Mle M (claimOf6 sl st o) := by
  have h0 : sl.getD 0 ⟨[], 0⟩ ∈ sl := by
    rw [List.getD_eq_getElem _ _ (by omega)]; exact List.getElem_mem _
  have h1 : sl.getD 1 ⟨[], 0⟩ ∈ sl := by
    rw [List.getD_eq_getElem _ _ (by omega)]; exact List.getElem_mem _
  refine mle_batch M _ _ fun c hc ↦ ?_
  rcases mem_placeRing hc with rfl | rfl | hc'
  · exact ringOf_mle M _ (hlen _ h0) _ _
  · exact ringOf_mle M _ (hlen _ h1) _ _
  · exact hst c hc'

end Mle

/-- S's `Multiaffine` is RS's `Claim.Mle` (`bitsOf`). -/
theorem multiaffine_iff_mle (M : ℕ) (c : StackClaim6) : c.Multiaffine M ↔ Claim.Mle M c := by
  constructor
  · intro h y
    rw [h (List.ofFn y) (by simp), ← (bitsOf_bijective M).sum_comp]
    refine Finset.sum_congr rfl fun x _ ↦ ?_
    rw [boolPt_eq, eqPt_ofFn]
  · intro h pt hpt
    obtain ⟨y, rfl⟩ : ∃ y : Fin M → E2, pt = List.ofFn y :=
      ⟨fun i ↦ pt[i.val]'(by rw [hpt]; exact i.2),
        List.ext_getElem (by simp [hpt]) fun i _ _ ↦ by simp⟩
    rw [h y, ← (bitsOf_bijective M).sum_comp]
    refine Finset.sum_congr rfl fun x _ ↦ ?_
    rw [boolPt_eq, eqPt_ofFn]

/-! ## The group in the DSL -/

section Dsl

/-- The 33 answers as the challenge tuple. -/
def outOf33 (c : Fin 33 → E) : X6 × E2 :=
  (((fun i ↦ e2OfE (c ⟨i, by omega⟩), fun j ↦ e2OfE (c ⟨8 + j, by omega⟩)),
    (fun j ↦ e2OfE (c ⟨16 + j, by omega⟩), fun j ↦ e2OfE (c ⟨24 + j, by omega⟩))), e2OfE (c 32))

theorem ringOut6_ofFn (c : Fin 33 → E) : ringOut6 (List.ofFn c) = outL (outOf33 c) := by
  simp only [ringOut6, outL, outOf33, Prod.mk.injEq]
  refine ⟨⟨⟨?_, ?_⟩, ?_, ?_⟩, ?_⟩
  all_goals first
    | (apply List.ext_getElem (by simp); intro i h1 h2; simp)
    | simp

/-- **The product-set count of the group**: the accepted answer lists whose challenges lie in `B`
are at most `2^(64−g)·|K|^32·|B|` (RS's `card_powOK_outOf_le` at 33 answers). -/
theorem card_powOK_outOf33_le {g : ℕ} (hg : g ≤ 64) (B : X6 × E2 → Prop) [DecidablePred B] :
    (univ.filter fun c : Fin 33 → E ↦ powOK g (c 0) ∧ B (outOf33 c)).card ≤
      2 ^ (64 - g) * (2 ^ 64) ^ 32 * (univ.filter B).card := by
  classical
  let Ψ : (Fin 33 → E2) → X6 × E2 := fun y ↦
    (((fun i ↦ y ⟨i, by omega⟩, fun j ↦ y ⟨8 + j, by omega⟩),
      (fun j ↦ y ⟨16 + j, by omega⟩, fun j ↦ y ⟨24 + j, by omega⟩)), y 32)
  let Y := univ.filter fun y : Fin 33 → E2 ↦ B (Ψ y)
  let Ks := univ.filter fun k : Fin 33 → K ↦ kToNat (k 0) < 2 ^ (64 - g)
  have h1 : (univ.filter fun c : Fin 33 → E ↦ powOK g (c 0) ∧ B (outOf33 c)).card ≤
      (Y ×ˢ Ks).card := by
    refine Finset.card_le_card_of_injOn (fun c ↦ (fun i ↦ e2OfE (c i), fun i ↦ (c i).limb 2))
      (fun c hc ↦ ?_) (fun c _ c' _ he ↦ ?_)
    · simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hc
      simp only [Finset.coe_product, Set.mem_prod, Finset.coe_filter, Finset.mem_univ, true_and,
        Set.mem_ofPred_eq, Y, Ks]
      exact ⟨hc.2, (powOK_iff_lane2 hg _).mp hc.1⟩
    · funext i
      have e1 := congrFun (congrArg Prod.fst he) i
      have e2 := congrFun (congrArg Prod.snd he) i
      exact eSplit.injective (Prod.ext e1 e2)
  have hY : Y.card ≤ (univ.filter B).card := by
    refine Finset.card_le_card_of_injOn Ψ (fun y hy ↦ ?_) (fun y _ y' _ he ↦ ?_)
    · simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq, Y] at hy ⊢
      exact hy
    · have e1 := congrArg (fun p ↦ p.1.1.1) he
      have e2 := congrArg (fun p ↦ p.1.1.2) he
      have e3 := congrArg (fun p ↦ p.1.2.1) he
      have e4 := congrArg (fun p ↦ p.1.2.2) he
      have e5 := congrArg (fun p ↦ p.2) he
      simp only [Ψ] at e1 e2 e3 e4 e5
      funext t
      obtain ⟨k, hk⟩ := t
      rcases (show k < 8 ∨ (8 ≤ k ∧ k < 16) ∨ (16 ≤ k ∧ k < 24) ∨ (24 ≤ k ∧ k < 32) ∨ k = 32 by
        omega) with h | h | h | h | h
      · exact congrFun e1 ⟨k, h⟩
      · have := congrFun e2 ⟨k - 8, by omega⟩
        simp only at this
        rwa [show (⟨8 + (k - 8), by omega⟩ : Fin 33) = ⟨k, hk⟩ from Fin.ext (by simp; omega)]
          at this
      · have := congrFun e3 ⟨k - 16, by omega⟩
        simp only at this
        rwa [show (⟨16 + (k - 16), by omega⟩ : Fin 33) = ⟨k, hk⟩ from Fin.ext (by simp; omega)]
          at this
      · have := congrFun e4 ⟨k - 24, by omega⟩
        simp only at this
        rwa [show (⟨24 + (k - 24), by omega⟩ : Fin 33) = ⟨k, hk⟩ from Fin.ext (by simp; omega)]
          at this
      · subst h; exact e5
  have hK : Ks.card ≤ 2 ^ (64 - g) * (2 ^ 64) ^ 32 := by
    refine (Finset.card_le_card_of_injOn (fun k ↦ (k 0, fun i : Fin 32 ↦ k i.succ))
      (t := (univ.filter fun x : K ↦ kToNat x < 2 ^ (64 - g)) ×ˢ univ)
      (fun k hk ↦ ?_) (fun k _ k' _ he ↦ ?_)).trans ?_
    · simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq, Ks] at hk
      simp only [Finset.coe_product, Set.mem_prod, Finset.coe_filter, Finset.mem_univ, true_and,
        Set.mem_ofPred_eq, Finset.coe_univ, Set.mem_univ, and_true]
      exact hk
    · funext t
      refine Fin.cases ?_ (fun i ↦ ?_) t
      · exact congrArg Prod.fst he
      · exact congrFun (congrArg Prod.snd he) i
    · rw [Finset.card_product, card_kToNat_lt (by omega), Finset.card_univ, Fintype.card_fun,
        Fintype.card_fin]
      simp only [BF64.card_bf64, le_refl]
  rw [Finset.card_product] at h1
  calc _ ≤ Y.card * Ks.card := h1
    _ ≤ (univ.filter B).card * (2 ^ (64 - g) * (2 ^ 64) ^ 32) := Nat.mul_le_mul hY hK
    _ = _ := by ring

theorem two_inv_pow_mul_two_pow' (m n : ℕ) :
    (2 : ℝ≥0∞)⁻¹ ^ (m + n) * 2 ^ m = 2⁻¹ ^ n := by
  rw [pow_add, mul_comm ((2 : ℝ≥0∞)⁻¹ ^ m), mul_assoc, ← mul_pow,
    ENNReal.inv_mul_cancel two_ne_zero ENNReal.ofNat_ne_top, one_pow, mul_one]

/-- The group's escape in the certificate's units (33 answers). -/
theorem escape_arith33 (L n g : ℕ) (hg : g ≤ 64) :
    (Fintype.card E : ℝ≥0∞)⁻¹ ^ 33 *
        ((L : ℝ≥0∞) * ((2 ^ (64 - g) * (2 ^ 64) ^ 32 * (n * (2 ^ 128) ^ 32) : ℕ) : ℝ≥0∞)) =
      grpEpsE L n g := by
  rw [card_E, grpEpsE]
  simp only [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
  have key : ((2 : ℝ≥0∞) ^ 192)⁻¹ ^ 33 * (2 ^ (64 - g) * (2 ^ 64) ^ 32 * (2 ^ 128) ^ 32) =
      2⁻¹ ^ g * (2 ^ 128)⁻¹ := by
    rw [ENNReal.inv_pow, ENNReal.inv_pow, ← pow_mul, ← pow_mul, ← pow_mul, ← pow_add, ← pow_add,
      show 192 * 33 = (64 - g + 64 * 32 + 128 * 32) + (g + 128) by omega,
      two_inv_pow_mul_two_pow', pow_add]
  calc _ = (L : ℝ≥0∞) * (n * (((2 : ℝ≥0∞) ^ 192)⁻¹ ^ 33 *
          (2 ^ (64 - g) * (2 ^ 64) ^ 32 * (2 ^ 128) ^ 32))) := by ring
    _ = _ := by rw [key]; ring

theorem εI_coe : ((7 * (2 : NNReal)⁻¹ ^ 131 : NNReal) : ℝ≥0∞) = εI := by
  simp [εI, ENNReal.coe_mul, ENNReal.coe_pow, ENNReal.coe_inv, ENNReal.inv_pow]

theorem εI_lt_one : εI < 1 := by
  rw [← εI_coe, ← ENNReal.coe_one, ENNReal.coe_lt_coe, ← NNReal.coe_lt_coe]
  push_cast; norm_num

variable {β : Type}

/-- `escRet_doomed_stable` with a history-free conjunct `P` on the returned value. -/
theorem escRet_doomed_stableP {α : Type} {C : List Ev → Set β} (hst : Stable C) (P : α → Prop)
    (A' : α → β → Prop) (h₀ : List Ev) :
    ∀ (p : VerifierProgram α) (l : List Ev), commits l = [] →
      VerifierProgram.escRet (fun x h ↦ P x ∧ Doomed C (A' x) h) h₀ l p =
        VerifierProgram.escRet (fun x _ ↦ P x ∧ Doomed C (A' x) h₀) h₀ l p
  | .ret x, l, hl => by
    simp only [VerifierProgram.escRet, VerifierProgram.retExp]
    have hd := Doomed.append (A := A' x) hst (h₀ := h₀) hl
    by_cases h1 : P x ∧ Doomed C (A' x) h₀
    · rw [ite_eq_left h1, ite_eq_left ⟨h1.1, hd.mpr h1.2⟩]
    · rw [ite_eq_right h1, ite_eq_right fun h ↦ h1 ⟨h.1, hd.mp h.2⟩]
  | .fail, _, _ => by simp [VerifierProgram.escRet, VerifierProgram.retExp]
  | .read _, _, _ => by simp [VerifierProgram.escRet, VerifierProgram.retExp]
  | .grind _ _, _, _ => by simp [VerifierProgram.escRet, VerifierProgram.retExp]
  | .commit _ _ _, _, _ => by simp [VerifierProgram.escRet, VerifierProgram.retExp]
  | .sample k, l, hl => by
    simp only [VerifierProgram.escRet, VerifierProgram.retExp]
    congr 1
    refine Finset.sum_congr rfl fun c _ ↦ ?_
    exact escRet_doomed_stableP hst P A' h₀ (k c) _ (by rw [commits_append_sample, hl])
  | .query i ps k, l, hl => by
    simp only [VerifierProgram.escRet, VerifierProgram.retExp]
    split
    · exact escRet_doomed_stableP hst P A' h₀ _ _ (by rw [commits_append_query, hl])
    · rfl

/-- **§6.5 in season 1's doom shape** (RS's `ringSpec6` for two maps): from doom of "the slice and
stack claims hold, and `R`" to doom of "the batched claim holds, and `R`", lead `0`, the group's
escape `L₀·2^-g·(|st| + 3)/2^128` charged at the nonce's boundary, at most `εI` by `ringOK`. The
returned claim is multiaffine when the stacked claims are (`claimOf6_mle`, W1 F-3): the conjunct
is carried through the escape computation, where the returned value is explicit. -/
theorem ringSpec6v24 [Finite β] {C : List Ev → Set β} {L₀ : ℕ} (hst : Stable C)
    (hcard : ∀ h, (C h).ncard ≤ L₀) (sh : Shape) (sl : List SliceClaim) (st : List StackClaim6)
    (hsl : sl.length ≤ 2) (hJ : st.length ≤ sh.J₀) (hL : L₀ ≤ sh.L₀)
    (hma : ∀ c ∈ st, Claim.Mle sh.M c) (stk : β → Stack) (R : β → Prop) :
    Nonempty (Spec (ringPhase6 sh sl st)
      (Doomed C fun q ↦ ((∀ c ∈ sl, c.Holds sh.M (stk q)) ∧ ∀ c ∈ st, c.Holds sh.M (stk q)) ∧
        R q)
      (fun out h ↦ Claim.Mle sh.M out ∧ Doomed C (fun q ↦ out.Holds sh.M (stk q) ∧ R q) h)
      εI 0 0) := by
  classical
  let A : β → Prop := fun q ↦
    ((∀ c ∈ sl, c.Holds sh.M (stk q)) ∧ ∀ c ∈ st, c.Holds sh.M (stk q)) ∧ R q
  let A' : StackClaim6 → β → Prop := fun out q ↦ out.Holds sh.M (stk q) ∧ R q
  let e : ℝ≥0∞ := grpEpsE L₀ (st.length + 3) sh.gRing
  refine ⟨(Spec.require (c := ringOK sh sl) (Post := fun _ h ↦ Doomed C A h ∧ ringOK sh sl)
    fun _ hp hc ↦ ⟨hp, hc⟩).bind' fun _ ↦ ?_⟩
  by_cases hok : ringOK sh sl
  swap
  · exact Spec.dead.mono (fun _ hp ↦ hok hp.2) (fun _ _ h ↦ h) le_rfl le_rfl le_rfl
  obtain ⟨hadm, hg, hlen, hsl2⟩ := hok
  have hmle : ∀ o, Claim.Mle sh.M (claimOf6 sl st o) := fun o ↦
    claimOf6_mle sh.M sl st o hlen hsl2 hma
  have heI : e ≤ εI := by
    have h1 : e ≤ errG sh.gRing ((sh.J₀ + 3) * sh.L₀) := by
      show grpEpsE L₀ (st.length + 3) sh.gRing ≤ _
      rw [← errG_grpEpsE]
      unfold errG
      have hc : ((L₀ : ℕ) : ℝ≥0∞) * ((st.length + 3 : ℕ) : ℝ≥0∞) ≤
          (((sh.J₀ + 3) * sh.L₀ : ℕ) : ℝ≥0∞) := by
        rw [← Nat.cast_mul]
        exact_mod_cast (show L₀ * (st.length + 3) ≤ (sh.J₀ + 3) * sh.L₀ by
          rw [mul_comm]; exact Nat.mul_le_mul (by omega) hL)
      calc (L₀ : ℝ≥0∞) * ((2 : ℝ≥0∞)⁻¹ ^ sh.gRing * (((st.length + 3 : ℕ) : ℝ≥0∞) *
            ((2 : ℝ≥0∞) ^ 128)⁻¹))
          = (2 : ℝ≥0∞)⁻¹ ^ sh.gRing * (((L₀ : ℕ) : ℝ≥0∞) * ((st.length + 3 : ℕ) : ℝ≥0∞) *
            ((2 : ℝ≥0∞) ^ 128)⁻¹) := by ring
        _ ≤ _ := by gcongr
    exact h1.trans ((errG_le_εI hadm).trans εI_coe.le)
  have he1 : e < 1 := lt_of_le_of_lt heI εI_lt_one
  have he : e + 0 ≤ εI := by rw [add_zero]; exact heI
  have hreq : ∀ P : Prop, ∀ [Decidable P], NoMoves (VerifierProgram.require P) := by
    intro P _
    unfold VerifierProgram.require
    split
    · exact NoMoves.ret ()
    · exact NoMoves.fail
  have hnm : NoMoves (ringBody sh.gRing sl st) :=
    (noMoves_sampleN 33).bind fun l ↦ (hreq _).bind fun _ ↦ NoMoves.ret _
  have hesc : ∀ h₀, Doomed C A h₀ → VerifierProgram.escRet
      (fun o h ↦ Claim.Mle sh.M o ∧ Doomed C (A' o) h) h₀ [] (ringBody sh.gRing sl st) ≤ e := by
    intro h₀ hpre
    have hfin : (C h₀).Finite := Set.toFinite _
    rw [escRet_doomed_stableP hst (Claim.Mle sh.M) A' h₀ _ [] rfl]
    unfold VerifierProgram.escRet
    rw [show ringBody sh.gRing sl st = (VerifierProgram.sampleChallenges 33).bind
        (fun cs ↦ (VerifierProgram.require (powOK sh.gRing (cs.headD 0))).bind fun _ ↦
          VerifierProgram.ret (claimOf6 sl st (ringOut6 cs))) from rfl, retExp_bind]
    let G : List E → ℝ≥0∞ := fun l ↦ if powOK sh.gRing (l.headD 0) then
      (if Doomed C (A' (claimOf6 sl st (ringOut6 l))) h₀ then 0 else 1) else 0
    have hin : (fun (l : List E) (h : List Ev) ↦ VerifierProgram.retExp (fun o (_ : List Ev) ↦
        @ite _ (Claim.Mle sh.M o ∧ Doomed C (A' o) h₀) (Classical.propDecidable _) (0 : ℝ≥0∞) 1)
          h []
          ((VerifierProgram.require (powOK sh.gRing (l.headD 0))).bind fun _ ↦
            VerifierProgram.ret (claimOf6 sl st (ringOut6 l)))) = fun l _ ↦ G l := by
      funext l h
      simp only [G, VerifierProgram.require]
      split_ifs <;> simp_all [VerifierProgram.bind, VerifierProgram.retExp]
    beta_reduce
    rw [hin, retExp_sampleN]
    have hcover : ∀ f : Fin 33 → E, G (List.ofFn f) ≤ ∑ q ∈ hfin.toFinset,
        (if powOK sh.gRing (f 0) ∧ A' (claimOf6 sl st (outL (outOf33 f))) q then 1 else 0 :
          ℝ≥0∞) := by
      intro f
      have hhead : (List.ofFn f).headD 0 = f 0 := by simp [List.ofFn_succ]
      simp only [G, hhead, ringOut6_ofFn]
      split_ifs with hp hd
      · exact zero_le
      · simp only [Doomed, not_forall, not_not, exists_prop] at hd
        obtain ⟨q, hq, hA⟩ := hd
        refine le_trans ?_ (Finset.single_le_sum (f := fun q ↦ (if powOK sh.gRing (f 0) ∧
          A' (claimOf6 sl st (outL (outOf33 f))) q then 1 else 0 : ℝ≥0∞)) (fun _ _ ↦ zero_le)
            (hfin.mem_toFinset.2 hq))
        rw [if_pos ⟨hp, hA⟩]
      · exact zero_le
    have hone : ∀ q ∈ C h₀, (univ.filter fun f : Fin 33 → E ↦ powOK sh.gRing (f 0) ∧
        A' (claimOf6 sl st (outL (outOf33 f))) q).card ≤
          2 ^ (64 - sh.gRing) * (2 ^ 64) ^ 32 * ((st.length + 3) * (2 ^ 128) ^ 32) := by
      intro q hq
      refine (card_powOK_outOf33_le hg (fun y ↦ A' (claimOf6 sl st (outL y)) q)).trans
        (Nat.mul_le_mul_left _ ?_)
      by_cases hR : R q
      · refine (Finset.card_le_card fun y hy ↦ ?_).trans
          (card_bad6_le sh.M sl st hsl hlen (stk q) fun hsc ↦ hpre q hq ⟨hsc, hR⟩)
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, A'] at hy ⊢
        exact hy.1
      · have : (univ.filter fun y : X6 × E2 ↦ A' (claimOf6 sl st (outL y)) q) = ∅ := by
          ext y; simp [A', hR]
        rw [this, Finset.card_empty]
        exact Nat.zero_le _
    calc (Fintype.card E : ℝ≥0∞)⁻¹ ^ 33 * ∑ f : Fin 33 → E, G (List.ofFn f)
        ≤ (Fintype.card E : ℝ≥0∞)⁻¹ ^ 33 * ∑ f : Fin 33 → E, ∑ q ∈ hfin.toFinset,
            (if powOK sh.gRing (f 0) ∧ A' (claimOf6 sl st (outL (outOf33 f))) q
              then 1 else 0 : ℝ≥0∞) := by
          gcongr with f; exact hcover f
      _ = (Fintype.card E : ℝ≥0∞)⁻¹ ^ 33 * ∑ q ∈ hfin.toFinset,
            ((univ.filter fun f : Fin 33 → E ↦ powOK sh.gRing (f 0) ∧
              A' (claimOf6 sl st (outL (outOf33 f))) q).card : ℝ≥0∞) := by
          rw [Finset.sum_comm]
          congr 1
          refine Finset.sum_congr rfl fun q _ ↦ ?_
          rw [Finset.sum_boole]
      _ ≤ (Fintype.card E : ℝ≥0∞)⁻¹ ^ 33 * ∑ _q ∈ hfin.toFinset,
            ((2 ^ (64 - sh.gRing) * (2 ^ 64) ^ 32 * ((st.length + 3) * (2 ^ 128) ^ 32) : ℕ) :
              ℝ≥0∞) := by
          gcongr with q hq
          exact_mod_cast hone q (hfin.mem_toFinset.1 hq)
      _ ≤ (Fintype.card E : ℝ≥0∞)⁻¹ ^ 33 * ((L₀ : ℝ≥0∞) *
            ((2 ^ (64 - sh.gRing) * (2 ^ 64) ^ 32 * ((st.length + 3) * (2 ^ 128) ^ 32) : ℕ) :
              ℝ≥0∞)) := by
          rw [Finset.sum_const, nsmul_eq_mul]
          gcongr
          rw [← Set.ncard_eq_toFinset_card _ hfin]
          exact_mod_cast hcard h₀
      _ = e := escape_arith33 L₀ (st.length + 3) sh.gRing hg
  exact ((doomSep6 (εmax := εI) (T := 0) hst hcard A).mono (fun _ hp ↦ hp.1) (fun _ _ h ↦ h)
    le_rfl le_rfl le_rfl).bind' fun _ ↦
    (doomRead hst A he).bind' fun _ ↦ Spec.ofNoMove hnm.noMove he1 hesc

end Dsl

/-! ## S's list form -/

open Classical in
/-- **Season 1's doom shape at `L₀` candidates gives S's list form** (K1's `doomSpec_of` with a list
bound in place of one candidate). -/
theorem listSpec_of {α : Type} {p : VerifierProgram α} {L₀ : ℕ} {Pre' : Stack → Prop}
    {Post' : α → Stack → Prop} {Q : α → Prop}
    (H : ∀ {β : Type} [Finite β] (C : List Ev → Set β), Stable C → (∀ hh, (C hh).ncard ≤ L₀) →
      ∀ (stk : β → Stack),
        Nonempty (Spec p (Doomed C (fun q ↦ Pre' (stk q) ∧ True))
          (fun out hist ↦ Q out ∧ Doomed C (fun q ↦ Post' out (stk q) ∧ True) hist) εI 0 0))
    (C : List Ev → Set Stack) (G : List Ev → Prop) (hG : ∀ h₀ l, G h₀ → C (h₀ ++ l) = C h₀)
    (hfin : ∀ h, G h → (C h).Finite ∧ (C h).ncard ≤ L₀) :
    Nonempty (Spec p (fun h ↦ G h ∧ Doomed C Pre' h) (fun out h ↦ Q out ∧ Doomed C (Post' out) h)
      εI 0 0) := by
  let C' : List Ev → Set Stack := fun h₀ ↦ {q | G h₀ ∧ q ∈ C h₀}
  have hfin' : ∀ h₀, (C' h₀).Finite := fun h₀ ↦ by
    by_cases hg : G h₀
    · exact (hfin h₀ hg).1.subset fun q hq ↦ hq.2
    · exact Set.finite_empty.subset fun q hq ↦ hg hq.1
  have hcard : ∀ h₀ (hh : List Ev), (Set.univ : Set ↥(C' h₀)).ncard ≤ L₀ := fun h₀ _ ↦ by
    rw [Set.ncard_univ, Nat.card_coe_set_eq]
    by_cases hg : G h₀
    · exact (Set.ncard_le_ncard (fun q hq ↦ hq.2) (hfin h₀ hg).1).trans (hfin h₀ hg).2
    · rw [show C' h₀ = ∅ from Set.eq_empty_of_forall_notMem fun q hq ↦ hg hq.1]; simp
  let S : ∀ h₀ : List Ev, Spec p
      (Doomed (fun _ ↦ (Set.univ : Set ↥(C' h₀))) (fun q ↦ Pre' q.1 ∧ True))
      (fun out hist ↦ Q out ∧
        Doomed (fun _ ↦ (Set.univ : Set ↥(C' h₀))) (fun q ↦ Post' out q.1 ∧ True) hist) εI 0 0 :=
    fun h₀ ↦ (@H ↥(C' h₀) (hfin' h₀).to_subtype (fun _ ↦ Set.univ) (fun _ _ _ ↦ rfl) (hcard h₀)
      Subtype.val).some
  refine ⟨{
    D := fun h₀ l ↦ G h₀ ∧ (S h₀).D h₀ l
    V := fun h₀ l ↦ if G h₀ then (S h₀).V h₀ l else 1
    le_one := ?_, start_D := ?_, start_V := ?_, read := ?_, grind := ?_, commit := ?_,
    sample := ?_, query := ?_, moveEnd := ?_, retEnd := ?_, retDoom := ?_, post := ?_,
    bound := ?_ }⟩
  · intro h₀ l
    split_ifs
    · exact (S h₀).le_one h₀ l
    · exact le_rfl
  · intro h₀ hP
    exact ⟨hP.1, (S h₀).start_D h₀ fun q _ hq ↦ hP.2 q.1 q.2.2 hq.1⟩
  · intro h₀ hP
    simp only [if_pos hP.1]
    exact (S h₀).start_V h₀ fun q _ hq ↦ hP.2 q.1 q.2.2 hq.1
  · intro h₀ l k x hl ha hD
    exact ⟨hD.1, (S h₀).read x hl ha hD.2⟩
  · intro h₀ l b k hl ha hD
    exact ⟨hD.1, (S h₀).grind hl ha hD.2⟩
  · intro h₀ l ht w k word hl ha hw hD
    exact ⟨hD.1, (S h₀).commit word hl ha hw hD.2⟩
  · intro h₀ l k hl ha
    by_cases hg : G h₀
    · simp only [if_pos hg]
      exact (S h₀).sample hl ha
    · simp only [if_neg hg]
      rw [Finset.sum_const, Finset.card_univ, nsmul_one]
      exact le_of_eq (ENNReal.inv_mul_cancel (by exact_mod_cast Fintype.card_ne_zero)
        (ENNReal.natCast_ne_top _))
  · intro h₀ l i ps k rows hl ha hans
    by_cases hg : G h₀
    · simp only [if_pos hg]
      exact (S h₀).query hl ha hans
    · simp only [if_neg hg, le_refl]
  · intro h₀ l q hl ha hm hD
    by_cases hg : G h₀
    · simp only [if_pos hg]
      exact (S h₀).moveEnd hl ha hm fun h ↦ hD ⟨hg, h⟩
    · simp only [if_neg hg, le_refl]
  · intro h₀ l a hl ha hD
    by_cases hg : G h₀
    · simp only [if_pos hg]
      exact (S h₀).retEnd hl ha fun h ↦ hD ⟨hg, h⟩
    · simp only [if_neg hg, le_refl]
  · intro h₀ l a hl ha hD
    simp only [if_pos hD.1]
    exact (S h₀).retDoom hl ha hD.2
  · intro h₀ l a hl ha hD
    refine ⟨((S h₀).post hl ha hD.2).1, fun q hq hh ↦ ?_⟩
    rw [hG h₀ l hD.1] at hq
    exact ((S h₀).post hl ha hD.2).2 ⟨q, hD.1, hq⟩ (Set.mem_univ _) ⟨hh, trivial⟩
  · intro h₀ l hl hne hm hD
    simp only [if_pos hD.1]
    exact (S h₀).bound hl hne hm hD.2

/-- **T4' for `prog6`**: §6.5 at v2.4 meets WP S's `Stmt.ringSpec6` (list form). -/
theorem ringSpec6_asm : Stmt.ringSpec6 ringPhase6 := by
  intro sh sl st hsl hJ hma C G hG hfin
  have hma' : ∀ c ∈ st, Claim.Mle sh.M c := fun c hc ↦ (multiaffine_iff_mle sh.M c).mp (hma c hc)
  obtain ⟨S⟩ := listSpec_of (L₀ := sh.L₀) (Q := Claim.Mle sh.M)
    (Pre' := fun q ↦ (∀ c ∈ sl, c.Holds sh.M q) ∧ ∀ c ∈ st, c.Holds sh.M q)
    (Post' := fun (out : StackClaim6) q ↦ out.Holds sh.M q) (fun {β} _ C' hst hcard stk ↦
    ringSpec6v24 hst hcard sh sl st hsl (by omega) le_rfl hma' stk (fun _ ↦ True)) C G hG hfin
  exact ⟨S.mono (fun _ h ↦ h) (fun out _ h ↦ ⟨(multiaffine_iff_mle sh.M out).mpr h.1, h.2⟩)
    le_rfl le_rfl le_rfl⟩

end Lvm6
