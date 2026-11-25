-- New for lvm6 (WP ASM): the composed verifier program `prog6` (FORMAT6 v2.4 order) and its schedule.
import Lvm6Stmt
import Lvm6FSGroup
import Lvm6KStmt
import Lvm6KProgS6
import Lvm6SpProg

/-!
# The composed verifier program `prog6`

BLUEPRINT v3 §5 (T5, T7); FORMAT6 v2.4 §6. The certified scheme is `schemeOf prog6`
(`Lvm6Stmt`: V1's `V.schemeP` with the interactive program `prog6`).

* **`Phases`**: the phase programs, typed as WP S's phase statements (`Lvm6StmtPhase`):
  commitment (§6.1, claim 0), tree batch (§6.2), sponge batch (§6.3: caller, core, link), typed
  phases and mini-bus (§6.4), ring switching and stack batch (§6.5), opening (§6.6).
* **`prog6 Φ sh vk x`**: the phases in FORMAT6 order on the header view `hdrView sh x`; the stacked
  claims passed to §6.5 are claim 0, the tree's, the sponge's and the typed claims, in that order
  (the ring phase places its two ring claims, FORMAT6 §6.5); before §6.5, **`batchJ`** rejects more
  than `J₀` stacked claims (RV3 M2, WP S's `Stmt.ringSpec6` hypothesis).
* **`Follows p os`**: every path of `p` performs the transcript operations `os` in order (a read, a
  draw, a cap of `2^ht` rows of `w` words, an opening of commitment `i`), up to a rejection; no
  `grind` node. `opsOf L items` is V1's schedule walk read as operations (`Prims.walk`).
* **`prog6_sched`**: if every phase follows its part of `sched6 sh`, then `prog6 Φ sh vk x` follows
  `sched6 sh`, for every shape (so `P18` too). By construction: `sched6` is the concatenation of
  the parts and `Follows` composes through `bind` (`Follows.bind`).
* **`prog6_noGrind`**: a following program has no `grind` node (`kcert6`'s `hng`).
* **`commit6`**: §6.1 as a program (`CAP(0)`, `B`, `G(g_ood[0]) D(M−1)`, `E(1)`; claim 0 is
  `q̃(z₀) = y₀`), with `commit6_follows`. The tree phase is WP K2's `treeProgS6` (`treeProgS29` with
  `Shape.treePart`'s four constants checked; `Lvm6KS6`: `treeSpecS6`, `treeProgS6_follows`); the
  sponge phase is WP SPH's `SP.spongePhase6` (`Lvm6SpPhase`: `spongeSpecS6`, `spongePhase6_follows`,
  `spongePhase6_noCommit`).
-/

set_option autoImplicit false

namespace Lvm6

open RecursionFast LeanVM.Parameters LeanVM.Protocol.Compile LeanVM.Protocol.Verifier Lvm.E2V
open LeanVM.Protocol.EndToEnd.Front (Doomed)

/-! ## Transcript operations and `Follows` -/

/-- A transcript operation of the compiled verifier. -/
inductive Op
  /-- One read (its width is the scheme's, by position). -/
  | rd
  /-- One draw. -/
  | smp
  /-- A cap of `2^ht` rows of `w` words. -/
  | cap (ht w : ℕ)
  /-- The openings of commitment `i`. -/
  | opn (i : ℕ)
  deriving DecidableEq

/-- V1's schedule primitives read as operation lists. -/
def PO : V.Prims (List Op) where
  skip := []
  seq := (· ++ ·)
  rd _ := [.rd]
  draw _ _ := [.smp]
  cap ht w := [.cap ht w]
  reset := []
  opn i := [.opn i]

/-- **The operations of a schedule** (V1's walk, `PO`). -/
def opsOf (L : List V.Lev) (s : List V.Item) : List Op := PO.walk L s

theorem opsOf_nil (L : List V.Lev) : opsOf L [] = [] := rfl

theorem opsOf_append (L : List V.Lev) (s t : List V.Item) :
    opsOf L (s ++ t) = opsOf L s ++ opsOf L t := by
  induction s with
  | nil => rfl
  | cons it s ih =>
    show PO.item L it ++ opsOf L (s ++ t) = (PO.item L it ++ opsOf L s) ++ opsOf L t
    rw [ih, List.append_assoc]

theorem po_rep (o : Op) : ∀ m, PO.rep [o] m = List.replicate m o
  | 0 => rfl
  | m + 1 => by
    show [o] ++ PO.rep [o] m = o :: List.replicate m o
    rw [po_rep o m]; rfl

theorem po_rep_draw (c : ℕ → Bool) (u : List ℕ → ℕ → List ℕ) (m : ℕ) :
    PO.rep (PO.draw c u) m = List.replicate m .smp := po_rep .smp m

theorem po_rep_rd (w m : ℕ) : PO.rep (PO.rd w) m = List.replicate m .rd := po_rep .rd m

/-- **`p` follows `os`**: every path performs the operations `os` in order (or rejects). -/
def Follows {α : Type} : VerifierProgram α → List Op → Prop
  | .ret _, os => os = []
  | .fail, _ => True
  | .grind _ _, _ => False
  | .read k, os => os.head? = some .rd ∧ ∀ x, Follows (k x) os.tail
  | .sample k, os => os.head? = some .smp ∧ ∀ c, Follows (k c) os.tail
  | .commit ht w k, os => os.head? = some (.cap ht w) ∧ Follows k os.tail
  | .query i _ k, os => os.head? = some (.opn i) ∧ ∀ r, Follows (k r) os.tail

section Follows

variable {α β : Type}

theorem Follows.bind {p : VerifierProgram α} {f : α → VerifierProgram β} {o₁ o₂ : List Op}
    (hp : Follows p o₁) (hf : ∀ a, Follows (f a) o₂) : Follows (p.bind f) (o₁ ++ o₂) := by
  induction p generalizing o₁ with
  | ret a =>
    have h : o₁ = [] := hp
    subst h; exact hf a
  | fail => trivial
  | grind _ _ _ => exact hp.elim
  | read k ih =>
    obtain ⟨h1, h2⟩ := hp
    cases o₁ with
    | nil => simp at h1
    | cons o os => exact ⟨by simpa using h1, fun x ↦ ih x (h2 x)⟩
  | sample k ih =>
    obtain ⟨h1, h2⟩ := hp
    cases o₁ with
    | nil => simp at h1
    | cons o os => exact ⟨by simpa using h1, fun c ↦ ih c (h2 c)⟩
  | commit ht w k ih =>
    obtain ⟨h1, h2⟩ := hp
    cases o₁ with
    | nil => simp at h1
    | cons o os => exact ⟨by simpa using h1, ih h2⟩
  | query i ps k ih =>
    obtain ⟨h1, h2⟩ := hp
    cases o₁ with
    | nil => simp at h1
    | cons o os => exact ⟨by simpa using h1, fun r ↦ ih r (h2 r)⟩

theorem Follows.bind' {p : VerifierProgram α} {f : α → VerifierProgram β} {o₁ o₂ : List Op}
    (hp : Follows p o₁) (hf : ∀ a, Follows (f a) o₂) : Follows (p >>= f) (o₁ ++ o₂) :=
  Follows.bind hp hf

/-- A following program asks no proof of work in the language. -/
theorem Follows.noGrind : ∀ {p : VerifierProgram α} {os : List Op}, Follows p os → p.NoGrind
  | .ret _, _, _ => trivial
  | .fail, _, _ => trivial
  | .grind _ _, _, h => h.elim
  | .read _, _, h => fun x ↦ (h.2 x).noGrind
  | .sample _, _, h => fun c ↦ (h.2 c).noGrind
  | .commit _ _ _, _, h => h.2.noGrind
  | .query _ _ _, _, h => fun r ↦ (h.2 r).noGrind

theorem follows_require (c : Prop) [Decidable c] : Follows (VerifierProgram.require c) [] := by
  unfold VerifierProgram.require; split <;> trivial

theorem follows_drawN {f : List E → VerifierProgram α} {o : List Op}
    (hf : ∀ cs, Follows (f cs) o) : ∀ n, Follows (drawN n f) (List.replicate n .smp ++ o)
  | 0 => hf []
  | n + 1 => ⟨rfl, fun c ↦ follows_drawN (f := fun cs ↦ f (c :: cs)) (fun cs ↦ hf _) n⟩

/-- F1's group `G(g) D(k)`: a read, then `k + 1` draws. -/
theorem follows_grp6 (g k : ℕ) :
    Follows (grp6 g k) (.rd :: List.replicate (k + 1) .smp) := by
  refine ⟨rfl, fun _ ↦ ⟨rfl, fun c ↦ ?_⟩⟩
  show Follows (if powOK g c then _ else _) _
  split
  · simpa using follows_drawN (f := fun cs ↦ VerifierProgram.ret (e2OfE c :: cs.map e2OfE))
      (o := []) (fun _ ↦ rfl) k
  · trivial

end Follows

/-! ## The phases and the composed program -/

/-- **The phase programs**, typed as WP S's phase statements. -/
structure Phases where
  /-- §6.1: the stack's cap, a bind, the OOD point, the value; claim 0. -/
  commit : Shape → VerifierProgram StackClaim6
  /-- §6.2: the tree batch (WP K2's `treeProgS6`). -/
  tree : Shape → Hdr → VerifierProgram TreeOut
  /-- §6.3: the sponge caller, core and link; the sponge block's slices and claims 16–45. -/
  sponge : Shape → Hdr → VerifierProgram TreeOut
  /-- §6.4: the typed phases and the mini-bus; claims 46–52. -/
  typed : Shape → Hdr → VerifierProgram (List StackClaim6)
  /-- §6.5: ring switching of the slice sets and the stack batch (`B`, `G(17) D(32)`). -/
  ring : Shape → List SliceClaim → List StackClaim6 → VerifierProgram StackClaim6
  /-- §6.6: the opening of the batched claim. -/
  whir : Shape → StackClaim6 → VerifierProgram Bool

variable (Φ : Phases)

/-- **§6.5 with the `J₀` bound**: at most `J₀` stacked claims (slice sets and stack claims), then
the ring phase. -/
def batchJ (sh : Shape) (sl : List SliceClaim) (st : List StackClaim6) :
    VerifierProgram StackClaim6 :=
  VerifierProgram.require (sl.length + st.length ≤ sh.J₀) >>= fun _ ↦ Φ.ring sh sl st

/-- The stacked claims of §6.5 (FORMAT6 order, ring claims aside): claim 0, the tree's, the
sponge's, the typed ones. -/
def stackedOf (c0 : StackClaim6) (t s : TreeOut) (ty : List StackClaim6) : List StackClaim6 :=
  c0 :: (t.claims ++ (s.claims ++ ty))

/-- The program after the commitment (§6.2–§6.6) on a header view. -/
def rest6 (sh : Shape) (x : Hdr) (c0 : StackClaim6) : VerifierProgram Bool :=
  Φ.tree sh x >>= fun t ↦ Φ.sponge sh x >>= fun s ↦ Φ.typed sh x >>= fun ty ↦
    batchJ Φ sh [t.slices, s.slices] (stackedOf c0 t s ty) >>= fun cl ↦ Φ.whir sh cl

/-- **The composed verifier program** of header bytes `x` (FORMAT6 v2.4 §6 order). -/
def prog6 (sh : Shape) (_vk : Digest) (x : List UInt8) : VerifierProgram Bool :=
  Φ.commit sh >>= fun c0 ↦ rest6 Φ sh (hdrView sh x) c0

/-! ## The schedule -/

/-- **Each phase follows its part of `sched6 sh`.** -/
structure PhasesFollow (sh : Shape) : Prop where
  commit : Follows (Φ.commit sh) (opsOf sh.levs sh.commitPart)
  tree : ∀ x, Follows (Φ.tree sh x) (opsOf sh.levs sh.treePart)
  sponge : ∀ x, Follows (Φ.sponge sh x) (opsOf sh.levs sh.spongePart)
  typed : ∀ x, Follows (Φ.typed sh x) (opsOf sh.levs (sh.subT.typed ++ sh.subT.bus))
  ring : ∀ sl st, Follows (Φ.ring sh sl st) (opsOf sh.levs sh.ringPart)
  whir : ∀ cl, Follows (Φ.whir sh cl) (opsOf sh.levs sh.openPart)

theorem sched6_split (sh : Shape) : opsOf sh.levs (sched6 sh) =
    opsOf sh.levs sh.commitPart ++ (opsOf sh.levs sh.treePart ++ (opsOf sh.levs sh.spongePart ++
      (opsOf sh.levs (sh.subT.typed ++ sh.subT.bus) ++ (opsOf sh.levs sh.ringPart ++
        opsOf sh.levs sh.openPart)))) := by
  simp only [sched6, opsOf_append, List.append_assoc]

/-- **`prog6_sched`**: the composed program follows `sched6 sh` (FORMAT6 §6), by construction. -/
theorem prog6_sched {sh : Shape} (h : PhasesFollow Φ sh) (vk : Digest) (x : List UInt8) :
    Follows (prog6 Φ sh vk x) (opsOf sh.levs (sched6 sh)) := by
  rw [sched6_split]
  refine Follows.bind' h.commit fun c0 ↦ Follows.bind' (h.tree _) fun t ↦
    Follows.bind' (h.sponge _) fun s ↦ Follows.bind' (h.typed _) fun ty ↦
      Follows.bind' (Follows.bind' (o₁ := []) (o₂ := opsOf sh.levs sh.ringPart)
        (follows_require _) fun _ ↦ h.ring _ _) fun cl ↦ h.whir cl

/-- **`prog6_noGrind`** (`kcert6`'s `hng`). -/
theorem prog6_noGrind {sh : Shape} (h : PhasesFollow Φ sh) (vk : Digest) (x : List UInt8) :
    (prog6 Φ sh vk x).NoGrind :=
  (prog6_sched Φ h vk x).noGrind

/-! ## §6.1 and §6.2 as programs -/

/-- **§6.1**: `CAP(0)` (level 0: `2^ht` rows of `rowW 0` words), `B`, `G(g_ood[0]) D(M−1)` →
`z₀ ∈ E^M`, `E(1)` → `y₀`; claim 0 is `q̃(z₀) = y₀`. -/
def commit6 (sh : Shape) : VerifierProgram StackClaim6 :=
  VerifierProgram.readCommitment (sh.levs.getD 0 default).ht (sh.levs.getD 0 default).wd >>=
    fun _ ↦ e2Sep >>= fun _ ↦ grp6 (sh.lvl 0).gOod (sh.M - 1) >>= fun z ↦
      e2Read >>= fun y ↦ pure (fun pt ↦ eqPt z pt, y)

theorem commit6_follows (sh : Shape) : Follows (commit6 sh) (opsOf sh.levs sh.commitPart) := by
  have hops : opsOf sh.levs sh.commitPart = [.cap (sh.levs.getD 0 default).ht
      (sh.levs.getD 0 default).wd] ++ ([.smp] ++ ((.rd :: List.replicate (sh.M - 1 + 1) .smp) ++
        ([.rd] ++ []))) := by
    simp only [opsOf, Shape.commitPart, V.Prims.walk, V.Prims.item, po_rep_draw, po_rep_rd]
    simp [PO, List.replicate_succ]
  rw [hops]
  exact Follows.bind' ⟨rfl, rfl⟩ fun _ ↦ Follows.bind' ⟨rfl, fun _ ↦ rfl⟩ fun _ ↦
    Follows.bind' (follows_grp6 _ _) fun _ ↦ Follows.bind' ⟨rfl, fun _ ↦ rfl⟩ fun _ ↦ rfl

/-- **The phases with the three programs fixed here**: §6.1 `commit6`, WP K2's `treeProgS6` and
WP SPH's `SP.spongePhase6` (§6.3: K1's caller and core, season 1's link, `SP.spS`); the typed, ring
and opening programs are the owners' (Y1/CD, RS, W1). -/
def phases6 (typed : Shape → Hdr → VerifierProgram (List StackClaim6))
    (ring : Shape → List SliceClaim → List StackClaim6 → VerifierProgram StackClaim6)
    (whir : Shape → StackClaim6 → VerifierProgram Bool) : Phases :=
  ⟨commit6, K.treeProgS6, SP.spongePhase6, typed, ring, whir⟩

end Lvm6
