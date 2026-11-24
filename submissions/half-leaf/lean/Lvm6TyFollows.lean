-- New for lvm6 Y1 (2026-11-23): the typed phases and the mini-bus follow their part of the schedule (WP ASM's
-- `PhasesFollow.typed`: `Follows (typed …) (opsOf levs (subT.typed ++ subT.bus))`, FORMAT6 §6.4).
import Lvm6TyStmt
import Lvm6AsmProg

/-!
# The typed phases follow FORMAT6 §6.4

* `FollowsP P p os`: `Follows` whose return also satisfies `P` (the GKR walk's round count is the current point's
  length, so a step's continuation needs the point's length); `FollowsP.bind`, `FollowsP.follows`.
* The leaves (`e2Read`, `e2Reads`, `e2Sample`, `e2Samples`, `e2SampleN`, a round, `sumcheckE2`), the GKR step and
  walk (`layOps`), the bus phase and the mini-bus, the four typed phases.
* **`typedProgE_follows`**: `typedProgE` performs exactly `opsOf levs (subT17.typed ++ subT17.bus)`;
  **`typedPhase6_follows`**: so does the phase on the stack at a shape whose sub-schedules are `subT17`.
-/

set_option autoImplicit false

namespace Lvm6.Ty

open LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.Compile LeanVM.Protocol.Compile.VerifierProgram
open Lvm.E2V Lvm6.Mb
open Lvm6 (Op Follows opsOf)
open Lvm.Typed (xVars yVars)

/-! ## `Follows` with a postcondition -/

section FollowsP

variable {α β : Type}

/-- **`p` follows `os` and returns a value satisfying `P`.** -/
def FollowsP (P : α → Prop) : VerifierProgram α → List Op → Prop
  | .ret a, os => os = [] ∧ P a
  | .fail, _ => True
  | .grind _ _, _ => False
  | .read k, os => os.head? = some .rd ∧ ∀ x, FollowsP P (k x) os.tail
  | .sample k, os => os.head? = some .smp ∧ ∀ c, FollowsP P (k c) os.tail
  | .commit ht w k, os => os.head? = some (.cap ht w) ∧ FollowsP P k os.tail
  | .query i _ k, os => os.head? = some (.opn i) ∧ ∀ r, FollowsP P (k r) os.tail

theorem FollowsP.bind {P : α → Prop} {Q : β → Prop} {p : VerifierProgram α} {f : α → VerifierProgram β}
    {o₁ o₂ : List Op} (hp : FollowsP P p o₁) (hf : ∀ a, P a → FollowsP Q (f a) o₂) :
    FollowsP Q (p >>= f) (o₁ ++ o₂) := by
  show FollowsP Q (p.bind f) (o₁ ++ o₂)
  induction p generalizing o₁ with
  | ret a =>
    obtain ⟨h, hP⟩ := hp
    subst h; exact hf a hP
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

theorem FollowsP.follows {P : α → Prop} : ∀ {p : VerifierProgram α} {os : List Op}, FollowsP P p os → Follows p os
  | .ret _, _, h => h.1
  | .fail, _, _ => trivial
  | .grind _ _, _, h => h.elim
  | .read _, _, h => ⟨h.1, fun x ↦ (h.2 x).follows⟩
  | .sample _, _, h => ⟨h.1, fun c ↦ (h.2 c).follows⟩
  | .commit _ _ _, _, h => ⟨h.1, h.2.follows⟩
  | .query _ _ _, _, h => ⟨h.1, fun r ↦ (h.2 r).follows⟩

theorem FollowsP.ofFollows : ∀ {p : VerifierProgram α} {os : List Op}, Follows p os → FollowsP (fun _ ↦ True) p os
  | .ret _, _, h => ⟨h, trivial⟩
  | .fail, _, _ => trivial
  | .grind _ _, _, h => h.elim
  | .read _, _, h => ⟨h.1, fun x ↦ FollowsP.ofFollows (h.2 x)⟩
  | .sample _, _, h => ⟨h.1, fun c ↦ FollowsP.ofFollows (h.2 c)⟩
  | .commit _ _ _, _, h => ⟨h.1, FollowsP.ofFollows h.2⟩
  | .query _ _ _, _, h => ⟨h.1, fun r ↦ FollowsP.ofFollows (h.2 r)⟩

theorem FollowsP.mono {P Q : α → Prop} (hPQ : ∀ a, P a → Q a) :
    ∀ {p : VerifierProgram α} {os : List Op}, FollowsP P p os → FollowsP Q p os
  | .ret a, _, h => ⟨h.1, hPQ a h.2⟩
  | .fail, _, _ => trivial
  | .grind _ _, _, h => h.elim
  | .read _, _, h => ⟨h.1, fun x ↦ FollowsP.mono hPQ (h.2 x)⟩
  | .sample _, _, h => ⟨h.1, fun c ↦ FollowsP.mono hPQ (h.2 c)⟩
  | .commit _ _ _, _, h => ⟨h.1, FollowsP.mono hPQ h.2⟩
  | .query _ _ _, _, h => ⟨h.1, fun r ↦ FollowsP.mono hPQ (h.2 r)⟩

theorem fp_ret {P : α → Prop} (a : α) (h : P a) : FollowsP P (pure a) [] := ⟨rfl, h⟩

/-- `bind` with the operations given up to an equation. -/
theorem FollowsP.bind_eq {P : α → Prop} {Q : β → Prop} {p : VerifierProgram α} {f : α → VerifierProgram β}
    {o₁ o₂ os : List Op} (hp : FollowsP P p o₁) (hf : ∀ a, P a → FollowsP Q (f a) o₂) (h : o₁ ++ o₂ = os) :
    FollowsP Q (p >>= f) os := h ▸ FollowsP.bind hp hf

theorem fp_require (c : Prop) {_ : Decidable c} : FollowsP (fun _ ↦ True) (VerifierProgram.require c) [] := by
  unfold VerifierProgram.require; split
  · exact ⟨rfl, trivial⟩
  · trivial

theorem fp_readScalar : FollowsP (fun _ ↦ True) VerifierProgram.readScalar [.rd] := ⟨rfl, fun _ ↦ ⟨rfl, trivial⟩⟩

theorem fp_sampleChallenge : FollowsP (fun _ ↦ True) VerifierProgram.sampleChallenge [.smp] :=
  ⟨rfl, fun _ ↦ ⟨rfl, trivial⟩⟩

theorem fp_sampleChallenges : ∀ n, FollowsP (fun cs : List E ↦ cs.length = n)
    (VerifierProgram.sampleChallenges n) (List.replicate n .smp)
  | 0 => ⟨rfl, rfl⟩
  | n + 1 => by
    unfold VerifierProgram.sampleChallenges
    exact FollowsP.bind_eq fp_sampleChallenge (fun c _ ↦ FollowsP.bind_eq (fp_sampleChallenges n)
      (fun cs hcs ↦ fp_ret (P := fun cs : List E ↦ cs.length = n + 1) (c :: cs) (by simp [hcs])) rfl)
      (by simp [List.replicate_succ])

end FollowsP

/-! ## The `E2` reads, samples and rounds -/

/-- A group `G(g)`'s operations: the nonce, the draw. -/
abbrev gOps : List Op := [.rd, .smp]

theorem fp_e2Read : FollowsP (fun _ ↦ True) e2Read [.rd] := by
  unfold e2Read
  exact FollowsP.bind_eq fp_readScalar (fun x _ ↦ fp_ret (P := fun _ : E2 ↦ True) (e2OfE x) trivial) rfl

theorem fp_e2Reads : ∀ n, FollowsP (fun xs : List E2 ↦ xs.length = n) (e2Reads n) (List.replicate n .rd)
  | 0 => ⟨rfl, rfl⟩
  | n + 1 => by
    unfold e2Reads
    exact FollowsP.bind_eq fp_e2Read (fun x _ ↦ FollowsP.bind_eq (fp_e2Reads n)
      (fun xs hxs ↦ fp_ret (P := fun xs : List E2 ↦ xs.length = n + 1) (x :: xs) (by simp [hxs])) rfl)
      (by simp [List.replicate_succ])

theorem fp_e2Sample (g : ℕ) : FollowsP (fun _ ↦ True) (e2Sample g) gOps := by
  unfold e2Sample
  exact FollowsP.bind_eq fp_readScalar (fun _ _ ↦ FollowsP.bind_eq fp_sampleChallenge (fun c _ ↦
    FollowsP.bind_eq (fp_require _) (fun _ _ ↦ fp_ret (P := fun _ : E2 ↦ True) (e2OfE c) trivial) rfl) rfl) rfl

theorem fp_e2Samples (g : ℕ) : ∀ n, FollowsP (fun xs : List E2 ↦ xs.length = n) (e2Samples g n)
    (List.replicate n gOps).flatten
  | 0 => ⟨rfl, rfl⟩
  | n + 1 => by
    unfold e2Samples
    exact FollowsP.bind_eq (fp_e2Sample g) (fun x _ ↦ FollowsP.bind_eq (fp_e2Samples g n)
      (fun xs hxs ↦ fp_ret (P := fun xs : List E2 ↦ xs.length = n + 1) (x :: xs) (by simp [hxs])) rfl)
      (by simp [List.replicate_succ])

theorem fp_e2SampleN (g n : ℕ) : FollowsP (fun ys : List E2 ↦ ys.length = n + 1) (e2SampleN g (n + 1))
    (gOps ++ List.replicate n .smp) := by
  unfold e2SampleN
  exact FollowsP.bind_eq fp_readScalar (fun _ _ ↦ FollowsP.bind_eq fp_sampleChallenge (fun c _ ↦
    FollowsP.bind_eq (fp_require _) (fun _ _ ↦ FollowsP.bind_eq (fp_sampleChallenges n) (fun cs hcs ↦
      fp_ret (P := fun ys : List E2 ↦ ys.length = n + 1) ((c :: cs).map e2OfE) (by simp [hcs])) rfl) rfl) rfl)
    (by simp)

/-- A round's message: `count − 1` reads. -/
theorem fp_roundPolyE2 (count : ℕ) (hc : 2 ≤ count) (claim : E2) (mode : Option E2) :
    FollowsP (fun _ ↦ True) (roundPolyE2 count claim mode) (List.replicate (count - 1) .rd) := by
  cases mode with
  | none =>
    unfold roundPolyE2
    exact FollowsP.bind_eq fp_e2Read (fun c0 _ ↦ FollowsP.bind_eq (fp_e2Reads (count - 2)) (fun tail _ ↦
      fp_ret (P := fun _ ↦ True) (c0 :: (claim + sumF tail) :: tail) trivial) rfl)
      (by rw [show count - 1 = count - 2 + 1 by omega, List.replicate_succ]; simp)
  | some r =>
    unfold roundPolyE2
    exact FollowsP.bind_eq (fp_e2Reads (count - 1)) (fun tail _ ↦
      fp_ret (P := fun _ ↦ True) ((claim + r * sumF tail) :: tail) trivial) (by simp)

/-- A sumcheck round's operations: the message, the group. -/
abbrev rdOps (count : ℕ) : List Op := List.replicate (count - 1) .rd ++ gOps

theorem fp_sumcheckE2 (g count : ℕ) (hc : 2 ≤ count) : ∀ (modes : List (Option E2)) (claim : E2),
    FollowsP (fun rf : List E2 × E2 ↦ rf.1.length = modes.length) (sumcheckE2 g claim count modes)
      (List.replicate modes.length (rdOps count)).flatten
  | [], _ => ⟨rfl, rfl⟩
  | m :: ms, claim => by
    unfold sumcheckE2
    exact FollowsP.bind_eq (fp_roundPolyE2 count hc claim m) (fun msg _ ↦ FollowsP.bind_eq (fp_e2Sample g)
      (fun c _ ↦ FollowsP.bind_eq (fp_sumcheckE2 g count hc ms _) (fun res hres ↦
        fp_ret (P := fun rf : List E2 × E2 ↦ rf.1.length = (m :: ms).length) (c :: res.1, res.2)
          (by simp [hres])) rfl) rfl) (by simp [List.replicate_succ, List.append_assoc])

/-! ## The GKR walk and the bus phase -/

/-- **A step's operations** (`step ≥ 1`, at a point of `m` coordinates): `λ`, `m` rounds of `2^step + 1`
coefficients, three children, `y` as one group. -/
def stepOps (step m : ℕ) : List Op :=
  gOps ++ (List.replicate m (rdOps (2 ^ step + 1))).flatten ++ List.replicate (3 * 2 ^ step) .rd ++
    (gOps ++ List.replicate (step - 1) .smp)

theorem fp_gkrStepG (gy step : ℕ) (hs : 1 ≤ step) (s : GkrStateG) :
    FollowsP (fun s' : GkrStateG ↦ s'.point.length = step + s.point.length) (gkrStepG gy step s)
      (stepOps step s.point.length) := by
  obtain ⟨st, rfl⟩ : ∃ st, step = st + 1 := ⟨step - 1, by omega⟩
  have hc : 2 ≤ 2 ^ (st + 1) + 1 := by have := Nat.one_le_two_pow (n := st + 1); omega
  unfold gkrStepG
  refine FollowsP.bind_eq (fp_e2Sample gLam) (fun lam _ ↦ FollowsP.bind_eq
    (fp_sumcheckE2 gRd _ hc (s.point.map some) (polyEvalF s.values lam)) (fun rf hrf ↦
      FollowsP.bind_eq (fp_e2Reads (2 ^ (st + 1))) (fun c0 _ ↦ FollowsP.bind_eq (fp_e2Reads (2 ^ (st + 1)))
        (fun c1 _ ↦ FollowsP.bind_eq (fp_e2Reads (2 ^ (st + 1))) (fun c2 _ ↦ FollowsP.bind_eq (fp_require _)
          (fun _ _ ↦ FollowsP.bind_eq (fp_e2SampleN gy st) (fun y hy ↦
            fp_ret (P := fun s' : GkrStateG ↦ s'.point.length = st + 1 + s.point.length)
              (⟨[c0, c1, c2].map (multilinearEvalF · y), y ++ rf.1⟩ : GkrStateG)
              (by simp only [List.length_append, hy, hrf, List.length_map])) rfl) rfl) rfl) rfl) rfl) rfl) ?_
  unfold stepOps
  have e : List.replicate (3 * 2 ^ (st + 1)) Op.rd = List.replicate (2 ^ (st + 1)) .rd ++
      (List.replicate (2 ^ (st + 1)) .rd ++ List.replicate (2 ^ (st + 1)) .rd) := by
    simp only [List.replicate_append_replicate]; congr 1; ring
  rw [e, List.length_map, Nat.add_sub_cancel]
  simp only [List.append_assoc, List.nil_append, List.append_nil]

/-- **The walk's operations** with `n` levels left at a point of `m` coordinates (`gkrLayersG`'s recursion). -/
def layOps : ℕ → ℕ → List Op
  | 0, _ => []
  | 1, m => stepOps 1 m
  | n + 2, m => if n % 2 = 1 then stepOps 1 m ++ layOps (n + 1) (1 + m) else stepOps 2 m ++ layOps n (2 + m)

theorem fp_gkrLayersG : ∀ (n : ℕ) (s : GkrStateG),
    FollowsP (fun s' : GkrStateG ↦ s'.point.length = n + s.point.length) (gkrLayersG n s) (layOps n s.point.length)
  | 0, s => ⟨rfl, by simp⟩
  | 1, s => by
    unfold gkrLayersG layOps
    exact fp_gkrStepG _ 1 le_rfl s
  | n + 2, s => by
    unfold gkrLayersG layOps
    split
    · refine FollowsP.bind (fp_gkrStepG _ 1 le_rfl s) fun s' hs' ↦ ?_
      have h := fp_gkrLayersG (n + 1) s'
      rw [hs'] at h
      exact h.mono fun a ha ↦ by rw [ha]; omega
    · refine FollowsP.bind (fp_gkrStepG _ 2 (by norm_num) s) fun s' hs' ↦ ?_
      have h := fp_gkrLayersG n s'
      rw [hs'] at h
      exact h.mono fun a ha ↦ by rw [ha]; omega

/-- The bus phase's operations at depth `μ`. -/
def busOps (μ : ℕ) : List Op := gOps ++ List.replicate 4 .smp ++ [.rd, .rd] ++ layOps μ 0

theorem fp_verifyGkrG (μ : ℕ) :
    FollowsP (fun _ ↦ True) (verifyGkrGrandProductsG μ) ([.rd, .rd] ++ layOps μ 0) := by
  unfold verifyGkrGrandProductsG
  exact FollowsP.bind_eq fp_e2Read (fun shared _ ↦ FollowsP.bind_eq fp_e2Read (fun count _ ↦
    FollowsP.bind_eq (fp_gkrLayersG μ ⟨[shared, shared, count], []⟩) (fun s _ ↦
      fp_ret (P := fun _ ↦ True) (count, s.point, s.values) trivial) (List.append_nil _)) rfl) rfl

theorem follows_lvmBusProgG (μ : ℕ) : Follows (lvmBusProgG μ) (busOps μ) := by
  unfold lvmBusProgG
  exact (FollowsP.bind_eq (fp_e2SampleN gAB 4) (fun ab _ ↦ FollowsP.bind_eq (fp_verifyGkrG μ) (fun r _ ↦
    FollowsP.bind_eq (fp_require _) (fun _ _ ↦ fp_ret (P := fun _ ↦ True)
      (⟨ab.take 4, ab.getD 4 0, r.2.1, r.2.2⟩ : LBusG) trivial) rfl) (List.append_nil _))
    (by simp [busOps, List.append_assoc])).follows

theorem follows_miniBusLProg6 (L : Lvm.M3.Lay) (tabs : List Lvm.M3.Tab) (μ : ℕ) :
    Follows (miniBusLProg6 L tabs μ) (busOps μ) := by
  unfold miniBusLProg6
  exact (FollowsP.bind_eq (FollowsP.ofFollows (follows_lvmBusProgG μ)) (fun b _ ↦
    fp_ret (P := fun _ ↦ True) ((mbClaimsG L.nuMain tabs b).map (·.onStack)) trivial) (List.append_nil _)).follows

/-! ## The typed phases -/

/-- The zerocheck's operations. -/
def zeroOps : List Op :=
  (List.replicate xVars gOps).flatten ++ (List.replicate xVars (rdOps 3)).flatten ++ List.replicate 3 .rd

theorem follows_zeroProgE : Follows zeroProgE zeroOps := by
  unfold zeroProgE
  refine (FollowsP.bind_eq (Q := fun _ ↦ True) (fp_e2Samples gTau xVars) (fun τ hτ ↦ ?_) (List.append_assoc _ _ _).symm).follows
  have hs := fp_sumcheckE2 gZero 3 (by norm_num) (τ.map some) 0
  rw [List.length_map, hτ] at hs
  exact FollowsP.bind_eq hs (fun rf _ ↦ FollowsP.bind_eq (fp_e2Reads 3) (fun v _ ↦ FollowsP.bind_eq (fp_require _)
    (fun _ _ ↦ fp_ret (P := fun _ ↦ True) (rf.1, v) trivial) rfl) (List.append_nil _)) rfl

/-- The wiring's operations. -/
def wireOps : List Op :=
  gOps ++ ((List.replicate yVars (rdOps 3)).flatten ++ (List.replicate 4 .rd ++ List.replicate 4 .rd))

theorem follows_wireProgE (Ti : TInst6) (pw : ℕ → Lvm.FK) (v : List E2) : Follows (wireProgE Ti pw v) wireOps := by
  unfold wireProgE
  refine (FollowsP.bind_eq (Q := fun _ ↦ True) (fp_e2Sample gGamma) (fun γ _ ↦ ?_) rfl).follows
  have hs := fp_sumcheckE2 gWire 3 (by norm_num) (List.replicate yVars none) (wBatchE γ v)
  rw [List.length_replicate] at hs
  exact FollowsP.bind_eq hs (fun rf _ ↦ FollowsP.bind_eq (fp_e2Reads 4) (fun vs _ ↦ FollowsP.bind_eq (fp_e2Reads 4)
    (fun rv _ ↦ FollowsP.bind_eq (fp_require _) (fun _ _ ↦ fp_ret (P := fun _ ↦ True) (rf.1, vs, rv) trivial) rfl)
    (List.append_nil _)) rfl) rfl

/-- The relayout's operations. -/
def relayOps : List Op := (List.replicate relayRounds (rdOps 3)).flatten ++ [.rd]

theorem follows_relayProgE (Ti : TInst6) (ry : List E2) (vS : E2) : Follows (relayProgE Ti ry vS) relayOps := by
  unfold relayProgE
  have hs := fp_sumcheckE2 gWire 3 (by norm_num) (List.replicate relayRounds none) vS
  rw [List.length_replicate] at hs
  exact (FollowsP.bind_eq hs (fun rf _ ↦ FollowsP.bind_eq fp_e2Read (fun vR _ ↦ FollowsP.bind_eq (fp_require _)
    (fun _ _ ↦ fp_ret (P := fun _ ↦ True) (rf.1, vR) trivial) rfl) rfl) rfl).follows

/-- A23's operations with `n` scalars of `h`. -/
def accOps (n : ℕ) : List Op := (List.replicate selBitsE gOps).flatten ++ (List.replicate n .rd ++ gOps)

theorem follows_accShape (n : ℕ) (P : List E2 → List E2 → E2 → Prop) (dec : ∀ a b c, Decidable (P a b c)) :
    Follows (e2Samples gKappa selBitsE >>= fun κ ↦ e2Reads n >>= fun hs ↦ e2Sample gT >>= fun t ↦
      @VerifierProgram.require (P κ hs t) (dec κ hs t)) (accOps n) :=
  (FollowsP.bind_eq (fp_e2Samples gKappa selBitsE) (fun _ _ ↦ FollowsP.bind_eq (fp_e2Reads n) (fun _ _ ↦
    FollowsP.bind_eq (fp_e2Sample gT) (fun _ _ ↦ fp_require _) (List.append_nil _)) rfl) rfl).follows

theorem follows_accProgE (Q : Lvm.Loop.Program) (lay : Lvm.Typed.Lay) (yIn : E2) (a rxy vs : List E2) :
    Follows (accProgE Q lay yIn a rxy vs) (accOps (phiVarsE + 1)) :=
  follows_accShape (phiVarsE + 1) _ _

/-- **The typed phases' and the mini-bus's operations.** -/
def typedOps : List Op := zeroOps ++ (wireOps ++ (relayOps ++ (accOps (phiVarsE + 1) ++ busOps miniDepth)))

/-- An item that does not read the levels (not a cap, not a position group). -/
def NoLev : Lvm6.V.Item → Bool
  | .cap _ => false
  | .pos _ _ => false
  | _ => true

theorem opsOf_noLev (L L' : List Lvm6.V.Lev) : ∀ (l : List Lvm6.V.Item), (∀ it ∈ l, NoLev it = true) →
    opsOf L l = opsOf L' l
  | [], _ => rfl
  | it :: l, h => by
    have ih := opsOf_noLev L L' l fun it' hit' ↦ h it' (List.mem_cons_of_mem _ hit')
    have hit := h it List.mem_cons_self
    show Lvm6.PO.item L it ++ opsOf L l = Lvm6.PO.item L' it ++ opsOf L' l
    rw [ih]
    cases it <;> simp_all [NoLev, Lvm6.V.Prims.item]

theorem typedOps_eq0 : typedOps = opsOf [] (subT17.typed ++ subT17.bus) := by decide +kernel

theorem subT17_noLev : ∀ it ∈ subT17.typed ++ subT17.bus, NoLev it = true := by decide +kernel

/-- **They are FORMAT6 §6.4's** (`subT17`, FORMAT6 v2.6's lists: 18 relayout rounds). -/
theorem typedOps_eq (levs : List Lvm6.V.Lev) : typedOps = opsOf levs (subT17.typed ++ subT17.bus) :=
  typedOps_eq0.trans (opsOf_noLev [] levs _ subT17_noLev)

/-- **`typedProgE` follows FORMAT6 §6.4** (WP ASM's `PhasesFollow.typed`, at `subT17`). -/
theorem typedProgE_follows (Ti : TInst6) (L : Lvm.M3.Lay) (pw : ℕ → Lvm.FK) (acc : List E2 × E2)
    (levs : List Lvm6.V.Lev) : Follows (typedProgE Ti L pw acc) (opsOf levs (subT17.typed ++ subT17.bus)) := by
  rw [← typedOps_eq levs]
  unfold typedProgE typedOps
  exact (FollowsP.bind_eq (FollowsP.ofFollows follows_zeroProgE) (fun z _ ↦ FollowsP.bind_eq
    (FollowsP.ofFollows (follows_wireProgE Ti pw z.2)) (fun w _ ↦ FollowsP.bind_eq
      (FollowsP.ofFollows (follows_relayProgE Ti w.1 (w.2.2.getD 1 0))) (fun r _ ↦ FollowsP.bind_eq
        (FollowsP.ofFollows (follows_accProgE Ti.Q Ti.lay acc.2 acc.1 (z.1 ++ w.1) w.2.1)) (fun _ _ ↦
          FollowsP.bind_eq (FollowsP.ofFollows (follows_miniBusLProg6 L Ti.mbT miniDepth)) (fun cl _ ↦
            fp_ret (P := fun _ ↦ True) (typedClaimsE Ti w.1 w.2.2 r.1 r.2 cl) trivial) (List.append_nil _))
          rfl) rfl) rfl) rfl).follows

/-- **The typed phase on the stack follows FORMAT6 §6.4** at a shape whose sub-schedules are `subT17`. -/
theorem typedPhase6_follows (sh : Lvm6.Shape) (hsub : sh.subT = subT17) (i : TyInst6) :
    Follows (typedPhase6 sh i) (opsOf sh.levs (sh.subT.typed ++ sh.subT.bus)) := by
  unfold typedPhase6
  split
  · rw [hsub]
    exact (FollowsP.bind_eq (FollowsP.ofFollows (typedProgE_follows i.Ti L6 i.pw i.acc sh.levs)) (fun out _ ↦
      fp_ret (P := fun _ ↦ True) (claimsOnStack out) trivial) (List.append_nil _)).follows
  · trivial

end Lvm6.Ty
