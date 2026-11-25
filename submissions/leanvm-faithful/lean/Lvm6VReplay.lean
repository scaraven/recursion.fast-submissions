-- New for lvm6 (WP-V1, part 2): the walk-then-decide scheme refines any interleaved program that follows the
-- schedule: if the walk accepts with the decision "replay the program on the transcript", the program itself
-- accepts (on every log). This connects `scheme6V` to the scheme whose program is the phase programs (`prog6`).
import Lvm6VEq

/-!
# Replaying a program on the walk's transcript

`replay p tr` runs a program `p` of the verifier language on a transcript `tr` (oldest first): a read takes
the next `.e x`, a sample the next `.c c`, a commit the next `.cap ht w` (same shape), a query the next
`.rows i ps r` (same commitment and positions); `ret b` needs the transcript used up; anything else is
`false`. So a program whose reads, draws, caps and openings follow the schedule is replayed to its verdict,
and any other program is replayed to `false`.

**`replay_refines`**: for every program `prog` (any interleaving of checks with the transcript operations),
if the compiled walk with the decision `replay (prog x) tr.reverse` accepts on a log, so does the compiled
`prog` (the same scheme with `P := prog`). With `VS6_refines` this gives `refines6` for `prog6` once the
executable decision `F` agrees with `replay (prog6 x)` on the transcript read off `π`.

The proof is a backward simulation (`RSim`), primitive by primitive: an accepting run of the walk's step
gives an accepting run of the program's matching step on the same state, the same log entries and the
same body; where the program does something else, the residual is `fail` and the walk cannot accept.
-/

set_option autoImplicit false

namespace Lvm6.V

open RecursionFast LeanVM.Parameters Lvm.FS
open LeanVM.Protocol.Compile hiding Proof Bytes Word

/-- **Replay** a program on a transcript (oldest first). -/
def replay : VerifierProgram Bool → List Val → Bool
  | .ret b, [] => b
  | .read k, .e x :: tr => replay (k x) tr
  | .sample k, .c c :: tr => replay (k c) tr
  | .commit ht w k, .cap ht' w' :: tr => (ht == ht' && w == w') && replay k tr
  | .query i ps k, .rows i' ps' r :: tr => (i == i' && ps == ps') && replay (k r) tr
  | _, _ => false

@[simp] theorem replay_fail (tr : List Val) : replay .fail tr = false := by cases tr <;> rfl

section RSim

variable (S : Scheme) (Lg : Log) (p0 : VerifierProgram Bool)

/-- `p` is the residual of `p0` after the transcript `acc` (newest first). -/
def Res (p : VerifierProgram Bool) (acc : List Val) : Prop := ∀ rest, replay p0 (acc.reverse ++ rest) = replay p rest

/-- The run accepts on the log. -/
abbrev Acc (o : OProg Bool) : Prop := o.runLog Lg = some true

/-- A continuation of the walk is good: whenever it accepts, so does the residual program. -/
def KGood (ks : Kt) : Prop :=
  ∀ ps acc p n st buf caps body, Res p0 p acc → Acc Lg (S.runW n (ks ps acc) st buf caps body) →
    Acc Lg (S.runW n p st buf caps body)

/-- **Backward simulation** of a step of the walk. -/
def RSim (f : St) : Prop :=
  ∀ ks, KGood S Lg p0 ks → ∀ ps acc p n st buf caps body, Res p0 p acc →
    Acc Lg (S.runW n (f ps acc ks) st buf caps body) → Acc Lg (S.runW n p st buf caps body)

theorem rsim_skip : RSim S Lg p0 PS.skip := fun _ hk => hk

theorem rsim_seq {f g : St} (hf : RSim S Lg p0 f) (hg : RSim S Lg p0 g) : RSim S Lg p0 (PS.seq f g) :=
  fun ks hk => hf _ (fun ps acc p n st buf caps body hr ha => hg ks hk ps acc p n st buf caps body hr ha)

theorem rsim_reset : RSim S Lg p0 PS.reset := fun _ hk _ acc p n st buf caps body hr ha =>
  hk [] acc p n st buf caps body hr ha

theorem res_cons {p : VerifierProgram Bool} {acc : List Val} (hr : Res p0 p acc) (v : Val) (p' : VerifierProgram Bool)
    (h : ∀ rest, replay p (v :: rest) = replay p' rest) : Res p0 p' (v :: acc) := fun rest => by
  rw [List.reverse_cons, List.append_assoc, List.singleton_append, hr, h]

theorem runW_fail_not (n : Nat) (st : Digest) (buf : Bytes) (caps : List CapI) (body : Bytes) :
    ¬ Acc Lg (S.runW n .fail st buf caps body) := by
  simp [Acc, Scheme.runW, OProg.runLog]

theorem rsim_rd (w : Nat) : RSim S Lg p0 (PS.rd w) := by
  intro ks hk ps acc p n st buf caps body hr ha
  simp only [Acc] at ha ⊢
  simp only [PS, Scheme.runW] at ha
  split at ha
  · simp [OProg.runLog] at ha
  · rename_i hlen
    cases p with
    | read k =>
      simp only [Scheme.runW, if_neg hlen]
      exact hk _ _ _ _ _ _ _ _ (res_cons p0 hr _ _ fun _ => rfl) ha
    | _ =>
      exact absurd (hk _ _ .fail _ _ _ _ _ (res_cons p0 hr _ _ fun _ => by simp [replay]) ha)
        (runW_fail_not S Lg _ _ _ _ _)

theorem rsim_draw (chk : Nat → Bool) (upd : List Nat → Nat → List Nat) : RSim S Lg p0 (PS.draw chk upd) := by
  intro ks hk ps acc p n st buf caps body hr ha
  simp only [Acc] at ha ⊢
  simp only [PS, Scheme.runW] at ha
  split at ha
  · rename_i hcap
    simp only [OProg.runLog] at ha
    rcases he : Lg.find? (fun e => decide (e.1 = toQ (st.toList ++ buf))) with _ | e
    · rw [he] at ha; simp at ha
    · rw [he, Option.bind_some] at ha
      by_cases hc : chk (LeanVM.Protocol.Verifier.eToNat (S.chal e.2)) = true
      · rw [if_pos hc] at ha
        cases p with
        | sample k =>
          simp only [Scheme.runW, if_pos hcap, OProg.runLog, he, Option.bind_some]
          exact hk _ _ _ _ _ _ _ _ (res_cons p0 hr _ _ fun _ => rfl) ha
        | _ =>
          exact absurd (hk _ _ .fail _ _ _ _ _ (res_cons p0 hr _ _ fun _ => by simp [replay]) ha)
            (runW_fail_not S Lg _ _ _ _ _)
      · rw [if_neg hc] at ha
        exact absurd ha (runW_fail_not S Lg _ _ _ _ _)
  · simp [OProg.runLog] at ha

theorem rsim_cap (ht w : Nat) : RSim S Lg p0 (PS.cap ht w) := by
  intro ks hk ps acc p n st buf caps body hr ha
  simp only [Acc] at ha ⊢
  simp only [PS, Scheme.runW] at ha
  split at ha
  · simp [OProg.runLog] at ha
  · rename_i hlen
    cases p with
    | commit ht' w' k =>
      by_cases hs : ht' = ht ∧ w' = w
      · obtain ⟨rfl, rfl⟩ := hs
        simp only [Scheme.runW, if_neg hlen]
        exact hk _ _ _ _ _ _ _ _ (res_cons p0 hr _ _ fun _ => by simp [replay]) ha
      · refine absurd (hk _ _ .fail _ _ _ _ _ (res_cons p0 hr _ _ fun _ => ?_) ha) (runW_fail_not S Lg _ _ _ _ _)
        simp only [replay, replay_fail, Bool.and_eq_false_iff, beq_eq_false_iff_ne]
        by_cases h1 : ht' = ht
        · exact Or.inl (Or.inr fun h2 => hs ⟨h1, h2⟩)
        · exact Or.inl (Or.inl h1)
    | _ =>
      exact absurd (hk _ _ .fail _ _ _ _ _ (res_cons p0 hr _ _ fun _ => by simp [replay]) ha)
        (runW_fail_not S Lg _ _ _ _ _)

theorem rsim_open (i : Nat) : RSim S Lg p0 (PS.opn i) := by
  intro ks hk ps acc p n st buf caps body hr ha
  simp only [Acc] at ha ⊢
  simp only [PS, Scheme.runW] at ha
  rcases hci : caps[i]? with _ | ci
  · rw [hci] at ha; simp [OProg.runLog] at ha
  · rw [hci] at ha
    simp only [OProgFacts.runLog_bind] at ha
    rcases ho : (S.openAll ci ps body).runLog Lg with _ | o
    · rw [ho] at ha; simp at ha
    · rw [ho, Option.bind_some] at ha
      rcases o with _ | ⟨rows, rest⟩
      · simp [OProg.runLog] at ha
      · cases p with
        | query i' ps' k =>
          by_cases hs : i' = i ∧ ps' = ps
          · obtain ⟨rfl, rfl⟩ := hs
            simp only [Scheme.runW, hci, OProgFacts.runLog_bind, ho, Option.bind_some]
            exact hk _ _ _ _ _ _ _ _ (res_cons p0 hr _ _ fun _ => by simp [replay]) ha
          · refine absurd (hk _ _ .fail _ _ _ _ _ (res_cons p0 hr _ _ fun _ => ?_) ha)
              (runW_fail_not S Lg _ _ _ _ _)
            simp only [replay, replay_fail, Bool.and_eq_false_iff, beq_eq_false_iff_ne]
            by_cases h1 : i' = i
            · exact Or.inl (Or.inr fun h2 => hs ⟨h1, h2⟩)
            · exact Or.inl (Or.inl h1)
        | _ =>
          exact absurd (hk _ _ .fail _ _ _ _ _ (res_cons p0 hr _ _ fun _ => by simp [replay]) ha)
            (runW_fail_not S Lg _ _ _ _ _)

variable (L : List Lev)

theorem rsim_rep {f : St} (hf : RSim S Lg p0 f) : ∀ m, RSim S Lg p0 (PS.rep f m)
  | 0 => rsim_skip S Lg p0
  | m + 1 => rsim_seq S Lg p0 hf (rsim_rep hf m)

theorem rsim_posRest (ht : Nat) : ∀ cs, RSim S Lg p0 (PS.posRest ht cs)
  | [] => rsim_skip S Lg p0
  | _ :: cs => rsim_seq S Lg p0 (rsim_draw S Lg p0 _ _) (rsim_posRest ht cs)

theorem rsim_item (it : Item) : RSim S Lg p0 (PS.item L it) := by
  cases it with
  | E k => exact rsim_rep S Lg p0 (rsim_rd S Lg p0 16) _
  | K k => exact rsim_rep S Lg p0 (rsim_rd S Lg p0 8) _
  | cap i => exact rsim_cap S Lg p0 _ _
  | G g => exact rsim_seq S Lg p0 (rsim_rd S Lg p0 8) (rsim_draw S Lg p0 _ _)
  | D k => exact rsim_rep S Lg p0 (rsim_draw S Lg p0 _ _) k
  | B => exact rsim_draw S Lg p0 _ _
  | pos i g =>
    exact rsim_seq S Lg p0 (rsim_reset S Lg p0) (rsim_seq S Lg p0 (rsim_rd S Lg p0 8)
      (rsim_seq S Lg p0 (rsim_draw S Lg p0 _ _) (rsim_posRest S Lg p0 _ _)))
  | «open» i => exact rsim_open S Lg p0 i

theorem rsim_walk : ∀ s, RSim S Lg p0 (PS.walk L s)
  | [] => rsim_skip S Lg p0
  | it :: s => rsim_seq S Lg p0 (rsim_item S Lg p0 L it) (rsim_walk s)

/-- The walk's final continuation (the decision `replay p0`) is good. -/
theorem kgood_final : KGood S Lg p0 fun _ acc => .ret (replay p0 acc.reverse) := by
  intro ps acc p n st buf caps body hr ha
  have h0 := hr []
  rw [List.append_nil] at h0
  simp only [Acc, Scheme.runW, OProg.runLog, h0, Option.some.injEq, Bool.and_eq_true] at ha ⊢
  obtain ⟨h1, h2⟩ := ha
  cases p with
  | ret b =>
    cases b
    · simp [replay] at h1
    · simp [Scheme.runW, OProg.runLog, h2]
  | _ => simp [replay] at h1

end RSim

/-! ## The compiled run does not read the program field -/

section Congr

variable {S T : Scheme} (hrw : S.rw = T.rw) (hE : S.decE = T.decE) (hc : S.chal = T.chal)
  (hcap : S.capOf = T.capOf) (hocc : S.occ = T.occ) (hK : S.decK = T.decK)
include hrw hE hc hcap hocc hK

theorem runW_congr : ∀ (p : VerifierProgram Bool) (n : Nat) (st : Digest) (buf : Bytes) (caps : List CapI)
    (body : Bytes), S.runW n p st buf caps body = T.runW n p st buf caps body := by
  have hcb : S.capBytes = T.capBytes := by funext ht w; simp only [Scheme.capBytes, hcap]
  have hci : S.capI = T.capI := by funext ht w b; simp only [Scheme.capI, Scheme.capBytes, hcap]
  have hoa' : ∀ ci ps body, S.openAll ci ps body = T.openAll ci ps body := by
    intro ci ps
    induction ps with
    | nil => intro; rfl
    | cons p ps ih =>
      intro body
      simp only [Scheme.openAll, Scheme.openOne, Scheme.lb, Scheme.padRow, hocc, hK, ih]
      rfl
  have hoa : S.openAll = T.openAll := by funext ci ps body; exact hoa' ci ps body
  intro p
  induction p with
  | ret b => intros; rfl
  | fail => intros; rfl
  | grind _ _ _ => intros; rfl
  | read k ih =>
    intro n st buf caps body
    simp only [Scheme.runW, hrw, hE]
    split_ifs
    · rfl
    · exact ih _ _ _ _ _ _
  | sample k ih =>
    intro n st buf caps body
    simp only [Scheme.runW, hc]
    split_ifs
    · exact congrArg (OProg.query _) (funext fun a => ih _ _ _ _ _ _)
    · rfl
  | commit ht w k ih =>
    intro n st buf caps body
    simp only [Scheme.runW, hcb, hci]
    split_ifs
    · rfl
    · exact ih _ _ _ _ _
  | query i ps k ih =>
    intro n st buf caps body
    simp only [Scheme.runW, hoa]
    cases caps[i]? with
    | none => rfl
    | some ci =>
      simp only
      congr 1
      funext o
      rcases o with _ | ⟨rows, rest⟩
      · rfl
      · exact ih rows _ _ _ _ _

end Congr

/-- The scheme `scheme6V` with the program `prog` in place of the walk. -/
def schemeP (sh : VShape) (vk : Digest) (prog : List UInt8 → VerifierProgram Bool) : Scheme :=
  { scheme6V sh vk (fun x acc => replay (prog x) acc.reverse) with P := prog }

/-- **The walk refines every program**: if the compiled walk with the decision `replay (prog x)` accepts
on a log, the compiled `prog` accepts on it. -/
theorem replay_refines (sh : VShape) (vk : Digest) (prog : List UInt8 → VerifierProgram Bool) (Lg : Log)
    (c : Digest) (π : Proof)
    (h : ((scheme6V sh vk (fun x acc => replay (prog x) acc.reverse)).V c π).runLog Lg = some true) :
    ((schemeP sh vk prog).V c π).runLog Lg = some true := by
  rw [Scheme.runLog_V] at h ⊢
  have hhdr : (schemeP sh vk prog).hdr π = (scheme6V sh vk (fun x acc => replay (prog x) acc.reverse)).hdr π := rfl
  rw [hhdr]
  rcases hx : (scheme6V sh vk (fun x acc => replay (prog x) acc.reverse)).hdr π with _ | ⟨x, body⟩
  · rw [hx] at h; simp at h
  · rw [hx] at h
    simp only at h ⊢
    have hpre : (schemeP sh vk prog).preOk c x =
        (scheme6V sh vk (fun x acc => replay (prog x) acc.reverse)).preOk c x := rfl
    rw [hpre]
    split at h
    · rename_i hok
      rw [if_pos hok]
      rcases h0 : Lg.find? (fun e => decide (e.1 = toQ (scheme6V sh vk (fun x acc => replay (prog x) acc.reverse)).q0))
        with _ | e₀
      · rw [h0] at h; simp at h
      · rw [h0, Option.bind_some] at h
        have h0' : Lg.find? (fun e => decide (e.1 = toQ (schemeP sh vk prog).q0)) = some e₀ := h0
        rw [h0', Option.bind_some]
        rcases h1 : Lg.find? (fun e => decide (e.1 =
            (scheme6V sh vk (fun x acc => replay (prog x) acc.reverse)).seedQ e₀.2 x)) with _ | e₁
        · rw [h1] at h; simp at h
        · rw [h1, Option.bind_some] at h
          have h1' : Lg.find? (fun e => decide (e.1 = (schemeP sh vk prog).seedQ e₀.2 x)) = some e₁ := h1
          rw [h1', Option.bind_some]
          rw [← Scheme.runLog_runW] at h ⊢
          rw [runW_congr (S := schemeP sh vk prog) (T := scheme6V sh vk (fun x acc => replay (prog x) acc.reverse))
            rfl rfl rfl rfl rfl rfl]
          exact rsim_walk (scheme6V sh vk (fun x acc => replay (prog x) acc.reverse)) Lg (prog x) sh.levs sh.sched _
            (kgood_final _ Lg (prog x)) [] [] (prog x) _ _ [] [] body (fun _ => rfl) h
    · simp at h

end Lvm6.V
