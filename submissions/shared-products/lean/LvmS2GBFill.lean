-- New for lvm2 MP-B cap pruning (CAP-V, 2026-11-17; lead decision D-V1): the definitions of `refinesB20`'s statement
-- (moved verbatim from `LvmS2GBRef`) and the S2GB stream reader `ivpWB`. The compiled verifier (`Scheme.V`) climbs every path to the sent cap with all siblings in the
-- body, while an S2GB proof carries only the `D` lower siblings (the upper ones are heap answers): the specification
-- runs on `fillB P20B π w`, π's static part with `m − c` upper siblings per path from `w` (static size `pzB`).
import LvmS2GBV

/-!
# S2GB's expanded proof, scheme and format (owner V)

* **`fillB p π w`**: π's header and static body in schedule order; after each opened path's leaf and `D` inline
  siblings, the next `32 · (m − c)` bytes of `w` (the path's upper siblings, levels `D … h − c − 1`); the π tail is
  dropped. **`pzB p`**: its size, `piStatic p + 32 · Σ t (m − c)` over the openings (`pzB_P20B`: 325,336).
* **`capOfB`**: the sent caps' levels (`c = 1` at `C_main`'s root, height 19; `0`, the root, at levels 1–2);
  **`schemeSWB`**: `schemeSWS` with `capOf := capOfB`; **`rwB20`**, **`fmtB20`**: S2GB's static format at `pzB P20B`.
* **`typedProgLB d`**, **`midGB`**: S2GS's middle phases with the mini-bus GKR at depth `d = 13` (RE-FREEZE P2) and
  the tape over `contIvSB aSP`.
* **`ivpWB`**, **`RefAtPWB`**: `ivpW` / `RefAtPW` on the S2GB stream: a commit reads `2^cap` nodes (the sent cap), an
  opening's paths climb `pth i` levels and its `hq i` heap entries follow (`pthB`, `hqB`).
-/

set_option autoImplicit false

namespace Lvm

open RecursionFast

/-- One opening's expanded paths: `k` paths of `n` bytes of `b` from `o`, each followed by the next `u` bytes of
`w`. -/
def fillPaths (b : List UInt8) (n u : Nat) : Nat → Nat → List UInt8 → List UInt8
  | 0, _, _ => []
  | k + 1, o, w => (b.drop o).take n ++ w.take u ++ fillPaths b n u k (o + n) (w.drop u)

/-- **The expanded body** from the body cursor `o` of `b` over the items, the upper siblings read from `w`. -/
def fillItems (p : Params) (b : List UInt8) : List Item → Nat → List UInt8 → List UInt8
  | [], _, _ => []
  | .read m :: rest, o, w => (b.drop o).take (eBytes * m) ++ fillItems p b rest (o + eBytes * m) w
  | .readW m wd :: rest, o, w => (b.drop o).take (wd * m) ++ fillItems p b rest (o + wd * m) w
  | .cap c r :: rest, o, w =>
    (b.drop o).take (nodeBytes * 2 ^ p.capSendBits r.lv c) ++
      fillItems p b rest (o + nodeBytes * 2 ^ p.capSendBits r.lv c) w
  | .sample :: rest, o, w => fillItems p b rest o w
  | .positions _ :: rest, o, w => fillItems p b rest o w
  | .opening r :: rest, o, w =>
    let L := p.level r
    let n := L.row + nodeBytes * L.path
    let u := nodeBytes * (L.cap - p.capSendBits r.lv L.cap)
    fillPaths b n u L.t o w ++ fillItems p b rest (o + L.t * n) (w.drop (L.t * u))

/-- **The expanded proof**: π's header, then its static body with the upper siblings from `w` (the tail dropped). -/
def fillB (p : Params) (π : ByteArray) (w : List UInt8) : ByteArray :=
  ⟨(π.data.toList.take (headerBytesP p) ++
    fillItems p π.data.toList (schedule p) (headerBytesP p) w).toArray⟩

/-- The upper-sibling bytes the expansion adds: `32 · t · (m − c)` per opening. -/
def expandBytes (p : Params) : Nat :=
  (schedule p).foldl (fun a it => match it with
    | .opening r => a + (p.level r).t * (nodeBytes * ((p.level r).cap - p.capSendBits r.lv (p.level r).cap))
    | _ => a) 0

/-- **The expanded proof's size**. -/
def pzB (p : Params) : Nat := piStatic p + expandBytes p

/-- **The width of the `i`-th read** at S2GB (24 past the schedule). -/
def rwB20 (i : Nat) : Nat := (readWidthsP P20B).getD i eBytes

end Lvm

namespace Lvm.ASM

open RecursionFast Lvm.FS
open LeanVM.Protocol.Compile hiding Proof Bytes

/-- **The sent caps' levels at S2GB**: `C_main`'s root (height 19) sends 2 nodes, levels 1–2 (heights 16, 13) the
root (RE-FREEZE P1). -/
def capOfB (ht _w : ℕ) : ℕ := if ht = 19 then 1 else 0

/-- **The `S` branch's scheme at a format, S2GB**: `schemeSWS` with the sent caps (`capOfB`); it reads the expanded
proof `fillB`. -/
def schemeSWB (f : SFmt) (vk : RecursionFast.Digest) (P : List UInt8 → VerifierProgram Bool) : Scheme :=
  { schemeSWS f vk P with capOf := capOfB }

end Lvm.ASM

namespace Lvm

open RecursionFast

/-- The sent caps agree with the schedule: every cap item of `C_main`'s level `r` sends `2^capOfB` nodes of the
committed shape, and every opening of `r` climbs the shape's height (lead RE-FREEZE R3 (d)). -/
def capAgreeB (p : Params) : Bool :=
  (schedule p).all fun it => match it with
    | .cap c r => Lvm.ASM.capOfB (Lvm.VEq.shpS (Lvm.VEq.idxS r)).1 (Lvm.VEq.shpS (Lvm.VEq.idxS r)).2 ==
        p.capSendBits r.lv c
    | .opening r => (Lvm.VEq.shpS (Lvm.VEq.idxS r)).1 == (p.level r).height &&
        Lvm.ASM.capOfB (Lvm.VEq.shpS (Lvm.VEq.idxS r)).1 (Lvm.VEq.shpS (Lvm.VEq.idxS r)).2 ==
          p.capSendBits r.lv (p.level r).cap
    | _ => true

/-- An opening's expanded bytes (`expandBytes`'s step). -/
def expStepB (p : Params) : Item → ℕ
  | .opening r => (p.level r).t * (nodeBytes * ((p.level r).cap - p.capSendBits r.lv (p.level r).cap))
  | _ => 0

/-- A cap or opening item's agreement (`capAgreeB`'s step). -/
def capStepB (p : Params) (it : Item) : Bool :=
  match it with
  | .cap c r => Lvm.ASM.capOfB (Lvm.VEq.shpS (Lvm.VEq.idxS r)).1 (Lvm.VEq.shpS (Lvm.VEq.idxS r)).2 ==
      p.capSendBits r.lv c
  | .opening r => (Lvm.VEq.shpS (Lvm.VEq.idxS r)).1 == (p.level r).height &&
      Lvm.ASM.capOfB (Lvm.VEq.shpS (Lvm.VEq.idxS r)).1 (Lvm.VEq.shpS (Lvm.VEq.idxS r)).2 ==
        p.capSendBits r.lv (p.level r).cap
  | _ => true

/-- A `readW` item's positive width. -/
def rwStepB (it : Item) : Bool := match it with | .readW _ w => decide (0 < w) | _ => true

/-- Proof help: the schedule's expanded bytes, `readW` widths and cap agreement in one `List.rec` pass. -/
def schedSumB (p : Params) (l : List Item) : ℕ × Bool × Bool :=
  l.rec (0, true, true) fun it _ ih => (expStepB p it + ih.1, rwStepB it && ih.2.1, capStepB p it && ih.2.2)

theorem foldl_schedSumB (p : Params) (f : ℕ → Item → ℕ) (hf : ∀ a it, f a it = a + expStepB p it) :
    ∀ (l : List Item) (a : ℕ), l.foldl f a = a + (schedSumB p l).1
  | [], a => rfl
  | it :: l, a => by
    rw [List.foldl_cons, foldl_schedSumB p f hf l, hf]
    show _ = a + (expStepB p it + (schedSumB p l).1)
    omega

theorem expandBytes_eq (p : Params) : expandBytes p = (schedSumB p (schedule p)).1 :=
  (foldl_schedSumB p _ (fun a it => by cases it <;> rfl) _ 0).trans (Nat.zero_add _)

theorem schedSumB_snd (p : Params) : ∀ l : List Item,
    (schedSumB p l).2 = (l.all rwStepB, l.all (capStepB p))
  | [] => rfl
  | it :: l => by
    show (rwStepB it && (schedSumB p l).2.1, capStepB p it && (schedSumB p l).2.2) = _
    rw [schedSumB_snd p l]
    rfl

set_option maxRecDepth 100000 in
/-- Proof help: S2GB's expanded size (`piStatic` from `sizes_P20B`), its `readW` widths and the sent caps' agreement in
one kernel evaluation of the schedule (`schedSumB`). -/
private theorem schedFactsB : pzB P20B = 325336 ∧
    (schedule P20B).all (fun it => match it with | .readW _ w => decide (0 < w) | _ => true) = true ∧
    capAgreeB P20B = true := by
  have h : schedSumB P20B (schedule P20B) = (56000, true, true) := by
    rw [schedule_P20B_litA]; decide +kernel
  have h1 := expandBytes_eq P20B
  have h2 := schedSumB_snd P20B (schedule P20B)
  rw [h] at h1 h2
  simp only [Prod.mk.injEq] at h2
  refine ⟨?_, h2.1.symm, h2.2.symm⟩
  rw [pzB, sizes_P20B.1.1, h1]
  rfl

/-- **S2GB's expanded size** [exact, decide]: `269,336 + 32 · 7 · (115 + 77 + 58) = 325,336`. -/
theorem pzB_P20B : pzB P20B = 325336 := schedFactsB.1

/-- Every `readW` item of the S2GB schedule has a positive width. -/
theorem readWPos_P20B :
    (schedule P20B).all (fun it => match it with | .readW _ w => decide (0 < w) | _ => true) = true :=
  schedFactsB.2.1

/-- **`capOfB_agree`** (RE-FREEZE R3 (d)): at `P20B`, a cap item `.cap c r` sends `2^capOfB` nodes of `r`'s shape
(`capSendBits r.lv c = capOfB`), and an opening of `r` is at `r`'s shape's height with `capOfB` its sent cap. -/
theorem capOfB_agree :
    ∀ it ∈ schedule P20B, match it with
      | .cap c r => Lvm.ASM.capOfB (Lvm.VEq.shpS (Lvm.VEq.idxS r)).1 (Lvm.VEq.shpS (Lvm.VEq.idxS r)).2 =
          P20B.capSendBits r.lv c
      | .opening r => (Lvm.VEq.shpS (Lvm.VEq.idxS r)).1 = (P20B.level r).height ∧
          Lvm.ASM.capOfB (Lvm.VEq.shpS (Lvm.VEq.idxS r)).1 (Lvm.VEq.shpS (Lvm.VEq.idxS r)).2 =
            P20B.capSendBits r.lv (P20B.level r).cap
      | _ => True := by
  intro it hit
  have h := List.all_eq_true.mp schedFactsB.2.2 it hit
  cases it with
  | cap c r => simpa [capAgreeB] using h
  | opening r => simpa only [Bool.and_eq_true, beq_iff_eq] using h
  | _ => trivial

/-- Every read width at S2GB is positive. -/
theorem rwB20_pos : ∀ n, 0 < rwB20 n := fun n ↦ by
  have h := readWidthsP_all_ofL P20B (fun w ↦ decide (0 < w)) (by decide) readWPos_P20B
  unfold rwB20
  rw [List.getD_eq_getElem?_getD]
  cases hn : (readWidthsP P20B)[n]? with
  | none => exact Nat.zero_lt_succ _
  | some w => exact of_decide_eq_true (List.all_eq_true.mp h w (List.mem_of_getElem? hn))

end Lvm


namespace Lvm.CT

open Lvm Lvm.ASM

/-- **S2GB's format**: `rwB20`, the expanded size `pzB P20B`, header `headerBytesP P20B`, S2GU's occupied words. -/
def fmtB20 : SFmt := ⟨rwB20, rwB20_pos, pzB P20B, headerBytesP P20B, occOfU⟩

end Lvm.CT

namespace Lvm.E2S

open RecursionFast Lvm Lvm.T Lvm.ASM Lvm.CT Lvm.E2F Lvm.E2U Lvm.E2L Lvm.E2T Lvm.Typed
open LeanVM.Protocol.Compile
open Lvm.M3 (Tab mbLinB)

/-- **The typed phases with the mini-bus GKR at depth `d`** (`typedProgL`'s body; `typedProgL` is depth
`miniDepth = 12`). -/
def typedProgLB (d : ℕ) (Ti : TInst) (pub : Lvm.Pub) : VerifierProgram OpenClaims :=
  zeroProgT >>= fun z ↦ wireProgT Ti pub z.2 >>= fun w ↦ relayProgT Ti w.1 (w.2.2.getD 1 0) >>= fun r ↦
    accProgT Ti.Q Ti.lay true (accYT pub) (accPtT pub) (z.1 ++ w.1) w.2.1 >>= fun _ ↦
      miniBusLProg Ti.mbT d >>= fun cl ↦ pure (typedClaimsL Ti w.1 w.2.2 r.1 r.2 cl)

/-- **S2GB's middle phases**: S2GS's (`midGS`) with the mini-bus at depth 13 (`busDepth` of `P20B`) and the tape over
`contIvSB aSP`. -/
def midGB (Ti : TInst) (x : List UInt8) : VerifierProgram OpenClaims :=
  typedProgLB 13 Ti (pubXTS x) >>= fun a ↦ tapeProgL (contIvSB aSP) (Lvm.VEq.hdX x).s (Lvm.VEq.pubX x).n >>= fun k ↦
    pure (assembleU₂ x a k)

end Lvm.E2S

namespace Lvm.VEq

open RecursionFast Lvm LeanVM.Protocol.Compile

section IvpB

variable (cap : ℕ → ℕ → ℕ) (occ : ℕ → ℕ → ℕ) (shp : ℕ → ℕ × ℕ) (pth hq : ℕ → ℕ) (rw : ℕ → ℕ)

/-- **A program read off the S2GB stream** (`ivpW` with the opening's path `pth i` and its `hq i` heap entries of 104
bytes after the paths; a commit reads `2^cap` nodes). At `pth i = (shp i).1 − cap …` and `hq = 0` it is `ivpW`. -/
def ivpWB {α : Type} : VerifierProgram α → ByteArray → RS → ℕ → Option α × RS × ℕ
  | .ret a, _, s, i => (some a, s, i)
  | .fail, _, s, i => (none, s, i)
  | .grind _ _, _, s, i => (none, s, i)
  | .read k, sig, s, i =>
    ivpWB (k (Lvm.FS.eOfBytes (sbs sig (s.ent + 40 + s.msg) (rw i)))) sig
      { s with msg := s.msg + rw i } (i + 1)
  | .sample k, sig, s, i =>
    ivpWB (k (Lvm.FS.chalOf (digestAt sig (s.ent + 40 + s.msg)))) sig
      { s with ent := s.ent + 72 + s.msg, msg := 0 } i
  | .commit ht w k, sig, s, i => ivpWB k sig { s with msg := s.msg + 32 * 2 ^ cap ht w } i
  | .query i' ps k, sig, s, i =>
    let r := opRows sig (shp i').2 (occ (shp i').1 (shp i').2) (pth i') ps.length s.ent
    ivpWB (k r.1) sig { s with ent := r.2 + 104 * hq i' } i

/-- **`d` refines `P` on the S2GB stream under the promise `Q`** (`RefAtPW` with `ivpWB`). -/
def RefAtPWB {α β : Type} (sig : ByteArray) (i : ℕ) (d : DM β) (P : VerifierProgram α) (R : β → α → Prop)
    (Q : β → Prop) (j : ℕ) : Prop :=
  ∀ s, (runD d sig s).2.ok = true → Q (runD d sig s).1 →
    ∃ a, (ivpWB cap occ shp pth hq rw P sig s i).1 = some a ∧
      (ivpWB cap occ shp pth hq rw P sig s i).2.1.ent = (runD d sig s).2.ent ∧
      (ivpWB cap occ shp pth hq rw P sig s i).2.1.msg = (runD d sig s).2.msg ∧
      (ivpWB cap occ shp pth hq rw P sig s i).2.2 = j ∧ R (runD d sig s).1 a

end IvpB

/-- **The S2GB paths**: commitment `i` climbs `D = height − capS` levels inline (S2GS's path). -/
def pthB (i : ℕ) : ℕ := (shpS i).1 - capS (shpS i).1 (shpS i).2

/-- **The S2GB heap entries** of commitment `i`'s opening: `2^capS − 2^capOfB` (`Params.heapQ`). -/
def hqB (i : ℕ) : ℕ := 2 ^ capS (shpS i).1 (shpS i).2 - 2 ^ Lvm.ASM.capOfB (shpS i).1 (shpS i).2

end Lvm.VEq

namespace Lvm.E2T

open Lvm Lvm.Typed

/-- **`TRefHypT` at S2GB** (RE-FREEZE R3 (a)): the mini-bus record fits `P20B` (`busDepth` 13, 888 table columns). -/
structure TRefHypTB (N : TNatT) (Q : Lvm.Loop.Program) (lay : Lay) : Prop where
  /-- The shape check the closed forms rely on. -/
  ok : N.toN.okB P20.nuMain P20.nuRec = true
  /-- The native regions are the layout's. -/
  hlay : N.toN.layOk lay = true
  /-- The record is the S2GB mini-bus's. -/
  mini : Lvm.TypedV.fitsMiniB P20B N.mbT = true
  /-- Every mini-bus table takes part in the table sumcheck. -/
  sc : Lvm.M3.AllSc N.mbT
  /-- V_S's `Φ_Q` at `E2` is the specification's at `45` coordinates. -/
  phiT : ∀ pt : List FE2, pt.length = phiVarsT → N.phiT pt = PhiQFT Q lay pt

end Lvm.E2T
