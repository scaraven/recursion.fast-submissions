-- lvm6 X7b (X6b §4 item 2): the descent's fold loaders. A straight-line kit (`sIR`: constants, register
-- operations, `K` products, heap loads, run on a functional register file); the `E2` fold of a position-major
-- word (`foldIR`, one `loopK`, 7 `K` products a lane); the loader of a round's folded word (`ldF`, register-
-- addressed through a table, X7a's interface) meeting `LoadOkB`. New.
import Lvm6XDescLoad
import Lvm6FDNw

/-!
# Fold loaders

* **`sIR os`**, **`sIR_sem`**: a list of straight-line operations (`SOp`: `cst`, `op`, `mul` = `mulKC`, `ld`) runs
  as the pure `sRun` on the registers `< 4` and `≥ 9` (the field scratch `5 … 8` and `cTmp` are not tracked);
  the heap is kept.
* **`foldIR h m inB outB chA`**: for `k < 2^(h+m)`, position `x = k >> m`, `c = α + β·ptK x`
  (`α`, `β` the `E2` values at `chA`, `chA + 2`): `out[k] = in[2k+1] + c · in[2k]` (`E2` values, two words each,
  `in` lanes at `inB + 2i`, `out` at `outB + 2k`). **`foldIR_sem`**; **`foldIR_holds`**: on a position-major word
  (`HoldsW`: lane `u` of position `p` at `buf + 2(p·2^m + ⟨u⟩)`), the output is W1's `foldQ (domE h) α β`.
  Exact cost `cost_foldIR`: `42 + 2^(h+m) · 152`; size `sizeIR_foldIR = 196`.
* **`ldF tb B ℓ`**: round `r` (register 248), `K`-lane `q` (register 249): the table at `tb + 2r` gives the base
  and the row stride of round `r`'s word, then `2^ℓ` words `base + occ·p + q` to `yA B ℓ`. **`ldF_ok`**: X7a's
  obligation `LoadOkB I (.seq (.blk [.const 248 r, .const 249 q]) (ldF tb B ℓ)) ℓ B M₀ (ysF M₀ tb r q)`;
  **`ysF_coord`**: on a `HoldsW` buffer (`occ = 2^(m+1)`) the lane values are `basisE2.coord (q % 2)` of lane
  `q / 2`. **`ldF_part`**: `PartOk … ldCap`, `AllBelow 248`.
-/

set_option autoImplicit false

namespace Lvm6.X

open RecursionFast Lvm.X Lvm.Nb Lvm6.FD Finset Lvm6.Whir LeanVM.Parameters LeanVM.Protocol.Whir

attribute [local irreducible] entryK storeM

/-! ## The straight-line kit -/

/-- The registers the kit tracks: the constants and every register from `9`. -/
def Trk (r : ℕ) : Prop := r < regs ∧ (r < 4 ∨ 9 ≤ r)

/-- A straight-line operation. -/
inductive SOp where
  | cst (d : ℕ) (w : Word)
  | op (o : XOp) (d a b : ℕ)
  | mul (d a b : ℕ)
  | ld (d a : ℕ)

namespace SOp

/-- The operation as `XIR`. -/
def ir : SOp → XIR
  | cst d w => .blk [.const d w]
  | op o d a b => .blk [.op o d a b]
  | mul d a b => .blk (mulKC d a b)
  | ld d a => .load d a

/-- Its registers are tracked. -/
def Ok : SOp → Prop
  | cst d _ => 9 ≤ d ∧ d < regs
  | op _ d a b => 9 ≤ d ∧ d < regs ∧ Trk a ∧ Trk b
  | mul d a b => 9 ≤ d ∧ d < regs ∧ 9 ≤ a ∧ 9 ≤ b ∧ a < regs ∧ b < regs
  | ld d a => 9 ≤ d ∧ d < regs ∧ Trk a

/-- One operation on the register file `f`, the heap read through `H`. -/
def step (H : ℕ → Word) (f : ℕ → Word) : SOp → ℕ → Word
  | cst d w => Function.update f d w
  | op o d a b => Function.update f d (o.eval (f a) (f b))
  | mul d a b => Function.update f d (mulKW (f a) (f b))
  | ld d a => Function.update f d (H (f a).toNat)

/-- A load reads the heap. -/
def LdOk (f : ℕ → Word) : SOp → Prop
  | ld _ a => regs ≤ (f a).toNat
  | _ => True

end SOp

/-- The operations in order. -/
def sIR : List SOp → XIR
  | [] => .blk []
  | o :: os => .seq o.ir (sIR os)

/-- The pure run on the register file. -/
def sRun (H : ℕ → Word) : List SOp → (ℕ → Word) → ℕ → Word
  | [], f => f
  | o :: os, f => sRun H os (o.step H f)

/-- Every load of the run reads the heap. -/
def sLd (H : ℕ → Word) : List SOp → (ℕ → Word) → Prop
  | [], _ => True
  | o :: os, f => o.LdOk f ∧ sLd H os (o.step H f)

theorem sOp_sem (I : Array Word) (s : St) (hM : Inv s.M) (o : SOp) (ho : o.Ok) (H f : ℕ → Word)
    (hf : ∀ r, Trk r → rd s.M r = f r) (hH : ∀ x, regs ≤ x → rd s.M x = H x) (hl : o.LdOk f) :
    (∀ r, Trk r → rd (semXIR I o.ir s).M r = o.step H f r) ∧
      (∀ x, regs ≤ x → rd (semXIR I o.ir s).M x = rd s.M x) ∧ Inv (semXIR I o.ir s).M ∧
      (semXIR I o.ir s).o = s.o := by
  have hs : regs ≤ s.M.size := hM.1
  cases o with
  | cst d w =>
    obtain ⟨h1, h2⟩ := ho
    refine ⟨fun r hr ↦ ?_, fun x hx ↦ ?_, inv_sem I (P := .blk [.const d w]) (by
      simp only [WF, List.mem_cons, List.mem_nil_iff, or_false, forall_eq, Prim.dst]; omega) hM, rfl⟩
    · rw [show semXIR I (SOp.cst d w).ir s = ⟨(Prim.const d w).run s.M, s.o⟩ from rfl]
      simp only [Prim.run, SOp.step, rd_set, Function.update_apply]
      by_cases e : r = d
      · subst e; simp [show r < s.M.size by omega]
      · rw [if_neg (by omega), if_neg e, hf r hr]
    · rw [show semXIR I (SOp.cst d w).ir s = ⟨(Prim.const d w).run s.M, s.o⟩ from rfl]
      exact rd_set_ne (by omega)
  | op o d a b =>
    obtain ⟨h1, h2, ha, hb⟩ := ho
    refine ⟨fun r hr ↦ ?_, fun x hx ↦ ?_, inv_sem I (P := .blk [.op o d a b]) (by
      simp only [WF, List.mem_cons, List.mem_nil_iff, or_false, forall_eq, Prim.dst]; omega) hM, rfl⟩
    · rw [show semXIR I (SOp.op o d a b).ir s = ⟨(Prim.op o d a b).run s.M, s.o⟩ from rfl]
      simp only [Prim.run, SOp.step, rd_set, Function.update_apply, hf a ha, hf b hb]
      by_cases e : r = d
      · subst e; simp [show r < s.M.size by omega]
      · rw [if_neg (by omega), if_neg e, hf r hr]
    · rw [show semXIR I (SOp.op o d a b).ir s = ⟨(Prim.op o d a b).run s.M, s.o⟩ from rfl]
      exact rd_set_ne (by omega)
  | mul d a b =>
    obtain ⟨h1, h2, ha, hb, ha', hb'⟩ := ho
    have hI : Inv (runPrims (mulKC d a b) s.M) := mulKC_inv d a b (by omega) hM
    rw [show semXIR I (SOp.mul d a b).ir s = ⟨runPrims (mulKC d a b) s.M, s.o⟩ from rfl]
    dsimp only
    refine ⟨fun r hr ↦ ?_, fun x hx ↦ ?_, hI, rfl⟩
    · simp only [SOp.step, Function.update_apply]
      by_cases e : r = d
      · subst e
        rw [if_pos rfl, mulKC_run hM h1 h2 ha hb, hf a ⟨ha', Or.inr ha⟩, hf b ⟨hb', Or.inr hb⟩]
      · rw [if_neg e, mulKC_frame d a b (by rcases hr.2 with h | h <;> omega) e, hf r hr]
    · exact mulKC_frame d a b (by simp only [regs] at hx; omega) (by omega) s.M
  | ld d a =>
    obtain ⟨h1, h2, ha⟩ := ho
    have hI : Inv (s.M.setIfInBounds d (rd s.M (rd s.M a).toNat)) :=
      inv_sem I (P := .load d a) (by simp only [WF]; omega) hM
    rw [show semXIR I (SOp.ld d a).ir s = ⟨s.M.setIfInBounds d (rd s.M (rd s.M a).toNat), s.o⟩ from rfl]
    dsimp only
    refine ⟨fun r hr ↦ ?_, fun x hx ↦ ?_, hI, rfl⟩
    · simp only [SOp.step, rd_set, Function.update_apply, hf a ha]
      by_cases e' : r = d
      · subst e'
        simp only [SOp.LdOk] at hl
        simp [show r < s.M.size by omega, hH _ hl]
      · rw [if_neg (by omega), if_neg e', hf r hr]
    · exact rd_set_ne (by omega)

/-- **The kit on the machine.** -/
theorem sIR_sem (I : Array Word) (H : ℕ → Word) :
    ∀ (os : List SOp) (s : St) (f : ℕ → Word), Inv s.M → (∀ o ∈ os, o.Ok) →
      (∀ r, Trk r → rd s.M r = f r) → (∀ x, regs ≤ x → rd s.M x = H x) → sLd H os f →
      (∀ r, Trk r → rd (semXIR I (sIR os) s).M r = sRun H os f r) ∧
        (∀ x, regs ≤ x → rd (semXIR I (sIR os) s).M x = rd s.M x) ∧ Inv (semXIR I (sIR os) s).M ∧
        (semXIR I (sIR os) s).o = s.o
  | [], s, f, hM, _, hf, _, _ => ⟨fun r hr ↦ hf r hr, fun _ _ ↦ rfl, hM, rfl⟩
  | o :: os, s, f, hM, hok, hf, hH, hl => by
    obtain ⟨a1, a2, a3, a4⟩ := sOp_sem I s hM o (hok o List.mem_cons_self) H f hf hH hl.1
    obtain ⟨b1, b2, b3, b4⟩ := sIR_sem I H os (semXIR I o.ir s) (o.step H f) a3
      (fun o' ho' ↦ hok o' (List.mem_cons_of_mem _ ho')) a1 (fun x hx ↦ (a2 x hx).trans (hH x hx)) hl.2
    refine ⟨fun r hr ↦ b1 r hr, fun x hx ↦ (b2 x hx).trans (a2 x hx), b3, b4.trans a4⟩

theorem size_sIR (I : Array Word) (os : List SOp) (s : St) : (semXIR I (sIR os) s).M.size = s.M.size :=
  size_sem I _ s

/-- The kit's cost: one step per operation (13 per product), one per `seq`, one for the end. -/
def sCost : List SOp → ℕ
  | [] => 1
  | .mul .. :: os => 14 + sCost os
  | _ :: os => 2 + sCost os

theorem cost_sIR : ∀ (os : List SOp) (t : ℕ), cost (sIR os) t = sCost os
  | [], _ => rfl
  | .cst .. :: os, t => by simp only [sIR, SOp.ir, cost, blkSteps, cost_sIR os t, sCost]; simp; omega
  | .op .. :: os, t => by simp only [sIR, SOp.ir, cost, blkSteps, cost_sIR os t, sCost]; simp; omega
  | .mul .. :: os, t => by simp only [sIR, SOp.ir, cost, blkSteps, len_mulKC, cost_sIR os t, sCost]; simp; omega
  | .ld .. :: os, t => by simp only [sIR, SOp.ir, cost, cost_sIR os t, sCost]; omega

/-- The kit's size. -/
def sSize : List SOp → ℕ
  | [] => 1
  | .mul .. :: os => 14 + sSize os
  | _ :: os => 2 + sSize os

theorem sizeIR_sIR : ∀ os : List SOp, sizeIR (sIR os) = sSize os
  | [] => rfl
  | .cst .. :: os => by simp only [sIR, SOp.ir, sizeIR, blkSteps, sizeIR_sIR os, sSize]; simp; omega
  | .op .. :: os => by simp only [sIR, SOp.ir, sizeIR, blkSteps, sizeIR_sIR os, sSize]; simp; omega
  | .mul .. :: os => by simp only [sIR, SOp.ir, sizeIR, blkSteps, len_mulKC, sizeIR_sIR os, sSize]; simp; omega
  | .ld .. :: os => by simp only [sIR, SOp.ir, sizeIR, sizeIR_sIR os, sSize]; omega

theorem noLoopT_sIR : ∀ os : List SOp, NoLoopT (sIR os)
  | [] => trivial
  | o :: os => ⟨by cases o <;> trivial, noLoopT_sIR os⟩

theorem outs_sIR : ∀ (os : List SOp) (t : ℕ), outs (sIR os) t = 0
  | [], _ => rfl
  | o :: os, t => by cases o <;> simp [sIR, SOp.ir, outs, outs_sIR os t]

/-- The destination. -/
def SOp.dst : SOp → ℕ
  | .cst d _ => d
  | .op _ d _ _ => d
  | .mul d _ _ => d
  | .ld d _ => d

/-- A product (it also writes the scratch `5 … 8`). -/
def SOp.isMul : SOp → Prop
  | .mul .. => True
  | _ => False

/-- The cells an operation names. -/
def SOp.Wr (o : SOp) (r : ℕ) : Prop := r = o.dst ∨ (o.isMul ∧ 5 ≤ r ∧ r < 9)

theorem writes_sIR_iff : ∀ (os : List SOp) (r : ℕ), Writes (sIR os) r ↔ ∃ o ∈ os, o.Wr r
  | [], r => by simp [sIR, Writes]
  | o :: os, r => by
    rw [sIR, Writes, writes_sIR_iff os r]
    simp only [List.mem_cons, or_and_right, exists_or, exists_eq_left]
    apply or_congr_left
    cases o with
    | cst d w => simp [SOp.ir, Writes, Prim.dst, SOp.Wr, SOp.dst, SOp.isMul, eq_comm]
    | op o d a b => simp [SOp.ir, Writes, Prim.dst, SOp.Wr, SOp.dst, SOp.isMul, eq_comm]
    | ld d a => simp [SOp.ir, Writes, SOp.Wr, SOp.dst, SOp.isMul]
    | mul d a b =>
      simp only [SOp.ir, Writes, SOp.Wr, SOp.dst, SOp.isMul, true_and]
      constructor
      · rintro ⟨p, hp, rfl⟩
        rcases mulKC_dst d a b p hp with h | h
        · exact Or.inl h
        · exact Or.inr h
      · rintro (rfl | ⟨h5, h9⟩)
        · exact ⟨.op .xor r 7 8, by simp [mulKC, redC], rfl⟩
        · simp only [mulKC, redC, List.cons_append, List.nil_append, List.mem_cons, List.mem_nil_iff,
            or_false, exists_eq_or_imp, Prim.dst, exists_eq_left]
          omega

theorem wf_sIR : ∀ os : List SOp, (∀ o ∈ os, o.Ok) → WF (sIR os)
  | [], _ => by simp [sIR, WF]
  | o :: os, h => by
    refine ⟨?_, wf_sIR os fun o' ho' ↦ h o' (List.mem_cons_of_mem _ ho')⟩
    have ho := h o List.mem_cons_self
    cases o with
    | cst d w =>
      have := ho.1
      simp only [SOp.ir, WF, List.mem_cons, List.mem_nil_iff, or_false, forall_eq, Prim.dst]
      omega
    | op o d a b =>
      have := ho.1
      simp only [SOp.ir, WF, List.mem_cons, List.mem_nil_iff, or_false, forall_eq, Prim.dst]
      omega
    | ld d a =>
      have := ho.1
      simp only [SOp.ir, WF]
      omega
    | mul d a b =>
      have := ho.1
      intro p hp
      rcases mulKC_dst d a b p hp with h' | h' <;> omega

theorem allBelow_sIR {b : ℕ} (hb : 9 ≤ b) : ∀ os : List SOp, (∀ o ∈ os, SOp.dst o < b) →
    AllBelow b (sIR os)
  | [], _ => by simp [sIR, AllBelow]
  | o :: os, h => by
    refine ⟨?_, allBelow_sIR hb os fun o' ho' ↦ h o' (List.mem_cons_of_mem _ ho')⟩
    have ho := h o List.mem_cons_self
    cases o with
    | cst d w => simpa [SOp.ir, AllBelow, Prim.dst, SOp.dst] using ho
    | op o d a b => simpa [SOp.ir, AllBelow, Prim.dst, SOp.dst] using ho
    | ld d a => simpa [SOp.ir, AllBelow, SOp.dst] using ho
    | mul d a b =>
      intro p hp
      simp only [SOp.dst] at ho
      rcases mulKC_dst d a b p hp with h' | h' <;> omega

/-! ## `E2` values on the machine -/

/-- The `E2` value in cells `a`, `a + 1` (`re`, `im`). -/
def rdE2 (M : Mem) (a : ℕ) : E2 := ⟨rdK M a, rdK M (a + 1)⟩

/-- **A position-major word**: lane `u` of position `p` at `buf + 2 (p·2^m + ⟨u⟩)`. -/
def HoldsW (M : Mem) (buf h m : ℕ) (W : Wd E2 (2 ^ h) m) : Prop :=
  ∀ (p : Fin (2 ^ h)) (u : Fin m → Bool), rdE2 M (buf + 2 * (p * 2 ^ m + bitsToNat u)) = W u p

/-! ## The fold program -/

/-- Fold registers. -/ def fC : ℕ := 210
/-- A fold register. -/ def fNn : ℕ := 211
/-- A fold register. -/ def fK : ℕ := 212
/-- A fold register. -/ def fP : ℕ := 213
/-- A fold register. -/ def fQ : ℕ := 214
/-- A fold register. -/ def fM : ℕ := 215
/-- A fold register. -/ def fX : ℕ := 216
/-- A fold register. -/ def fA0 : ℕ := 217
/-- A fold register. -/ def fA1 : ℕ := 218
/-- A fold register. -/ def fB0 : ℕ := 219
/-- A fold register. -/ def fB1 : ℕ := 220
/-- A fold register. -/ def fT : ℕ := 221
/-- A fold register. -/ def fa0 : ℕ := 222
/-- A fold register. -/ def fa1 : ℕ := 223
/-- A fold register. -/ def fb0 : ℕ := 224
/-- A fold register. -/ def fb1 : ℕ := 225
/-- A fold register. -/ def fc0 : ℕ := 226
/-- A fold register. -/ def fc1 : ℕ := 227
/-- A fold register. -/ def ft0 : ℕ := 228
/-- A fold register. -/ def ft1 : ℕ := 229
/-- A fold register. -/ def ft2 : ℕ := 230
/-- A fold register. -/ def ft3 : ℕ := 231
/-- A fold register. -/ def ft4 : ℕ := 232
/-- A fold register. -/ def fG : ℕ := 233
/-- A fold register. -/ def fV : ℕ := 234
/-- A fold register. -/ def fW : ℕ := 235
/-- A fold register. -/ def f4 : ℕ := 236
/-- A fold register. -/ def f2 : ℕ := 237
/-- A fold register. -/ def fQ1 : ℕ := 238

/-- The prologue: pointers, constants, the challenges `α` (`fA0`, `fA1`) and `β` (`fB0`, `fB1`). -/
def foldPro (m inB outB chA K : ℕ) : List SOp :=
  [.cst fP (toWord inB), .cst fQ (toWord outB), .cst fK (toWord 0), .cst fM (toWord m), .cst fG (toWord 2), .cst f4 (toWord 4), .cst f2 (toWord 2),
    .cst fNn (toWord K), .cst fT (toWord chA), .ld fA0 fT, .op .add fT fT cOne, .ld fA1 fT, .op .add fT fT cOne,
    .ld fB0 fT, .op .add fT fT cOne, .ld fB1 fT]

/-- One position-lane: the loads, `x = k >> m`, `c = α + βx`, `out = b + c·a` (7 products). -/
def foldPre : List SOp :=
  [.ld fa0 fP, .op .add fT fP cOne, .ld fa1 fT, .op .add fT fT cOne, .ld fb0 fT, .op .add fT fT cOne, .ld fb1 fT,
    .op .shr fX fK fM, .mul fc0 fB0 fX, .op .xor fc0 fc0 fA0, .mul fc1 fB1 fX, .op .xor fc1 fc1 fA1,
    .mul ft0 fc0 fa0, .mul ft1 fc1 fa1, .mul ft2 fc0 fa1, .mul ft3 fc1 fa0, .mul ft4 fG ft1,
    .op .xor fV ft0 ft1, .op .xor fV fV fb0, .op .xor fW ft2 ft3, .op .xor fW fW ft4, .op .xor fW fW fb1,
    .op .add fQ1 fQ cOne]

/-- The pointer steps. -/
def foldPost : List SOp := [.op .add fP fP f4, .op .add fQ fQ f2, .op .add fK fK cOne]

/-- The loop body. -/
def foldBody : XIR := .seq (sIR foldPre) (.seq (.store fQ fV) (.seq (.store fQ1 fW) (sIR foldPost)))

/-- **The `E2` fold** of `2^(h+m)` output lanes. -/
def foldIR (h m inB outB chA : ℕ) : XIR :=
  .seq (sIR (foldPro m inB outB chA (2 ^ (h + m)))) (.loopK fC fNn (toWord (2 ^ (h + m))) foldBody)

/-! ## Structure, cost, size -/

theorem wf_foldIR (h m inB outB chA : ℕ) : WF (foldIR h m inB outB chA) := by
  refine ⟨wf_sIR _ ?_, ?_⟩
  · simp +decide [foldPro, SOp.Ok, Trk, regs, fP, fQ, fK, fM, fG, f4, f2, fNn, fT, fA0, fA1, fB0, fB1, cOne]
  · refine ⟨by decide, by decide, ?_, ?_⟩
    · simp only [foldBody, Writes, writes_sIR_iff, not_or, not_exists, not_and]
      refine ⟨?_, by decide, by decide, ?_⟩ <;>
        simp +decide [foldPre, foldPost, SOp.Wr, SOp.dst, SOp.isMul, fC, fP, fT, fa0, fa1, fb0, fb1,
          fX, fc0, fc1, ft0, ft1, ft2, ft3, ft4, fV, fW, fQ1, fQ, fK, cTmp]
    · refine ⟨wf_sIR _ ?_, (by simp only [WF]; decide), (by simp only [WF]; decide), wf_sIR _ ?_⟩
      · simp +decide [foldPre, SOp.Ok, Trk, regs, fP, fT, fa0, fa1, fb0, fb1, fX, fK, fM, fc0, fc1, fB0, fB1,
          fA0, fA1, ft0, ft1, ft2, ft3, ft4, fG, fV, fW, fQ1, fQ, cOne]
      · simp +decide [foldPost, SOp.Ok, Trk, regs, fP, fQ, fK, f4, f2, cOne]

theorem noLoopT_foldIR (h m inB outB chA : ℕ) : NoLoopT (foldIR h m inB outB chA) :=
  ⟨noLoopT_sIR _, noLoopT_sIR _, trivial, trivial, noLoopT_sIR _⟩

theorem outs_foldIR (h m inB outB chA t : ℕ) : outs (foldIR h m inB outB chA) t = 0 := by
  simp [foldIR, foldBody, outs, outs_sIR]

/-- **The fold's exact cost**: `42 + 2^(h+m) · 152` steps. -/
theorem cost_foldIR (h m inB outB chA t : ℕ) (hK : 2 ^ (h + m) < 2 ^ 64) :
    cost (foldIR h m inB outB chA) t = 42 + 2 ^ (h + m) * 152 := by
  simp only [foldIR, foldBody, cost, cost_sIR, toNat_toWord hK]
  simp only [foldPro, foldPre, foldPost, sCost]
  ring

theorem sizeIR_foldIR (h m inB outB chA : ℕ) : sizeIR (foldIR h m inB outB chA) = 196 := by
  simp only [foldIR, foldBody, sizeIR, sizeIR_sIR, foldPro, foldPre, foldPost, sSize]

theorem allBelow_foldIR (h m inB outB chA : ℕ) : AllBelow 248 (foldIR h m inB outB chA) := by
  refine ⟨allBelow_sIR (by norm_num) _ ?_, by decide, by decide, allBelow_sIR (by norm_num) _ ?_,
    (by simp only [AllBelow]; decide), (by simp only [AllBelow]; decide), allBelow_sIR (by norm_num) _ ?_⟩ <;>
  simp +decide [foldPro, foldPre, foldPost, SOp.dst, fP, fQ, fK, fM, fG, f4, f2, fNn, fT, fA0, fA1, fB0, fB1,
    fa0, fa1, fb0, fb1, fX, fc0, fc1, ft0, ft1, ft2, ft3, ft4, fV, fW, fQ1]

/-! ## The fold's semantics -/

/-- **The fold's value at output lane `k`**: `in[2k+1] + (α + β·ptK (k >> m)) · in[2k]`. -/
def foldV (M : Mem) (inB chA m k : ℕ) : E2 :=
  rdE2 M (inB + 4 * k + 2) + (rdE2 M chA + rdE2 M (chA + 2) * algebraMap K E2 (ptK (k / 2 ^ m))) *
    rdE2 M (inB + 4 * k)

/-- The machine's words compute the fold's `E2` components. -/
theorem foldArith (a0 a1 b0 b1 α0 α1 β0 β1 x gw : Word) (hg : wK gw = g) :
    wK ((mulKW (mulKW β0 x ^^^ α0) a0 ^^^ mulKW (mulKW β1 x ^^^ α1) a1) ^^^ b0) =
        ((⟨wK b0, wK b1⟩ : E2) + (⟨wK α0, wK α1⟩ + ⟨wK β0, wK β1⟩ * algebraMap K E2 (wK x)) *
          ⟨wK a0, wK a1⟩).re ∧
      wK (((mulKW (mulKW β0 x ^^^ α0) a1 ^^^ mulKW (mulKW β1 x ^^^ α1) a0) ^^^
          mulKW gw (mulKW (mulKW β1 x ^^^ α1) a1)) ^^^ b1) =
        ((⟨wK b0, wK b1⟩ : E2) + (⟨wK α0, wK α1⟩ + ⟨wK β0, wK β1⟩ * algebraMap K E2 (wK x)) *
          ⟨wK a0, wK a1⟩).im := by
  simp only [wK_xor, mulKW_spec, hg, QuadraticAlgebra.re_add, QuadraticAlgebra.im_add, QuadraticAlgebra.re_mul,
    QuadraticAlgebra.im_mul, QuadraticAlgebra.algebraMap_re, QuadraticAlgebra.algebraMap_im]
  constructor <;> ring

/-- The registers the position-lane step writes. -/
def preDst : List ℕ := [fa0, fT, fa1, fb0, fb1, fX, fc0, fc1, ft0, ft1, ft2, ft3, ft4, fV, fW, fQ1]

/-- **The position-lane step, pure.** -/
theorem foldPre_run (H f : ℕ → Word) {P Q j m : ℕ} (hP : f fP = toWord P) (hQ : f fQ = toWord Q)
    (hK : f fK = toWord j) (hMm : f fM = toWord m) (h1 : f cOne = 1) (hP2 : P + 3 < 2 ^ 64)
    (hQ2 : Q + 1 < 2 ^ 64) (hj : j < 2 ^ 64) (hm : m < 64) (hPr : regs ≤ P) :
    sLd H foldPre f ∧
    sRun H foldPre f fV = (mulKW (mulKW (f fB0) (toWord (j / 2 ^ m)) ^^^ f fA0) (H P) ^^^
        mulKW (mulKW (f fB1) (toWord (j / 2 ^ m)) ^^^ f fA1) (H (P + 1))) ^^^ H (P + 2) ∧
    sRun H foldPre f fW = ((mulKW (mulKW (f fB0) (toWord (j / 2 ^ m)) ^^^ f fA0) (H (P + 1)) ^^^
        mulKW (mulKW (f fB1) (toWord (j / 2 ^ m)) ^^^ f fA1) (H P)) ^^^
        mulKW (f fG) (mulKW (mulKW (f fB1) (toWord (j / 2 ^ m)) ^^^ f fA1) (H (P + 1)))) ^^^ H (P + 3) ∧
    sRun H foldPre f fQ1 = toWord (Q + 1) ∧
    ∀ r, r ∉ preDst → sRun H foldPre f r = f r := by
  have e1 : XOp.add.eval (toWord P) 1 = toWord (P + 1) := add_one_toWord P
  have e2 : XOp.add.eval (toWord (P + 1)) 1 = toWord (P + 2) := add_one_toWord (P + 1)
  have e3 : XOp.add.eval (toWord (P + 2)) 1 = toWord (P + 3) := add_one_toWord (P + 2)
  have e4 : XOp.add.eval (toWord Q) 1 = toWord (Q + 1) := add_one_toWord Q
  have e5 : XOp.shr.eval (toWord j) (toWord m) = toWord (j / 2 ^ m) := shr_toWord hj hm
  have t0 : (toWord P).toNat = P := toNat_toWord (by omega)
  have t1 : (toWord (P + 1)).toNat = P + 1 := toNat_toWord (by omega)
  have t2 : (toWord (P + 2)).toNat = P + 2 := toNat_toWord (by omega)
  have t3 : (toWord (P + 3)).toNat = P + 3 := toNat_toWord (by omega)
  simp only [regs] at hPr
  replace hP : f 213 = toWord P := hP
  replace hQ : f 214 = toWord Q := hQ
  replace hK : f 212 = toWord j := hK
  replace hMm : f 215 = toWord m := hMm
  replace h1 : f 0 = 1 := h1
  refine ⟨?_, ?_, ?_, ?_, fun r hr ↦ ?_⟩
  · simp only [↓reduceIte, Nat.reduceEqDiff, sLd, foldPre, SOp.LdOk, SOp.step, Function.update_apply, fa0, fT,
      fa1, fb0, fb1, fX, fK, fM, fc0, fc1, fB0, fB1, fA0, fA1, ft0, ft1, ft2, ft3, ft4, fG, fV, fW, fQ1, fQ, fP,
      cOne, regs, hP, h1, e1, e2, e3, t0, t1, t2, t3]
    simp
    omega
  rotate_left 3
  · simp only [preDst, fa0, fT, fa1, fb0, fb1, fX, fc0, fc1, ft0, ft1, ft2, ft3, ft4, fV, fW, fQ1,
      List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    obtain ⟨n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11, n12, n13, n14, n15, n16⟩ := hr
    simp [sRun, foldPre, SOp.step, Function.update_apply, fa0, fT, fa1, fb0, fb1, fX, fc0, fc1, ft0, ft1, ft2,
      ft3, ft4, fV, fW, fQ1, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11, n12, n13, n14, n15, n16]
  all_goals simp only [↓reduceIte, Nat.reduceEqDiff, sRun, foldPre, SOp.step, Function.update_apply, fa0, fT,
      fa1, fb0, fb1, fX, fK, fM, fc0, fc1, fB0, fB1, fA0, fA1, ft0, ft1, ft2, ft3, ft4, fG, fV, fW, fQ1, fQ, fP,
      cOne, hP, hQ, hK, hMm, h1, e1, e2, e3, e4, e5, t0, t1, t2, t3, eval_xor]

theorem hasOut_sIR : ∀ os : List SOp, hasOut (sIR os) = false
  | [] => rfl
  | o :: os => by cases o <;> simp [sIR, SOp.ir, hasOut, hasOut_sIR os]

/-- The registers the prologue writes. -/
def proDst : List ℕ := [fP, fQ, fK, fM, fG, f4, f2, fNn, fT, fA0, fA1, fB0, fB1]

/-- **The prologue, pure.** -/
theorem foldPro_run (H f : ℕ → Word) {m inB outB chA K : ℕ} (h1 : f 0 = 1) (hc2 : chA + 3 < 2 ^ 64)
    (hcr : regs ≤ chA) :
    sLd H (foldPro m inB outB chA K) f ∧
    sRun H (foldPro m inB outB chA K) f fP = toWord inB ∧
    sRun H (foldPro m inB outB chA K) f fQ = toWord outB ∧
    sRun H (foldPro m inB outB chA K) f fK = toWord 0 ∧
    sRun H (foldPro m inB outB chA K) f fM = toWord m ∧
    sRun H (foldPro m inB outB chA K) f fG = toWord 2 ∧
    sRun H (foldPro m inB outB chA K) f f4 = toWord 4 ∧
    sRun H (foldPro m inB outB chA K) f f2 = toWord 2 ∧
    sRun H (foldPro m inB outB chA K) f fNn = toWord K ∧
    sRun H (foldPro m inB outB chA K) f fA0 = H chA ∧
    sRun H (foldPro m inB outB chA K) f fA1 = H (chA + 1) ∧
    sRun H (foldPro m inB outB chA K) f fB0 = H (chA + 2) ∧
    sRun H (foldPro m inB outB chA K) f fB1 = H (chA + 3) ∧
    ∀ r, r ∉ proDst → sRun H (foldPro m inB outB chA K) f r = f r := by
  have e1 : XOp.add.eval (toWord chA) 1 = toWord (chA + 1) := add_one_toWord chA
  have e2 : XOp.add.eval (toWord (chA + 1)) 1 = toWord (chA + 2) := add_one_toWord (chA + 1)
  have e3 : XOp.add.eval (toWord (chA + 2)) 1 = toWord (chA + 3) := add_one_toWord (chA + 2)
  have t0 : (toWord chA).toNat = chA := toNat_toWord (by omega)
  have t1 : (toWord (chA + 1)).toNat = chA + 1 := toNat_toWord (by omega)
  have t2 : (toWord (chA + 2)).toNat = chA + 2 := toNat_toWord (by omega)
  have t3 : (toWord (chA + 3)).toNat = chA + 3 := toNat_toWord (by omega)
  simp only [regs] at hcr
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun r hr ↦ ?_⟩
  · simp only [↓reduceIte, Nat.reduceEqDiff, sLd, foldPro, SOp.LdOk, SOp.step, Function.update_apply, fP, fQ,
      fK, fM, fG, f4, f2, fNn, fT, fA0, fA1, fB0, fB1, cOne, regs, h1, e1, e2, e3, t0, t1, t2, t3]
    simp
    omega
  rotate_left 12
  · simp only [proDst, fP, fQ, fK, fM, fG, f4, f2, fNn, fT, fA0, fA1, fB0, fB1,
      List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    obtain ⟨n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11, n12, n13⟩ := hr
    simp [sRun, foldPro, SOp.step, Function.update_apply, fP, fQ, fK, fM, fG, f4, f2, fNn, fT, fA0, fA1, fB0,
      fB1, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11, n12, n13]
  all_goals simp only [↓reduceIte, Nat.reduceEqDiff, sRun, foldPro, SOp.step, Function.update_apply, fP, fQ,
      fK, fM, fG, f4, f2, fNn, fT, fA0, fA1, fB0, fB1, cOne, h1, e1, e2, e3, t0, t1, t2, t3]

/-- **The pointer steps, pure.** -/
theorem foldPost_run (H f : ℕ → Word) {P Q j : ℕ} (hP : f fP = toWord P) (hQ : f fQ = toWord Q)
    (hK : f fK = toWord j) (h4 : f f4 = toWord 4) (h2 : f f2 = toWord 2) (h1 : f 0 = 1) :
    sLd H foldPost f ∧ sRun H foldPost f fP = toWord (P + 4) ∧ sRun H foldPost f fQ = toWord (Q + 2) ∧
      sRun H foldPost f fK = toWord (j + 1) ∧
      ∀ r, r ≠ fP → r ≠ fQ → r ≠ fK → sRun H foldPost f r = f r := by
  replace hP : f 213 = toWord P := hP
  replace hQ : f 214 = toWord Q := hQ
  replace hK : f 212 = toWord j := hK
  replace h4 : f 236 = toWord 4 := h4
  replace h2 : f 237 = toWord 2 := h2
  have e1 := add_toWord P 4
  have e2 := add_toWord Q 2
  have e3 := add_one_toWord j
  refine ⟨by simp [sLd, foldPost, SOp.LdOk], ?_, ?_, ?_, fun r r1 r2 r3 ↦ ?_⟩
  · simp only [↓reduceIte, Nat.reduceEqDiff, sRun, foldPost, SOp.step, Function.update_apply, fP, fQ, fK, f4,
      f2, cOne, hP, hQ, hK, h4, h2, h1, e1, e2, e3]
  · simp only [↓reduceIte, Nat.reduceEqDiff, sRun, foldPost, SOp.step, Function.update_apply, fP, fQ, fK, f4,
      f2, cOne, hP, hQ, hK, h4, h2, h1, e1, e2, e3]
  · simp only [↓reduceIte, Nat.reduceEqDiff, sRun, foldPost, SOp.step, Function.update_apply, fP, fQ, fK, f4,
      f2, cOne, hP, hQ, hK, h4, h2, h1, e1, e2, e3]
  · simp only [fP, fQ, fK] at r1 r2 r3
    simp [sRun, foldPost, SOp.step, Function.update_apply, fP, fQ, fK, r1, r2, r3]

theorem ok_foldPro (m inB outB chA K : ℕ) : ∀ o ∈ foldPro m inB outB chA K, o.Ok := by
  simp +decide [foldPro, SOp.Ok, Trk, regs, fP, fQ, fK, fM, fG, f4, f2, fNn, fT, fA0, fA1, fB0, fB1, cOne]

theorem ok_foldPre : ∀ o ∈ foldPre, o.Ok := by
  simp +decide [foldPre, SOp.Ok, Trk, regs, fP, fT, fa0, fa1, fb0, fb1, fX, fK, fM, fc0, fc1, fB0, fB1,
    fA0, fA1, ft0, ft1, ft2, ft3, ft4, fG, fV, fW, fQ1, fQ, cOne]

theorem ok_foldPost : ∀ o ∈ foldPost, o.Ok := by
  simp +decide [foldPost, SOp.Ok, Trk, regs, fP, fQ, fK, f4, f2, cOne]

/-- The registers the loop keeps from the prologue. -/
def keepL : List ℕ := [fM, fG, f4, f2, fA0, fA1, fB0, fB1]

theorem trk_of_mem {r : ℕ} (h : r ∈ keepL) : Trk r := by
  simp only [keepL, fM, fG, f4, f2, fA0, fA1, fB0, fB1, List.mem_cons, List.not_mem_nil, or_false] at h
  simp only [Trk, regs]; omega

/-- **The fold on the machine**: output lane `k` is `foldV` of the input heap; the heap outside the output is
kept. -/
theorem foldIR_sem (I : Array Word) (s : St) (hM : Inv s.M) {h m inB outB chA : ℕ} (hm : m < 64)
    (hin : regs ≤ inB) (hin2 : inB + 4 * 2 ^ (h + m) < 2 ^ 64) (hch : regs ≤ chA) (hch2 : chA + 4 < 2 ^ 64)
    (hout : regs ≤ outB) (hout2 : outB + 2 * 2 ^ (h + m) < 2 ^ 64) (hsz : outB + 2 * 2 ^ (h + m) ≤ s.M.size)
    (hdi : inB + 4 * 2 ^ (h + m) ≤ outB ∨ outB + 2 * 2 ^ (h + m) ≤ inB)
    (hdc : chA + 4 ≤ outB ∨ outB + 2 * 2 ^ (h + m) ≤ chA) :
    (∀ k < 2 ^ (h + m), rdE2 (semXIR I (foldIR h m inB outB chA) s).M (outB + 2 * k) =
        foldV s.M inB chA m k) ∧
      (∀ x, regs ≤ x → (x < outB ∨ outB + 2 * 2 ^ (h + m) ≤ x) →
        rd (semXIR I (foldIR h m inB outB chA) s).M x = rd s.M x) ∧
      Inv (semXIR I (foldIR h m inB outB chA) s).M ∧ (semXIR I (foldIR h m inB outB chA) s).o = s.o := by
  set K := 2 ^ (h + m) with hKdef
  have hK : K < 2 ^ 64 := by omega
  have hs := hM.1
  have c1 : rd s.M 0 = 1 := hM.2 0 (by decide)
  simp only [regs] at hin hch hout hs
  suffices H : (∀ k < K, rdE2 (semXIR I (foldIR h m inB outB chA) s).M (outB + 2 * k) =
        foldV s.M inB chA m k) ∧
      (∀ x, regs ≤ x → (x < outB ∨ outB + 2 * K ≤ x) →
        rd (semXIR I (foldIR h m inB outB chA) s).M x = rd s.M x) ∧
      Inv (semXIR I (foldIR h m inB outB chA) s).M by
    exact ⟨H.1, H.2.1, H.2.2, sem_o I _ s (by simp [foldIR, foldBody, hasOut, hasOut_sIR])⟩
  rw [foldIR, semXIR_seq]
  · 
    obtain ⟨p1, p2, p3, -⟩ := sIR_sem I (rd s.M) (foldPro m inB outB chA K) s (rd s.M) hM (ok_foldPro m inB outB chA K)
      (fun _ _ ↦ rfl) (fun _ _ ↦ rfl) (foldPro_run (m := m) (inB := inB) (outB := outB) (chA := chA) (K := K) (rd s.M) (rd s.M) c1 (by omega) (by simp only [regs]; omega)).1
    obtain ⟨-, v1, v2, v3, v4, v5, v6, v7, v8, v9, v10, v11, v12, -⟩ :=
      foldPro_run (K := K) (inB := inB) (outB := outB) (m := m) (chA := chA) (rd s.M) (rd s.M) c1 (by omega)
        (by simp only [regs]; omega)
    have z0 := size_sIR I (foldPro m inB outB chA K) s
    generalize semXIR I (sIR (foldPro m inB outB chA K)) s = s0 at p1 p2 p3 z0
    have q : ∀ r, Trk r → rd s0.M r = sRun (rd s.M) (foldPro m inB outB chA K) (rd s.M) r := p1
    have hTrk : ∀ r, r < regs → 9 ≤ r → Trk r := fun r h1 h2 ↦ ⟨h1, Or.inr h2⟩
    -- the loop invariant
    let Pinv : ℕ → St → Prop := fun j s' ↦ Inv s'.M ∧ s'.M.size = s.M.size ∧
      rd s'.M fP = toWord (inB + 4 * j) ∧ rd s'.M fQ = toWord (outB + 2 * j) ∧ rd s'.M fK = toWord j ∧
      (∀ r ∈ keepL, rd s'.M r = rd s0.M r) ∧
      (∀ k < j, rdE2 s'.M (outB + 2 * k) = foldV s.M inB chA m k) ∧
      (∀ x, regs ≤ x → (x < outB ∨ outB + 2 * j ≤ x) → rd s'.M x = rd s.M x)
    have hE : ∀ i, i ≠ fC → i ≠ cTmp → rd (entryK fC fNn (toWord K) s0.M) i = rd s0.M i :=
      fun i h1 h2 ↦ entryK_frame _ (Ne.symm h1) (Ne.symm h2)
    have h0 : Pinv 0 ⟨entryK fC fNn (toWord K) s0.M, s0.o⟩ := by
      refine ⟨inv_entryK p3 (by decide), by simp only [size_entryK, z0], ?_, ?_, ?_, fun r hr ↦ ?_,
        fun k hk ↦ absurd hk (Nat.not_lt_zero _), fun x hx _ ↦ ?_⟩ <;> dsimp only
      · rw [hE _ (by decide) (by decide), q _ (hTrk _ (by decide) (by decide)), v1, Nat.mul_zero, Nat.add_zero]
      · rw [hE _ (by decide) (by decide), q _ (hTrk _ (by decide) (by decide)), v2, Nat.mul_zero, Nat.add_zero]
      · rw [hE _ (by decide) (by decide), q _ (hTrk _ (by decide) (by decide)), v3]
      · have := trk_of_mem hr
        rw [hE _ (by simp only [keepL, fM, fG, f4, f2, fA0, fA1, fB0, fB1, List.mem_cons, List.not_mem_nil,
          or_false] at hr; simp only [fC]; omega) (by simp only [Trk, cTmp] at this ⊢; omega)]
      · simp only [regs] at hx
        rw [hE _ (by simp only [fC]; omega) (by simp only [cTmp]; omega), p2 x (by simp only [regs]; omega)]
    have hstep : ∀ j s', j < K → Pinv j s' → Pinv (j + 1) (decS fC (semXIR I foldBody s')) := by
      rintro j s' hj ⟨i1, i2, i3, i4, i5, i6, i7, i8⟩
      have hs' := i1.1
      have k4 : ∀ r ∈ keepL, rd s'.M r = sRun (rd s.M) (foldPro m inB outB chA K) (rd s.M) r :=
        fun r hr ↦ (i6 r hr).trans (q r (trk_of_mem hr))
      have hjK : j + 1 ≤ K := hj
      have hPj : inB + 4 * j + 3 < inB + 4 * K := by omega
      have hQj : outB + 2 * j + 1 < outB + 2 * K := by omega
      obtain ⟨pr0, pr1, pr2, pr3, pr4⟩ := foldPre_run (rd s'.M) (rd s'.M) i3 i4 i5
        ((k4 fM (by simp [keepL])).trans v4) (i1.2 0 (by decide)) (by omega) (by omega) (by omega) hm
        (by simp only [regs]; omega)
      rw [foldBody, semXIR_seq]
      obtain ⟨a1, a2, a3, -⟩ := sIR_sem I (rd s'.M) foldPre s' (rd s'.M) i1 ok_foldPre (fun _ _ ↦ rfl)
        (fun _ _ ↦ rfl) pr0
      have z1 := size_sIR I foldPre s'
      generalize semXIR I (sIR foldPre) s' = s1 at a1 a2 a3 z1
      have nP : ∀ r, Trk r → r ∉ preDst → rd s1.M r = rd s'.M r := fun r hr hn ↦ (a1 r hr).trans (pr4 r hn)
      -- the stores
      rw [semXIR_seq]
      obtain ⟨c1, c2, hM2⟩ := store_sem I s1 a3 (p := fQ) (v := fV) (x := outB + 2 * j) (by decide) (by decide)
        ((nP _ (hTrk _ (by decide) (by decide)) (by decide)).trans i4) (by simp only [regs]; omega) (by omega)
        (by omega)
      have z2 := size_sem I (.store fQ fV) s1
      generalize semXIR I (.store fQ fV) s1 = s2 at c1 c2 hM2 z2
      have hr2 : ∀ r, r < regs → rd s2.M r = if r = cTmp then rd s2.M r else rd s1.M r := fun r hr ↦ by
        split
        · rfl
        · exact c2 r (by simp only [regs] at hr; omega) (by assumption)
      rw [semXIR_seq]
      obtain ⟨d1, d2, hM3⟩ := store_sem I s2 hM2 (p := fQ1) (v := fW) (x := outB + 2 * j + 1) (by decide)
        (by decide) (by rw [c2 _ (by simp only [fQ1]; omega) (by decide), a1 _ (hTrk _ (by decide) (by decide)),
          pr3]) (by simp only [regs]; omega) (by omega) (by omega)
      have z3 := size_sem I (.store fQ1 fW) s2
      generalize semXIR I (.store fQ1 fW) s2 = s3 at d1 d2 hM3 z3
      -- registers of `s3`
      have r3 : ∀ r, Trk r → r ≠ cTmp → rd s3.M r = rd s1.M r := fun r hr hc ↦ by
        rw [d2 r (by simp only [Trk, regs] at hr; omega) hc, c2 r (by simp only [Trk, regs] at hr; omega) hc]
      obtain ⟨po0, po1, po2, po3, po4⟩ := foldPost_run (rd s3.M) (rd s3.M) (P := inB + 4 * j)
        (Q := outB + 2 * j) (j := j)
        (by rw [r3 _ (hTrk _ (by decide) (by decide)) (by decide), nP _ (hTrk _ (by decide) (by decide))
          (by decide), i3])
        (by rw [r3 _ (hTrk _ (by decide) (by decide)) (by decide), nP _ (hTrk _ (by decide) (by decide))
          (by decide), i4])
        (by rw [r3 _ (hTrk _ (by decide) (by decide)) (by decide), nP _ (hTrk _ (by decide) (by decide))
          (by decide), i5])
        (by rw [r3 _ (hTrk _ (by decide) (by decide)) (by decide), nP _ (hTrk _ (by decide) (by decide))
          (by decide), k4 f4 (by simp [keepL]), v6])
        (by rw [r3 _ (hTrk _ (by decide) (by decide)) (by decide), nP _ (hTrk _ (by decide) (by decide))
          (by decide), k4 f2 (by simp [keepL]), v7])
        (hM3.2 0 (by decide))
      obtain ⟨e1, e2, e3, -⟩ := sIR_sem I (rd s3.M) foldPost s3 (rd s3.M) hM3 ok_foldPost (fun _ _ ↦ rfl)
        (fun _ _ ↦ rfl) po0
      have z4 := size_sIR I foldPost s3
      generalize semXIR I (sIR foldPost) s3 = s4 at e1 e2 e3 z4
      have hd : ∀ x, x ≠ fC → rd (decS fC s4).M x = rd s4.M x := fun x hx ↦ rd_decS (Ne.symm hx) _
      -- the heap after the body
      have hH : ∀ x, regs ≤ x → x ≠ outB + 2 * j → x ≠ outB + 2 * j + 1 →
          rd (decS fC s4).M x = rd s'.M x := fun x hx h1 h2 ↦ by
        simp only [regs] at hx
        rw [hd x (by simp only [fC]; omega), e2 x (by simp only [regs]; omega),
          d2 x h2 (by simp only [cTmp]; omega), c2 x h1 (by simp only [cTmp]; omega), a2 x (by simp only [regs]; omega)]
      have v0 : rd (decS fC s4).M (outB + 2 * j) = rd s1.M fV := by
        rw [hd _ (by simp only [fC]; omega), e2 _ (by simp only [regs]; omega),
          d2 _ (by omega) (by simp only [cTmp]; omega), c1]
      have w0 : rd (decS fC s4).M (outB + 2 * j + 1) = rd s1.M fW := by
        rw [hd _ (by simp only [fC]; omega), e2 _ (by simp only [regs]; omega), d1,
          c2 _ (by simp only [fW]; omega) (by decide)]
      have hin' : ∀ i < 4, rd s'.M (inB + 4 * j + i) = rd s.M (inB + 4 * j + i) := fun i hi ↦
        i8 _ (by simp only [regs]; omega) (by omega)
      refine ⟨inv_decS e3 (by decide), by rw [size_decS, z4, z3, z2, z1, i2], ?_, ?_, ?_, fun r hr ↦ ?_,
        fun k hk ↦ ?_, fun x hx hx' ↦ ?_⟩
      · rw [hd _ (by decide), e1 _ (hTrk _ (by decide) (by decide)), po1]; congr 1
      · rw [hd _ (by decide), e1 _ (hTrk _ (by decide) (by decide)), po2]; congr 1
      · rw [hd _ (by decide), e1 _ (hTrk _ (by decide) (by decide)), po3]
      · have ht := trk_of_mem hr
        simp only [keepL, fM, fG, f4, f2, fA0, fA1, fB0, fB1, List.mem_cons, List.not_mem_nil, or_false] at hr
        rw [hd _ (by simp only [fC]; omega), e1 _ ht, po4 _ (by simp only [fP]; omega) (by simp only [fQ]; omega)
          (by simp only [fK]; omega), r3 _ ht (by simp only [cTmp]; omega), nP _ ht (by
            simp only [preDst, fa0, fT, fa1, fb0, fb1, fX, fc0, fc1, ft0, ft1, ft2, ft3, ft4, fV, fW, fQ1,
              List.mem_cons, List.not_mem_nil, or_false]; omega), i6 r (by
            simp only [keepL, fM, fG, f4, f2, fA0, fA1, fB0, fB1, List.mem_cons, List.not_mem_nil, or_false]
            omega)]
      · rcases Nat.lt_succ_iff_lt_or_eq.1 hk with hk | rfl
        · have h1 := i7 k hk
          simp only [rdE2, rdK] at h1 ⊢
          rw [hH _ (by simp only [regs]; omega) (by omega) (by omega),
            hH _ (by simp only [regs]; omega) (by omega) (by omega), h1]
        · simp only [rdE2, rdK]
          rw [v0, w0, a1 _ (hTrk _ (by decide) (by decide)), a1 _ (hTrk _ (by decide) (by decide)), pr1, pr2]
          have g0 := k4 fA0 (by simp [keepL])
          have g1 := k4 fA1 (by simp [keepL])
          have g2 := k4 fB0 (by simp [keepL])
          have g3 := k4 fB1 (by simp [keepL])
          have g4 := k4 fG (by simp [keepL])
          rw [v9] at g0; rw [v10] at g1; rw [v11] at g2; rw [v12] at g3; rw [v5] at g4
          rw [g0, g1, g2, g3, g4]
          have x0 := hin' 0 (by norm_num)
          have x1 := hin' 1 (by norm_num)
          have x2 := hin' 2 (by norm_num)
          have x3 := hin' 3 (by norm_num)
          simp only [Nat.add_zero] at x0
          rw [x0, x1, x2, x3]
          obtain ⟨f1, f2⟩ := foldArith (rd s.M (inB + 4 * k)) (rd s.M (inB + 4 * k + 1))
            (rd s.M (inB + 4 * k + 2)) (rd s.M (inB + 4 * k + 3)) (rd s.M chA) (rd s.M (chA + 1))
            (rd s.M (chA + 2)) (rd s.M (chA + 3)) (toWord (k / 2 ^ m)) (toWord 2) rfl
          rw [f1, f2]
          rfl
      · rw [hH x hx (by omega) (by omega), i8 x hx (by omega)]
    have hfin := loopK_run I foldBody Pinv s0 p3 (c := fC) (n := fNn) (K := K) (by decide) (by decide)
      (by decide) ((q _ (hTrk _ (by decide) (by decide))).trans v8) hK h0 hstep
    obtain ⟨f1, -, -, -, -, -, f7, f8⟩ := hfin
    exact ⟨f7, fun x hx hx' ↦ f8 x hx hx', f1⟩


/-! ## The loader of a round's folded word (X7a's interface: round in register 248, lane in 249) -/

/-- A loader register. -/ def lT : ℕ := 239
/-- A loader register. -/ def lU : ℕ := 240
/-- X7a's round register. -/ def xR : ℕ := 248
/-- X7a's lane register. -/ def xQ : ℕ := 249

/-- The loader's prologue: `lU := M[tb + 2r]` (base), `yStr := M[tb + 2r + 1]` (row stride), `ySr := base + q`,
`yDs := yA B ℓ`. -/
def ldPro (tb B ℓ : ℕ) : List SOp :=
  [.op .add lT xR xR, .cst lU (toWord tb), .op .add lT lT lU, .ld lU lT, .op .add lT lT cOne, .ld yStr lT,
    .op .add ySr lU xQ, .cst yDs (toWord (yA B ℓ))]

/-- **The loader** of `K`-lane `q` of round `r`'s word: `2^ℓ` words `base + q + occ·p`. -/
def ldF (tb B ℓ : ℕ) : XIR := .seq (sIR (ldPro tb B ℓ)) (mcpLoop (2 ^ ℓ))

/-- Round `r`'s word base in the table at `tb`. -/
def tbBase (M : Mem) (tb r : ℕ) : ℕ := (rd M (tb + 2 * r)).toNat
/-- Round `r`'s row stride in the table at `tb`. -/
def tbOcc (M : Mem) (tb r : ℕ) : ℕ := (rd M (tb + 2 * r + 1)).toNat

/-- **The lane values the loader writes**: word `q` of every row of round `r`'s word. -/
def ysF (M₀ : Mem) (tb r q p : ℕ) : BF64 := rdK M₀ (tbBase M₀ tb r + q + tbOcc M₀ tb r * p)

theorem toWord_toNat (w : Word) : toWord w.toNat = w := BitVec.eq_of_toNat_eq (toNat_toWord w.isLt)

/-- The registers the loader's prologue writes. -/
def ldDst : List ℕ := [lT, lU, yStr, ySr, yDs]

/-- **The loader's prologue, pure.** -/
theorem ldPro_run (H f : ℕ → Word) {tb B ℓ r q : ℕ} (hR : f xR = toWord r) (hQ : f xQ = toWord q)
    (h1 : f 0 = 1) (htb : regs ≤ tb) (h64 : tb + 2 * r + 2 < 2 ^ 64) :
    sLd H (ldPro tb B ℓ) f ∧ sRun H (ldPro tb B ℓ) f ySr = toWord ((H (tb + 2 * r)).toNat + q) ∧
      sRun H (ldPro tb B ℓ) f yStr = toWord (H (tb + 2 * r + 1)).toNat ∧
      sRun H (ldPro tb B ℓ) f yDs = toWord (yA B ℓ) := by
  replace hR : f 248 = toWord r := hR
  replace hQ : f 249 = toWord q := hQ
  have e1 : XOp.add.eval (toWord r) (toWord r) = toWord (2 * r) := by
    rw [add_toWord]; congr 1; omega
  have e2 : XOp.add.eval (toWord (2 * r)) (toWord tb) = toWord (tb + 2 * r) := by
    rw [add_toWord]; congr 1; omega
  have e3 : XOp.add.eval (toWord (tb + 2 * r)) 1 = toWord (tb + 2 * r + 1) := add_one_toWord _
  have e4 : XOp.add.eval (H (tb + 2 * r)) (toWord q) = toWord ((H (tb + 2 * r)).toNat + q) := by
    conv_lhs => rw [← toWord_toNat (H (tb + 2 * r))]
    exact add_toWord _ _
  have t0 : (toWord (tb + 2 * r)).toNat = tb + 2 * r := toNat_toWord (by omega)
  have t1 : (toWord (tb + 2 * r + 1)).toNat = tb + 2 * r + 1 := toNat_toWord (by omega)
  simp only [regs] at htb
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp only [↓reduceIte, Nat.reduceEqDiff, sLd, ldPro, SOp.LdOk, SOp.step, Function.update_apply, lT, lU, xR,
      xQ, yStr, ySr, yDs, cOne, regs, hR, hQ, h1, e1, e2, e3, t0, t1]
    simp
    omega
  all_goals simp only [↓reduceIte, Nat.reduceEqDiff, sRun, ldPro, SOp.step, Function.update_apply, lT, lU, xR,
      xQ, yStr, ySr, yDs, cOne, hR, hQ, h1, e1, e2, e3, e4, t0, t1, toWord_toNat]

theorem ok_ldPro (tb B ℓ : ℕ) : ∀ o ∈ ldPro tb B ℓ, o.Ok := by
  simp +decide [ldPro, SOp.Ok, Trk, regs, lT, lU, xR, xQ, yStr, ySr, yDs, cOne]

theorem wf_mcpLoop (n : ℕ) : WF (mcpLoop n) := by
  simp +decide [mcpLoop, mcpBody, WF, Writes, Prim.dst, ySr, yDs, yStr, yV, yC, yN, cTmp, regs]

theorem wf_ldF (tb B ℓ : ℕ) : WF (ldF tb B ℓ) := ⟨wf_sIR _ (ok_ldPro tb B ℓ), wf_mcpLoop _⟩

theorem noLoopT_ldF (tb B ℓ : ℕ) : NoLoopT (ldF tb B ℓ) :=
  ⟨noLoopT_sIR _, by simp [mcpLoop, mcpBody, NoLoopT]⟩

theorem outs_ldF (tb B ℓ t : ℕ) : outs (ldF tb B ℓ) t = 0 := by
  simp [ldF, outs, outs_sIR, mcpLoop, mcpBody]

theorem hasOut_ldF (tb B ℓ : ℕ) : hasOut (ldF tb B ℓ) = false := by
  simp [ldF, hasOut, hasOut_sIR, mcpLoop, mcpBody]

/-- **The loader's exact cost**: `28 + 13·2^ℓ`. -/
theorem cost_ldF (tb B ℓ t : ℕ) (hℓ : 2 ^ ℓ < 2 ^ 64) : cost (ldF tb B ℓ) t = 28 + 13 * 2 ^ ℓ := by
  simp only [ldF, cost, cost_sIR, ldPro, sCost, mcpLoop, mcpBody, blkSteps, List.length_cons, List.length_nil,
    toNat_toWord hℓ]
  norm_num; ring

theorem sizeIR_ldF (tb B ℓ : ℕ) : sizeIR (ldF tb B ℓ) = 42 := by
  simp only [ldF, sizeIR, sizeIR_sIR, ldPro, sSize, mcpLoop, mcpBody, blkSteps, List.length_cons,
    List.length_nil]
  norm_num

theorem allBelow_ldF (tb B ℓ : ℕ) : AllBelow 248 (ldF tb B ℓ) := by
  refine ⟨allBelow_sIR (by norm_num) _ ?_, ?_⟩
  · simp +decide [ldPro, SOp.dst, lT, lU, yStr, ySr, yDs]
  · simp +decide [mcpLoop, mcpBody, AllBelow, Prim.dst, ySr, yDs, yV, yC, yN, cTmp]

/-- **The loader is a part within `ldCap`** (`ℓ ≤ 21`). -/
theorem ldF_part (tb B : ℕ) {ℓ : ℕ} (hℓ : ℓ ≤ 21) : PartOk (ldF tb B ℓ) ldCap where
  wf := wf_ldF ..
  noLoopT := noLoopT_ldF ..
  outs t := outs_ldF _ _ _ t
  cost t := by
    have hp : 2 ^ ℓ ≤ 2 ^ 21 := Nat.pow_le_pow_right (by norm_num) hℓ
    rw [cost_ldF _ _ _ t (lt_of_le_of_lt hp (by norm_num)), ldCap]
    omega

/-- **X7a's loader obligation**: with round `r` and lane `q` in registers 248, 249, `ldF` meets `LoadOkB` with
the lane values `ysF M₀ tb r q`, when the table entry and the rows it names lie in the heap below `B`. -/
theorem ldF_ok (I : Array Word) {tb B ℓ r q : ℕ} (M₀ : Mem) (htb : regs ≤ tb) (htb2 : tb + 2 * r + 2 ≤ B)
    (hocc : tbOcc M₀ tb r ≤ 4096) (hsr : regs ≤ tbBase M₀ tb r + q)
    (hsrc : ∀ p < 2 ^ ℓ, tbBase M₀ tb r + q + tbOcc M₀ tb r * p < B) (h64 : fdEnd B ℓ < 2 ^ 64) :
    LoadOkB I (.seq (.blk [.const 248 (toWord r), .const 249 (toWord q)]) (ldF tb B ℓ)) ℓ B M₀ (ysF M₀ tb r q) := by
  intro s hM hsz h0
  have hs := hM.1
  have eY : yA B ℓ = B + 4096 + 2 ^ ℓ := rfl
  have eE : fdEnd B ℓ = B + 4096 + 11 * 2 ^ ℓ := rfl
  simp only [regs] at hs htb hsr
  have hpos : 0 < 2 ^ ℓ := pow_pos (by norm_num) ℓ
  rw [semXIR_seq]
  -- the round and lane registers
  have w0 : WF (.blk [.const 248 (toWord r), .const 249 (toWord q)]) := by
    simp +decide [WF, Prim.dst]
  have hM0 := inv_sem I w0 hM
  have z0 := size_sem I (.blk [.const 248 (toWord r), .const 249 (toWord q)]) s
  have r0 : rd (semXIR I (.blk [.const 248 (toWord r), .const 249 (toWord q)]) s).M xR = toWord r ∧
      rd (semXIR I (.blk [.const 248 (toWord r), .const 249 (toWord q)]) s).M xQ = toWord q := by
    rw [sem_blk']; simp only [runPrims, List.foldl, Prim.run, xR, xQ]
    exact ⟨by rw [rd_set_ne (by decide), rd_set_self (by omega)], by rw [rd_set_self (by simp; omega)]⟩
  have k0 : ∀ x, regs ≤ x → rd (semXIR I (.blk [.const 248 (toWord r), .const 249 (toWord q)]) s).M x =
      rd s.M x := fun x hx ↦ rd_blk_of_not_dst I _ s (by simp only [regs] at hx; simp [Prim.dst]; omega)
  have o0 : (semXIR I (.blk [.const 248 (toWord r), .const 249 (toWord q)]) s).o = s.o := rfl
  generalize semXIR I (.blk [.const 248 (toWord r), .const 249 (toWord q)]) s = s0 at hM0 z0 r0 k0 o0
  have hB0 : ∀ x, regs ≤ x → x < B → rd s0.M x = rd M₀ x := fun x hx hxB ↦ (k0 x hx).trans (h0 x hx hxB)
  -- the prologue
  have eb : rd s0.M (tb + 2 * r) = rd M₀ (tb + 2 * r) := hB0 _ (by simp only [regs]; omega) (by omega)
  have eo : rd s0.M (tb + 2 * r + 1) = rd M₀ (tb + 2 * r + 1) := hB0 _ (by simp only [regs]; omega) (by omega)
  have hsrc0 := hsrc 0 hpos
  have hsrcL := hsrc (2 ^ ℓ - 1) (by omega)
  have hmul : tbOcc M₀ tb r * 2 ^ ℓ = tbOcc M₀ tb r * (2 ^ ℓ - 1) + tbOcc M₀ tb r := by
    rw [← Nat.mul_succ]; congr 1; omega
  obtain ⟨pr0, pr1, pr2, pr3⟩ := ldPro_run (tb := tb) (B := B) (ℓ := ℓ) (rd s0.M) (rd s0.M) r0.1 r0.2 (hM0.2 0 (by decide))
    (by simp only [regs]; omega) (by omega)
  rw [ldF, semXIR_seq]
  obtain ⟨a1, a2, a3, a4⟩ := sIR_sem I (rd s0.M) (ldPro tb B ℓ) s0 (rd s0.M) hM0 (ok_ldPro tb B ℓ)
    (fun _ _ ↦ rfl) (fun _ _ ↦ rfl) pr0
  have z1 := size_sIR I (ldPro tb B ℓ) s0
  generalize semXIR I (sIR (ldPro tb B ℓ)) s0 = s1 at a1 a2 a3 a4 z1
  rw [eb] at pr1; rw [eo] at pr2
  have hT : ∀ r, r < regs → 9 ≤ r → Trk r := fun r h1 h2 ↦ ⟨h1, Or.inr h2⟩
  obtain ⟨c1, c2, c3⟩ := mcpLoop_sem I s1 a3 (n := 2 ^ ℓ) (src := tbBase M₀ tb r + q) (str := tbOcc M₀ tb r)
    (dst := yA B ℓ) (by omega) (by omega) (by simp only [regs]; omega) (by omega) (by omega)
    (fun i hi ↦ Or.inl (by have := hsrc i hi; omega)) (fun i hi ↦ by simp only [regs]; omega)
    ((a1 _ (hT _ (by decide) (by decide))).trans pr1) ((a1 _ (hT _ (by decide) (by decide))).trans pr3)
    ((a1 _ (hT _ (by decide) (by decide))).trans pr2)
  refine ⟨fun j hj ↦ ?_, c3, ?_, fun x hx hx' ↦ ?_⟩
  · simp only [rdK, ysF]
    rw [c1 j hj, a2 _ (by have := hsrc j hj; simp only [regs]; omega), hB0 _ (by simp only [regs]; omega)
      (hsrc j hj)]
  · rw [sem_o I _ s1 (by simp [hasOut, mcpLoop, mcpBody]), a4, o0]
  · rw [c2 x (keepC_of_regs hx) hx', a2 x hx, k0 x hx]


/-! ## The fold and the loader on position-major words -/

theorem bitsToNat_cons' {m : ℕ} (b : Bool) (u : Fin m → Bool) :
    bitsToNat (Fin.cons b u : Fin (m + 1) → Bool) = b.toNat + 2 * bitsToNat u := by
  simp only [bitsToNat, Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ, Fin.val_zero, pow_zero,
    mul_one, Fin.val_succ, pow_succ, Finset.mul_sum]
  congr 1
  exact Finset.sum_congr rfl fun i _ ↦ by ring

/-- **The fold of a position-major word is W1's `foldQ`** (`domE h`, the challenges at `chA`, `chA + 2`). -/
theorem foldIR_holds (I : Array Word) (s : St) (hM : Inv s.M) {h m inB outB chA : ℕ} (hh : h ≤ 64)
    (hm : m < 64) (hin : regs ≤ inB) (hin2 : inB + 4 * 2 ^ (h + m) < 2 ^ 64) (hch : regs ≤ chA)
    (hch2 : chA + 4 < 2 ^ 64) (hout : regs ≤ outB) (hout2 : outB + 2 * 2 ^ (h + m) < 2 ^ 64)
    (hsz : outB + 2 * 2 ^ (h + m) ≤ s.M.size) (hdi : inB + 4 * 2 ^ (h + m) ≤ outB ∨ outB + 2 * 2 ^ (h + m) ≤ inB)
    (hdc : chA + 4 ≤ outB ∨ outB + 2 * 2 ^ (h + m) ≤ chA) {W : Wd E2 (2 ^ h) (m + 1)} {α β : E2}
    (hW : HoldsW s.M inB h (m + 1) W) (hα : rdE2 s.M chA = α) (hβ : rdE2 s.M (chA + 2) = β) :
    HoldsW (semXIR I (foldIR h m inB outB chA) s).M outB h m (foldQ (domE h hh) α β W) := by
  intro p u
  have hu := bitsToNat_lt u
  have hp := p.isLt
  have hk : (p : ℕ) * 2 ^ m + bitsToNat u < 2 ^ (h + m) := by
    rw [pow_add]
    have : ((p : ℕ) + 1) * 2 ^ m ≤ 2 ^ h * 2 ^ m := Nat.mul_le_mul_right _ hp
    rw [Nat.add_mul, one_mul] at this
    omega
  rw [(foldIR_sem I s hM hm hin hin2 hch hch2 hout hout2 hsz hdi hdc).1 _ hk, foldV, hα, hβ, foldQ]
  have h0 := hW p (Fin.cons false u)
  have h1 := hW p (Fin.cons true u)
  rw [bitsToNat_cons'] at h0 h1
  have e2 : 2 ^ (m + 1) = 2 * 2 ^ m := by rw [pow_succ]; ring
  rw [e2] at h0 h1
  have ediv : ((p : ℕ) * 2 ^ m + bitsToNat u) / 2 ^ m = p := by
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ (by positivity), Nat.div_eq_of_lt hu, Nat.zero_add]
  rw [ediv]
  simp only [Bool.toNat_false, Bool.toNat_true, Nat.zero_add] at h0 h1
  rw [show inB + 4 * ((p : ℕ) * 2 ^ m + bitsToNat u) = inB + 2 * (p * (2 * 2 ^ m) + 2 * bitsToNat u) by ring,
    show inB + 2 * ((p : ℕ) * (2 * 2 ^ m) + 2 * bitsToNat u) + 2 =
      inB + 2 * (p * (2 * 2 ^ m) + (1 + 2 * bitsToNat u)) by ring, h0, h1]
  rfl

theorem coord0_E2 (z : E2) : basisE2.coord 0 z = z.re := by
  simp [basisE2, Module.Basis.coord_apply]

theorem coord1_E2 (z : E2) : basisE2.coord 1 z = z.im := by
  simp [basisE2, Module.Basis.coord_apply]

/-- **The loader's lane values on a position-major word**: with round `r`'s table entry `(buf, 2^(m+1))`, lane
`2⟨u⟩ + i` at position `p` is component `i` of `W u p`. -/
theorem ysF_coord {M₀ : Mem} {tb r buf h m : ℕ} {W : Wd E2 (2 ^ h) m} (hW : HoldsW M₀ buf h m W)
    (hb : tbBase M₀ tb r = buf) (ho : tbOcc M₀ tb r = 2 * 2 ^ m) (u : Fin m → Bool) (p : Fin (2 ^ h)) :
    ysF M₀ tb r (2 * bitsToNat u) p = basisE2.coord 0 (W u p) ∧
      ysF M₀ tb r (2 * bitsToNat u + 1) p = basisE2.coord 1 (W u p) := by
  have h0 := hW p u
  rw [coord0_E2, coord1_E2, ← h0]
  simp only [ysF, hb, ho, rdE2]
  constructor
  · congr 1; ring
  · congr 1; ring

end Lvm6.X
