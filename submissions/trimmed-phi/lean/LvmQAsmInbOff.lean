/- `LvmQAsmInbOff` (GOLF2 off-path move, group 41 of 48): declarations that the certificate `certified`
   does not use, moved here verbatim (same names, same namespaces and context) from LvmQAsmInbCore, LvmQAsmInb,
   so that `Solution`'s import closure need not elaborate them. Import this module where they are needed;
   the name -> module map is GOLF2's moved.tsv. -/
import LvmQAsmInbCore
import LvmQAsmInb
import LvmMPCertOff
import LvmNodeSoundCircOff
import LvmNodeSoundTOff
import LvmQAsmHar47Off
import LvmQTypedHarZOff
import LvmJBMutual
import LvmMlListLemmas
import LvmQAsmHar47
import LvmSpecRulesCert

-- ===== from `LvmQAsmInbCore` =====

section
set_option autoImplicit false
namespace Lvm.Loop
open FE

theorem findExp_isSome {α : FK} {lo m k : Nat} (hk : k < 2 ^ m) (h : FK.x ^ (lo + k) = α) :
    (findExp α lo m).isSome = true := by
  unfold findExp
  rw [Option.isSome_map, List.find?_isSome]
  exact ⟨k, List.mem_range.2 hk, by simp [h]⟩

end Lvm.Loop
end

section
set_option autoImplicit false
namespace Lvm.Loop
open FE
namespace Program
variable (Q : Program)

/-- One step keeps `inb` when the instance's address is in region in a memory the state agrees
with below the clocks. -/
theorem step_inb_of (M : Mem) (s : St) (i : Inst) (hag : M.Agrees s.mem i.ck i.ce)
    (hok : InstOk Q i) (hin : RdIn M i) (hs : s.inb = true) : (Q.step s i).inb = true := by
  rcases hop : i.row.op with _ | ⟨k, k'⟩ | _ | _ | _ | ⟨lo, m⟩ <;>
    simp only [step, hop, St.put_inb] <;> try exact hs
  have ht := hok.typeOk
  simp only [Row.typeOk, hop, beq_iff_eq] at ht
  have hl : 0 < i.row.args.length := by
    have := congrArg List.length ht; simp at this; omega
  have hR : s.rd (i.row.args.getD 0 default).ty ((i.row.args.getD 0 default).at i.j) = M.arg i 0 := by
    have hlt := hok.reads _ (arg_mem hl)
    simp only [Inst.arg] at hlt
    rw [Inst.clock_eq_pick] at hlt
    rw [St.rd_eq_mem, Mem.arg]
    exact (Mem.rd_agree hag _ _ (by cases h : (i.row.args.getD 0 default).ty <;>
      simp only [h, Ty.pick] at hlt ⊢ <;> exact hlt)).symm
  simp only [RdIn, hop] at hin
  obtain ⟨k, hk, hx⟩ := hin
  rw [hR]
  obtain ⟨e, he⟩ := Option.isSome_iff_exists.mp (findExp_isSome hk hx)
  rw [he]
  simp only [St.put_inb]
  exact hs

/-- The fold keeps `inb` (WP-10's `fold_spec`, its agreement carried along). -/
theorem fold_inb (M : Mem) (hinj : GInj (max (Q.cells .K) (Q.cells .E))) :
    ∀ (L : List Inst) (s : St) (k e : Nat), Chain k e L → s.kc.size = k → s.ec.size = e →
      M.Agrees s.mem k e → (∀ i ∈ L, Q.RowDef M i ∧ InstOk Q i ∧ RdIn M i) → s.inb = true →
      (L.foldl Q.step s).inb = true
  | [], _, _, _, _, _, _, _, _, hs => hs
  | i :: L, s, k, e, ⟨hck, hce, hch⟩, hk, he, hag, hL, hs => by
    subst hck hce
    have hi := hL i (by simp)
    have h1 := Q.step_inb_of M s i hag hi.2.1 hi.2.2 hs
    obtain ⟨g1, g2, g3, -⟩ := Q.step_spec M s i hk he hag hi.1 hi.2.1 hinj h1
    exact fold_inb M hinj L (Q.step s i) _ _ hch g2 g3 g1 (fun j hj => hL j (by simp [hj])) h1

/-- **`inb` from a memory**: the inputs, every row relation, every `readd` address in its region. -/
theorem inb_of_mem (hwf : Q.wf = true) (inK : Array FK) (inE : Array FE)
    (hsz : inK.size = Q.nInK ∧ inE.size = Q.nInE) (M : Mem) (hin : Q.Inputs M inK inE)
    (hM : Q.Holds M) (hinj : GInj (max (Q.cells .K) (Q.cells .E)))
    (hR : ∀ i ∈ Q.insts, RdIn M i) : (Q.interp inK inE).inb = true := by
  obtain ⟨hch, -, -⟩ := Q.chain_insts
  exact Q.fold_inb M hinj Q.insts ⟨inK, inE, true, true⟩ Q.nInK Q.nInE hch hsz.1 hsz.2
    ⟨fun n hn => hin.1 n hn, fun n hn => hin.2 n hn⟩
    (fun i hi => ⟨hM i hi, Q.instOk_of_mem hwf hi, hR i hi⟩) rfl

end Program
end Lvm.Loop
end

section
set_option autoImplicit false
namespace Lvm.Loop
open FE
namespace Program
variable (Q : Program)

theorem foldl_kc : ∀ (L : List Inst) (s : St) (n : Nat), n < s.kc.size →
    (L.foldl Q.step s).kc.getD n 0 = s.kc.getD n 0
  | [], _, _, _ => rfl
  | i :: L, s, n, hn => by
    have hsz : n < (Q.step s i).kc.size ∧ (Q.step s i).kc.getD n 0 = s.kc.getD n 0 := by
      rcases Q.step_kc s i with h | ⟨v, h⟩
      · rw [h]; exact ⟨hn, rfl⟩
      · rw [h]; exact ⟨by simp; omega, getD_push_lt _ _ _ hn⟩
    rw [List.foldl_cons, foldl_kc L _ n hsz.1, hsz.2]

/-- **The interpreter's memory holds the `K` inputs** (with or without `inb`). -/
theorem interpMem_inK (inK : Array FK) (inE : Array FE) {n : Nat} (hn : n < inK.size) :
    (Q.interpMem inK inE).k n = inK.getD n 0 :=
  Q.foldl_kc Q.insts ⟨inK, inE, true, true⟩ n hn

end Program
end Lvm.Loop
end

section
set_option autoImplicit false
namespace Lvm.Loop
open FE
namespace Build

/-- Every instance of block `B` at `p` is in region. -/
def BlockIn (M : Mem) (p : Ptr) (B : Block) : Prop :=
  ∀ jf < B.size, ∀ t < B.tpl.length, RdIn M (instAt p B jf t)

/-- **Every `readd` of the segments `δ` at `p` is in region in `M`.** -/
def SegsIn (M : Mem) : Ptr → List Seg → Prop
  | _, [] => True
  | p, .row r :: δ => RdIn M (rowInst p r) ∧ SegsIn M (p.adv [.row r]) δ
  | p, .blk B :: δ => BlockIn M p B ∧ SegsIn M (p.adv [.blk B]) δ

theorem segsIn_append (M : Mem) : ∀ (p : Ptr) (δ₁ δ₂ : List Seg),
    SegsIn M p (δ₁ ++ δ₂) ↔ SegsIn M p δ₁ ∧ SegsIn M (p.adv δ₁) δ₂
  | p, [], δ₂ => by simp [SegsIn]
  | p, .row r :: δ₁, δ₂ => by
    simp only [List.cons_append, SegsIn]
    rw [segsIn_append M _ δ₁ δ₂, ← Ptr.adv_cons, and_assoc]
  | p, .blk B :: δ₁, δ₂ => by
    simp only [List.cons_append, SegsIn]
    rw [segsIn_append M _ δ₁ δ₂, ← Ptr.adv_cons, and_assoc]

theorem in_bind {α β : Type} (M : Mem) (m : BM α) (f : α → BM β) (p : Ptr) :
    SegsIn M p ((m >>= f) p).2 ↔
      SegsIn M p (m p).2 ∧ SegsIn M (p.adv (m p).2) (f (m p).1 (p.adv (m p).2)).2 := by
  rw [bind_apply]; exact segsIn_append M _ _ _

/-- Every block of `bs` is in region at its pointer. -/
def BlocksIn (M : Mem) : Ptr → List Block → Prop
  | _, [] => True
  | p, B :: bs => BlockIn M p B ∧ BlocksIn M (p.advBs [B]) bs

theorem blocksIn_iff (M : Mem) : ∀ (p : Ptr) (bs : List Block),
    BlocksIn M p bs ↔ ∀ b < bs.length, BlockIn M (p.advBs (bs.take b)) (bs.getD b default)
  | p, [] => by simp [BlocksIn]
  | p, B :: bs => by
    simp only [BlocksIn, blocksIn_iff M _ bs, List.length_cons]
    constructor
    · rintro ⟨h0, h⟩ b hb
      rcases b with _ | b
      · simpa [Ptr.advBs] using h0
      · have := h b (by omega)
        simpa [List.take_succ_cons, Ptr.advBs_cons p B (bs.take b)] using this
    · intro h
      refine ⟨by simpa [Ptr.advBs] using h 0 (by omega), fun b hb => ?_⟩
      have := h (b + 1) (by omega)
      simpa [List.take_succ_cons, Ptr.advBs_cons p B (bs.take b)] using this

theorem glueI_iff (M : Mem) : ∀ (p : Ptr) (rs : List Row),
    BlockIn M p ⟨[], rs⟩ ↔ SegsIn M p (rs.map .row)
  | p, [] => by simp [BlockIn, SegsIn]
  | p, r :: rs => by
    have ih := glueI_iff M (p.adv [.row r]) rs
    simp only [List.map_cons, SegsIn, ← ih, BlockIn, Block.size, Block.lsize, List.sum_nil,
      pow_zero, Nat.lt_one_iff, forall_eq, List.length_cons]
    constructor
    · intro h
      refine ⟨by simpa [instAt_glue_zero] using h 0 (by omega), fun t ht => ?_⟩
      have := h (t + 1) (by omega)
      rwa [instAt_glue_succ] at this
    · rintro ⟨h0, h⟩ t ht
      rcases t with _ | t
      · rw [instAt_glue_zero]; exact h0
      · rw [instAt_glue_succ]; exact h t (by omega)

theorem blocksIn_glueB (M : Mem) (p : Ptr) (rs : List Row) (bs : List Block) :
    BlocksIn M p (glueB rs bs) ↔ SegsIn M p (rs.map .row) ∧ BlocksIn M (p.adv (rs.map .row)) bs := by
  unfold glueB
  rcases rs with _ | ⟨r, rs⟩
  · simp [SegsIn]
  · simp only [List.isEmpty_cons, Bool.false_eq_true, ite_false, BlocksIn, glueI_iff, advBs_glue]

theorem groupAux_in (M : Mem) : ∀ (p : Ptr) (δ : List Seg),
    SegsIn M p δ ↔ SegsIn M p ((groupAux δ).1.map .row) ∧
      BlocksIn M (p.adv ((groupAux δ).1.map .row)) (groupAux δ).2
  | p, [] => by simp [SegsIn, BlocksIn, groupAux]
  | p, .row r :: δ => by
    rw [groupAux_row]
    split
    · simp only [SegsIn, List.map_cons, List.map_nil, and_true]
      rw [groupAux_in M _ δ, blocksIn_glueB]
    · simp only [SegsIn, List.map_cons]
      rw [groupAux_in M _ δ, Ptr.adv_cons p (.row r) ((groupAux δ).1.map .row), and_assoc]
  | p, .blk B :: δ => by
    rw [groupAux_blk]
    simp only [SegsIn, List.map_nil, Ptr.adv_nil, BlocksIn, true_and]
    rw [groupAux_in M _ δ, blocksIn_glueB, advBs_blk]

theorem group_in (M : Mem) (p : Ptr) (δ : List Seg) : BlocksIn M p (group δ) ↔ SegsIn M p δ := by
  rw [group_eq, blocksIn_glueB, groupAux_in M p δ]

theorem rdIn_inst (M : Mem) (Q : Program) (b jf t : Nat) :
    RdIn M (Q.inst b jf t) ↔ RdIn M (instAt ⟨Q.start .K b, Q.start .E b⟩ (Q.blk b) jf t) := Iff.rfl

/-- `RdIn` on every instance, block by block. -/
theorem ins_iff (Q : Program) (M : Mem) :
    (∀ i ∈ Q.insts, RdIn M i) ↔ BlocksIn M ⟨Q.nInK, Q.nInE⟩ Q.blocks := by
  rw [blocksIn_iff]
  constructor
  · intro h b hb jf hjf t ht
    have hi := (Q.mem_insts (Q.inst b jf t)).mpr ⟨b, hb, jf, by simpa [Program.blk] using hjf, t,
      by simpa [Program.blk] using ht, rfl⟩
    simpa [rdIn_inst, start_ptr, Program.blk] using h _ hi
  · intro h i hi
    obtain ⟨b, hb, jf, hjf, t, ht, rfl⟩ := (Q.mem_insts i).mp hi
    rw [rdIn_inst, start_ptr]
    exact h b hb jf (by simpa [Program.blk] using hjf) t (by simpa [Program.blk] using ht)

/-- **The bridge**: a gadget's segments in region ⇒ every instance of its program in region. -/
theorem toProgram_in {α : Type} (nK nE : Nat) (m : BM α) (M : Mem)
    (h : SegsIn M ⟨nK, nE⟩ (m ⟨nK, nE⟩).2) : ∀ i ∈ (toProgram nK nE m).insts, RdIn M i :=
  (ins_iff _ M).mpr ((group_in M _ _).mpr h)

end Build
end Lvm.Loop
end

section
set_option autoImplicit false
namespace Lvm.Loop
open FE
namespace Build

/-- No `readd` in the segments (checked by `decide` on a concrete gadget). -/
def noReaddSegs : List Seg → Bool
  | [] => true
  | .row r :: δ => rowNoRd r && noReaddSegs δ
  | .blk B :: δ => B.tpl.all rowNoRd && noReaddSegs δ

end Build
end Lvm.Loop
end

section
set_option autoImplicit false
namespace Lvm.Loop
open FE
namespace Build

theorem segsIn_of_noReadd (M : Mem) : ∀ (p : Ptr) (δ : List Seg), noReaddSegs δ = true → SegsIn M p δ
  | _, [], _ => trivial
  | p, .row r :: δ, h => by
    simp only [noReaddSegs, Bool.and_eq_true] at h
    exact ⟨rdIn_of_noRd h.1, segsIn_of_noReadd M _ δ h.2⟩
  | p, .blk B :: δ, h => by
    simp only [noReaddSegs, Bool.and_eq_true, List.all_eq_true] at h
    refine ⟨fun jf _ t ht => rdIn_of_noRd ?_, segsIn_of_noReadd M _ δ h.2⟩
    show rowNoRd (B.tpl.getD t default) = true
    rw [List.getD_eq_getElem _ _ ht]
    exact h.1 _ (List.getElem_mem ht)

/-- **`m`'s `readd`s are in region wherever its rows hold.** -/
def InOk (c : Ctx) (M : Mem) {α : Type} (m : BM α) : Prop :=
  ∀ p, SegsHold c M p (m p).2 → SegsIn M p (m p).2

theorem inOk_pure {c : Ctx} {M : Mem} {α : Type} (x : α) : InOk c M (pure x : BM α) :=
  fun _ _ => trivial

theorem inOk_bind {c : Ctx} {M : Mem} {α β : Type} {m : BM α} {f : α → BM β} (hm : InOk c M m)
    (hf : ∀ p, InOk c M (f (m p).1)) : InOk c M (m >>= f) := by
  intro p h
  rw [hold_bind] at h
  rw [in_bind]
  exact ⟨hm p h.1, hf p _ h.2⟩

theorem inOk_seqAll {c : Ctx} {M : Mem} {α : Type} :
    ∀ (ms : List (BM α)), (∀ m ∈ ms, InOk c M m) → InOk c M (seqAll ms)
  | [], _ => inOk_pure _
  | m :: ms, h => by
    simp only [seqAll]
    exact inOk_bind (h m (by simp)) fun _ =>
      inOk_bind (inOk_seqAll ms fun m' hm' => h m' (by simp [hm'])) fun _ => inOk_pure _

theorem inOk_noReadd {c : Ctx} {M : Mem} {α : Type} {m : BM α} (h : ∀ p, noReaddSegs (m p).2 = true) :
    InOk c M m := fun p _ => segsIn_of_noReadd M p _ (h p)

end Build
end Lvm.Loop
end

section
set_option autoImplicit false
namespace Lvm.Loop
open FE
namespace Build

/-- **A loop is in region** when each `readd` template row's address is, at every iteration. -/
theorem loop_in {M : Mem} {dims : List Nat} {tpl : List LRow} {p : Ptr}
    (h : ∀ jf < 2 ^ dims.sum, ∀ t < tpl.length, ∀ lo m args, tpl.getD t default = ⟨.readd lo m, .K, args⟩ →
      ∃ k < 2 ^ m, FK.x ^ (lo + k) = ((args.getD 0 default).val M ⟨p, dims, tpl⟩ jf).c₀)
    (hK : ∀ t < tpl.length, ∀ lo m, (tpl.getD t default).op = .readd lo m → (tpl.getD t default).ty = .K) :
    SegsIn M p (loop dims tpl p).2 := by
  simp only [loop_apply, SegsIn, and_true]
  intro jf hjf t ht
  have ht' : t < tpl.length := by simpa [mkLoop] using ht
  refine (loop_in_iff M ⟨p, dims, tpl⟩ jf t).mpr ?_
  show match (tpl.getD t default).op with
    | .readd lo m => ∃ k < 2 ^ m, FK.x ^ (lo + k) = (LoopOut.arg M ⟨p, dims, tpl⟩ jf t 0).c₀
    | _ => True
  rcases hr : tpl.getD t default with ⟨op, ty, args⟩
  cases op with
  | readd lo m =>
    have hty : ty = .K := by have := hK t ht' lo m (by rw [hr]); rwa [hr] at this
    subst hty
    simp only [LoopOut.arg, hr]
    exact h jf hjf t ht' lo m args hr
  | _ => trivial

end Build
end Lvm.Loop
end

-- ===== from `LvmQAsmInb` =====

section
section
set_option autoImplicit false
namespace Lvm.NS
open Lvm Lvm.Loop Lvm.Loop.Build Lvm.QSig Lvm.SigBits Lvm.BitsTab Lvm.M3

/-- **The six tables first in `aux`.** -/
theorem sigTabsIn_append (I : SigIn) (o : SigOut) (bpl : Nat → Nat → Bool × Nat) (rest : List Tab) :
    SigTabsIn I o bpl ((sigSpecs I o bpl).map BSpec.tab ++ rest) :=
  fun _ hS => List.mem_append_left _ (List.mem_map_of_mem hS)

/-- **The input regions** the six tables name, with their extents, below `C`. -/
structure SigRegLt (C : Nat) (I : SigIn) : Prop where
  sg : I.sg + 533 ≤ C
  bi : I.bi + 18 ≤ C
  md : I.md + 4 ≤ C
  bd : I.bd + 256 ≤ C
  bc : I.bc + 10 ≤ C
  bx : I.bx + 3192 ≤ C
  be : I.be + 1064 ≤ C
  bp : I.bp + 256 ≤ C
  hd : I.hd + 18 ≤ C
  bh : I.bh + 8 ≤ C
  bcl : I.bcl + 8 ≤ C
  yls : I.yls + 4 ≤ C
  bls : I.bls + 8 ≤ C
  bn : I.bn + I.ln + 5 ≤ C

/-- **Q_sig's chain and path cells** below `C`. -/
structure SigOutLt (C : Nat) (o : SigOut) : Prop where
  chain : ∀ i < 133, ∀ t < 28, chainCell o i t < C
  path : ∀ t < 16, ∀ c < 12, (o.pa.cell c t).n < C

/-- **`SigCellsLt` from the layout.** -/
theorem sigCellsLt_of {Q : Program} {I : SigIn} {o : SigOut} (bpl : Nat → Nat → Bool × Nat)
    (hR : SigRegLt (Q.cells .K) I) (hO : SigOutLt (Q.cells .K) o) : SigCellsLt Q I o bpl := by
  intro S hS x hx
  simp only [sigSpecs, List.mem_cons, List.not_mem_nil, or_false] at hS
  have R := hR
  rcases hS with rfl | rfl | rfl | rfl | rfl | rfl
  · simp only [sIdx] at hx ⊢
    refine ⟨fun _ => by have := R.sg; omega, fun j hj => ?_⟩
    simp only [List.length_cons, List.length_append, List.length_map, List.length_range,
      List.length_nil] at hj
    have := R.bi; omega
  · simp only [sMd] at hx ⊢
    refine ⟨fun _ => by have := R.md; omega, fun j hj => ?_⟩
    simp only [List.length_map, List.length_range] at hj
    have := R.bd; omega
  · simp only [sCs] at hx ⊢
    refine ⟨fun h => absurd h (by decide), fun j hj => ?_⟩
    simp only [List.length_map, List.length_range] at hj
    have := R.bc; omega
  · simp only [s24] at hx ⊢
    refine ⟨fun _ => ?_, fun j hj => ?_⟩
    · unfold xin
      split
      · have := R.sg; omega
      · exact hO.chain _ (by omega) _ (by omega)
    · simp only [List.length_cons, List.length_nil] at hj
      have := R.bx; omega
  · simp only [s8] at hx ⊢
    refine ⟨fun _ => ?_, fun j hj => ?_⟩
    · split
      · exact hO.chain _ (by omega) _ (by omega)
      · split
        · exact hO.path _ (by omega) _ (by omega)
        · split
          · have := R.hd; omega
          · split
            · have := R.hd; omega
            · have := R.yls; omega
    · simp only [List.length_cons, List.length_nil] at hj
      split
      · have := R.be; omega
      · split
        · have := R.bp; omega
        · split
          · have := R.bh; omega
          · split
            · have := R.bcl; omega
            · have := R.bls; omega
  · simp only [sN] at hx ⊢
    refine ⟨fun _ => by have := R.hd; omega, fun j hj => ?_⟩
    simp only [List.length_cons, List.length_append, List.length_map, List.length_range,
      List.length_nil] at hj
    have := R.bn; omega

/-- A gadget placed at `p` ends at or below `C`. -/
def Inside (C : Nat) {α : Type} (m : BM α) (p : Ptr) : Prop := (p.adv (m p).2).k ≤ C

theorem inside_bind {C : Nat} {α β : Type} {m : BM α} {f : α → BM β} {p : Ptr}
    (h : Inside C (m >>= f) p) :
    Inside C m p ∧ Inside C (f (m p).1) (p.adv (m p).2) ∧
      ((m >>= f) p).1 = (f (m p).1 (p.adv (m p).2)).1 := by
  unfold Inside at h ⊢
  rw [bind_apply, Ptr.adv_append] at h
  refine ⟨?_, h, rfl⟩
  have : (p.adv (m p).2).k ≤ ((p.adv (m p).2).adv (f (m p).1 (p.adv (m p).2)).2).k := by
    simp only [Ptr.adv]; omega
  omega

theorem inside_seqAll_get {C : Nat} :
    ∀ (ms : List (BM LoopOut)) (p : Ptr), Inside C (seqAll ms) p →
      ∀ u < ms.length, ∃ q, Inside C (ms.getD u (pure dLoop)) q ∧
        (seqAll ms p).1.getD u dLoop = ((ms.getD u (pure dLoop)) q).1
  | [], _, _, u, hu => absurd hu (by simp)
  | m :: ms, p, h, u, hu => by
    unfold Inside at h
    rw [seqAll_cons_apply, Ptr.adv_append, Ptr.adv_append] at h
    have h1 : (p.adv (m p).2).k ≤ C := by
      have : (p.adv (m p).2).k ≤
          (((p.adv (m p).2).adv (seqAll ms (p.adv (m p).2)).2).adv []).k := by
        simp only [Ptr.adv]; omega
      omega
    have h2 : Inside C (seqAll ms) (p.adv (m p).2) := by
      unfold Inside; simpa using h
    cases u with
    | zero => exact ⟨p, h1, by simp [seqAll_cons_apply]⟩
    | succ u =>
      obtain ⟨q, hq, e⟩ := inside_seqAll_get ms _ h2 u (by simpa using hu)
      refine ⟨q, by simpa using hq, ?_⟩
      simp only [seqAll_cons_apply, List.getD_cons_succ]
      exact e

theorem inside_forN_get {C n : Nat} {f : Nat → BM LoopOut} {p : Ptr} (h : Inside C (forN n f) p) :
    ∀ u < n, ∃ q, Inside C (f u) q ∧ (forN n f p).1.getD u dLoop = (f u q).1 := by
  intro u hu
  obtain ⟨q, hq, e⟩ := inside_seqAll_get _ p h u (by simpa using hu)
  have hg : ((List.range n).map f).getD u (pure dLoop) = f u := by
    rw [List.getD_eq_getElem _ _ (by simpa using hu)]; simp
  rw [hg] at hq e
  exact ⟨q, hq, e⟩

set_option maxRecDepth 100000 in
/-- **Where Q_sig's loops sit** (the pointer form of `qsig_parts`): each loop whose cells the
tables name ends at or below `C`. -/
theorem qsig_inside {C : Nat} {p : Ptr} {I : SigIn} (h : Inside C (qsig I) p) :
    let o := (qsig I p).1
    (∃ q, Inside C (loop [7] (chainM I o.pre.1.n o.pre.2.1.n)) q ∧
      (loop [7] (chainM I o.pre.1.n o.pre.2.1.n) q).1 = o.cm) ∧
    (∀ u < 5, ∃ q, Inside C (loop [] (chainC I o.pre.1.n o.pre.2.1.n u)) q ∧
      (loop [] (chainC I o.pre.1.n o.pre.2.1.n u) q).1 = o.cc.getD u dLoop) ∧
    (∃ q, Inside C (loop [4] (pathTpl I)) q ∧ (loop [4] (pathTpl I) q).1 = o.pa) := by
  unfold qsig at h ⊢
  intro o
  obtain ⟨-, h, e1⟩ := inside_bind h
  obtain ⟨o2, h, e2⟩ := inside_bind h
  obtain ⟨o3, h, e3⟩ := inside_bind h
  obtain ⟨-, h, e4⟩ := inside_bind h
  obtain ⟨o5, -, e5⟩ := inside_bind h
  refine ⟨⟨_, o2, rfl⟩, fun u hu => ?_, ⟨_, o5, rfl⟩⟩
  obtain ⟨q, hq, e⟩ := inside_forN_get o3 u hu
  exact ⟨q, hq, e.symm⟩

/-- The pointer after a loop (QA2's `loop_adv`, LvmQWhirBase). -/
theorem loop_adv' (dims : List Nat) (tpl : List LRow) (p : Ptr) :
    p.adv (loop dims tpl p).2 = ⟨p.k + ltw .K tpl * 2 ^ dims.sum, p.e + ltw .E tpl * 2 ^ dims.sum⟩ := by
  have := mkLoop_tw p dims tpl
  simp only [loop_apply, Ptr.adv, segsW, List.map, Seg.w, this, Block.size, Block.lsize, List.sum_cons,
    List.sum_nil, add_zero]
  simp [mkLoop]

/-- A template row writing `K` comes before the end of the `K` rows. -/
theorem lrank_lt {tpl : List LRow} {t : Nat} (ht : t < tpl.length)
    (hw : LRow.w .K (tpl.getD t default) = 1) : lrank .K tpl t + 1 ≤ ltw .K tpl := by
  unfold lrank ltw
  conv_rhs => rw [← List.take_append_drop t tpl]
  rw [List.map_append, List.sum_append, List.drop_eq_getElem_cons ht, List.map_cons, List.sum_cons]
  rw [List.getD_eq_getElem _ _ ht] at hw
  omega

/-- **A loop's `K` cells lie below the pointer after it.** -/
theorem loop_cell_lt {C : Nat} {dims : List Nat} {tpl : List LRow} {q : Ptr}
    (h : Inside C (loop dims tpl) q) {t jf : Nat} (ht : t < tpl.length)
    (hty : (tpl.getD t default).ty = .K) (hw : LRow.w .K (tpl.getD t default) = 1)
    (hjf : jf < 2 ^ dims.sum) : ((loop dims tpl q).1.cell t jf).n < C := by
  unfold Inside at h
  rw [loop_adv'] at h
  simp only at h
  have hr := lrank_lt ht hw
  simp only [loop_apply, LoopOut.cell, hty, Ptr.at]
  have : ltw .K tpl * jf + ltw .K tpl ≤ ltw .K tpl * 2 ^ dims.sum := by
    rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left _ hjf
  omega

/-- Every row of a chain template writes one `K` cell. -/
theorem chainTpl_rows (d0 d1 Z O : Opd) (ots o1 o2 o3 : Nat → Opd) :
    ∀ r ∈ chainTpl d0 d1 Z O ots o1 o2 o3, r.ty = .K ∧ LRow.w .K r = 1 := by
  intro r hr
  simp only [chainTpl, List.mem_append, List.mem_cons, List.mem_map, List.mem_range,
    List.not_mem_nil, or_false] at hr
  rcases hr with ((((((h | h | h | h) | ⟨_, -, h⟩) | ⟨_, -, h⟩) | ⟨_, -, h⟩) | ⟨_, -, h⟩) | ⟨_, -, h⟩) |
    ⟨_, -, h⟩ <;> subst h <;> exact ⟨rfl, rfl⟩

theorem chainTpl_length (d0 d1 Z O : Opd) (ots o1 o2 o3 : Nat → Opd) :
    (chainTpl d0 d1 Z O ots o1 o2 o3).length = 28 := by
  simp [chainTpl]

theorem pathTpl_rows (I : SigIn) : ∀ r ∈ pathTpl I, r.ty = .K ∧ LRow.w .K r = 1 := by
  intro r hr
  simp only [pathTpl, List.mem_append, List.mem_map, List.mem_range] at hr
  rcases hr with (⟨_, -, h⟩ | ⟨_, -, h⟩) | ⟨_, -, h⟩ <;> subst h <;> exact ⟨rfl, rfl⟩

theorem pathTpl_length (I : SigIn) : (pathTpl I).length = 12 := by simp [pathTpl]

theorem getD_mem {tpl : List LRow} {t : Nat} (ht : t < tpl.length) : tpl.getD t default ∈ tpl := by
  rw [List.getD_eq_getElem _ _ ht]; exact List.getElem_mem ht

/-- **Q_sig's chain and path cells lie below the pointer after it.** -/
theorem sigOutLt_qsig {C : Nat} (I : SigIn) (p : Ptr) (hP : (p.adv (qsig I p).2).k ≤ C) :
    SigOutLt C (qsig I p).1 := by
  obtain ⟨⟨q2, h2, e2⟩, h3, ⟨q5, h5, e5⟩⟩ := qsig_inside (C := C) (p := p) (I := I) hP
  constructor
  · intro i hi t ht
    unfold chainCell
    split
    · rw [← e2]
      have ht' : t < (chainM I (qsig I p).1.pre.1.n (qsig I p).1.pre.2.1.n).length := by
        unfold chainM; rw [chainTpl_length]; exact ht
      have hr := chainTpl_rows _ _ _ _ _ _ _ _ _ (getD_mem ht')
      exact loop_cell_lt h2 ht' hr.1 hr.2 (by simp; omega)
    · obtain ⟨q, hq, e⟩ := h3 (i - 128) (by omega)
      rw [← e]
      have ht' : t < (chainC I (qsig I p).1.pre.1.n (qsig I p).1.pre.2.1.n (i - 128)).length := by
        unfold chainC; rw [chainTpl_length]; exact ht
      have hr := chainTpl_rows _ _ _ _ _ _ _ _ _ (getD_mem ht')
      exact loop_cell_lt hq ht' hr.1 hr.2 (by simp)
  · intro t ht c hc
    rw [← e5]
    have hc' : c < (pathTpl I).length := by rw [pathTpl_length]; exact hc
    have hr := pathTpl_rows I _ (getD_mem hc')
    exact loop_cell_lt h5 hc' hr.1 hr.2 (by simp; omega)

/-- **`SigCellsLt` for `Q_sig` placed at `p`**, ending at or below `Q`'s `K` cells. -/
theorem sigCellsLt_qsig {Q : Program} {I : SigIn} {p : Ptr} (bpl : Nat → Nat → Bool × Nat)
    (hR : SigRegLt (Q.cells .K) I) (hP : (p.adv (qsig I p).2).k ≤ Q.cells .K) :
    SigCellsLt Q I (qsig I p).1 bpl :=
  sigCellsLt_of bpl hR (sigOutLt_qsig I p hP)

end Lvm.NS
end
end

section
section
set_option autoImplicit false
namespace Lvm.NS
open RecursionFast Lvm Lvm.T Lvm.ASM Lvm.Replay Lvm.Loop Lvm.Loop.Build Lvm.QLink Lvm.QSig Lvm.M3
open Lvm.SigBits LeanVM.Protocol

/-- Transport of `M3Holds` along an equality of the tables. -/
theorem m3Holds_congr {L : Lay} {t t' : List Tab} (h : t = t') {hτ : ∀ u ∈ t, u.τ ≤ L.μ}
    {hτ' : ∀ u ∈ t', u.τ ≤ L.μ} {q : Column L.μ} (hm : M3Holds (inst L t hτ) () q) :
    M3Holds (inst L t' hτ') () q := by
  subst h; exact hm

end Lvm.NS
end
end

section
section
set_option autoImplicit false
namespace Lvm.NS
open RecursionFast Lvm Lvm.T Lvm.ASM Lvm.Replay Lvm.Loop Lvm.Loop.Build Lvm.QLink Lvm.QSig Lvm.M3
open Lvm.SigBits LeanVM.Protocol
section Main
variable {α : Type} (lay : Layout) (I : SigIn) (qa : BM α) (nK nE : ℕ)
  (pl : ℕ → Var → Bool × ℕ) (groups : List Grp) (arrsX : List UInt8 → List InArr) (aux : List Tab)
  (hτ' : ∀ x, ∀ t ∈ lvmTabs (Qn lay I qa nK nE) pl groups (arrsX x) aux, t.τ ≤ lay26.μ)

/-- **`AuxHyps` without `M3Holds` and `inb`**: the static checks (decided on the concrete program). -/
structure AuxStatic (arrs : List InArr) : Prop where
  wf : (Qn lay I qa nK nE).wf = true
  grp : GrpOk (Qn lay I qa nK nE) groups
  inOk : InOk (Qn lay I qa nK nE) arrs
  auxSeeds : ∀ t ∈ aux, t.seeds = []
  cnt : ∀ t ∈ lvmTabs (Qn lay I qa nK nE) pl groups arrs aux, ∀ r ∈ t.reads, r.2 < t.w
  len : nReads (lvmTabs (Qn lay I qa nK nE) pl groups arrs aux) < 2 ^ 64 - 1
  inj : GInj (max ((Qn lay I qa nK nE).cells .K) ((Qn lay I qa nK nE).cells .E))

/-- The memory of the node program on the pair `(qm, qr)` of statement `x`. -/
noncomputable abbrev memX (x : List UInt8) (qm : Column CMain.nu20) (qr : Column 19) : Mem :=
  memN lay I qa nK nE pl groups (arrsX x) aux lay26 (hτ' x) (stackOf lay26 qm qr)

/-- **The input map** (A19) on the committed memory of a node statement `x` (`b = 1`) and a pair:
where each part's inputs are and what they hold. -/
structure InMapN (vk : RecursionFast.Digest) (x : List UInt8) (qm : Column CMain.nu20) (qr : Column 19) : Prop where
  /-- The stream lanes (Q_link's and Q_sig's stream region; `C_rec`'s stream columns). -/
  stream : ∀ j < 2 ^ lay.m, (memX lay I qa nK nE pl groups arrsX aux hτ' x qm qr).k (lay.sb + j) =
    laneK (wsOf (Lvm.X.laneOf (wOfCol qr))) j
  /-- Q_sig's gate is on. -/
  flag : (memX lay I qa nK nE pl groups arrsX aux hτ' x qm qr).k I.flag = 1
  /-- `KS`'s `X` message lanes (rows `2^14 + r`) on Q_sig's message cells (A19 route (a)). -/
  xs : ∀ r < 449, ∀ l < 17, (memX lay I qa nK nE pl groups arrsX aux hτ' x qm qr).k (I.xs + 17 * r + l) =
    FK.ofBF64 (msgX qm r l)
  /-- `KS`'s output lanes `0 … 3` on Q_sig's digest cells: chain steps, key leaf and path, the two
  statements. -/
  ys : ∀ r < 399, ∀ l < 4, (memX lay I qa nK nE pl groups arrsX aux hτ' x qm qr).k (I.ys + 4 * r + l) =
    FK.ofBF64 (Yq qm (ksSplit P20 + r) l)
  yc : ∀ t ≤ 16, ∀ l < 4, (memX lay I qa nK nE pl groups arrsX aux hτ' x qm qr).k (I.yc + 4 * t + l) =
    FK.ofBF64 (Yq qm (ksSplit P20 + 430 + t) l)
  yls : ∀ l < 4, (memX lay I qa nK nE pl groups arrsX aux hτ' x qm qr).k (I.yls + l) =
    FK.ofBF64 (Yq qm (ksSplit P20 + 447) l)
  yns : ∀ l < 4, (memX lay I qa nK nE pl groups arrsX aux hτ' x qm qr).k (I.yns + l) =
    FK.ofBF64 (Yq qm (ksSplit P20 + 448) l)
  /-- `PUB`: the key, the left statement, the leaf signature. -/
  vk : digAt (memX lay I qa nK nE pl groups arrsX aux hτ' x qm qr).k I.vk = vk
  cL : digAt (memX lay I qa nK nE pl groups arrsX aux hτ' x qm qr).k I.cL = (hdrOf x).cL
  sl : sigAt' (memX lay I qa nK nE pl groups arrsX aux hτ' x qm qr).k I.sl = (hdrOf x).sig
  /-- The trace-digest cells: `KS` row `B − 1`'s output lanes `0 … 3`. -/
  md : ∀ l < 4, (memX lay I qa nK nE pl groups arrsX aux hτ' x qm qr).k (I.md + l) =
    FK.ofBF64 (Yq qm (spongeBlocks P20 - 1) l)
  /-- `σ'`'s cells: `C_rec`'s column 17. -/
  sg : sigAt' (memX lay I qa nK nE pl groups arrsX aux hτ' x qm qr).k I.sg =
    Lvm.X.sigOfF (Lvm.X.sigCol (wOfCol qr))
  /-- Q_sig's child-header cells are the stream's lanes `11 …`. -/
  hd : ∀ k < 615, (memX lay I qa nK nE pl groups arrsX aux hτ' x qm qr).k (I.hd + k) =
    laneK (wsOf (Lvm.X.laneOf (wOfCol qr))) (11 + k)
  /-- (A23) the whole `PUB` array from `I.flag`: the header's 702 lanes, `acc_in`'s 87 among them
  (`LvmAccNodePub`: `hdrLanes x = (pubX x).hdrLanes`; Q_acc reads the current `acc_in` there). -/
  pub : ∀ j < pubLanes, (memX lay I qa nK nE pl groups arrsX aux hτ' x qm qr).k (I.flag + j) = hdrLane x j

end Main
end Lvm.NS
end
end

section
section
set_option autoImplicit false
namespace Lvm.NS
open RecursionFast Lvm Lvm.T Lvm.ASM Lvm.Replay Lvm.Loop Lvm.Loop.Build Lvm.QLink Lvm.QSig Lvm.M3
open Lvm.SigBits LeanVM.Protocol
section Main
variable {α : Type} (lay : Layout) (I : SigIn) (qa : BM α) (nK nE : ℕ)
  (pl : ℕ → Var → Bool × ℕ) (groups : List Grp) (arrsX : List UInt8 → List InArr) (aux : List Tab)
  (hτ' : ∀ x, ∀ t ∈ lvmTabs (Qn lay I qa nK nE) pl groups (arrsX x) aux, t.τ ≤ lay26.μ)
variable {lay I qa nK nE pl groups arrsX aux hτ'}

/-- **`NodeSound` for the node program** (see the module docstring for the hypotheses). -/
theorem nodeSound_main (m : M3) (vk : RecursionFast.Digest)
    {T : List UInt8 → List Tab} {hτ : ∀ x, ∀ t ∈ T x, t.τ ≤ lay26.μ} {Good : GoodRel}
    (hGood : ∀ x qm qr, Good x qm qr → GoodN T hτ x qm qr)
    (hT : ∀ x, T x = lvmTabs (Qn lay I qa nK nE) pl groups (arrsX x) aux)
    (hst : ∀ x, AuxStatic lay I qa nK nE pl groups aux (arrsX x))
    (hinb : ∀ c x qm qr, okS vk c x = true → (hdrOf x).b = 1 → GoodN T hτ x qm qr →
      ((Qn lay I qa nK nE).interp (inKOf (Qn lay I qa nK nE) pl groups (arrsX x) aux lay26 (hτ' x)
        (stackOf lay26 qm qr)) (inEOf (Qn lay I qa nK nE) pl groups (arrsX x) aux lay26 (hτ' x)
        (stackOf lay26 qm qr))).inb = true)
    (hS : StreamOk P20) (hQ : QOk P20 lay) (hws : 2 ^ lay.m ≤ 17 * 2 ^ 14) (hfg : lay.fg = I.flag)
    (hln : I.ln = 20)
    (hqlt : ∀ c x qm qr, okS vk c x = true → (hdrOf x).b = 1 → GoodN T hτ x qm qr →
      ∀ y < (qltData P20 lay).length,
        (memX lay I qa nK nE pl groups arrsX aux hτ' x qm qr).k (lay.qt + y) = (qltData P20 lay).getD y 0)
    (hpos : ∀ c x qm qr, okS vk c x = true → (hdrOf x).b = 1 → GoodN T hτ x qm qr →
      ∀ k < (opens P20).length, ∀ j < ((opens P20).getD k default).L.t,
        ∀ z < ((opens P20).getD k default).L.height,
        (memX lay I qa nK nE pl groups arrsX aux hτ' x qm qr).k
            (bitBase P20 lay k + ((opens P20).getD k default).L.height * j + z) =
          if ansBit P20 (wsOf (Lvm.X.laneOf (wOfCol qr))) (((opens P20).getD k default).pe + j / 8)
            (j % 8 * ((opens P20).getD k default).L.height + z) then 1 else 0)
    (hNs : lay.sb + 2 ^ lay.m ≤ max ((Qn lay I qa nK nE).cells .K) ((Qn lay I qa nK nE).cells .E))
    (bpl : ℕ → ℕ → Bool × ℕ) (rest : List Tab)
    (haux : aux = (sigSpecs I (qsig I (p1 lay nK nE)).1 bpl).map BitsTab.BSpec.tab ++ rest)
    (hR : SigRegLt ((Qn lay I qa nK nE).cells .K) I)
    (hP : (p2 lay I nK nE).k ≤ (Qn lay I qa nK nE).cells .K)
    (hmap : ∀ c x qm qr, okS vk c x = true → (hdrOf x).b = 1 → GoodN T hτ x qm qr →
      InMapN lay I qa nK nE pl groups arrsX aux hτ' vk x qm qr)
    (harith : ∀ c x qm qr, okS vk c x = true → (hdrOf x).b = 1 → Good x qm qr →
      InMapN lay I qa nK nE pl groups arrsX aux hτ' vk x qm qr →
      LaneLink P20 (wsOf (Lvm.X.laneOf (wOfCol qr))) → LinkOk P20 (decode P20 (wsOf (Lvm.X.laneOf (wOfCol qr)))) →
      Ok (ctxOf (Qn lay I qa nK nE)) (memX lay I qa nK nE pl groups arrsX aux hτ' x qm qr) qa
        (p2 lay I nK nE) →
      decideF P20 m vk (hdrOf x).cL (traceBytesB (decode P20 (wsOf (Lvm.X.laneOf (wOfCol qr))))) = true) :
    NodeSound (VS P20 m) vk Good childS := by
  refine nodeSound_of (fun c x qm qr hok hG ↦ chain_of_goodN hok (hGood _ _ _ hG))
    fun c x qm qr hok hb hG' ↦ ?_
  have hG := hGood _ _ _ hG'
  have st := hst x
  have H : AuxHyps (Qn lay I qa nK nE) pl groups (arrsX x) aux lay26 (hτ' x) (stackOf lay26 qm qr) :=
    ⟨st.wf, st.grp, st.inOk, st.auxSeeds, st.cnt, st.len, st.inj,
      m3Holds_congr (hT x) hG.1, hinb c x qm qr hok hb hG⟩
  have mp := hmap c x qm qr hok hb hG
  have hwsl : 2 ^ lay.m ≤ (wsOf (Lvm.X.laneOf (wOfCol qr))).length := by
    rw [wsOf, List.length_map, List.length_range]; exact hws
  have hqin : QIn P20 lay (wsOf (Lvm.X.laneOf (wOfCol qr)))
      (memX lay I qa nK nE pl groups arrsX aux hτ' x qm qr) :=
    ⟨by rw [hfg]; exact mp.flag, mp.stream, hqlt c x qm qr hok hb hG, hpos c x qm qr hok hb hG⟩
  obtain ⟨hLL, hlink, hpad⟩ := link_of_aux H hS hQ hqin hwsl hNs
  have hks := sigKSin_of_goodK hG.2 mp.xs mp.ys mp.yc mp.yls mp.yns
  have hTabs : SigTabsIn I (qsig I (p1 lay nK nE)).1 bpl aux := by
    rw [haux]; exact sigTabsIn_append _ _ bpl rest
  obtain ⟨hsig, hchild⟩ := sig_of_aux H mp.flag hks bpl hTabs (sigCellsLt_qsig bpl hR hP) hln
  have hmd := (digAt_of_cells mp.md).trans (traceDigest_of_goodK hG.2 hLL hpad)
  have har := harith c x qm qr hok hb hG' mp hLL hlink (parts_of_aux H).2.2
  exact accV_childW_of hdrBridge trBridge m (wOfCol qr) hlink har hsig hchild hln mp.vk mp.cL mp.sl hmd mp.sg
    mp.hd (okS_sig hok hb)

end Main
end Lvm.NS
end
end

section
section
set_option autoImplicit false
namespace Lvm.Loop.Build
open Lvm.Loop

/-- The region condition from an address `g^e`, `lo ≤ e < lo + 2^m`. -/
theorem rd_of_gpow {v : FE} {e lo m : Nat} (hv : v = FE.ofK (gpow e)) (h1 : lo ≤ e) (h2 : e < lo + 2 ^ m) :
    ∃ k < 2 ^ m, FK.x ^ (lo + k) = v.c₀ :=
  ⟨e - lo, by omega, by rw [hv, show lo + (e - lo) = e by omega]; rfl⟩

theorem qltLoop_in {c : Ctx} {M : Mem} {p : Ptr} {a qt lo m g : Nat}
    (h : SegsHold c M p (qltLoop a qt lo m (kc g) p).2)
    (hE : ∀ jf < 2 ^ a, ∃ e₁ e₂, M.k (qt + 3 * jf) = gpow e₁ ∧ M.k (qt + 1 + 3 * jf) = gpow e₂ ∧
      lo ≤ e₁ ∧ e₁ + 5 ≤ lo + 2 ^ m ∧ lo ≤ e₂ ∧ e₂ + 4 ≤ lo + 2 ^ m) :
    SegsIn M p (qltLoop a qt lo m (kc g) p).2 := by
  simp only [qltLoop, hold_bind] at h
  simp only [qltLoop, in_bind, SegsIn, and_true]
  refine ⟨loop_in (fun jf hjf t ht lo' m' args hr => ?_) (fun t ht lo' m' hop => ?_), trivial⟩
  · have hj : jf < 2 ^ [a].sum := by simpa using hjf
    have hjf' : jf < 2 ^ a := by simpa using hjf
    obtain ⟨e₁, e₂, hα, hβ, h1, h2, h3, h4⟩ := hE jf hjf'
    set o : LoopOut := ⟨p, [a], qltTpl qt lo m (kc g)⟩ with ho
    have hR : ∀ t < 26, LRel c M o jf t := fun t ht => loop_rel h.1 hj (t := t) (by simp [qltTpl]; omega)
    have hu : unflat o.dims jf = [jf] := unflat_one' hj
    have vα : (Opd.abs ⟨.K, qt, [3]⟩).val M o jf = FE.ofK (gpow e₁) := by
      rw [Opd.val_absK, hu]; simp only [dot, Nat.add_zero]; rw [hα]
    have vβ : (Opd.abs ⟨.K, qt + 1, [3]⟩).val M o jf = FE.ofK (gpow e₂) := by
      rw [Opd.val_absK, hu]; simp only [dot, Nat.add_zero]; rw [hβ]
    have hadr : ∀ (t l e : Nat) (x : Opd), o.tpl.getD t default = ⟨.lin (gpow l + 1) 0, .K, [x, x]⟩ →
        x.val M o jf = FE.ofK (gpow e) → t < 26 → (Opd.cur t).val M o jf = FE.ofK (gpow (e + l)) := by
      intro t l e x hr hx ht
      rw [Opd.val_cur _ _ hj, lrel_lin hr (hR t ht)]
      simp only [List.getD_cons_zero, List.getD_cons_succ, hx, ofK_zero, add_zero]
      rw [← ofK_mul, ← ofK_add, ← gpow_scale l e, add_zero]
    have a1 := hadr 0 1 e₁ _ rfl vα (by omega)
    have a2 := hadr 1 2 e₁ _ rfl vα (by omega)
    have a3 := hadr 2 3 e₁ _ rfl vα (by omega)
    have a4 := hadr 3 4 e₁ _ rfl vα (by omega)
    have b1 := hadr 4 1 e₂ _ rfl vβ (by omega)
    have b2 := hadr 5 2 e₂ _ rfl vβ (by omega)
    have b3 := hadr 6 3 e₂ _ rfl vβ (by omega)
    have ht26 : t < 26 := by simpa [qltTpl] using ht
    interval_cases t <;>
      simp only [qltTpl, List.getD_cons_succ, List.getD_cons_zero, LRow.mk.injEq, Op.readd.injEq,
        reduceCtorEq, false_and] at hr <;> obtain ⟨⟨rfl, rfl⟩, -, rfl⟩ := hr <;>
      simp only [List.getD_cons_zero] <;>
      first
      | (rw [vα]; exact rd_of_gpow rfl (by omega) (by omega))
      | (rw [vβ]; exact rd_of_gpow rfl (by omega) (by omega))
      | (rw [a1]; exact rd_of_gpow rfl (by omega) (by omega))
      | (rw [a2]; exact rd_of_gpow rfl (by omega) (by omega))
      | (rw [a3]; exact rd_of_gpow rfl (by omega) (by omega))
      | (rw [a4]; exact rd_of_gpow rfl (by omega) (by omega))
      | (rw [b1]; exact rd_of_gpow rfl (by omega) (by omega))
      | (rw [b2]; exact rd_of_gpow rfl (by omega) (by omega))
      | (rw [b3]; exact rd_of_gpow rfl (by omega) (by omega))
  · have ht26 : t < 26 := by simpa [qltTpl] using ht
    interval_cases t <;> simp only [qltTpl, List.getD_cons_succ, List.getD_cons_zero, reduceCtorEq] at hop ⊢

/-- The rows of the cap template past the address chain (`capLoop_spec`'s `hpost`). -/
theorem capTpl_post (lenL row A lo rlo m : Nat) (s : List Nat) (bt : Nat) (sb : List Nat) (c z : Nat)
    (sz : List Nat) (hc : 1 ≤ c) (i : Nat) :
    (capTpl lenL row A lo rlo m s bt sb c z sz).getD (2 * c + 1 + i) default =
      ([⟨.lin (gpow 1 + 1) 0, .K, [.cur (2 * c), .cur (2 * c)]⟩, ⟨.lin (gpow 2 + 1) 0, .K, [.cur (2 * c), .cur (2 * c)]⟩,
       ⟨.lin (gpow 3 + 1) 0, .K, [.cur (2 * c), .cur (2 * c)]⟩,
       ⟨.readd rlo m, .K, [.cur (2 * c)]⟩, ⟨.readd rlo m, .K, [.cur (2 * c + 1)]⟩, ⟨.readd rlo m, .K, [.cur (2 * c + 2)]⟩,
       ⟨.readd rlo m, .K, [.cur (2 * c + 3)]⟩,
       ⟨.lin 1 0, .K, [.cur (2 * c + 4), .abs ⟨.K, A, s⟩]⟩, ⟨.assert0, .K, [.cur (2 * c + 8), .abs ⟨.K, z, sz⟩]⟩,
       ⟨.lin 1 0, .K, [.cur (2 * c + 5), .abs ⟨.K, A + 1, s⟩]⟩, ⟨.assert0, .K, [.cur (2 * c + 10), .abs ⟨.K, z, sz⟩]⟩,
       ⟨.lin 1 0, .K, [.cur (2 * c + 6), .abs ⟨.K, A + 2, s⟩]⟩, ⟨.assert0, .K, [.cur (2 * c + 12), .abs ⟨.K, z, sz⟩]⟩,
       ⟨.lin 1 0, .K, [.cur (2 * c + 7), .abs ⟨.K, A + 3, s⟩]⟩, ⟨.assert0, .K, [.cur (2 * c + 14), .abs ⟨.K, z, sz⟩]⟩] :
        List LRow).getD i default := by
  have e : 2 * c + 1 + i = [(default : LRow), default, default].length + (capChain bt sb c).length + i := by
    simp [capChain_length]; omega
  rw [e]; exact getD_app3

theorem capTpl_length (lenL row A lo rlo m : Nat) (s : List Nat) (bt : Nat) (sb : List Nat) (c z : Nat)
    (sz : List Nat) (hc : 1 ≤ c) : (capTpl lenL row A lo rlo m s bt sb c z sz).length = 2 * c + 16 := by
  simp [capTpl, capChain_length]; omega

/-- **The cap address chain** (`capLoop_spec`'s chain, without the gate): with Boolean cap bits, the
addresses at rows `2c + i` are `g^(lo + 4·idx + i)`, `i < 4`. -/
theorem capAddr {cx : Ctx} {M : Mem} {p : Ptr} {dims : List Nat} {lenL row A lo rlo m bt c z : Nat}
    {s sb sz : List Nat}
    (h : SegsHold cx M p (capLoop dims lenL row A lo rlo m s bt sb c z sz p).2) {jf : Nat} (hjf : jf < 2 ^ dims.sum)
    (hc : 1 ≤ c)
    (hb : ∀ y < c, M.k (bt + y + dot sb (unflat dims jf)) = 0 ∨ M.k (bt + y + dot sb (unflat dims jf)) = 1) :
    ∀ i < 4, (Opd.cur (2 * c + i)).val M (loop dims (capTpl lenL row A lo rlo m s bt sb c z sz) p).1 jf =
      FE.ofK (gpow (lo + 4 * bitSum M bt sb (unflat dims jf) c + i)) := by
  simp only [capLoop, hold_bind] at h
  have hlen := capTpl_length lenL row A lo rlo m s bt sb c z sz hc
  have hR := fun t (ht : t < 2 * c + 16) => loop_rel h.1 hjf (t := t) (by rw [hlen]; exact ht)
  generalize hJ : unflat dims jf = J at *
  have vK : ∀ (b : Nat) (st : List Nat),
      (Opd.abs ⟨.K, b, st⟩).val M (loop dims (capTpl lenL row A lo rlo m s bt sb c z sz) p).1 jf =
        FE.ofK (M.k (b + dot st J)) := fun b st => by
    rw [Opd.val_absK]; show _ = FE.ofK (M.k (b + dot st J)); rw [← hJ]; rfl
  have vc : ∀ t, (Opd.cur t).val M (loop dims (capTpl lenL row A lo rlo m s bt sb c z sz) p).1 jf =
      ((loop dims (capTpl lenL row A lo rlo m s bt sb c z sz) p).1.cell t jf).val M := fun t => Opd.val_cur _ _ hjf t
  have hpost := capTpl_post lenL row A lo rlo m s bt sb c z sz hc
  have chain : ∀ y < c, ((loop dims (capTpl lenL row A lo rlo m s bt sb c z sz) p).1.cell (2 * y + 2) jf).val M =
      FE.ofK (gpow (lo + 4 * bitSum M bt sb J (y + 1))) := by
    intro y
    induction y with
    | zero =>
      intro _
      have h2 := lrel_lin (t := 2) rfl (hR 2 (by omega))
      simp only [List.getD_cons_zero, List.getD_cons_succ, vK] at h2
      rw [h2, ← ofK_mul, ← ofK_add, ← ofK_add]
      congr 1
      rw [bitSum_succ, show bitSum M bt sb J 0 = 0 from rfl, Nat.zero_add, Nat.add_zero]
      rcases hb 0 hc with h0 | h1
      · simp only [Nat.add_zero] at h0; rw [h0]; simp [show (0 : FK) ≠ 1 from by decide, gpow]
      · simp only [Nat.add_zero] at h1
        rw [h1, if_pos rfl, mul_one]
        have e : (1 : FK) + (gpow lo * (gpow 4 + 1) + 1) + gpow lo =
            gpow lo * gpow 4 + ((1 + 1) + (gpow lo + gpow lo)) := by ring
        rw [e, FK.add_self, FK.add_self, add_zero, add_zero, ← gpow_add]
        simp
    | succ y ih =>
      intro hy
      have ihv := ih (by omega)
      obtain ⟨k1, k2⟩ := capChain_getD bt sb c y hy
      have r1 := capTpl_chain lenL row A lo rlo m s bt sb c z sz (i := 2 * y) (by omega)
      have r2 := capTpl_chain lenL row A lo rlo m s bt sb c z sz (i := 2 * y + 1) (by omega)
      rw [k1] at r1; rw [k2] at r2
      rw [show 3 + 2 * y = 2 * y + 3 by omega] at r1
      rw [show 3 + (2 * y + 1) = 2 * (y + 1) + 2 by omega] at r2
      have e1 := lrel_lin r1 (hR _ (by omega))
      have e2 := lrel_muladd r2 (hR _ (by omega))
      simp only [List.getD_cons_zero, List.getD_cons_succ, vK, vc, ofK_zero, add_zero] at e1 e2
      rw [show 2 * (y + 1) = 2 * y + 2 by ring] at e1 e2
      rw [show 2 * y + 2 + 1 = 2 * y + 3 by ring] at e2
      rw [show 2 * (y + 1) + 2 = 2 * y + 2 + 2 by ring, e2, e1, ihv]
      simp only [← ofK_mul, ← ofK_add]
      congr 1
      have hsel := bit_select (gpow (lo + 4 * bitSum M bt sb J (y + 1))) (gpow (4 * 2 ^ (y + 1)))
        (M.k (bt + (y + 1) + dot sb J)) (hb (y + 1) hy)
      rw [add_zero] at hsel
      rw [hsel, bitSum_succ (n := y + 1)]
      split_ifs with hβ
      · rw [← gpow_add]; congr 1; ring
      · simp
  have hα0 := chain (c - 1) (by omega)
  rw [show 2 * (c - 1) + 2 = 2 * c by omega, show c - 1 + 1 = c by omega] at hα0
  generalize bitSum M bt sb J c = idx at hα0 ⊢
  have sc : ∀ i < 3, ((loop dims (capTpl lenL row A lo rlo m s bt sb c z sz) p).1.cell (2 * c + 1 + i) jf).val M =
      FE.ofK (gpow (lo + 4 * idx + (i + 1))) := by
    intro i hi
    have key : ∀ l, (loop dims (capTpl lenL row A lo rlo m s bt sb c z sz) p).1.tpl.getD (2 * c + 1 + i) default =
        ⟨.lin (gpow l + 1) 0, .K, [.cur (2 * c), .cur (2 * c)]⟩ → l = i + 1 →
        ((loop dims (capTpl lenL row A lo rlo m s bt sb c z sz) p).1.cell (2 * c + 1 + i) jf).val M =
          FE.ofK (gpow (lo + 4 * idx + (i + 1))) := by
      intro l hr hl
      have e := lrel_lin hr (hR _ (by omega))
      simp only [List.getD_cons_zero, List.getD_cons_succ, vc, hα0, ofK_zero, add_zero] at e
      rw [e, ← ofK_mul, ← ofK_add, ← hl, ← gpow_scale l, add_zero]
    interval_cases i
    · exact key 1 (hpost 0) rfl
    · exact key 2 (hpost 1) rfl
    · exact key 3 (hpost 2) rfl
  intro i hi
  rw [vc]
  rcases i with _ | i
  · simpa using hα0
  · have := sc i (by omega); rw [show 2 * c + (i + 1) = 2 * c + 1 + i by omega, this]

/-- **A cap loop's `readd`s are in region**: Boolean cap bits at every iteration, and the cap
region `[lo, lo + 4·2^c)` inside the `readd` region `[rlo, rlo + 2^m)`. -/
theorem capLoop_in {cx : Ctx} {M : Mem} {p : Ptr} {dims : List Nat} {lenL row A lo rlo m bt c z : Nat}
    {s sb sz : List Nat}
    (h : SegsHold cx M p (capLoop dims lenL row A lo rlo m s bt sb c z sz p).2) (hc : 1 ≤ c)
    (hb : ∀ jf < 2 ^ dims.sum, ∀ y < c,
      M.k (bt + y + dot sb (unflat dims jf)) = 0 ∨ M.k (bt + y + dot sb (unflat dims jf)) = 1)
    (h1 : rlo ≤ lo) (h2 : lo + 4 * 2 ^ c ≤ rlo + 2 ^ m) :
    SegsIn M p (capLoop dims lenL row A lo rlo m s bt sb c z sz p).2 := by
  have hlen := capTpl_length lenL row A lo rlo m s bt sb c z sz hc
  have hpost := capTpl_post lenL row A lo rlo m s bt sb c z sz hc
  -- the rows before the post rows are not `readd`s
  have hpre : ∀ t < 2 * c + 1, ¬ ∃ lo' m', ((capTpl lenL row A lo rlo m s bt sb c z sz).getD t default).op =
      .readd lo' m' := by
    rintro t ht ⟨lo', m', hop⟩
    by_cases h3 : t < 3
    · interval_cases t <;> simp [capTpl] at hop
    · obtain ⟨i, rfl⟩ : ∃ i, t = 3 + i := ⟨t - 3, by omega⟩
      rw [capTpl_chain _ _ _ _ _ _ _ _ _ _ _ _ (by omega)] at hop
      rcases Nat.even_or_odd' i with ⟨y, rfl | rfl⟩
      · have hy : y + 1 < c := by omega
        rw [(capChain_getD bt sb c y hy).1] at hop; simp at hop
      · have hy : y + 1 < c := by omega
        rw [(capChain_getD bt sb c y hy).2] at hop; simp at hop
  simp only [capLoop, hold_bind] at h
  simp only [capLoop, in_bind, SegsIn, and_true]
  refine ⟨loop_in (fun jf hjf t ht lo' m' args hr => ?_) (fun t ht lo' m' hop => ?_), trivial⟩
  · have hA := capAddr (p := p) (h := by simp only [capLoop, hold_bind]; exact ⟨h.1, trivial⟩) hjf hc (hb jf hjf)
    have hidx := bitSum_lt M bt sb (unflat dims jf) c
    rw [hlen] at ht
    by_cases ht1 : t < 2 * c + 1
    · exact absurd ⟨lo', m', by rw [hr]⟩ (hpre t ht1)
    · obtain ⟨i, rfl⟩ : ∃ i, t = 2 * c + 1 + i := ⟨t - (2 * c + 1), by omega⟩
      rw [hpost i] at hr
      have hi : i < 15 := by omega
      have hf : 4 * bitSum M bt sb (unflat dims jf) c + 4 ≤ 4 * 2 ^ c := by omega
      interval_cases i <;> simp at hr <;> obtain ⟨⟨rfl, rfl⟩, rfl⟩ := hr <;>
        simp only [List.getD_cons_zero]
      · exact rd_of_gpow (hA 0 (by omega)) (by omega) (by omega)
      · exact rd_of_gpow (hA 1 (by omega)) (by omega) (by omega)
      · exact rd_of_gpow (hA 2 (by omega)) (by omega) (by omega)
      · exact rd_of_gpow (hA 3 (by omega)) (by omega) (by omega)
  · rw [hlen] at ht
    by_cases ht1 : t < 2 * c + 1
    · exact absurd ⟨lo', m', hop⟩ (hpre t ht1)
    · obtain ⟨i, rfl⟩ : ∃ i, t = 2 * c + 1 + i := ⟨t - (2 * c + 1), by omega⟩
      rw [hpost i] at hop ⊢
      have hi : i < 15 := by omega
      interval_cases i <;> simp at hop ⊢

end Lvm.Loop.Build
end
end

section
section
set_option autoImplicit false
namespace Lvm.QLink
open RecursionFast Lvm Lvm.Replay Lvm.Loop Lvm.Loop.Build

theorem qltPadded_mem (p : Params) (lay : Layout) {jf : Nat} (hjf : jf < (qltPadded p lay).length) :
    (qltPadded p lay).getD jf (0, 0, 0) ∈ qltEntries p lay := by
  have h0 : (lay.sb, lay.sb + 1, lane0C) ∈ qltEntries p lay := by simp [qltEntries]
  unfold qltPadded at hjf ⊢
  rw [List.getD_eq_getElem _ _ hjf]
  rcases List.mem_append.mp (List.getElem_mem hjf) with h | h
  · exact h
  · rw [List.eq_of_mem_replicate h]; exact h0

end Lvm.QLink
end
end

section
section
set_option autoImplicit false
namespace Lvm.QLink
open RecursionFast Lvm Lvm.Replay Lvm.Loop Lvm.Loop.Build
variable {p : Params} {lay : Layout} {c : Ctx} {M : Mem}

attribute [local irreducible] Lvm.schedule in
/-- **Every `readd` of Q_link is in region** (its rows holding in `M`): the QLT cells hold
`qltData`, and every cap bit of every padded position is a bit. -/
theorem qlink_in (hQ : QOk p lay)
    (htab : ∀ x < (qltData p lay).length, M.k (lay.qt + x) = (qltData p lay).getD x 0)
    (hbits : ∀ k < (opens p).length, ∀ j < padT ((opens p).getD k default).L.t,
      ∀ z < ((opens p).getD k default).L.height,
      M.k (bitBase p lay k + ((opens p).getD k default).L.height * j + z) = 0 ∨
        M.k (bitBase p lay k + ((opens p).getD k default).L.height * j + z) = 1) :
    InOk c M (qlink p lay) := by
  have ho : ∀ k < (opens p).length, (opens p).getD k default ∈ opens p := fun k hk => by
    rw [List.getD_eq_getElem _ _ hk]; exact List.getElem_mem hk
  -- the QLT loop
  have hqlt : ∀ zo : Nat, InOk c M (qltLoop lay.aQ lay.qt lay.sb lay.m (kc lay.fg)) := by
    intro _ q h
    refine qltLoop_in h fun jf hjf => ?_
    have hl := qltPadded_length p lay hQ.qlen
    have hlen : (qltData p lay).length = 3 * 2 ^ lay.aQ := by rw [qltData, tblOf_length, hl]
    obtain ⟨g1, g2, -⟩ := tblOf_getD (qltPadded p lay) (k := jf) (by omega)
    obtain ⟨b1, b2, b3, b4, -⟩ := hQ.qbound _ (qltPadded_mem p lay (jf := jf) (by omega))
    refine ⟨_, _, ?_, ?_, b1, b3, b2, b4⟩
    · rw [htab _ (by omega)]; exact g1
    · rw [show lay.qt + 1 + 3 * jf = lay.qt + (3 * jf + 1) by omega, htab _ (by omega)]; exact g2
  -- one opening
  have hopen : ∀ zo k, k < (opens p).length →
      InOk c M (openLoops p lay zo (bitBase p lay k) ((opens p).getD k default)) := by
    intro zo k hk
    obtain ⟨hp1, hph, -, hcap, -⟩ := hQ.opens _ (ho k hk)
    generalize hog : (opens p).getD k default = o at hbits hp1 hph hcap
    have hb := hbits k hk
    rw [hog] at hb
    unfold openLoops
    refine inOk_bind (inOk_seqAll _ fun m hm => ?_) fun _ => inOk_pure _
    obtain ⟨cc, hcc, rfl⟩ := List.mem_map.mp hm
    have hend := pchunks_end cc hcc
    refine inOk_bind (fun q h => capLoop_in h (by omega) (fun jf hjf y hy => ?_) (by omega) (by omega))
      fun _ => inOk_bind (inOk_seqAll _ fun m' hm' => ?_) fun _ => inOk_pure _
    · have hj : jf < 2 ^ cc.2 := by simpa using hjf
      simp only [unflat_one' hjf, Loop.dot, Nat.add_zero]
      rw [show bitBase p lay k + o.L.height * cc.1 + o.L.path + y + o.L.height * jf =
        bitBase p lay k + o.L.height * (cc.1 + jf) + (o.L.path + y) by rw [Nat.mul_add]; omega]
      exact hb _ (by omega) _ (by omega)
    · obtain ⟨dd, -, rfl⟩ := List.mem_map.mp hm'
      exact inOk_noReadd fun _ => rfl
  unfold qlink qlinkCore
  refine inOk_bind (inOk_noReadd fun _ => rfl) fun _ =>
    inOk_bind (inOk_noReadd fun _ => rfl) fun q => inOk_bind (hqlt 0) fun _ =>
      inOk_bind (inOk_seqAll _ fun m hm => ?_) fun _ => inOk_pure _
  obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hm
  exact hopen _ k (List.mem_range.mp hk)

end Lvm.QLink
end
end

section
section
set_option autoImplicit false
namespace Lvm.Loop.Build
open Lvm.Loop

theorem bitsNat_lt (M : Mem) : ∀ bs : List Cell, bitsNat M bs < 2 ^ bs.length
  | [] => by simp [bitsNat]
  | _ :: bs => by
    have := bitsNat_lt M bs
    simp only [bitsNat, List.length_cons, Nat.pow_succ]
    split <;> omega

/-- **A straight-line `readd`'s region condition** is its address cell's. -/
theorem readd_in {M : Mem} {p : Ptr} {τ : Ty} {lo m : Nat} {α : Cell}
    (h : ∃ k < 2 ^ m, FK.x ^ (lo + k) = (α.val M).c₀) : SegsIn M p (readd τ lo m α p).2 := by
  refine ⟨?_, trivial⟩
  show ∃ k < 2 ^ m, FK.x ^ (lo + k) = (M.arg (rowInst p ⟨.readd lo m, τ, [α.addr]⟩) 0).c₀
  rw [rowInst_arg]
  exact h

theorem readd_in_gpow {M : Mem} {p : Ptr} {τ : Ty} {lo m e : Nat} {α : Cell}
    (hα : α.ty = .K) (hv : M.k α.n = gpow e) (h1 : lo ≤ e) (h2 : e < lo + 2 ^ m) :
    SegsIn M p (readd τ lo m α p).2 := by
  refine readd_in ⟨e - lo, by omega, ?_⟩
  obtain ⟨n, rfl⟩ : ∃ n, α = kc n := ⟨α.n, by cases α; simp_all [kc]⟩
  rw [show lo + (e - lo) = e by omega]
  simp only [Cell.val_K] at hv ⊢
  rw [hv]; rfl

theorem gpowBitsGo_noReadd (s : Nat) : ∀ (k : Nat) (acc : Cell) (bs : List Cell) (p : Ptr),
    noReaddSegs (gpowBits.gpowBitsGo s k acc bs p).2 = true
  | _, _, [], _ => rfl
  | k, acc, β :: bs, p => by
    rw [gpowBitsGo_cons]
    simp only [List.cons_append, List.nil_append, noReaddSegs, rowNoRd, Bool.true_and]
    exact gpowBitsGo_noReadd s _ _ bs _

/-- The address chain has no `readd`. -/
theorem gpowBits_noReadd (lo s : Nat) (x : Cell) : ∀ (bs : List Cell) (p : Ptr),
    noReaddSegs (gpowBits lo s x bs p).2 = true
  | [], _ => rfl
  | β :: bs, p => by
    rw [gpowBits_cons]
    simp only [List.cons_append, List.nil_append, noReaddSegs, rowNoRd, Bool.true_and]
    exact gpowBitsGo_noReadd s _ _ bs _

/-- **The address from bits is in `[lo, lo + s·(2^|bs| − 1)]`**: a `K` cell `g^e` with
`lo ≤ e ≤ lo + s·(2^|bs| − 1)`. -/
theorem gpowBits_in {c : Ctx} {M : Mem} {lo s : Nat} {x : Cell} {bs : List Cell} {p : Ptr}
    (hx : x.ty = .K) (hb : ∀ β ∈ bs, IsBit M β) (h : SegsHold c M p (gpowBits lo s x bs p).2) :
    (gpowBits lo s x bs p).1.ty = .K ∧ ∃ e, M.k (gpowBits lo s x bs p).1.n = gpow e ∧ lo ≤ e ∧
      e ≤ lo + s * (2 ^ bs.length - 1) := by
  obtain ⟨h1, h2⟩ := gpowBits_spec hx hb h
  have := bitsNat_lt M bs
  exact ⟨h1, _, h2, by omega, by have := Nat.mul_le_mul_left s (show bitsNat M bs ≤ 2 ^ bs.length - 1 by omega); omega⟩

/-- **Read at an address from bits**: `g^(lo + s · Σ β_k 2^k)`, then `readd τ rlo m`. -/
def readdBits (τ : Ty) (rlo m lo s : Nat) (x : Cell) (bs : List Cell) : BM Cell := do
  let a ← gpowBits lo s x bs
  readd τ rlo m a

/-- **A `readdBits` site is in region** (its rows holding, its bits bits) when the bits' range
`[lo, lo + s·(2^|bs| − 1)]` lies in the `readd` region. One instance per new site. -/
theorem readdBits_in {c : Ctx} {M : Mem} {τ : Ty} {rlo m lo s : Nat} {x : Cell} {bs : List Cell}
    (hx : x.ty = .K) (hb : ∀ β ∈ bs, IsBit M β) (h1 : rlo ≤ lo)
    (h2 : lo + s * (2 ^ bs.length - 1) < rlo + 2 ^ m) : InOk c M (readdBits τ rlo m lo s x bs) := by
  intro p h
  unfold readdBits at h ⊢
  rw [hold_bind] at h
  rw [in_bind]
  obtain ⟨hK, e, he, he1, he2⟩ := gpowBits_in hx hb h.1
  exact ⟨segsIn_of_noReadd M p _ (gpowBits_noReadd lo s x bs p),
    readd_in_gpow hK he (by omega) (by omega)⟩

end Lvm.Loop.Build
end
end

section
section
set_option autoImplicit false
namespace Lvm.Inb
open LeanVM.Parameters LeanVM.Protocol CompPoly Lvm Lvm.Bits Lvm.M3 Lvm.Loop Lvm.BitsTab
section Aux
variable (Q : Program) (pl : ℕ → Var → Bool × ℕ) (groups : List Grp) (arrs : List InArr)
  (aux : List Tab) (L : Lay) (hτ : ∀ t ∈ lvmTabs Q pl groups arrs aux, t.τ ≤ L.μ)

/-- WP-9b's `AuxHyps` without `wf` and `inb`. -/
structure AuxH0 (q : Column L.μ) : Prop where
  grp : GrpOk Q groups
  inOk : InOk Q arrs
  auxSeeds : ∀ t ∈ aux, t.seeds = []
  cnt : ∀ t ∈ lvmTabs Q pl groups arrs aux, ∀ r ∈ t.reads, r.2 < t.w
  len : nReads (lvmTabs Q pl groups arrs aux) < 2 ^ 64 - 1
  inj : GInj (max (Q.cells .K) (Q.cells .E))
  holds : M3Holds (lvmInst Q pl groups arrs aux L hτ) () q

/-- The seed memory's `K` cells on the stack `q`. -/
noncomputable def seedK (q : Column L.μ) : Nat → FK :=
  (Q.seedMem (witOf Q pl groups arrs aux L hτ q) (inKOf Q pl groups arrs aux L hτ q)
    (inEOf Q pl groups arrs aux L hτ q)).k

/-- **An auxiliary table's read is a cell of the interpreter's run** (the `BITS` bridge). At row `x`
of auxiliary table `k` (instance table `groups.length + arrs.length + k`), the read `r`'s
separator, address and value limbs, evaluated on the row, are those of cell `e` of memory `τ` of
`seedMem (witOf q) (inKOf q) (inEOf q)`, for some `e` below the cell count. -/
theorem aux_read0 (q : Column L.μ) (H : AuxH0 Q pl groups arrs aux L hτ q) {k : ℕ}
    (hk : k < aux.length)
    (hj : groups.length + arrs.length + k < (lvmTabs Q pl groups arrs aux).length)
    (x : Fin (2 ^ ((lvmTabs Q pl groups arrs aux).get ⟨_, hj⟩).τ)) {r : Key × ℕ}
    (hr : r ∈ aux[k].reads) :
    ∃ τ e, e < Q.cells τ ∧ r.1.sep = sep τ ∧
      CPoly.evalB (CPoly.ext ((lvmInst Q pl groups arrs aux L hτ).row q ⟨_, hj⟩ x)) r.1.addr =
        FK.toBF64 (FK.x ^ e) ∧
      ∀ l < 13, CPoly.evalB (CPoly.ext ((lvmInst Q pl groups arrs aux L hτ).row q ⟨_, hj⟩ x))
          (r.1.val.getD l []) =
        FK.toBF64 ((limbsOf τ ((Q.seedMem (witOf Q pl groups arrs aux L hτ q) (inKOf Q pl groups arrs aux L hτ q)
          (inEOf Q pl groups arrs aux L hτ q)).rd τ e)).getD l 0) := by
  set W := witOf Q pl groups arrs aux L hτ q
  set inK := inKOf Q pl groups arrs aux L hτ q
  set inE := inEOf Q pl groups arrs aux L hτ q
  have hget := get_aux Q pl groups arrs aux hk hj
  set row := (lvmInst Q pl groups arrs aux L hτ).row q ⟨_, hj⟩ x
  have hrd : r ∈ ((lvmTabs Q pl groups arrs aux).get ⟨_, hj⟩).reads := by rw [hget]; exact hr
  have hu : evalV row (((lvmTabs Q pl groups arrs aux).get ⟨_, hj⟩).readVec r) ∈
      readTuples L (lvmTabs Q pl groups arrs aux) hτ q := by
    simp only [readTuples, partT, List.mem_flatMap, List.mem_map]
    refine ⟨⟨_, hj⟩, List.mem_finRange _, _, ⟨_, hrd, rfl⟩, x, ?_, rfl⟩
    simp [M3Instance.executed, inst]
  obtain ⟨s, hs, hks⟩ := List.mem_map.mp (mem_lookup L (lvmTabs Q pl groups arrs aux) hτ q
    H.holds.2.1 H.holds.2.2.1 H.cnt H.len _ hu)
  obtain ⟨m', -, hm', he⟩ := seed_key Q pl groups arrs aux L hτ H.grp H.inOk H.auxSeeds q hs
  obtain ⟨τ, e, hec, h1, h2, h3⟩ := Q.seed_cases W inK inE hm'
  have hkey : keyT (evalV row (((lvmTabs Q pl groups arrs aux).get ⟨_, hj⟩).readVec r)) =
      keyT (encT m') := hks.symm.trans he
  have hcoord : ∀ i (hi : i < 16), i ≠ 2 →
      (evalV row (((lvmTabs Q pl groups arrs aux).get ⟨_, hj⟩).readVec r))[i] = (encT m')[i] :=
    fun i hi hi2 ↦ keyT_coord hkey i hi hi2
  refine ⟨τ, e, hec, ?_, ?_, fun l hl ↦ ?_⟩
  · have := hcoord 0 (by norm_num) (by norm_num)
    simp only [evalV, Tab.readVec, Key.vec, Vector.getElem_map, Vector.getElem_ofFn, encT,
      if_true, MvPolynomial.eval_C] at this
    exact (FK.toBF64_injective this).trans h1
  · have := hcoord 1 (by norm_num) (by norm_num)
    simp only [evalV, Tab.readVec, Key.vec, Vector.getElem_map, Vector.getElem_ofFn, encT,
      show (1 : ℕ) ≠ 0 from by decide, if_true, if_false, CPoly.eval_toMv] at this
    rw [this, h2]
  · have := hcoord (l + 3) (by omega) (by omega)
    simp only [evalV, Tab.readVec, Key.vec, Vector.getElem_map, Vector.getElem_ofFn, encT,
      show l + 3 ≠ 0 from by omega, show l + 3 ≠ 1 from by omega, show l + 3 ≠ 2 from by omega,
      if_false, Nat.add_sub_cancel, CPoly.eval_toMv] at this
    rw [this, h3]


/-- **An auxiliary table's read at a known address is that cell of the interpreter's run**: if the
read names memory `τ` and evaluates its address to `g^a` with `a` below the cell count, its value
limbs are cell `a`'s. -/
theorem aux_read_at0 (q : Column L.μ) (H : AuxH0 Q pl groups arrs aux L hτ q) {k : ℕ}
    (hk : k < aux.length)
    (hj : groups.length + arrs.length + k < (lvmTabs Q pl groups arrs aux).length)
    (x : Fin (2 ^ ((lvmTabs Q pl groups arrs aux).get ⟨_, hj⟩).τ)) {r : Key × ℕ}
    (hr : r ∈ aux[k].reads) {τ : Ty} {a : ℕ} (hsep : r.1.sep = sep τ) (ha : a < Q.cells τ)
    (haddr : CPoly.evalB (CPoly.ext ((lvmInst Q pl groups arrs aux L hτ).row q ⟨_, hj⟩ x))
      r.1.addr = FK.toBF64 (FK.x ^ a)) :
    ∀ l < 13, CPoly.evalB (CPoly.ext ((lvmInst Q pl groups arrs aux L hτ).row q ⟨_, hj⟩ x))
        (r.1.val.getD l []) =
      FK.toBF64 ((limbsOf τ ((Q.seedMem (witOf Q pl groups arrs aux L hτ q) (inKOf Q pl groups arrs aux L hτ q)
          (inEOf Q pl groups arrs aux L hτ q)).rd τ a)).getD l 0) := by
  obtain ⟨τ', e, he, h1, h2, h3⟩ := aux_read0 Q pl groups arrs aux L hτ q H hk hj x hr
  obtain rfl : τ' = τ := sep_inj' (h1.symm.trans hsep)
  have hN : ∀ σ, Q.cells σ ≤ max (Q.cells .K) (Q.cells .E) := fun σ ↦ by cases σ <;> simp
  obtain rfl : e = a := H.inj _ _ (lt_of_lt_of_le he (hN _)) (lt_of_lt_of_le ha (hN _))
    (FK.toBF64_injective (h2.symm.trans haddr))
  exact h3


/-- **`BITS` soundness through the bus.** At a real row `x` of a `BITS` table of `aux`, whose
cells lie below `Q.cells .K`, the row's word `w` is the word cell's value (when `rd`) and output
cell `oc j x` holds output `j`'s word function of `w`. -/
theorem out_sound0 (q : Column L.μ) (H : AuxH0 Q pl groups arrs aux L hτ q) (S : BSpec)
    (hS : S.tab ∈ aux) {x : Nat} (hx : x < S.n) (hn : S.n ≤ 2 ^ S.τ)
    (hw : S.rd = true → S.wc x < Q.cells .K) (ho : ∀ j < S.outs.length, S.oc j x < Q.cells .K) :
    ∃ w : FK, (S.rd = true → seedK Q pl groups arrs aux L hτ q (S.wc x) = w) ∧
      ∀ j < S.outs.length, (S.out j).Valid →
        seedK Q pl groups arrs aux L hτ q (S.oc j x) = ⟨(S.out j).word w.val⟩ := by
  obtain ⟨k, hk, hak⟩ := List.mem_iff_getElem.mp hS
  have hj : groups.length + arrs.length + k < (lvmTabs Q pl groups arrs aux).length := by
    rw [lvmTabs_length]; omega
  have hT : (lvmTabs Q pl groups arrs aux).get ⟨_, hj⟩ = S.tab :=
    (get_aux Q pl groups arrs aux hk hj).trans hak
  have hxT : x < 2 ^ ((lvmTabs Q pl groups arrs aux).get ⟨_, hj⟩).τ := by
    rw [hT]; show x < 2 ^ S.τ; omega
  set xF : Fin (2 ^ ((lvmTabs Q pl groups arrs aux).get ⟨_, hj⟩).τ) := ⟨x, hxT⟩
  set u := CPoly.ext ((lvmInst Q pl groups arrs aux L hτ).row q ⟨_, hj⟩ xF) with hu
  set M := Q.seedMem (witOf Q pl groups arrs aux L hτ q) (inKOf Q pl groups arrs aux L hτ q)
          (inEOf Q pl groups arrs aux L hτ q)
  have hrow : S.row x = x := if_pos hx
  -- the fixed address columns
  have hfix : ∀ (c : Nat) (a : Nat → Nat), c < S.width → S.col c = S.adrCol a →
      u c = FK.toBF64 (FK.x ^ a x) := by
    intro c a hc hcol
    have hcw : c < ((lvmTabs Q pl groups arrs aux).get ⟨_, hj⟩).w := by
      rw [hT, BSpec.tab_w]; exact hc
    have hf : ((lvmTabs Q pl groups arrs aux).get ⟨_, hj⟩).fixedOf c =
        some fun x => FK.x ^ a (S.row x) := by
      rw [hT, Tab.fixedOf, BSpec.tab_cols S c hc, hcol]; rfl
    have := row_fixed Q pl groups arrs aux L hτ q ⟨_, hj⟩ xF ⟨c, hcw⟩ hf
    rw [hu, CPoly.ext, dif_pos hcw, this, hrow]
  -- a read at a fixed address column is the cell's value
  have hread : ∀ (r : Key × Nat) (c : Nat) (a : Nat → Nat) (P : CPoly), r ∈ S.reads → r.1.sep = sep .K →
      r.1.addr = CPoly.var c → r.1.val = [P] → c < S.width → S.col c = S.adrCol a →
      a x < Q.cells .K → CPoly.evalB u P = FK.toBF64 (M.k (a x)) := by
    intro r c a P hr hsep haddr hval hc hcol hlt
    have hr' : r ∈ aux[k].reads := by rw [hak]; exact hr
    have := aux_read_at0 Q pl groups arrs aux L hτ q H hk hj xF hr' hsep hlt
      (by rw [haddr, BitsTab.evalB_var]; exact hfix c a hc hcol) 0 (by norm_num)
    rw [hval] at this
    simpa [limbsOf, Mem.rd, FE.ofK] using this
  -- a read whose address evaluates to `g^e`
  have hreadA : ∀ (r : Key × Nat) (e : Nat) (P : CPoly), r ∈ S.reads → r.1.sep = sep .K →
      CPoly.evalB u r.1.addr = FK.toBF64 (FK.x ^ e) → r.1.val = [P] →
      e < Q.cells .K → CPoly.evalB u P = FK.toBF64 (M.k e) := by
    intro r e P hr hsep haddr hval hlt
    have hr' : r ∈ aux[k].reads := by rw [hak]; exact hr
    have := aux_read_at0 Q pl groups arrs aux L hτ q H hk hj xF hr' hsep hlt haddr 0 (by norm_num)
    rw [hval] at this
    simpa [limbsOf, Mem.rd, FE.ofK] using this
  -- the constraints on the `FK` row
  set v : Nat → FK := fun i => FK.ofBF64 (u i)
  have hcons : ∀ C ∈ cons, evalK v C = 0 := by
    intro C hC
    have hC' : C ∈ aux[k].cons := by rw [hak]; exact hC
    have := aux_cons Q pl groups arrs aux L hτ q H.holds hk hj xF hC'
    rw [evalB_eq] at this
    exact FK.toBF64_injective (this.trans FK.toBF64_zero.symm)
  obtain ⟨-, hout⟩ := row_sound (rowOf_cons hcons)
  have hwid : 66 < S.width := by unfold BSpec.width BSpec.ab; omega
  refine ⟨(rowOf v).w, fun hrd => ?_, fun j hj' hv => ?_⟩
  · have h := hread BSpec.wread 66 S.wc (CPoly.var 0)
      (by simp [BSpec.reads, hrd]) rfl rfl rfl hwid (by simp [BSpec.col]) (hw hrd)
    rw [BitsTab.evalB_var] at h
    show M.k (S.wc x) = FK.ofBF64 (u 0)
    rw [h]; rfl
  · have h := hreadA (S.oread j) (S.oc j x) (outPoly (S.out j))
      (by simp only [BSpec.reads, List.mem_append, List.mem_map, List.mem_range]
          exact Or.inr ⟨j, hj', rfl⟩)
      rfl (S.oaddr_eval u hx (fun c a hc hcol => hfix c a hc hcol) hj') rfl (ho j hj')
    rw [evalB_eq, rowOf_out, hout _ hv] at h
    exact (FK.toBF64_injective h).symm

theorem and_one_01 (u : UInt64) : u &&& 1 = 0 ∨ u &&& 1 = 1 := by
  rcases Nat.mod_two_eq_zero_or_one u.toNat with h | h
  · left; apply UInt64.toNat_inj.mp; simp [UInt64.toNat_and, Nat.and_one_is_mod, h]
  · right; apply UInt64.toNat_inj.mp; simp [UInt64.toNat_and, Nat.and_one_is_mod, h]

/-- **A `bit` output cell holds `0` or `1`** on the seed memory. -/
theorem seedK_bit (q : Column L.μ) (H : AuxH0 Q pl groups arrs aux L hτ q) (S : BSpec)
    (hS : S.tab ∈ aux) {x : Nat} (hx : x < S.n) (hn : S.n ≤ 2 ^ S.τ)
    (hw : S.rd = true → S.wc x < Q.cells .K) (ho : ∀ j < S.outs.length, S.oc j x < Q.cells .K)
    {j z : Nat} (hj : j < S.outs.length) (hb : S.out j = .bit z) (hz : z < 64) :
    seedK Q pl groups arrs aux L hτ q (S.oc j x) = 0 ∨ seedK Q pl groups arrs aux L hτ q (S.oc j x) = 1 := by
  obtain ⟨w, -, h2⟩ := out_sound0 Q pl groups arrs aux L hτ q H S hS hx hn hw ho
  have := h2 j hj (by rw [hb]; exact hz)
  rw [this, hb]
  rcases and_one_01 (w.val >>> z.toUInt64) with h | h
  · left; simp only [BOut.word, h]; rfl
  · right; simp only [BOut.word, h]; rfl

end Aux
end Lvm.Inb
end
end

section
section
set_option autoImplicit false
namespace Lvm.NS
open RecursionFast Lvm Lvm.T Lvm.ASM Lvm.Replay Lvm.Loop Lvm.Loop.Build Lvm.QLink Lvm.QSig Lvm.M3
open Lvm.SigBits Lvm.BitsTab Lvm.Inb LeanVM.Protocol

/-- **The position classes cover the cap bits**: every bit cell of every (padded) position of every
opening is a `bit z` output of a real row of a `BITS` table in `aux`, its cells inside `Q`. -/
def CapCov (p : Params) (Q : Program) (lay : Layout) (aux : List Tab) : Prop :=
  ∀ k < (opens p).length, ∀ j < padT ((opens p).getD k default).L.t,
    ∀ z < ((opens p).getD k default).L.height,
    ∃ S : BitsTab.BSpec, S.tab ∈ aux ∧ S.n ≤ 2 ^ S.τ ∧ ∃ x < S.n,
      (S.rd = true → S.wc x < Q.cells .K) ∧ (∀ jo < S.outs.length, S.oc jo x < Q.cells .K) ∧
      ∃ jo < S.outs.length, ∃ z' < 64, S.out jo = .bit z' ∧
        S.oc jo x = bitBase p lay k + ((opens p).getD k default).L.height * j + z

end Lvm.NS
end
end

section
section
set_option autoImplicit false
namespace Lvm.NS
open RecursionFast Lvm Lvm.T Lvm.ASM Lvm.Replay Lvm.Loop Lvm.Loop.Build Lvm.QLink Lvm.QSig Lvm.M3
open Lvm.SigBits Lvm.BitsTab Lvm.Inb LeanVM.Protocol
section Seed
variable {α : Type} {m : BM α} {nK nE : ℕ}
  {pl : ℕ → Var → Bool × ℕ} {groups : List Grp} {arrs : List InArr} {aux : List Tab} {L : Lay}
  {hτ : ∀ t ∈ lvmTabs (toProgram nK nE m) pl groups arrs aux, t.τ ≤ L.μ}

/-- The seed (committed) memory of a stack `q`. -/
noncomputable abbrev seedOf (q : Column L.μ) : Loop.Mem :=
  (toProgram nK nE m).seedMem (witOf (toProgram nK nE m) pl groups arrs aux L hτ q)
    (inKOf (toProgram nK nE m) pl groups arrs aux L hτ q) (inEOf (toProgram nK nE m) pl groups arrs aux L hτ q)

theorem seedOf_inK (q : Column L.μ) {n : ℕ} (hn : n < nK) :
    (seedOf (m := m) (pl := pl) (groups := groups) (arrs := arrs) (aux := aux) (hτ := hτ) q).k n =
      (inKOf (toProgram nK nE m) pl groups arrs aux L hτ q).getD n 0 := by
  show (if n < nK then _ else _) = _; rw [if_pos hn]

/-- **`inb` from the seed memory**: for any gadget `m`, if its segments' `readd`s are in region in
the seed memory whenever its rows hold there, the interpreter finds every cell. Each part of a node
program proves its `SegsIn` (by `InOk` lemmas: `qlink_in`, `readdBits_in`, `loop_in`, or
`segsIn_of_noReadd`), using the seed memory's facts (`seedOf_inK`, `seedK_bit`). -/
theorem inb_of_seed {q : Column L.μ} (hwf : (toProgram nK nE m).wf = true)
    (H0 : AuxH0 (toProgram nK nE m) pl groups arrs aux L hτ q)
    (hIn : SegsHold (ctxOf (toProgram nK nE m)) (seedOf (m := m) (pl := pl) (groups := groups) (arrs := arrs)
        (aux := aux) (hτ := hτ) q) ⟨nK, nE⟩ (m ⟨nK, nE⟩).2 →
      SegsIn (seedOf (m := m) (pl := pl) (groups := groups) (arrs := arrs) (aux := aux) (hτ := hτ) q)
        ⟨nK, nE⟩ (m ⟨nK, nE⟩).2) :
    ((toProgram nK nE m).interp (inKOf (toProgram nK nE m) pl groups arrs aux L hτ q)
      (inEOf (toProgram nK nE m) pl groups arrs aux L hτ q)).inb = true := by
  have hsz := And.intro (inKOf_size (toProgram nK nE m) pl groups arrs aux L hτ q)
    (inEOf_size (toProgram nK nE m) pl groups arrs aux L hτ q)
  obtain ⟨hH, -⟩ := (toProgram nK nE m).holds_seedMem hwf
    (loop_cons _ pl groups arrs aux L hτ H0.grp _ H0.holds)
    (loop_bus _ pl groups arrs aux L hτ H0.grp H0.inOk H0.auxSeeds H0.cnt H0.len _ H0.holds) H0.inj
  have hin : (toProgram nK nE m).Inputs (seedOf (m := m) (pl := pl) (groups := groups) (arrs := arrs)
      (aux := aux) (hτ := hτ) q) (inKOf (toProgram nK nE m) pl groups arrs aux L hτ q)
      (inEOf (toProgram nK nE m) pl groups arrs aux L hτ q) :=
    ⟨fun n hn => by simp [seedOf, Program.seedMem, hn], fun n hn => by simp [seedOf, Program.seedMem, hn]⟩
  exact (toProgram nK nE m).inb_of_mem hwf _ _ hsz _ hin hH H0.inj
    (toProgram_in nK nE m _ (hIn ((toProgram_holds nK nE m _).mp hH)))

end Seed
end Lvm.NS
end
end

section
section
set_option autoImplicit false
namespace Lvm.NS
open RecursionFast Lvm Lvm.T Lvm.ASM Lvm.Replay Lvm.Loop Lvm.Loop.Build Lvm.QLink Lvm.QSig Lvm.M3
open Lvm.SigBits Lvm.BitsTab Lvm.Inb LeanVM.Protocol
section Gen
variable {α : Type} {p : Params} {lay : Layout} {I : SigIn} {qa : BM α} {nK nE : ℕ}
  {pl : ℕ → Var → Bool × ℕ} {groups : List Grp} {arrs : List InArr} {aux : List Tab} {L : Lay}
  {hτ : ∀ t ∈ lvmTabs (toProgram nK nE (qprogP p lay I qa)) pl groups arrs aux, t.τ ≤ L.μ}

/-- **Every `readd` of the node program finds its cell** on any stack `q` with `M3Holds`: the
program check and `WP-9b`'s static facts (`AuxH0`), Q_link's static checks, the `QLT` input cells
holding `qltData`, the position classes covering the cap bits, no `readd` in Q_sig and Q_arith. -/
theorem inb_of_m3 {q : Column L.μ} (hwf : (toProgram nK nE (qprogP p lay I qa)).wf = true)
    (H0 : AuxH0 (toProgram nK nE (qprogP p lay I qa)) pl groups arrs aux L hτ q)
    (hQ : QOk p lay)
    (htabK : ∀ y < (qltData p lay).length, lay.qt + y < nK ∧
      (inKOf (toProgram nK nE (qprogP p lay I qa)) pl groups arrs aux L hτ q).getD (lay.qt + y) 0 =
        (qltData p lay).getD y 0)
    (hcov : CapCov p (toProgram nK nE (qprogP p lay I qa)) lay aux)
    (hsig : noReaddSegs (qsig I ((⟨nK, nE⟩ : Ptr).adv (qlink p lay ⟨nK, nE⟩).2)).2 = true)
    (harr : noReaddSegs (qa (((⟨nK, nE⟩ : Ptr).adv (qlink p lay ⟨nK, nE⟩).2).adv
      (qsig I ((⟨nK, nE⟩ : Ptr).adv (qlink p lay ⟨nK, nE⟩).2)).2)).2 = true) :
    ((toProgram nK nE (qprogP p lay I qa)).interp
      (inKOf (toProgram nK nE (qprogP p lay I qa)) pl groups arrs aux L hτ q)
      (inEOf (toProgram nK nE (qprogP p lay I qa)) pl groups arrs aux L hτ q)).inb = true := by
  refine inb_of_seed hwf H0 fun hh => ?_
  have htab : ∀ y < (qltData p lay).length, (seedOf (m := qprogP p lay I qa) (pl := pl) (groups := groups)
      (arrs := arrs) (aux := aux) (hτ := hτ) q).k (lay.qt + y) = (qltData p lay).getD y 0 := fun y hy => by
    rw [seedOf_inK q (htabK y hy).1]; exact (htabK y hy).2
  have hbits : ∀ k < (opens p).length, ∀ j < padT ((opens p).getD k default).L.t,
      ∀ z < ((opens p).getD k default).L.height,
      (seedOf (m := qprogP p lay I qa) (pl := pl) (groups := groups) (arrs := arrs) (aux := aux) (hτ := hτ) q).k
          (bitBase p lay k + ((opens p).getD k default).L.height * j + z) = 0 ∨
        (seedOf (m := qprogP p lay I qa) (pl := pl) (groups := groups) (arrs := arrs) (aux := aux) (hτ := hτ) q).k
          (bitBase p lay k + ((opens p).getD k default).L.height * j + z) = 1 := by
    intro k hk j hj z hz
    obtain ⟨S, hS, hn, xr, hx, hw, ho, jo, hjo, z', hz', hb, hc⟩ := hcov k hk j hj z hz
    have := seedK_bit _ pl groups arrs aux L hτ q H0 S hS hx hn hw ho hjo hb hz'
    rw [hc] at this
    exact this
  generalize seedOf (m := qprogP p lay I qa) (pl := pl) (groups := groups) (arrs := arrs) (aux := aux)
    (hτ := hτ) q = M at hh htab hbits ⊢
  have hh' := (hold_bind (ctxOf (toProgram nK nE (qprogP p lay I qa))) M (qlink p lay)
    (fun _ => (qsig I >>= fun _ => qa)) ⟨nK, nE⟩).mp hh
  exact (in_bind M (qlink p lay) (fun _ => (qsig I >>= fun _ => qa)) ⟨nK, nE⟩).mpr
    ⟨qlink_in hQ htab hbits _ hh'.1, (in_bind M _ _ _).mpr ⟨segsIn_of_noReadd M _ _ hsig,
      segsIn_of_noReadd M _ _ harr⟩⟩

end Gen
end Lvm.NS
end
end

section
section
set_option autoImplicit false
namespace Lvm.NS
open RecursionFast Lvm Lvm.T Lvm.ASM Lvm.Replay Lvm.Loop Lvm.Loop.Build Lvm.QLink Lvm.QSig Lvm.M3
open Lvm.SigBits Lvm.BitsTab Lvm.Inb LeanVM.Protocol
section Inb
variable {α : Type} {lay : Layout} {I : SigIn} {qa : BM α} {nK nE : ℕ}
  {pl : ℕ → Var → Bool × ℕ} {groups : List Grp} {arrsX : List UInt8 → List InArr} {aux : List Tab}
  {hτ' : ∀ x, ∀ t ∈ lvmTabs (Qn lay I qa nK nE) pl groups (arrsX x) aux, t.τ ≤ lay26.μ}

/-- **`hinb` for the node program** (`nodeSound_layout`'s hypothesis, `vk` outermost). `hqlt` is
`nodeSound_layout`'s own; it is used only on input cells (`interpMem_inK`, no `inb`). -/
theorem hinb_node {T : List UInt8 → List Tab} {hτ : ∀ x, ∀ t ∈ T x, t.τ ≤ lay26.μ}
    (hT : ∀ x, T x = lvmTabs (Qn lay I qa nK nE) pl groups (arrsX x) aux)
    (hst : ∀ x, AuxStatic lay I qa nK nE pl groups aux (arrsX x))
    (hQ : QOk P20 lay)
    (hqtK : lay.qt + (qltData P20 lay).length ≤ nK)
    (hcov : CapCov P20 (Qn lay I qa nK nE) lay aux)
    (hsig : noReaddSegs (qsig I (p1 lay nK nE)).2 = true)
    (harr : noReaddSegs (qa (p2 lay I nK nE)).2 = true)
    (hqlt : ∀ vk c x qm qr, okS vk c x = true → (hdrOf x).b = 1 → GoodN T hτ x qm qr →
      ∀ y < (qltData P20 lay).length,
        (memX lay I qa nK nE pl groups arrsX aux hτ' x qm qr).k (lay.qt + y) = (qltData P20 lay).getD y 0) :
    ∀ vk c x qm qr, okS vk c x = true → (hdrOf x).b = 1 → GoodN T hτ x qm qr →
      ((Qn lay I qa nK nE).interp (inKOf (Qn lay I qa nK nE) pl groups (arrsX x) aux lay26 (hτ' x)
        (stackOf lay26 qm qr)) (inEOf (Qn lay I qa nK nE) pl groups (arrsX x) aux lay26 (hτ' x)
        (stackOf lay26 qm qr))).inb = true := by
  intro vk c x qm qr hok hb hG
  have st := hst x
  have hM3 : M3Holds (lvmInst (Qn lay I qa nK nE) pl groups (arrsX x) aux lay26 (hτ' x)) ()
      (stackOf lay26 qm qr) := m3Holds_congr (hT x) hG.1
  have hsz := inKOf_size (Qn lay I qa nK nE) pl groups (arrsX x) aux lay26 (hτ' x) (stackOf lay26 qm qr)
  refine inb_of_m3 (p := P20) st.wf ⟨st.grp, st.inOk, st.auxSeeds, st.cnt, st.len, st.inj, hM3⟩ hQ
    (fun y hy => ⟨by omega, ?_⟩) hcov hsig harr
  rw [← hqlt vk c x qm qr hok hb hG y hy]
  exact ((Qn lay I qa nK nE).interpMem_inK _ _ (lt_of_lt_of_eq (show lay.qt + y < nK by omega) hsz.symm)).symm

end Inb
end Lvm.NS
end
end

section
set_option autoImplicit false
namespace Lvm.QAsm
open RecursionFast Lvm Lvm.T Lvm.ASM Lvm.Replay Lvm.Loop Lvm.Loop.Build Lvm.QLink Lvm.QSig Lvm.M3
open Lvm.SigBits Lvm.Bits Lvm.BitsTab Lvm.Inb Lvm.NS LeanVM.Protocol

/-- The position classes' cells lie inside `Q` (as Q_sig's `SigCellsLt`): per lane class `l` and class
row `r = (k, o, x, sb)`, the word cell (a stream lane) and every output cell (`posOc`). Independent of
the placement `bpl`. -/
def PosCellsLt (Q : Program) (C : QCfg) : Prop :=
  ∀ l < nPosCls C, ∀ r ∈ posRows C l, ansLane C.p (r.2.1.pe + r.2.2.1) + l < Q.cells .K ∧
    ∀ j < (lnOuts C.p l).length, posOc C l (lnOuts C.p l) r j < Q.cells .K

end Lvm.QAsm
end

section
set_option autoImplicit false
namespace Lvm.QAsm
open RecursionFast Lvm Lvm.T Lvm.ASM Lvm.Replay Lvm.Loop Lvm.Loop.Build Lvm.QLink Lvm.QSig Lvm.M3
open Lvm.SigBits Lvm.Bits Lvm.BitsTab Lvm.Inb Lvm.NS LeanVM.Protocol

/-- A class output that is not the opening's lies past its bits. -/
theorem laneBits_le_of_find {p : Params} {l : Nat} {ko : Nat × OpenInfo} (h : ko ∈ lnOps p l) {j : Nat}
    (hn : (laneOuts ko.2.L.height l).find? (fun e => e.1 == (lnOuts p l).getD j (.bit 0)) = none) :
    laneBits ko.2.L.height l ≤ j := by
  by_contra hj
  have hb : j < lnBits p l := lt_of_lt_of_le (by (clear * - hj; omega)) (laneBits_le_lnBits h)
  have hu : (lnOuts p l).getD j (.bit 0) = .bit j := by
    unfold lnOuts
    rw [List.getD_append _ _ _ _ (by simpa using hb)]
    simp [hb]
  have hm := mem_laneOuts_bit (H := ko.2.L.height) (l := l) (z := j) (by simp only [laneBits] at hj; (clear * - hj; omega))
    (by simp only [laneBits] at hj; (clear * - hj; omega))
  rw [List.find?_eq_none] at hn
  exact hn _ hm (by rw [hu]; simp)

end Lvm.QAsm
end

section
set_option autoImplicit false
namespace Lvm.QAsm
open RecursionFast Lvm Lvm.T Lvm.ASM Lvm.Replay Lvm.Loop Lvm.Loop.Build Lvm.QLink Lvm.QSig Lvm.M3
open Lvm.SigBits Lvm.Bits Lvm.BitsTab Lvm.Inb Lvm.NS LeanVM.Protocol

/-- **A class row's cells lie inside `Q`** (`PosCellsLt`). -/
theorem posCellsLt_spec {Q : Program} {C : QCfg} (hpc : PosCellsLt Q C) (bpl : Nat → Nat → Bool × Nat)
    {S : BSpec} (hS : S ∈ posSpecs C bpl) {y : Nat} (hy : y < S.n) :
    (S.rd = true → S.wc y < Q.cells .K) ∧ ∀ j < S.outs.length, S.oc j y < Q.cells .K := by
  obtain ⟨l, hl, rfl⟩ := List.mem_map.mp hS
  rw [posSpec_n] at hy
  have h := hpc l (List.mem_range.mp hl) _ (List.getElem_mem hy)
  refine ⟨fun _ => ?_, fun j hj => ?_⟩
  · rw [posSpec_wc, List.getD_eq_getElem _ _ hy]; exact h.1
  · rw [posSpec_outs] at hj
    rw [posSpec_oc, List.getD_eq_getElem _ _ hy]; exact h.2 j hj

end Lvm.QAsm
end

section
set_option autoImplicit false
namespace Lvm.QAsm
open RecursionFast Lvm Lvm.T Lvm.ASM Lvm.Replay Lvm.Loop Lvm.Loop.Build Lvm.QLink Lvm.QSig Lvm.M3
open Lvm.SigBits Lvm.Bits Lvm.BitsTab Lvm.Inb Lvm.NS LeanVM.Protocol

/-- **The position classes cover the cap bits.** -/
theorem capCov_pos (C : QCfg) (Q : Program) (aux : List Tab) (bpl : Nat → Nat → Bool × Nat)
    (haux : ∀ S ∈ posSpecs C bpl, S.tab ∈ aux) (hpc : PosCellsLt Q C) : CapCov C.p Q (lay C) aux := by
  intro k hk j hj z hz
  obtain ⟨S, hS, hτ, -, y, hy, -, jo, hjo, hout, hoc⟩ := posSpecs_bit C bpl hk hj hz
  have hc := posCellsLt_spec hpc bpl hS hy
  exact ⟨S, haux _ hS, hτ, y, hy, hc.1, hc.2, jo, hjo, _, Nat.mod_lt _ (by norm_num), hout, hoc⟩

theorem posSpecs_aux (C : QCfg) (D : QData) {S : BSpec} (h : S ∈ posSpecs C fun c => bplOf D (6 + c)) :
    S.tab ∈ aux C D :=
  List.mem_map_of_mem (List.mem_append_left _ (List.mem_append_right _ h))

set_option maxRecDepth 100000 in
theorem noReadd_sig20 : noReaddSegs (qsig (sigIn cfg20) (p1C cfg20)).2 = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem noReadd_sig8 : noReaddSegs (qsig (sigIn cfg8) (p1C cfg8)).2 = true := by decide +kernel

theorem qlt_le_nK20 (hQ : QOk P20 (lay cfg20)) : (lay cfg20).qt + (qltData P20 (lay cfg20)).length ≤ nK cfg20 := by
  rw [qltData, tblOf_length, qltPadded_length _ _ hQ.qlen]
  show qtB cfg20 + 3 * 2 ^ 11 ≤ qtB cfg20 + 2 ^ 13 + 2 ^ 15
  (clear * -; omega)

theorem qlt_le_nK8 (hQ : QOk P8 (lay cfg8)) : (lay cfg8).qt + (qltData P8 (lay cfg8)).length ≤ nK cfg8 := by
  rw [qltData, tblOf_length, qltPadded_length _ _ hQ.qlen]
  show qtB cfg8 + 3 * 2 ^ 11 ≤ qtB cfg8 + 2 ^ 13 + 2 ^ 16
  (clear * -; omega)

end Lvm.QAsm
end

section
set_option autoImplicit false
namespace Lvm.QAsm
open RecursionFast Lvm Lvm.T Lvm.ASM Lvm.Replay Lvm.Loop Lvm.Loop.Build Lvm.QLink Lvm.QSig Lvm.M3
open Lvm.SigBits Lvm.Bits Lvm.BitsTab Lvm.Inb Lvm.NS LeanVM.Protocol
section P20
variable {pl : ℕ → Var → Bool × ℕ} {groups : List Grp} {arrsX : List UInt8 → List InArr} {D : QData}
  {hτ' : ∀ x, ∀ t ∈ lvmTabs (Qn (lay cfg20) (sigIn cfg20) (qarith cfg20) (nK cfg20) 0) pl groups (arrsX x)
    (aux cfg20 D), t.τ ≤ lay26.μ}

/-- **`hinb` for WP-16a's `P20` node program** (`NodeHyp.hinb`): from `nodeSound_layout`'s `hT`,
`hst`, `hQ`, `hqlt` and the position classes' cell bounds. -/
theorem hinb20 {T : List UInt8 → List Tab} {hτ : ∀ x, ∀ t ∈ T x, t.τ ≤ lay26.μ}
    (hT : ∀ x, T x = lvmTabs (Qn (lay cfg20) (sigIn cfg20) (qarith cfg20) (nK cfg20) 0) pl groups (arrsX x)
      (aux cfg20 D))
    (hst : ∀ x, AuxStatic (lay cfg20) (sigIn cfg20) (qarith cfg20) (nK cfg20) 0 pl groups (aux cfg20 D) (arrsX x))
    (hQ : QOk P20 (lay cfg20))
    (hqlt : ∀ vk c x qm qr, okS vk c x = true → (hdrOf x).b = 1 → GoodN T hτ x qm qr →
      ∀ y < (qltData P20 (lay cfg20)).length,
        (memX (lay cfg20) (sigIn cfg20) (qarith cfg20) (nK cfg20) 0 pl groups arrsX (aux cfg20 D) hτ' x qm qr).k
          ((lay cfg20).qt + y) = (qltData P20 (lay cfg20)).getD y 0)
    (hpc : PosCellsLt (Qn (lay cfg20) (sigIn cfg20) (qarith cfg20) (nK cfg20) 0) cfg20)
    (hna : noReaddSegs (qarith cfg20 (p2C cfg20)).2 = true) :
    ∀ vk c x qm qr, okS vk c x = true → (hdrOf x).b = 1 → GoodN T hτ x qm qr →
      ((Qn (lay cfg20) (sigIn cfg20) (qarith cfg20) (nK cfg20) 0).interp
        (inKOf (Qn (lay cfg20) (sigIn cfg20) (qarith cfg20) (nK cfg20) 0) pl groups (arrsX x) (aux cfg20 D)
          lay26 (hτ' x) (stackOf lay26 qm qr))
        (inEOf (Qn (lay cfg20) (sigIn cfg20) (qarith cfg20) (nK cfg20) 0) pl groups (arrsX x) (aux cfg20 D)
          lay26 (hτ' x) (stackOf lay26 qm qr))).inb = true :=
  hinb_node hT hst hQ (qlt_le_nK20 hQ)
    (capCov_pos cfg20 _ (aux cfg20 D) (fun c => bplOf D (6 + c)) (fun _ h => posSpecs_aux cfg20 D h) hpc)
    noReadd_sig20 hna hqlt

end P20
end Lvm.QAsm
end

section
set_option autoImplicit false
namespace Lvm.QAsm
open RecursionFast Lvm Lvm.T Lvm.ASM Lvm.Replay Lvm.Loop Lvm.Loop.Build Lvm.QLink Lvm.QSig Lvm.M3
open Lvm.SigBits Lvm.Bits Lvm.BitsTab Lvm.Inb Lvm.NS LeanVM.Protocol
section P8
variable {pl : ℕ → Var → Bool × ℕ} {groups : List Grp} {arrs : List InArr} {D : QData} {L : Lay}
  {hτ : ∀ t ∈ lvmTabs (Q cfg8) pl groups arrs (aux cfg8 D), t.τ ≤ L.μ}

/-- **Every `readd` of WP-16a's `P8` node program finds its cell** on a stack with `M3Holds` (in
`AuxH0`), with the program check, Q_link's static checks, the `QLT` inputs and the position classes'
cell bounds. -/
theorem inb8 {q : Column L.μ} (hwf : (Q cfg8).wf = true)
    (H0 : AuxH0 (Q cfg8) pl groups arrs (aux cfg8 D) L hτ q) (hQ : QOk P8 (lay cfg8))
    (htab : ∀ y < (qltData P8 (lay cfg8)).length,
      (inKOf (Q cfg8) pl groups arrs (aux cfg8 D) L hτ q).getD ((lay cfg8).qt + y) 0 = (qltData P8 (lay cfg8)).getD y 0)
    (hpc : PosCellsLt (Q cfg8) cfg8) (hna : noReaddSegs (qarith cfg8 (p2C cfg8)).2 = true) :
    ((Q cfg8).interp (inKOf (Q cfg8) pl groups arrs (aux cfg8 D) L hτ q)
      (inEOf (Q cfg8) pl groups arrs (aux cfg8 D) L hτ q)).inb = true :=
  inb_of_m3 (p := P8) (lay := lay cfg8) (I := sigIn cfg8) (qa := qarith cfg8) hwf H0 hQ
    (fun y hy => ⟨by have := qlt_le_nK8 hQ; (clear * - hy this; omega), htab y hy⟩)
    (capCov_pos cfg8 _ (aux cfg8 D) (fun c => bplOf D (6 + c)) (fun _ h => posSpecs_aux cfg8 D h) hpc)
    noReadd_sig8 hna

end P8
end Lvm.QAsm
end
