-- lvm6 F1: facts about WP S's compiled scheme `schemeOf` (= V1's `V.scheme6V` walk) that the frame uses:
-- the seed (`FORMAT6.md` v2.5 §3), the commitments' caps and leaves (§5), and no language-level grind.
import Lvm6Stmt
import LvmCertSFrame

/-!
# `schemeOf` at `FORMAT6.md`'s bytes

`schemeOf prog sh vk` is V1's specified scheme (`Lvm6VSpec`) with the program `prog` (`V.schemeP`, WP ASM's
decision): the statement is the header bytes, reads of the widths `rwOf (sched6 sh)`, a draw `.sample` with
its proof of work as a `fail` branch. What this module checks:

* **`seedQ6`**, **`seed_length`**: after a passing header check, the seed is `a₀ ‖ HDR` (v2.5: `c`
  inside `HDR`), `168 + 16 v` bytes;
* **`leaf_P18`**: caps `2^7, 2^6, 2^5, 2^5, 2^5`, leaves of 368 and 256 bytes (level 0: 46 of 64 lanes;
  levels 1–4: 32-word rows), paths of 14, 14, 14, 13, 12 siblings;
* **`walk_noGrind`**: the schedule walk with any decision uses no `grind` node (season 1's compiler
  rejects it; grinding is the nonce lane and the draw's `pw` test). For `schemeOf prog`, `kcert6`'s
  `hng` is a hypothesis on `prog` (WP ASM: `prog6_noGrind`, from the schedule).

The draw value and the PoW lane are WP S's `e2OfE_chalOf` and `powOK6_iff`.
-/

set_option autoImplicit false

namespace Lvm6

open RecursionFast LeanVM.Parameters
open LeanVM.Protocol.Compile hiding Proof Bytes Word

variable {prog : Shape → Digest → List UInt8 → VerifierProgram Bool} {sh : Shape} {vk : Digest}

/-- **The seed** (§3, v2.5): after a passing header check, the compiled verifier's second query is
`a₀ ‖ HDR` (v2.5: `enc6` is the header bytes; `c` is inside `HDR`). -/
theorem seedQ6 {c : Digest} {x : List UInt8} (_h : (schemeOf prog sh vk).ok c x = true) (a₀ : Digest) :
    (schemeOf prog sh vk).seedQ a₀ x = Lvm.FS.toQ (a₀.toList ++ x) := by
  simp [Lvm.FS.Scheme.seedQ, schemeOf, V.schemeP, V.scheme6V, V.enc6]

/-- The seed's length: `168 + 16 v` for a header of `hdrLen sh` bytes (856 at `P18`). -/
theorem seed_length (a₀ : Digest) {x : List UInt8} (hx : x.length = hdrLen sh) :
    (a₀.toList ++ x).length = 168 + 16 * sh.phiVars := by
  simp only [List.length_append, Vector.length_toList, hx, hdrLen]
  omega

/-- **`P18`'s commitments** (§5): cap level, leaf bytes `8 · min(occ, w)`, siblings `ht − lv`. -/
theorem leaf_P18 :
    [(21, 64), (20, 32), (19, 32), (18, 32), (17, 32)].map (fun p : ℕ × ℕ ↦
        (V.capOfL P18.levs p.1 p.2, 8 * min (V.occL P18.levs p.1 p.2) p.2,
          p.1 - V.capOfL P18.levs p.1 p.2)) =
      [(7, 368, 14), (6, 256, 14), (5, 256, 14), (5, 256, 13), (5, 256, 12)] := by decide +kernel

/-! ## No language-level grind -/

/-- A step of the specification that keeps "no grind" for every continuation that has it. -/
def NGSt (f : V.St) : Prop :=
  ∀ ps acc (k : V.Kt), (∀ ps' acc', (k ps' acc').NoGrind) → (f ps acc k).NoGrind

theorem ngSt_seq {f g : V.St} (hf : NGSt f) (hg : NGSt g) : NGSt (V.PS.seq f g) :=
  fun ps acc k hk ↦ hf ps acc _ fun ps' acc' ↦ hg ps' acc' k hk

theorem ngSt_skip : NGSt V.PS.skip := fun ps acc _ hk ↦ hk ps acc

theorem ngSt_rd (w : ℕ) : NGSt (V.PS.rd w) := fun ps _ _ hk ↦ fun _ ↦ hk ps _

theorem ngSt_draw (chk : ℕ → Bool) (upd : List ℕ → ℕ → List ℕ) : NGSt (V.PS.draw chk upd) :=
  by
    intro ps acc k hk c
    show LeanVM.Protocol.Compile.VerifierProgram.NoGrind
      (if chk (LeanVM.Protocol.Verifier.eToNat c) then
        k (upd ps (LeanVM.Protocol.Verifier.eToNat c)) (.c c :: acc) else .fail)
    split
    · exact hk _ _
    · trivial

theorem ngSt_cap (ht w : ℕ) : NGSt (V.PS.cap ht w) := fun ps acc _ hk ↦ hk ps _

theorem ngSt_reset : NGSt V.PS.reset := fun _ acc _ hk ↦ hk [] acc

theorem ngSt_opn (i : ℕ) : NGSt (V.PS.opn i) := fun ps _ _ hk ↦ fun _ ↦ hk ps _

theorem ngSt_rep {f : V.St} (hf : NGSt f) : ∀ m, NGSt (V.PS.rep f m)
  | 0 => ngSt_skip
  | m + 1 => ngSt_seq hf (ngSt_rep hf m)

theorem ngSt_posRest (ht : ℕ) : ∀ cs, NGSt (V.PS.posRest ht cs)
  | [] => ngSt_skip
  | _ :: cs => ngSt_seq (ngSt_draw _ _) (ngSt_posRest ht cs)

theorem ngSt_item (L : List V.Lev) (it : V.Item) : NGSt (V.PS.item L it) := by
  cases it with
  | E k => exact ngSt_rep (ngSt_rd _) _
  | K k => exact ngSt_rep (ngSt_rd _) _
  | cap i => exact ngSt_cap _ _
  | G g => exact ngSt_seq (ngSt_rd _) (ngSt_draw _ _)
  | D k => exact ngSt_rep (ngSt_draw _ _) _
  | B => exact ngSt_draw _ _
  | pos i g => exact ngSt_seq ngSt_reset (ngSt_seq (ngSt_rd _) (ngSt_seq (ngSt_draw _ _)
      (ngSt_posRest _ _)))
  | «open» i => exact ngSt_opn _

theorem ngSt_walk (L : List V.Lev) : ∀ items, NGSt (V.PS.walk L items)
  | [] => ngSt_skip
  | it :: r => ngSt_seq (ngSt_item L it) (ngSt_walk L r)

/-- **The schedule walk uses no `grind` node**, for every decision. -/
theorem walk_noGrind (dec : List UInt8 → List V.Val → Bool) (x : List UInt8) :
    ((V.scheme6V (toV sh) vk dec).P x).NoGrind :=
  ngSt_walk _ _ [] [] _ fun _ _ ↦ trivial

end Lvm6
