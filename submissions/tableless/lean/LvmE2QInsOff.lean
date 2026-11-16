/- `LvmE2QInsOff` (GOLF2 off-path move, group 44 of 48): declarations that the certificate `certified`
   does not use, moved here verbatim (same names, same namespaces and context) from LvmE2QIns,
   so that `Solution`'s import closure need not elaborate them. Import this module where they are needed;
   the name -> module map is GOLF2's moved.tsv. -/
import LvmE2QIns

-- ===== from `LvmE2QIns` =====

section
set_option autoImplicit false
namespace Lvm.Q1
open Lvm Lvm.Loop Lvm.Loop.Build

end Lvm.Q1
end

section
set_option autoImplicit false
namespace Lvm.Q1
open Lvm Lvm.Loop Lvm.Loop.Build

/-- `a + b` in `E2`. -/
def add2I (a b : S2) : List Ins := lin2I 1 0 a b

theorem lin2I_val {xv : Src → FE} {ins : List Ins} {V : List FE} (hF : Fix xv ins V) {n : Nat} {k : FK}
    {k' : FE2} {a b : S2} (hseg : Seg ins n (lin2I k k' a b)) (hlen : n + 2 ≤ ins.length) :
    twinVal V n = a.val xv V + FE2.ofK k * b.val xv V + k' :=
  e2I_val hF hseg hlen

end Lvm.Q1
end

section
set_option autoImplicit false
namespace Lvm.Q1
open Lvm Lvm.Loop Lvm.Loop.Build

end Lvm.Q1
end

section
set_option autoImplicit false
namespace Lvm.Q1
open Lvm Lvm.Loop Lvm.Loop.Build

theorem horner2_length (x : S2) (n : Nat) (h : S2) (cs : List S2) :
    (horner2 x n h cs).length = 2 * cs.length := by
  induction cs generalizing n h with
  | nil => rfl
  | cons c cs ih => simp only [horner2, List.length_append, ih]; simp [mul2I, e2I]; omega

/-- A segment's prefix. -/
theorem seg_prefix {ins : List Ins} {n : Nat} {A B : List Ins} (h : Seg ins n (A ++ B)) : Seg ins n A := by
  intro i hi
  rw [h i (by simp; omega), List.getD_eq_getElem?_getD, List.getElem?_append_left hi,
    ← List.getD_eq_getElem?_getD]

/-- Where a Horner chain's value is. -/
def hornerSrc2 (n : Nat) (h : S2) (cs : List S2) : S2 := if cs = [] then h else locS2 (n + 2 * cs.length - 2)

/-- **The Horner chain's value.** -/
theorem horner2_val {xv : Src → FE} {ins : List Ins} {V : List FE} (hF : Fix xv ins V) (x : S2) :
    ∀ (cs : List S2) (n : Nat) (h : S2), Seg ins n (horner2 x n h cs) → n + 2 * cs.length ≤ ins.length →
      (hornerSrc2 n h cs).val xv V = (cs.map (S2.val xv V)).foldl (fun acc c ↦ acc * x.val xv V + c) (h.val xv V)
  | [], _, _, _, _ => rfl
  | c :: cs, n, h, hseg, hlen => by
    have hm : (mul2I h x c).length = 2 := rfl
    have h0 := mul2I_val hF (n := n) (a := h) (b := x) (d := c) (seg_prefix hseg) (by simp at hlen; omega)
    have hs : Seg ins (n + 2) (horner2 x (n + 2) (locS2 n) cs) := by
      have := seg_sub hseg (mul2I h x c) (horner2 x (n + 2) (locS2 n) cs) rfl
      rwa [hm] at this
    have ih := horner2_val hF x cs (n + 2) (locS2 n) hs (by simp at hlen; omega)
    rw [locS2_val, h0] at ih
    rw [List.map_cons, List.foldl_cons, ← ih]
    simp only [hornerSrc2, List.length_cons]
    by_cases hc : cs = []
    · subst hc; simp [locS2_val, h0]
    · simp only [hc, if_false, reduceCtorEq]
      congr 2 <;> omega

end Lvm.Q1
end
