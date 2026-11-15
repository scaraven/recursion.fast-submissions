-- New for lvm2 E2F (E2F-QH4): the `E2` Keccak layer template's layout facts (`layOk2`), decided by the kernel per shape
-- (`P = 15`: the tape at P20; `P = 9`: `KS` at P20), as `LvmQKeccakGkr`'s `layOk_11`/`layOk_15` for `E3`.
import LvmE2QKLayer

/-!
# `layOk2` at the P20 shapes

The kernel decides `layOk2 P` on the RMFE literals (`projLit`, `embedLit`): `layOk2_eq_lit` rewrites it into
`layOk2T (layerTB2T projLit embedLit) P`, where `layerTB2T` is `layerTB2` with the two tables as parameters
(`layerTB2_eq_tbl`, by `rfl`) and `layOk2T T` is `layOk2` with `T` in place of `layerTB2` (`layOk2_eq_T`, by `rfl`).
The proofs then rewrite `layerTB2T` into `layerTB2F` (`layerTB2T_eq_F`) and `layOk2T` into `layOk2TR` (`layOk2T_eq_R`),
the same values in forms the kernel evaluates faster (GOLF's `layOk` scheme for `E3`, `LvmQKeccakGkr` on `lvm2/GOLF`).
-/

set_option autoImplicit false

namespace Lvm.Q1

open Lvm Lvm.Loop Lvm.Loop.Build

/-- `layerTB2` with the RMFE tables `pr` (`rmfeProject`), `em` (`rmfeEmbed`) as parameters. -/
def layerTB2T (pr em : List Nat) (c : LCfg) : TB Unit :=
  let str := [c.str2]
  let value := c.pv2 0
  let mu := (List.range 16).map fun i => c.pv2 (1 + i)
  let kappa := c.pv2 17
  let point := (List.range (c.P + 1)).map fun i => c.pv2 (18 + i)
  let B := (List.range 25).map fun l => c.pv2 (19 + c.P + l)
  let a := (List.range 6).map fun i => c.pv2 (44 + c.P + i)
  let flips := (List.range 7).map fun i => c.pv2 (50 + c.P + i)
  let q := c.q
  let prod := (List.range productBits).map fun k => lane2 (q + 2 * k) str
  let s := lane2 (q + 104) str
  q2Base (.ext ⟨.K, q, str⟩) >>= fun base =>
  let zK := base.1
  let z := base.2.1
  let one := base.2.2
  q2Proj z pr mu prod >>= fun proj =>
  q2One (point.getD c.P default) >>= fun seg0 =>
  q2Dot z ((List.range 7).map fun i => (kS2 (c.k i) zK, flips.getD i default)) >>= fun in0 =>
  q2Dot z ((List.range 7).map fun i => (kS2 (c.k (7 + i)) zK, flips.getD i default)) >>= fun in1 =>
  q2Dot z [(seg0, in0), (point.getD c.P default, in1)] >>= fun iota =>
  q2Mul iota kappa proj >>= fun e1 => q2Add e1 value >>= fun e1' => q2Assert e1' (c.k 15) >>= fun _ =>
  q2Inst z one s em >>= fun mk =>
  q2Horner s (prod.getD 46 default) ((List.range 46).reverse.map fun k => prod.getD k default) >>= fun v0 =>
  q2PackRounds z str (q + 113) point v0 one >>= fun pk =>
  q2LocalRounds str 11 (q + 113 + 14 * (c.P + 1)) pk.1 >>= fun lc =>
  let q3 := q + 289 + 14 * (c.P + 1)
  let t := (List.range 3).map fun k => lane2 (q3 + 2 * k) str
  let beta := lane2 (q3 + 7) str
  q2EqTab z [one] (lc.2.take 3) >>= fun tbLo => q2EqTab z [one] ((lc.2.drop 3).take 3) >>= fun tbHi =>
  q2EqTab z [one] (a.take 3) >>= fun taLo => q2EqTab z [one] (a.drop 3) >>= fun taHi =>
  q2EqTab z [one] (lc.2.drop 6) >>= fun eL =>
  mapT2 (q2LowTab z taLo tbLo 0) (List.range 8) >>= fun L0 =>
  mapT2 (q2LowTab z taLo tbLo 1) (List.range 8) >>= fun L1 =>
  mapT2 (q2HighTab z taHi tbHi) (List.range 8) >>= fun H =>
  mapT2 (q2Shift z L0 L1 H) (List.range 64) >>= fun sh =>
  q2SumMap z 25 (fun l => q2LaneForm z B (fun r => sh.getD r default) l >>= fun lf =>
    q2Mul (eL.getD l default) lf z) >>= fun Wk =>
  q2SumMap z 25 (fun l => q2Mul (eL.getD l default) (B.getD l default) z) >>= fun dfB =>
  q2Index z 0 one (lc.2.take 6) >>= fun idx => q2Mul dfB idx z >>= fun Wf =>
  q2Add Wf Wk >>= fun d => q2Mul (kS2 (c.k 14) zK) d Wk >>= fun W =>
  q2Mul mk.2 (t.getD 0 default) z >>= fun kt0 => q2Add mk.2 (t.getD 1 default) >>= fun k1 =>
  q2Mul k1 (t.getD 2 default) kt0 >>= fun m => q2Mul pk.2.1 W z >>= fun sw => q2Mul sw m lc.1 >>= fun e2 =>
  q2Assert e2 (c.k 15) >>= fun _ =>
  q2Mul beta (t.getD 2 default) (t.getD 1 default) >>= fun tt => q2Mul beta tt (t.getD 0 default) >>= fun v' =>
  q2LaneW eL beta >>= fun B' =>
  q2EqTab z [one] (lc.2.take 6) >>= fun A' =>
  mapT2 (q2Flip z B' A') (List.range 7) >>= fun fl =>
  mapT2 q2Copy ([v'] ++ mk.1 ++ [mk.2] ++ pk.2.2 ++ B' ++ lc.2.take 6 ++ fl) >>= fun _ => pure ()

theorem layerTB2_eq_tbl : layerTB2 = layerTB2T rmfeProject rmfeEmbed := rfl

/-- `cbOf2` for the template builder `T`. -/
def cbOf2T (T : LCfg → TB Unit) (P : Nat) : Nat := (T ⟨P, 0, 0, 0⟩ 0).2.length - 2 * (57 + P)

/-- `lay02` for the template builder `T`. -/
def lay02T (T : LCfg → TB Unit) (P : Nat) : LCfg := ⟨P, 0, 0, cbOf2T T P⟩

/-- `layIns2` for the template builder `T`. -/
def layIns2T (T : LCfg → TB Unit) (P : Nat) : List Ins := (T (lay02T T P) 0).2

/-- `layOk2` for the template builder `T`. -/
def layOk2T (T : LCfg → TB Unit) (P : Nat) : Bool :=
  (layIns2T T P).length == cbOf2T T P + 2 * (57 + P) &&
  (layIns2T T P).all (fun i => i.op != .assert0 || i.args.getD 1 default == (lay02T T P).k 15) &&
  ((layIns2T T P).drop (cbOf2T T P)).all fun i => i.ty == .K && i.op != .assert0

theorem layOk2_eq_T (P : Nat) : layOk2 P = layOk2T layerTB2 P := rfl

theorem layOk2_eq_lit (P : Nat) : layOk2 P = layOk2T (layerTB2T projLit embedLit) P := by
  rw [layOk2_eq_T, layerTB2_eq_tbl, rmfeProject_eq, rmfeEmbed_eq]

/-! ## Fast evaluation of the layer template (proof help)

`mapT2` ends each step in `pure`, so its instructions are `l₀ ++ ((l₁ ++ (… ++ [])) ++ [])`: a kernel walk of the list
takes element `j` through `j` appends. The `F` copies build the same pair with every tail on the right (`mapT2_eq_F`
…, by induction, no evaluation); `layerTB2T_eq_F` puts them into the template before the kernel decides. -/

/-- `mapT2` with the tail on the right. -/
def mapT2F {α β : Type} (f : α → TB β) : List α → TB (List β)
  | [] => fun _ => ([], [])
  | a :: as => fun n =>
    let r := f a n
    let r' := mapT2F f as (n + r.2.length)
    (r.1 :: r'.1, r.2 ++ r'.2)

theorem mapT2_eq_F {α β : Type} : @mapT2 α β = @mapT2F α β := by
  funext f l n
  induction l generalizing n with
  | nil => rfl
  | cons a as ih => simp only [mapT2, mapT2F, tb_bind, tb_pure, ih, List.append_nil]

/-- `q2Powers` with the tail on the right. -/
def q2PowersF (z s : S2) : S2 → Nat → TB (List S2)
  | _, 0 => fun _ => ([], [])
  | acc, k + 1 => fun n =>
    let r := q2Mul acc s z n
    let r' := q2PowersF z s r.1 k (n + r.2.length)
    (acc :: r'.1, r.2 ++ r'.2)

theorem q2Powers_eq_F (z s : S2) : ∀ (acc : S2) (k : Nat), q2Powers z s acc k = q2PowersF z s acc k
  | _, 0 => rfl
  | acc, k + 1 => by
    funext n
    simp only [q2Powers, q2PowersF, tb_bind, tb_pure, q2Powers_eq_F z s _ k, List.append_nil]

/-- `q2SumMap` through `mapT2F`. -/
def q2SumMapF (z : S2) (k : Nat) (f : Nat → TB S2) : TB S2 :=
  mapT2F f (List.range k) >>= fun ts => q2Sum z ts

theorem q2SumMap_eq_F : q2SumMap = q2SumMapF := by
  funext z k f; simp only [q2SumMap, q2SumMapF, mapT2_eq_F]

/-- `q2Proj` through `q2SumMapF`. -/
def q2ProjF (z : S2) (masks : List Nat) (mu prod : List S2) : TB S2 :=
  q2SumMapF z prod.length fun c => q2Sum z (projSrcs2 masks mu c) >>= fun P => q2Mul P (prod.getD c default) z

theorem q2Proj_eq_F : q2Proj = q2ProjF := by
  funext z masks mu prod; simp only [q2Proj, q2ProjF, q2SumMap_eq_F]

/-- `q2Inst` through `q2PowersF`, `mapT2F`. -/
def q2InstF (z one s : S2) (embs : List Nat) : TB (List S2 × S2) :=
  q2PowersF z s one embedBits >>= fun pw => mapT2F (fun e => q2Sum z (embSrcs2 pw e)) embs >>= fun mu =>
    q2Sum z mu >>= fun kappa => pure (mu, kappa)

theorem q2Inst_eq_F : q2Inst = q2InstF := by
  funext z one s embs; simp only [q2Inst, q2InstF, q2Powers_eq_F, mapT2_eq_F]

/-- `q2EqStep` through `mapT2F`. -/
def q2EqStepF (z : S2) (tab : List S2) (r : S2) : TB (List S2) :=
  q2One r >>= fun r1 => mapT2F (fun e => q2Mul e r1 z) tab >>= fun lo =>
    mapT2F (fun e => q2Mul e r z) tab >>= fun hi => pure (lo ++ hi)

/-- `q2EqTab` through `q2EqStepF`. -/
def q2EqTabF (z : S2) : List S2 → List S2 → TB (List S2)
  | tab, [] => pure tab
  | tab, r :: rs => q2EqStepF z tab r >>= fun t => q2EqTabF z t rs

theorem q2EqTab_eq_F (z : S2) : ∀ (tab pt : List S2), q2EqTab z tab pt = q2EqTabF z tab pt
  | _, [] => rfl
  | tab, r :: rs => by
    have e : q2EqStep z tab r = q2EqStepF z tab r := by simp only [q2EqStep, q2EqStepF, mapT2_eq_F]
    simp only [q2EqTab, q2EqTabF, e, q2EqTab_eq_F z _ rs]

/-- `q2LowTab` through `q2SumMapF`. -/
def q2LowTabF (z : S2) (ta tb : List S2) (c rl : Nat) : TB S2 :=
  q2SumMapF z 8 fun zz => if (zz + rl) / 8 = c then q2Mul (tb.getD zz default) (ta.getD ((zz + rl) % 8) default) z
    else pure z

theorem q2LowTab_eq_F : q2LowTab = q2LowTabF := by
  funext z ta tb c rl; simp only [q2LowTab, q2LowTabF, q2SumMap_eq_F]

/-- `q2HighTab` through `q2SumMapF`. -/
def q2HighTabF (z : S2) (ta tb : List S2) (k : Nat) : TB S2 :=
  q2SumMapF z 8 fun zz => q2Mul (tb.getD zz default) (ta.getD ((zz + k) % 8) default) z

theorem q2HighTab_eq_F : q2HighTab = q2HighTabF := by
  funext z ta tb k; simp only [q2HighTab, q2HighTabF, q2SumMap_eq_F]

/-- `q2LaneW` through `mapT2F`. -/
def q2LaneWF (eL : List S2) (beta : S2) : TB (List S2) :=
  mapT2F (fun l => q2Mul beta (eL.getD (keccakAlong (64 * l) 3 / 64) default)
    (eL.getD (keccakAlong (64 * l) 4 / 64) default) >>= fun u => q2Mul beta u (eL.getD l default)) (List.range 25)

theorem q2LaneW_eq_F : q2LaneW = q2LaneWF := by
  funext eL beta; simp only [q2LaneW, q2LaneWF, mapT2_eq_F]

/-- `layerTB2T` through the `F` gadgets. -/
def layerTB2F (pr em : List Nat) (c : LCfg) : TB Unit :=
  let str := [c.str2]
  let value := c.pv2 0
  let mu := (List.range 16).map fun i => c.pv2 (1 + i)
  let kappa := c.pv2 17
  let point := (List.range (c.P + 1)).map fun i => c.pv2 (18 + i)
  let B := (List.range 25).map fun l => c.pv2 (19 + c.P + l)
  let a := (List.range 6).map fun i => c.pv2 (44 + c.P + i)
  let flips := (List.range 7).map fun i => c.pv2 (50 + c.P + i)
  let q := c.q
  let prod := (List.range productBits).map fun k => lane2 (q + 2 * k) str
  let s := lane2 (q + 104) str
  q2Base (.ext ⟨.K, q, str⟩) >>= fun base =>
  let zK := base.1
  let z := base.2.1
  let one := base.2.2
  q2ProjF z pr mu prod >>= fun proj =>
  q2One (point.getD c.P default) >>= fun seg0 =>
  q2Dot z ((List.range 7).map fun i => (kS2 (c.k i) zK, flips.getD i default)) >>= fun in0 =>
  q2Dot z ((List.range 7).map fun i => (kS2 (c.k (7 + i)) zK, flips.getD i default)) >>= fun in1 =>
  q2Dot z [(seg0, in0), (point.getD c.P default, in1)] >>= fun iota =>
  q2Mul iota kappa proj >>= fun e1 => q2Add e1 value >>= fun e1' => q2Assert e1' (c.k 15) >>= fun _ =>
  q2InstF z one s em >>= fun mk =>
  q2Horner s (prod.getD 46 default) ((List.range 46).reverse.map fun k => prod.getD k default) >>= fun v0 =>
  q2PackRounds z str (q + 113) point v0 one >>= fun pk =>
  q2LocalRounds str 11 (q + 113 + 14 * (c.P + 1)) pk.1 >>= fun lc =>
  let q3 := q + 289 + 14 * (c.P + 1)
  let t := (List.range 3).map fun k => lane2 (q3 + 2 * k) str
  let beta := lane2 (q3 + 7) str
  q2EqTabF z [one] (lc.2.take 3) >>= fun tbLo => q2EqTabF z [one] ((lc.2.drop 3).take 3) >>= fun tbHi =>
  q2EqTabF z [one] (a.take 3) >>= fun taLo => q2EqTabF z [one] (a.drop 3) >>= fun taHi =>
  q2EqTabF z [one] (lc.2.drop 6) >>= fun eL =>
  mapT2F (q2LowTabF z taLo tbLo 0) (List.range 8) >>= fun L0 =>
  mapT2F (q2LowTabF z taLo tbLo 1) (List.range 8) >>= fun L1 =>
  mapT2F (q2HighTabF z taHi tbHi) (List.range 8) >>= fun H =>
  mapT2F (q2Shift z L0 L1 H) (List.range 64) >>= fun sh =>
  q2SumMapF z 25 (fun l => q2LaneForm z B (fun r => sh.getD r default) l >>= fun lf =>
    q2Mul (eL.getD l default) lf z) >>= fun Wk =>
  q2SumMapF z 25 (fun l => q2Mul (eL.getD l default) (B.getD l default) z) >>= fun dfB =>
  q2Index z 0 one (lc.2.take 6) >>= fun idx => q2Mul dfB idx z >>= fun Wf =>
  q2Add Wf Wk >>= fun d => q2Mul (kS2 (c.k 14) zK) d Wk >>= fun W =>
  q2Mul mk.2 (t.getD 0 default) z >>= fun kt0 => q2Add mk.2 (t.getD 1 default) >>= fun k1 =>
  q2Mul k1 (t.getD 2 default) kt0 >>= fun m => q2Mul pk.2.1 W z >>= fun sw => q2Mul sw m lc.1 >>= fun e2 =>
  q2Assert e2 (c.k 15) >>= fun _ =>
  q2Mul beta (t.getD 2 default) (t.getD 1 default) >>= fun tt => q2Mul beta tt (t.getD 0 default) >>= fun v' =>
  q2LaneWF eL beta >>= fun B' =>
  q2EqTabF z [one] (lc.2.take 6) >>= fun A' =>
  mapT2F (q2Flip z B' A') (List.range 7) >>= fun fl =>
  mapT2F q2Copy ([v'] ++ mk.1 ++ [mk.2] ++ pk.2.2 ++ B' ++ lc.2.take 6 ++ fl) >>= fun _ => pure ()

theorem layerTB2T_eq_F : layerTB2T = layerTB2F := by
  funext pr em c
  simp only [layerTB2T, layerTB2F, mapT2_eq_F, q2Proj_eq_F, q2Inst_eq_F, q2EqTab_eq_F, q2LowTab_eq_F,
    q2HighTab_eq_F, q2SumMap_eq_F, q2LaneW_eq_F]

/-- `List.length` by the recursor (proof help: the kernel reduces it without the structural-recursion wrappers;
GOLF's `lenR`). -/
def lenR2 {α : Type} (l : List α) : Nat := List.rec 0 (fun _ _ n => n + 1) l

/-- `List.all` by the recursor. -/
def allR2 {α : Type} (p : α → Bool) (l : List α) : Bool := List.rec true (fun a _ r => p a && r) l

/-- `List.drop` through the recursor. -/
def dropR2 {α : Type} : Nat → List α → List α
  | 0, l => l
  | n + 1, l => List.rec [] (fun _ t _ => dropR2 n t) l

theorem lenR2_eq {α : Type} (l : List α) : lenR2 l = l.length := by
  induction l with
  | nil => rfl
  | cons a l ih => exact congrArg (· + 1) ih

theorem allR2_eq {α : Type} (p : α → Bool) (l : List α) : allR2 p l = l.all p := by
  induction l with
  | nil => rfl
  | cons a l ih => exact (congrArg (p a && ·) ih).trans (List.all_cons).symm

theorem dropR2_eq {α : Type} : ∀ (n : Nat) (l : List α), dropR2 n l = l.drop n
  | 0, _ => rfl
  | _ + 1, [] => rfl
  | n + 1, _ :: t => dropR2_eq n t

/-- `cbOf2T` through `lenR2`. -/
def cbOf2TR (T : LCfg → TB Unit) (P : Nat) : Nat := lenR2 (T ⟨P, 0, 0, 0⟩ 0).2 - 2 * (57 + P)

/-- `layOk2T` through `lenR2`, `allR2`, `dropR2` (`layOk2T_eq_R`), the form the kernel decides. -/
def layOk2TR (T : LCfg → TB Unit) (P : Nat) : Bool :=
  lenR2 (T ⟨P, 0, 0, cbOf2TR T P⟩ 0).2 == cbOf2TR T P + 2 * (57 + P) &&
  allR2 (fun i => i.op != .assert0 || i.args.getD 1 default == (LCfg.mk P 0 0 (cbOf2TR T P)).k 15)
    (T ⟨P, 0, 0, cbOf2TR T P⟩ 0).2 &&
  allR2 (fun i => i.ty == .K && i.op != .assert0) (dropR2 (cbOf2TR T P) (T ⟨P, 0, 0, cbOf2TR T P⟩ 0).2)

theorem layOk2T_eq_R (T : LCfg → TB Unit) (P : Nat) : layOk2T T P = layOk2TR T P := by
  simp only [layOk2T, layOk2TR, layIns2T, lay02T, cbOf2T, cbOf2TR, lenR2_eq, allR2_eq, dropR2_eq]

/-- The tape at P20 (`n_log = 20`: `P = 15`). -/
theorem layOk2_15 : layOk2 15 = true := by rw [layOk2_eq_lit, layerTB2T_eq_F, layOk2T_eq_R]; decide +kernel

/-- `KS` at P20 (`ksLog = 13`: `P = 9`). -/
theorem layOk2_9 : layOk2 9 = true := by rw [layOk2_eq_lit, layerTB2T_eq_F, layOk2T_eq_R]; decide +kernel

end Lvm.Q1
