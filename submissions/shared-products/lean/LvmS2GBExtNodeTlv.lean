-- New for lvm2 MP-B cap pruning (CAP-X4, 2026-11-17): S2GB's tail data (`tlvB20`) against the plan (one kernel
-- evaluation), for the node output's π tail (proof-help of `EXB_node`).
import LvmS2GBExtTailSem
import LvmS2GBExtProg

/-!
# S2GB's plan and the tail data

* `tlvEntOK P nP i e`: at an opening's first heap entry `i` (slot `2^m − 1`), `1 ≤ m ≤ 64`, `path + m = h`, every
  path's positions entry and the upper half's heap slots (entries `i … i + 2^(m−1) − 1`) are plan entries
  `1 … nP − 1`, every path's field ends in the answer's first three words, and those heap queries have 64 bytes;
* the plan facts at S2GB's plan (`tlvFacts_B20`) are in `LvmS2GBExtPlanW` (one walk over the plan).
-/

set_option autoImplicit false

namespace Lvm.XB

open RecursionFast Lvm Lvm.X Lvm.XS Lvm.Replay

/-- The static conditions at entry `i` of the plan `P` (of `nP` entries). -/
def tlvEntOK (P : List PE) (nP : ℕ) (i : ℕ) (e : PE) : Bool :=
  match e.k with
  | .heap pe h t path _ m k _ =>
    if k + 1 = 2 ^ m then
      decide (1 ≤ m) && decide (m ≤ 64) && decide (path + m = h) && decide (1 ≤ i) &&
      (List.range t).all (fun j => decide (1 ≤ pe + j / 8) && decide (pe + j / 8 < nP) &&
        decide (j % 8 * h + path + m ≤ 192)) &&
      decide (i + 2 ^ (m - 1) ≤ nP) && ((P.drop i).take (2 ^ (m - 1))).all (fun e' => e'.len == 64)
    else true
  | _ => true

/-- A list's entries with their indices from `k`. -/
def idxL : ℕ → List PE → List (ℕ × PE)
  | _, [] => []
  | k, e :: P => (k, e) :: idxL (k + 1) P

theorem idxL_eq : ∀ (P : List PE) (k : ℕ),
    (List.range P.length).map (fun i => (k + i, P.getD i default)) = idxL k P
  | [], _ => rfl
  | e :: P, k => by
    rw [List.length_cons, List.range_succ_eq_map, List.map_cons, List.map_map, idxL, Nat.add_zero]
    congr 1
    rw [← idxL_eq P (k + 1)]
    exact List.map_congr_left fun i _ => by simp [Nat.add_assoc, Nat.add_comm 1 i]

/-- The static conditions over the entries `Q` from index `k` of the plan `P`. -/
def tlvChkL (P : List PE) (nP : ℕ) : ℕ → List PE → Bool
  | _, [] => true
  | k, e :: Q => tlvEntOK P nP k e && tlvChkL P nP (k + 1) Q

theorem tlvChkL_mem (P : List PE) (nP : ℕ) : ∀ (k : ℕ) (Q : List PE), tlvChkL P nP k Q = true →
    ∀ q ∈ idxL k Q, tlvEntOK P nP q.1 q.2 = true
  | _, [], _, q, hq => by simp [idxL] at hq
  | k, e :: Q, h, q, hq => by
    simp only [tlvChkL, Bool.and_eq_true] at h
    rcases List.mem_cons.1 hq with rfl | hq
    · exact h.1
    · exact tlvChkL_mem P nP (k + 1) Q h.2 q hq

/-- A plan entry's bitmap size: `2^m` at an opening's first heap entry. -/
def bmOf (e : PE) : ℕ :=
  match e.k with
  | .heap _ _ _ _ _ m k _ => if k + 1 = 2 ^ m then 2 ^ m else 0
  | _ => 0

theorem idxL_snd : ∀ (k : ℕ) (P : List PE), (idxL k P).map Prod.snd = P
  | _, [] => rfl
  | k, e :: P => by rw [idxL, List.map_cons, idxL_snd (k + 1) P]

end Lvm.XB
