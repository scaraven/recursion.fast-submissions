-- New for `flock-recursive` (R-OPS §5.2, stage R3: controls of `rsWeight`'s replay).
import FRNodeRows4RepRsK

/-!
# Controls: `rsWeight`'s replay template and the chain library

Structural controls (by `decide`/`rfl` on small arguments; the template itself is never evaluated
by the kernel). The numeric KATs (honest witness against `rsWeightF4` at claim points in `K` and in
`F`, a perturbed local failing a row, a perturbed `ρ` changing the value) are the dev probe's
(`logs/R3/r3rs-1.log`).
-/

namespace FR
namespace N4s
open RecursionFast Rev4 Circ Tpl GM

/-- (+) The node operands' types (`r″ : AF 7`, `κ`, `β`, `ρ : AK 25`, four claims `AK 25`) parse. -/
theorem rsShape_pos :
    rsShape [.af 7, .f, .f, .ak 25, .ak 25, .ak 25, .ak 25, .ak 25] = some (25, [25, 25, 25, 25]) := rfl

/-- (−) A six-coordinate `r″`, a missing `β`, or an `F` claim do not. -/
theorem rsShape_neg : rsShape [.af 6, .f, .f, .ak 25, .ak 25] = none ∧
    rsShape [.af 7, .f, .ak 25, .ak 25] = none ∧ rsShape [.af 7, .f, .f, .ak 25, .af 25] = none :=
  ⟨rfl, rfl, rfl⟩

/-- (+) An `rsWeight` active at every index is covered; its operands are `r″, κ, β, ρ`, then the
claims of the index. -/
theorem isRS_pos : isRS (.rsWeight 1 (fun _ => [5, 6]) 2 3 (fun _ => true) 4) = true ∧
    rsArgs (.rsWeight 1 (fun ι => if ι = .P30 then [7] else [5, 6]) 2 3 (fun _ => true) 4) .N30 =
      [1, 2, 3, 4, 5, 6] := ⟨rfl, rfl⟩

/-- (−) Not where `act` fails at an index (there `β` is replaced by `1`), nor another op. -/
theorem isRS_neg : isRS (.rsWeight 1 (fun _ => [5]) 2 3 (fun ι => ι ≠ .P30) 4) = false ∧
    isRS (.linkWAll 1 2) = false := ⟨rfl, rfl⟩

/-- (−) At other operand types the sub-template has no gates and two empty outputs (which `rsIn`
rejects). -/
theorem rsT_neg : rsT .N4 [.af 7, .f] = ⟨[], [[], []]⟩ ∧ rsIn [.af 7, .f] = false := ⟨rfl, rfl⟩

/-- (+) The chain gadgets' sizes: a `K` squaring chain of 3 steps is 6 gates (two per step), a
product of three `K` pairs 6 (Karatsuba, two products), Horner over three entries 9. -/
theorem chain_sizes :
    (sqChainK 3 (I 0, I 1) 0).1.length = 6 ∧
      (prodK [(I 0, I 1), (I 2, I 3), (I 4, I 5)] 0).1.length = 6 ∧
      (hornerKG (fun _ => (I 0, I 1)) 0 [(I 2, I 3), (I 4, I 5), (I 6, I 7)] 0).1.length = 9 ∧
      (sqChainK 3 (I 0, I 1) 0).2.length = 4 := by
  decide

/-- (−) The squaring chain's locals follow each other: step 2 reads step 1's locals `0, 1`, not the
input. -/
theorem sqChain_reads : (sqChainK 2 (I 0, I 1) 0).1.getD 2 (.pad 0 0) =
    .mul (L 0 ++ sc F.alpha (L 1)) (L 0 ++ sc F.alpha (L 1)) := rfl

/-- (+) The replay template's locals start after `linkWAll`'s (`2^16 > 42,592`). -/
theorem cbRS_pos : cbLW + 42592 < cbRS := by decide

end N4s
end FR
