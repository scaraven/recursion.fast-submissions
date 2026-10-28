-- New for `flock-recursive` (BLUEPRINT revision 4.1, A.9 `finSh`, B-12; stage R4c).
import FRSoundness4R4Fin

/-!
# `finSh`'s flag at `FinP` on the relocated ops

3.x's `flag_finSh` (`FRVIRFinals`) for `gFinSh P`: the sizes (`P.S.s2`, `nb = P.S.mStar − 14`), the
kind tables and the boundary reads (`pe4 P.S`) are `P`'s; with `P.vn` (a segment, B-12) the masked
shift's operand is `τ ‖ L` (`τ` zero-padded by the statement's zero register, then `L`'s bits) and
the boundary's last block is `L` (`lastRegs`), and `E`, `Sh`, `E₀` are `shiftMask`'s.
-/

namespace FR.Snd.R4
open RecursionFast Rev4

section Flags
variable (impl : OpImpl) (κ : Kind) (inp : Input) (fi : FinIn) (r : Array Val) (P : FinP)

/-- **`relSh` at `P`**: (i) `shiftTarget(κ_s, τ, θ, bnd) = c₀^{S2}`; (ii) `(w_out + w_in)·α_Sh =
c_N^{S2}`, the weights' `E`, `Sh`, `E₀` from `shiftMask` on the masked operand when `P.vn` or a node,
else 3.x's leaf `eq`/`shiftEq`. -/
def relSh4 : Bool :=
  let co := coordsR fi "S1"; let rs := chals fi "S2" P.S.s2
  let m := P.kv.m κ; let nb := P.S.mStar - 14
  let ks := fv r (co.getD (nb + 10) 0)
  let τ := ((co.take (m - 14)).map (fv r) ++ List.replicate (P.S.mStar - m) 0).toArray
  let θ := (((co.drop nb).take 10).map (fv r)).toArray
  let rb := ((rs.take (m - 14)).map (fv r) ++ List.replicate (P.S.mStar - m) 0).toArray
  let rp := (((rs.drop (m - 14)).take 10).map (fv r)).toArray
  let tt := ((co.take (m - 14) ++ (co.drop nb).take 10).map (fv r)).toArray
  let rr := ((rs.take (m - 14) ++ (rs.drop (m - 14)).take 10).map (fv r)).toArray
  let tm : Array F := if P.vn then
      ((co.take (m - 14)).map (fv r) ++ List.replicate (P.S.mStar - m) (fv r (zeroReg fi)) ++
        (lastRegs fi).map (fv r)).toArray
    else τ
  let mk := P.vn || P.kv.node κ
  let sm := impl.shiftMask tm rb
  let e := if mk then sm.1 else eqPoint τ rb
  let sh := if mk then sm.2.1 else impl.shiftEq τ rb
  let e0 := if mk then sm.2.2 else eqPoint (Array.replicate nb 0) rb
  let sIn := if P.kv.node κ then impl.slotW κ 2 θ rp else impl.slotW κ 1 θ rp
  let wout := e * impl.slotW κ 0 θ rp
  let win := linkSum (impl.linkWAll κ tt rr) ks nLinkFam ((sh + ks * e0) * sIn) (ks * ks)
  let bnd : Array F := ((if P.kv.node κ then [0, 0, 0, 0]
    else [pe4 P.S inp fHdr 16, pe4 P.S inp fHdr 32, pe4 P.S inp fStmt 1, pe4 P.S inp fStmt 17]) ++
    (if P.vn then (lastRegs fi).map (fv r)
     else List.replicate (m - 14) 1 ++ List.replicate (P.S.mStar - m) 0)).toArray
  (Val.f (impl.shiftTarget ks τ θ bnd)).eqv (rd r (claim0 fi "S2")) &&
  (Val.f ((wout + win) * fv r (fi.zhat.getD 2 0))).eqv (rd r (claimN fi "S2"))

set_option maxRecDepth 8192 in
theorem flag_gFinSh (hin : ∀ x ∈ coordsR fi "S1" ++ chals fi "S2" P.S.s2 ++ lastRegs fi ++
      [claim0 fi "S2", claimN fi "S2", fi.zhat.getD 2 0, zeroReg fi,
       (coordsR fi "S1").getD (P.S.mStar - 14 + 10) 0], x < r.size) :
    ∃ L, pureRun impl κ inp ((gFinSh P fi r.size).1.map (reloc P.S)) r [] =
      some (L, relSh4 impl κ inp fi r P) := by
  simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hin
  have hco : ∀ x ∈ coordsR fi "S1", x < r.size := fun x hx => hin x (.inl (.inl (.inl hx)))
  have hrs : ∀ x ∈ chals fi "S2" P.S.s2, x < r.size := fun x hx => hin x (.inl (.inl (.inr hx)))
  have hlr : ∀ x ∈ lastRegs fi, x < r.size := fun x hx => hin x (.inl (.inr hx))
  have h1 := fun L => map_rd_app r L ((coordsR fi "S1").take (P.kv.m κ - 14))
    fun x hx => hco x (List.mem_of_mem_take hx)
  have h2 := fun L => map_rd_app r L (((coordsR fi "S1").drop (P.S.mStar - 14)).take 10)
    fun x hx => hco x (List.mem_of_mem_drop (List.mem_of_mem_take hx))
  have h3 := fun L => map_rd_app r L ((chals fi "S2" P.S.s2).take (P.kv.m κ - 14))
    fun x hx => hrs x (List.mem_of_mem_take hx)
  have h4 := fun L => map_rd_app r L (((chals fi "S2" P.S.s2).drop (P.kv.m κ - 14)).take 10)
    fun x hx => hrs x (List.mem_of_mem_drop (List.mem_of_mem_take hx))
  have h5 := fun L => map_rd_app r L ((coordsR fi "S1").take (P.kv.m κ - 14) ++
    ((coordsR fi "S1").drop (P.S.mStar - 14)).take 10) fun x hx => by
      rcases List.mem_append.1 hx with hx | hx
      · exact hco x (List.mem_of_mem_take hx)
      · exact hco x (List.mem_of_mem_drop (List.mem_of_mem_take hx))
  have h6 := fun L => map_rd_app r L ((chals fi "S2" P.S.s2).take (P.kv.m κ - 14) ++
    ((chals fi "S2" P.S.s2).drop (P.kv.m κ - 14)).take 10) fun x hx => by
      rcases List.mem_append.1 hx with hx | hx
      · exact hrs x (List.mem_of_mem_take hx)
      · exact hrs x (List.mem_of_mem_drop (List.mem_of_mem_take hx))
  have h7 := fun L => map_rd_app r L (lastRegs fi) hlr
  have tf : ∀ x, (Val.f x).toF = x := fun _ => rfl
  have taf : ∀ x, (Val.af x).toAF = x := fun _ => rfl
  have hH : fHdr < 19 := by decide
  have hS : fStmt < 19 := by decide
  simp only [gFinSh, gShCore, relSh4, gBndOps, gPadB]
  generalize claim0 fi "S2" = c0 at *
  generalize claimN fi "S2" = cN at *
  generalize fi.zhat.getD 2 0 = zo at *
  generalize zeroReg fi = zr at *
  generalize (coordsR fi "S1").getD (P.S.mStar - 14 + 10) 0 = ks at *
  have hc0 := hin c0 (.inr (.inl rfl)); have hcN := hin cN (.inr (.inr (.inl rfl)))
  have hzo := hin zo (.inr (.inr (.inr (.inl rfl))))
  have hzr := hin zr (.inr (.inr (.inr (.inr (.inl rfl)))))
  have hk := hin ks (.inr (.inr (.inr (.inr (.inr rfl)))))
  cases hv : P.vn <;> cases hκ : P.kv.node κ <;>
  simp only [hκ, Bool.cond_true, Bool.cond_false, Bool.true_or, Bool.false_or,
    Bool.false_eq_true, Nat.add_assoc, List.map_cons, List.map_nil, List.cons_append,
    List.nil_append, hH, hS, reloc, absOff_zero,
    pureRun, evalOp, tf, taf, h1, h2, h3, h4, h5, h6, h7, linkOps,
    List.map_append, List.map_replicate,
    nLinkFam, linkSum, List.range_succ, List.range_zero, List.flatMap_append, List.flatMap_cons,
    List.flatMap_nil, ↓reduceIte, Nat.reduceEqDiff, Nat.reduceAdd, Nat.reduceMul, Nat.reduceSub,
    rd_app, rd_app0, rd_app_left _ _ hc0, rd_app_left _ _ hcN,
    rd_app_left _ _ hzo, rd_app_left _ _ hk, rd_app_left _ _ hzr,
    List.getD_cons_succ, List.getD_cons_zero,
    Option.map_some, allK, Bool.not_true, Bool.false_or, Bool.true_and, Bool.and_true] <;>
  exact ⟨_, rfl⟩

end Flags

end FR.Snd.R4
