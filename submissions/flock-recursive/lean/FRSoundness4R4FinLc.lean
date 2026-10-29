-- New for `flock-recursive` (BLUEPRINT revision 4.1, A.9 `finLc`; stage R4c).
import FRSoundness4R4Fin

/-!
# `finLc`'s flag at `FinP` on the relocated ops

3.x's `flag_finLc` (`FRVIRFinals`, revision 3.16) for `gFinLc P`: Z3's `P.S.z3` challenges (the
first eight), the kind's node flag `P.kv.node`, and L3's message and the Z-end pair read at `S`'s
offsets (`pe4 P.S`). The 64-term sum (`dotOps`) and the tail (`lcTail`) read no proof byte, so the
relocation leaves them unchanged (`dotOps_reloc`, `lcTail_reloc`).
-/

namespace FR.Snd.R4
open RecursionFast Rev4

theorem dotOps_reloc (S : Seq) (x y z c : ℕ) : ∀ n, (dotOps x y z c n).map (reloc S) = dotOps x y z c n
  | 0 => rfl
  | n + 1 => by rw [dotOps, List.map_append, dotOps_reloc S x y z c n]; rfl

theorem lcTail_reloc (S : Seq) (fi : FinIn) (b d : ℕ) : (lcTail fi b d).map (reloc S) = lcTail fi b d := rfl

section Flags
variable (impl : OpImpl) (κ : Kind) (inp : Input) (fi : FinIn) (r : Array Val) (P : FinP)


/-- `finLc`'s claims `v_0 … v_7` (L3's message). -/
def lcV4 : List F := (List.range 8).map fun i => pe4 P.S inp fL2 (phaseOffOf P.S (phaseIx "L3") fL2 + 16 * i)

/-- `r′_hi`: Z3's first 8 challenges. -/
def lcRhi4 : Array F := (((chals fi "Z3" P.S.z3).take 8).map (fv r)).toArray

/-- **The walk** `Â + α B̂` at `rowW′ = maskRows w rowW` and `eq(r_k, ·)`; `w` = a node's
`nodeKindW v` (`free` weight 0, revision 3.16), a leaf's `v₀ :: 0^8`. -/
def lcWalk4 : F :=
  let α := fv r ((outsOf fi "L1").headD 0)
  let w : List F := if P.kv.node κ then nodeKindW (lcV4 inp P) else (lcV4 inp P).headD 0 :: List.replicate 8 0
  let rw := maskRows w.toArray (impl.rowW (fv r ((outsOf fi "Z2").headD 0)) (lcRhi4 fi r P))
  let cw := eqTab (lcRk fi r).toArray
  (impl.walkAB rw cw).1 + α * (impl.walkAB rw cw).2

/-- `v_free`: a node's `v₇`, a leaf's `0`. -/
def lcVf4 : F := if P.kv.node κ then pe4 P.S inp fL2 (phaseOffOf P.S (phaseIx "L3") fL2 + 16 * 7) else 0

/-- **`free`'s term without `(1 + α)`** (revision 3.16, R-V-M2): `v_free · (Σ_{s<64} L_s(λ)
eq(r_k[0..5], s)) · eq(r′_hi, r_k[6..13])` (`L_s(λ)` = `eqZ(λ, 0)[s]`); its spec is
`FRSpartan.linM_free_mle`, `⟨rowW, eq(r_k, ·)⟩` in closed form. -/
def lcFree4 : F :=
  lcVf4 κ inp P * (dotAcc 0 (impl.eqZ (fv r ((outsOf fi "Z2").headD 0)) 0)
    (eqTab (((chals fi "L2" 14).take 6).map (fv r)).toArray) 64 * eqPoint (lcRhi4 fi r P) (((chals fi "L2" 14).drop 6).map (fv r)).toArray)

/-- (+) **A leaf's `free` term is `0`**: `lcVf` is `0`, so a leaf's (ii) is the 3.15 walk. -/
theorem lcFree4_leaf (h : P.kv.node κ = false) : lcFree4 impl κ inp fi r P = 0 := by
  simp [lcFree4, lcVf4, h]

/-- **A.9's `finLc` relation** over the register values (revision 3.16): (i) `c₀ = â + α b̂`,
(iii) `Σ_{i<8} β^i v_i = α₂`, (ii) `c_Lc = walk + (1 + α)·lcFree` (as `Y + α Y`). -/
def relLc4 : Bool :=
  let α := fv r ((outsOf fi "L1").headD 0); let β := fv r ((outsOf fi "L3β").headD 0)
  let v := lcV4 inp P
  let vβ := (v.reverse.drop 1).foldl (fun acc x => x + β * acc) (v.getD 7 0)
  let y := lcFree4 impl κ inp fi r P
  ((Val.f (pe4 P.S inp fZend 0 + α * pe4 P.S inp fZend 16)).eqv (rd r (claim0 fi "L2")) &&
    (Val.f vβ).eqv (rd r (fi.zhat.getD 1 0))) &&
  (Val.f (lcWalk4 impl κ inp fi r P + (y + α * y))).eqv (rd r (claimN fi "L2"))

set_option maxRecDepth 4096 in
/-- **`flag_finLc` at `P`**: the relocated `gFinLc`'s flag is `relLc4`. -/
theorem flag_gFinLc (hin : ∀ x ∈ (chals fi "Z3" P.S.z3).take 8 ++ chals fi "L2" 14 ++
      [(outsOf fi "L1").headD 0, (outsOf fi "L3β").headD 0, (outsOf fi "Z2").headD 0,
       claim0 fi "L2", claimN fi "L2", fi.zhat.getD 1 0], x < r.size) :
    ∃ L, pureRun impl κ inp ((gFinLc P fi r.size).1.map (reloc P.S)) r [] = some (L, relLc4 impl κ inp fi r P) := by
  simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hin
  have h1 := fun L => map_rd_app r L ((chals fi "Z3" P.S.z3).take 8) fun x hx => hin x (.inl (.inl hx))
  have h2 := fun L => map_rd_app r L (chals fi "L2" 14) fun x hx => hin x (.inl (.inr hx))
  have h2a := fun L => map_rd_app r L ((chals fi "L2" 14).take 6)
    fun x hx => hin x (.inl (.inr (List.mem_of_mem_take hx)))
  have tf : ∀ x, (Val.f x).toF = x := fun _ => rfl
  have taf : ∀ x, (Val.af x).toAF = x := fun _ => rfl
  have hZ : fZend < 19 := by decide
  have hL2 : fL2 < 19 := by decide
  have ha := hin _ (.inr (.inl rfl)); have hb := hin _ (.inr (.inr (.inl rfl)))
  have hl := hin _ (.inr (.inr (.inr (.inl rfl))))
  have hc0 := hin _ (.inr (.inr (.inr (.inr (.inl rfl)))))
  have hcN := hin _ (.inr (.inr (.inr (.inr (.inr (.inl rfl))))))
  have hz := hin _ (.inr (.inr (.inr (.inr (.inr (.inr rfl))))))
  -- the head: registers `b … b + 40`
  obtain ⟨V1, f1, hA, hlen, hf1, g4, g14, g22, g37, g38, g40⟩ : ∃ V1 f1,
      pureRun impl κ inp ((gLcHead P fi r.size).map (reloc P.S)) r [] = some (V1, f1) ∧ V1.length = 41 ∧
      f1 = ((Val.f (pe4 P.S inp fZend 0 + fv r ((outsOf fi "L1").headD 0) * pe4 P.S inp fZend 16)).eqv
          (rd r (claim0 fi "L2")) &&
        (Val.f (((lcV4 inp P).reverse.drop 1).foldl
          (fun acc x => x + fv r ((outsOf fi "L3β").headD 0) * acc) ((lcV4 inp P).getD 7 0))).eqv
          (rd r (fi.zhat.getD 1 0))) ∧
      V1.getD 4 default = .af (lcRhi4 fi r P) ∧ V1.getD 14 default = .f 0 ∧
      V1.getD 22 default = .f (lcWalk4 impl κ inp fi r P) ∧ V1.getD 37 default = .f (lcVf4 κ inp P) ∧
      V1.getD 38 default = .af (impl.eqZ (fv r ((outsOf fi "Z2").headD 0)) 0) ∧
      V1.getD 40 default = .af (eqTab (((chals fi "L2" 14).take 6).map (fv r)).toArray) := by
    cases hk : P.kv.node κ
    all_goals
      apply Exists.intro
      apply Exists.intro
      refine ⟨?run, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      case run =>
        rw [pureRun_nil_rev]
        simp only [gLcHead, hk, List.map_cons, List.map_nil, hZ, hL2, reloc, absOff_zero, pureRun, evalOp, tf, taf, List.nil_append, List.cons_append, h1, h2,
            h2a, hornerOps, rd_revAcc, rd_revAcc0, revAcc_app_cons, List.append_nil,
            List.length_cons, List.length_nil, Array.reduceGetElem?, rd_app_left _ _ ha,
            rd_app_left _ _ hb,
            rd_app_left _ _ hl, rd_app_left _ _ hc0, rd_app_left _ _ hz, List.range_succ,
            List.range_zero, List.map_cons, List.map_nil, List.map_append,
            Option.getD_some, Option.map_some, allK, Bool.not_true, Bool.false_or, Bool.true_and,
            Bool.and_true, List.take_succ_cons, List.take_zero, List.replicate_succ,
            List.replicate_zero, ite_true, ite_false, Bool.false_eq_true, List.flatMap_append,
            List.flatMap_cons, List.flatMap_nil, ↓reduceIte, Nat.reduceEqDiff, Nat.reduceAdd,
            Nat.reduceMul, Nat.reduceSub]
        rfl
      all_goals
        try simp only [List.length_reverse, List.length_cons, List.length_nil, getD_revAcc,
          Nat.reduceAdd, Nat.reduceSub, Array.reduceGetElem?, Option.getD_some]
      all_goals
        try simp only [lcWalk4, lcV4, lcRhi4, lcRk, lcVf4, nodeKindW, hk, ite_true, ite_false,
          Bool.false_eq_true, List.range_succ, List.range_zero, List.map_cons, List.map_nil,
          List.map_append, List.nil_append, List.cons_append, List.getD_cons_succ,
          List.getD_cons_zero, List.take_succ_cons, List.take_zero, List.headD_cons,
          List.replicate_succ, List.replicate_zero, List.reverse_cons, List.reverse_nil,
          List.drop_succ_cons, List.drop_zero,
          List.foldl_cons, List.foldl_nil, List.getD_eq_getElem?_getD, List.getElem?_cons_succ,
          List.getElem?_cons_zero, Option.getD_some, Nat.reduceMul]
      all_goals rfl
  -- the 64-term sum: registers `b + 41 … b + 296`
  have hsz : (r ++ V1.toArray).size = r.size + 41 := by simp [hlen]
  have hD := run_dotOps impl κ inp (r ++ V1.toArray) (r.size + 38) (r.size + 40) (r.size + 14)
    (by rw [hsz]; omega) (by rw [hsz]; omega) (by rw [hsz]; omega) 64
  rw [hsz, rd_app, rd_app, rd_app, g14, g38, g40] at hD
  set dv := dotVals (Val.f 0).toF (Val.af (impl.eqZ (fv r ((outsOf fi "Z2").headD 0)) 0)).toAF
    (Val.af (eqTab (((chals fi "L2" 14).take 6).map (fv r)).toArray)).toAF 64 with hdv
  -- the tail: registers from `b + 297`
  set R2 := r ++ (V1 ++ dv).toArray with hR2def
  have hR2 : R2.size = r.size + 297 := by simp [R2, hlen, hdv, dotVals_length]
  have rr : ∀ i < r.size, ∀ L : List Val, rd (R2 ++ L.toArray) i = rd r i := fun i hi L => by
    rw [rd_app_left R2 L (by omega), hR2def, rd_app_left r _ hi]
  have rv : ∀ k < 41, ∀ L : List Val, rd (R2 ++ L.toArray) (r.size + k) = V1.getD k default :=
    fun k hk L => by
      rw [rd_app_left R2 L (by omega), hR2def, rd_app, List.getD_eq_getElem?_getD,
        List.getElem?_append_left (by omega), ← List.getD_eq_getElem?_getD]
  have rs : ∀ L : List Val, rd (R2 ++ L.toArray) (r.size + 296) =
      .f (dotAcc 0 (impl.eqZ (fv r ((outsOf fi "Z2").headD 0)) 0)
        (eqTab (((chals fi "L2" 14).take 6).map (fv r)).toArray) 64) := fun L => by
    rw [rd_app_left R2 L (by omega), hR2def, rd_app, List.getD_eq_getElem?_getD,
      List.getElem?_append_right (by omega), hlen, ← List.getD_eq_getElem?_getD, hdv,
      show 296 - 41 = 4 * 63 + 3 by norm_num, dotVals_last]
    rfl
  have h2b := fun L => map_rd_app' r R2 rr L ((chals fi "L2" 14).drop 6)
    fun x hx => hin x (.inl (.inr (List.mem_of_mem_drop hx)))
  obtain ⟨V3, hC⟩ : ∃ V3, pureRun impl κ inp (lcTail fi r.size R2.size) R2 [] =
      some (V3, (Val.f (lcWalk4 impl κ inp fi r P + (lcFree4 impl κ inp fi r P +
        fv r ((outsOf fi "L1").headD 0) * lcFree4 impl κ inp fi r P))).eqv (rd r (claimN fi "L2"))) := by
    rw [pureRun_nil_rev]
    simp only [lcTail, pureRun, evalOp, tf, taf, h2b, rd_revAcc, rd_revAcc0, revAcc_app_cons,
      List.append_nil, List.length_cons, List.length_nil, Nat.reduceAdd, Nat.reduceSub,
      Array.reduceGetElem?, Option.getD_some, rv 4 (by norm_num), rv 22 (by norm_num),
      rv 37 (by norm_num), rs, g4, g22, g37, rr _ ha, rr _ hb, rr _ hcN, Option.map_some,
      allK, Bool.not_true, Bool.false_or, Bool.true_and, Bool.and_true]
    exact ⟨_, rfl⟩
  have e : (gFinLc P fi r.size).1.map (reloc P.S) =
      ((gLcHead P fi r.size).map (reloc P.S) ++
        dotOps (r.size + 38) (r.size + 40) (r.size + 14) (r.size + 41) 64) ++
        lcTail fi r.size R2.size := by
    rw [hR2]; simp only [gFinLc, List.map_append, dotOps_reloc, lcTail_reloc, List.append_assoc]
  rw [e, pureRun_seq impl κ inp (pureRun_seq impl κ inp hA hD) hC, hf1]
  exact ⟨_, by simp only [relLc4, Bool.and_true]; rfl⟩



end Flags

end FR.Snd.R4
