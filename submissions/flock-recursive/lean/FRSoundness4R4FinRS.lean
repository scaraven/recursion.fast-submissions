-- New for `flock-recursive` (BLUEPRINT revision 4.1, A.9 `finRS`; stage R4c).
import FRSoundness4R4Fin

/-!
# `finRS` at `FinP` on the relocated ops

3.x's `exec_finRS` (`FRVIRFinalsSF`) for `gFinRS P`: the slice values are read at `S`'s RS0 offset
(`sv4`), the Sh point's low part is S2's `P.S.s2` challenges from `P.kv.m κ − 14`, a leaf's fourth
claim's zero check reads `S`'s offset (`rsLeafZero4`) and is gated by `P.kv.node`. The run kit
(`run_elemOps4`, `run_elemsOps4`, `run_claimOps4`, `run_rsTail4`) is 3.x's on the relocated ops.
-/

namespace FR.Snd.R4
open RecursionFast Rev4

/-- Slice value `i` of claim `j` at `S`'s RS0 offset. -/
def sv4 (S : Seq) (inp : Input) (j i : ℕ) : F :=
  F.ofBytes (bytesAt inp.π (fieldOffOf S fRS0 + rsOff j i) 16)

/-- A leaf's fourth claim's slice bytes are zero (at `S`'s RS0 offset). -/
def rsLeafZero4 (S : Seq) (inp : Input) : Bool :=
  (inp.π.extract (fieldOffOf S fRS0 + rsOff 3 0) (fieldOffOf S fRS0 + rsOff 3 0 + 2048)).data.all (· == 0)

section Run
variable (impl : OpImpl) (κ : Kind) (inp : Input) (r : Array Val) (S : Seq)


/-- **One slice value**: the claim value gains `c · s`, the switched claim `bitBasis i · Φ(s)`. -/
theorem run_elemOps4 (j i aA aT R : ℕ) (wop : ℕ → Op) (c A T : F) (rpp : Array F) (L : List Val)
    (hR : R < r.size + L.length) (hRv : (rd (r ++ L.toArray) R).toAF = rpp)
    (hA : aA < r.size + L.length) (hT : aT < r.size + L.length)
    (hAv : (rd (r ++ L.toArray) aA).toF = A) (hTv : (rd (r ++ L.toArray) aT).toF = T)
    (hw : ∀ X : List Val, evalOp impl κ inp (r ++ (L ++ X).toArray) (wop i) = .vals [.f c] true)
    (hwr : reloc S (wop i) = wop i) :
    ∃ M, pureRun impl κ inp ((elemOps j i wop R aA aT (r.size + L.length)).map (reloc S)) r L = some (L ++ M, true) ∧
      M.length = elemW ∧
      (rd (r ++ (L ++ M).toArray) (r.size + L.length + 3)).toF = A + c * sv4 S inp j i ∧
      (rd (r ++ (L ++ M).toArray) (r.size + L.length + elemW - 1)).toF =
        T + bb i * impl.phiRS rpp (sv4 S inp j i) := by
  set s := sv4 S inp j i
  have tf : ∀ x, (Val.f x).toF = x := fun _ => rfl
  have e0 : evalOp impl κ inp (r ++ L.toArray) (.piElem 0 (fieldOffOf S fRS0 + rsOff j i)) =
      .vals [.f s] true := by simp only [evalOp, absOff_zero]; rfl
  have hRS : fRS0 < 19 := by decide
  have e1 : evalOp impl κ inp (r ++ (L ++ [Val.f s]).toArray) (wop i) = .vals [.f c] true := hw _
  set φ := impl.phiRS rpp s
  refine ⟨[.f s, .f c, .f (c * s), .f (A + c * s), .f φ, .f (bb i), .f (bb i * φ),
    .f (T + bb i * φ)], ?_, rfl, ?_, ?_⟩
  · simp only [elemOps, List.map_cons, List.map_nil, hwr]
    simp only [hRS, reloc, ite_true]
    rw [pr_op impl κ inp r e0, pr_op impl κ inp r e1]
    simp only [pureRun, evalOp, List.append_assoc, List.cons_append, List.nil_append, rdX, rdX0,
      List.getD_cons_succ, List.getD_cons_zero, tf, rdL r hA, rdL r hT, rdL r hR, hAv, hTv, hRv,
      Option.map_some, Bool.true_and, Bool.and_true]
    rfl
  · rw [rdX]; rfl
  · rw [show r.size + L.length + elemW - 1 = r.size + L.length + 7 from rfl, rdX]; rfl

/-- **A claim's slice values, `n` of them**: the claim value and the switched claim as sums. -/
theorem run_elemsOps4 (j : ℕ) (wop : ℕ → Op) (R : ℕ) (rpp : Array F) (c : ℕ → F) (L₀ : List Val)
    (hR : R < r.size + L₀.length) (hRv : (rd (r ++ L₀.toArray) R).toAF = rpp)
    (hw : ∀ i (X : List Val), evalOp impl κ inp (r ++ (L₀ ++ X).toArray) (wop i) = .vals [.f (c i)] true)
    (hwr : ∀ i, reloc S (wop i) = wop i) (n : ℕ) : ∀ (i aA aT : ℕ) (A T : F) (X : List Val), aA < r.size + L₀.length + X.length →
    aT < r.size + L₀.length + X.length → (rd (r ++ (L₀ ++ X).toArray) aA).toF = A →
    (rd (r ++ (L₀ ++ X).toArray) aT).toF = T →
    ∃ M, pureRun impl κ inp ((elemsOps j wop R n i aA aT (r.size + L₀.length + X.length)).map (reloc S)) r (L₀ ++ X) =
      some (L₀ ++ X ++ M, true) ∧ M.length = n * elemW ∧
      (0 < n → (rd (r ++ (L₀ ++ X ++ M).toArray) (r.size + L₀.length + X.length + (n - 1) * elemW + 3)).toF =
          A + ∑ k ∈ Finset.range n, c (i + k) * sv4 S inp j (i + k) ∧
        (rd (r ++ (L₀ ++ X ++ M).toArray) (r.size + L₀.length + X.length + n * elemW - 1)).toF =
          T + ∑ k ∈ Finset.range n, bb (i + k) * impl.phiRS rpp (sv4 S inp j (i + k))) := by
  induction n with
  | zero => intro i aA aT A T X _ _ _ _; exact ⟨[], by simp [elemsOps, pureRun], by simp, by simp⟩
  | succ n ih =>
    intro i aA aT A T X hA hT hAv hTv
    have hlen : r.size + (L₀ ++ X).length = r.size + L₀.length + X.length := by simp; omega
    obtain ⟨M₁, h₁, hl₁, hα, hτ⟩ := run_elemOps4 impl κ inp r S j i aA aT R wop (c i) A T rpp (L₀ ++ X)
      (by rw [hlen]; omega) (by rw [rdL r hR, hRv]) (by rw [hlen]; exact hA) (by rw [hlen]; exact hT)
      hAv hTv (fun Y => by rw [List.append_assoc]; exact hw i _) (hwr i)
    rw [hlen] at h₁ hα hτ
    obtain ⟨M₂, h₂, hl₂, hv₂⟩ := ih (i + 1) (r.size + L₀.length + X.length + 3)
      (r.size + L₀.length + X.length + elemW - 1) (A + c i * sv4 S inp j i)
      (T + bb i * impl.phiRS rpp (sv4 S inp j i)) (X ++ M₁)
      (by simp only [List.length_append, hl₁, elemW]; omega)
      (by simp only [List.length_append, hl₁, elemW]; omega)
      (by simpa only [List.append_assoc] using hα) (by simpa only [List.append_assoc] using hτ)
    have hb : r.size + L₀.length + (X ++ M₁).length = r.size + L₀.length + X.length + elemW := by
      simp [hl₁]; omega
    rw [hb] at h₂ hv₂
    refine ⟨M₁ ++ M₂, ?_, by simp [hl₁, hl₂]; ring, fun _ => ?_⟩
    · simp only [elemsOps, List.map_append]
      rw [pr_app impl κ inp r h₁, List.append_assoc L₀ X M₁, h₂]; simp
    · rcases Nat.eq_zero_or_pos n with rfl | hn
      · rw [Nat.zero_mul, List.length_eq_zero_iff] at hl₂; subst hl₂
        simp only [List.append_nil, Nat.zero_add, Finset.sum_range_one, Nat.add_zero, Nat.sub_self,
          Nat.zero_mul, Nat.one_mul]
        exact ⟨hα, hτ⟩
      · obtain ⟨h3, h4⟩ := hv₂ hn
        have hk : ∀ k, i + 1 + k = i + (k + 1) := fun k => by omega
        simp only [List.append_assoc] at h3 h4 ⊢
        refine ⟨?_, ?_⟩
        · rw [show r.size + L₀.length + X.length + (n + 1 - 1) * elemW + 3 =
            r.size + L₀.length + X.length + elemW + (n - 1) * elemW + 3 by
              simp only [elemW]; omega, h3, Finset.sum_range_succ']
          simp only [hk, Nat.add_zero]; ring
        · rw [show r.size + L₀.length + X.length + (n + 1) * elemW - 1 =
            r.size + L₀.length + X.length + elemW + n * elemW - 1 by
              simp only [elemW]; omega, h4, Finset.sum_range_succ']
          simp only [hk, Nat.add_zero]; ring

theorem run_claimOps4 (j : ℕ) (wop : ℕ → Op) (R : ℕ) (rpp : Array F) (c : ℕ → F) (L₀ X : List Val)
    (hR : R < r.size + L₀.length) (hRv : (rd (r ++ L₀.toArray) R).toAF = rpp)
    (hw : ∀ i (X : List Val), evalOp impl κ inp (r ++ (L₀ ++ X).toArray) (wop i) = .vals [.f (c i)] true)
    (hwr : ∀ i, reloc S (wop i) = wop i) :
    ∃ M, pureRun impl κ inp ((claimOps j wop R (r.size + L₀.length + X.length)).map (reloc S)) r (L₀ ++ X) =
      some (L₀ ++ X ++ M, true) ∧ M.length = 1 + 128 * elemW ∧
      (rd (r ++ (L₀ ++ X ++ M).toArray) (r.size + L₀.length + X.length + 127 * elemW + 4)).toF =
        ∑ k ∈ Finset.range 128, c k * sv4 S inp j k ∧
      (rd (r ++ (L₀ ++ X ++ M).toArray) (r.size + L₀.length + X.length + 128 * elemW)).toF =
        ∑ k ∈ Finset.range 128, bb k * impl.phiRS rpp (sv4 S inp j k) := by
  set B := r.size + L₀.length + X.length
  have e0 : evalOp impl κ inp (r ++ (L₀ ++ X).toArray) (.const (fun _ => .f 0)) = .vals [.f 0] true := rfl
  have hz : (rd (r ++ (L₀ ++ (X ++ [Val.f 0])).toArray) B).toF = 0 := by
    rw [← List.append_assoc, show B = r.size + (L₀ ++ X).length by simp [B]; omega, rd_new1]; rfl
  obtain ⟨M, hM, hl, hv⟩ := run_elemsOps4 impl κ inp r S j wop R rpp c L₀ hR hRv hw hwr 128 0 B B 0 0
    (X ++ [Val.f 0]) (by simp [B]) (by simp [B]) hz hz
  have hb : r.size + L₀.length + (X ++ [Val.f 0]).length = B + 1 := by simp [B]; omega
  rw [hb] at hM hv
  obtain ⟨h1, h2⟩ := hv (by decide)
  refine ⟨[Val.f 0] ++ M, ?_, by simp [hl]; omega, ?_, ?_⟩
  · simp only [claimOps, List.map_cons]; rw [show reloc S (.const (fun _ => .f 0)) = .const (fun _ => .f 0) from rfl,
      pr_op impl κ inp r e0]
    simp only [List.append_assoc] at hM ⊢; exact hM
  · simp only [List.append_assoc, zero_add] at h1 ⊢
    rw [show B + 127 * elemW + 4 = B + 1 + (128 - 1) * elemW + 3 from rfl, h1]
  · simp only [List.append_assoc, zero_add] at h2 ⊢
    rw [show B + 128 * elemW = B + 1 + 128 * elemW - 1 from rfl, h2]


end Run

theorem run_rsTail4 (impl : OpImpl) (κ : Kind) (inp : Input) (r : Array Val) (P : FinP) (kap t₀ t₁ t₂ t₃ : ℕ)
    (Lc : List Val) (T₀ T₁ T₂ T₃ kp : F) (hk : kap < r.size) (hkv : (rd r kap).toF = kp)
    (h₀ : t₀ < r.size + Lc.length) (h₁ : t₁ < r.size + Lc.length) (h₂ : t₂ < r.size + Lc.length)
    (h₃ : t₃ < r.size + Lc.length)
    (v₀ : (rd (r ++ Lc.toArray) t₀).toF = T₀) (v₁ : (rd (r ++ Lc.toArray) t₁).toF = T₁)
    (v₂ : (rd (r ++ Lc.toArray) t₂).toF = T₂) (v₃ : (rd (r ++ Lc.toArray) t₃).toF = T₃) :
    ∃ M, pureRun impl κ inp ((gRsTail P kap t₀ t₁ t₂ t₃ (r.size + Lc.length)).map (reloc P.S)) r Lc =
        some (Lc ++ M, P.kv.node κ || rsLeafZero4 P.S inp) ∧
      (rd (r ++ (Lc ++ M).toArray) (r.size + Lc.length + 8)).toF =
        T₀ + kp * (T₁ + kp * (T₂ + kp * (if P.kv.node κ then T₃ else 0))) := by
  have tf : ∀ x, (Val.f x).toF = x := fun _ => rfl
  have hkr : ∀ X : List Val, (rd (r ++ X.toArray) kap).toF = kp := fun X => by rw [rd_app_left r X hk, hkv]
  have rL : ∀ {t T} (X : List Val), t < r.size + Lc.length → (rd (r ++ Lc.toArray) t).toF = T →
      (rd (r ++ (Lc ++ X).toArray) t).toF = T := fun X h v => by rw [rdL r h, v]
  set y := (if P.kv.node κ then T₃ else 0)
  set v' : Val := if P.kv.node κ = true then Val.f (T₃ + 0) else Val.f 0
  have hv' : (if P.kv.node κ = true then Val.f (T₃ + 0) else Val.f 0).toF = y := by
    simp only [y]; split <;> simp [tf]
  set by₁ := inp.π.extract (fieldOffOf P.S fRS0 + rsOff 3 0) (fieldOffOf P.S fRS0 + rsOff 3 0 + 2048)
  have hRS : fRS0 < 19 := by decide
  refine ⟨[.f 0, .f (T₃ + 0), v', .f (kp * y), .f (T₂ + kp * y),
    .f (kp * (T₂ + kp * y)), .f (T₁ + kp * (T₂ + kp * y)), .f (kp * (T₁ + kp * (T₂ + kp * y))),
    .f (T₀ + kp * (T₁ + kp * (T₂ + kp * y))), .b by₁], ?_, ?_⟩
  · simp only [gRsTail, List.map_cons, List.map_nil, hRS, reloc, ite_true, absOff_zero, pureRun, evalOp, List.append_assoc, List.cons_append, List.nil_append,
      rdX, rdX0, List.getD_cons_succ, List.getD_cons_zero, hkr, tf,
      rL _ h₀ v₀, rL _ h₁ v₁, rL _ h₂ v₂, rL _ h₃ v₃, hv', Bool.not_not, Val.isZero,
      Option.map_some, Bool.true_and, Bool.and_true, rsLeafZero4]
    rfl
  · rw [rdX]; rfl

section RS
variable (impl : OpImpl) (κ : Kind) (inp : Input) (fi : FinIn) (r : Array Val) (P : FinP)

/-- **The inner weights** `c_{j,i}` of the four claims (`rs_column`): `eqZ λ ρ₁` for Z; `eq` at the
low 7 coordinates of Lc's (L2) and Sh's (S2's position part) points; the packing basis `bb i` for
E4's `f̂(r′)` (revision 3.13). -/
def rsW4 (j i : ℕ) : F :=
  match j with
  | 0 => (impl.eqZ (fv r ((outsOf fi "Z2").headD 0)) (pinnedRho 0)).getD i 0
  | 1 => (eqTab (ptF r ((chals fi "L2" 14).take 7))).getD i 0
  | 2 => (eqTab (ptF r (((chals fi "S2" P.S.s2).drop (P.kv.m κ - 14)).take 7))).getD i 0
  | _ => bb i

/-- **Claim `j`'s value** `α_j = Σ_i c_{j,i} s_{j,i}`. -/
def rsAlpha4 (j : ℕ) : F := ∑ k ∈ Finset.range 128, rsW4 impl κ fi r P j k * sv4 P.S inp j k

/-- **Claim `j`'s switched claim** `T_j = Σ_i bitBasis i · Φ_{r″}(s_{j,i})` (`rsT`). -/
def rsTv4 (j : ℕ) : F := ∑ k ∈ Finset.range 128, bb k * impl.phiRS (ptF r (rsFsRegs fi)) (sv4 P.S inp j k)

/-- **`v_RS = Σ_j κ^j T_j`** (Horner; a leaf's `T₃` is `0`). -/
def rsV4 : F :=
  let kp := fv r ((coordsR fi "RS1").getD 7 0)
  rsTv4 impl inp fi r P 0 + kp * (rsTv4 impl inp fi r P 1 + kp * (rsTv4 impl inp fi r P 2 +
    kp * (if P.kv.node κ then rsTv4 impl inp fi r P 3 else 0)))

/-- `finRS`'s flag: a leaf's fourth claim has zero slice values. -/
def relRS4 : Bool := P.kv.node κ || rsLeafZero4 P.S inp

/-- The registers `finRS` reads. -/
def rsRefs4 : List Reg :=
  (List.range 8).map (fun p => (coordsR fi "RS1").getD p 0) ++ [(outsOf fi "Z2").headD 0] ++
    (chals fi "L2" 14).take 7 ++ ((chals fi "S2" P.S.s2).drop (P.kv.m κ - 14)).take 7

/-- **`exec_finRS`** (A.9, RS): `finRS` asks nothing; its flag is `relRS` (a leaf's fourth claim is
zero), its exports are the claim values `α_Z, α_Lc, α_Sh, α_E` (`rsAlpha`) and `v_RS` (`rsV`). -/
theorem exec_gFinRS (hin : ∀ x ∈ rsRefs4 κ fi P, x < r.size) :
    ∃ L, pureRun impl κ inp ((gFinRS P fi r.size).1.map (reloc P.S)) r [] = some (L, relRS4 κ inp P) ∧
      (∀ j < 4, (rd (r ++ L.toArray) ((gFinRS P fi r.size).2.getD j 0)).toF = rsAlpha4 impl κ inp fi r P j) ∧
      (rd (r ++ L.toArray) ((gFinRS P fi r.size).2.getD nRS 0)).toF = rsV4 impl κ inp fi r P := by
  simp only [rsRefs4, List.mem_append, List.mem_map, List.mem_range, List.mem_cons,
    List.not_mem_nil, or_false] at hin
  have tf : ∀ x, (Val.f x).toF = x := fun _ => rfl
  have hW : elemW = 8 := rfl
  set kap := (coordsR fi "RS1").getD 7 0 with hkapd
  set lam := (outsOf fi "Z2").headD 0 with hlamd
  have hkap : kap < r.size := hin _ (.inl (.inl (.inl ⟨7, by omega, rfl⟩)))
  have hlam : lam < r.size := hin _ (.inl (.inl (.inr rfl)))
  set x1 := (chals fi "L2" 14).take 7
  set x2 := ((chals fi "S2" P.S.s2).drop (P.kv.m κ - 14)).take 7
  set x4 := rsFsRegs fi
  have hx1 : ∀ x ∈ x1, x < r.size := fun x h => hin x (.inl (.inr h))
  have hx2 : ∀ x ∈ x2, x < r.size := fun x h => hin x (.inr h)
  have hx4 : ∀ x ∈ x4, x < r.size := fun x h => by
    simp only [x4, rsFsRegs, List.mem_map, List.mem_range] at h
    obtain ⟨p, hp, rfl⟩ := h; exact hin _ (.inl (.inl (.inl ⟨p, by omega, rfl⟩)))
  set ρ := pinnedRho 0
  set p1 := ptF r x1; set p2 := ptF r x2; set p4 := ptF r x4
  set ez := impl.eqZ (fv r lam) ρ
  set L₀ : List Val := [.f ρ, .af ez, .af p1, .af (eqTab p1), .af p2, .af (eqTab p2),
    .af p4] with hL₀
  have hpk : ∀ (xs : List Reg), (∀ x ∈ xs, x < r.size) → ∀ X : List Val,
      (xs.map fun x => (rd (r ++ X.toArray) x).toF).toArray = ptF r xs := fun xs h X => by
    rw [ptF, map_rd_app r X xs h]
  have es : ∀ ops, pureRun impl κ inp ([.const (fun _ => .f ρ), .eqZ lam r.size,
      .packF x1, .eqTable (r.size + 2),
      .packFK (fun κ => ((chals fi "S2" P.S.s2).drop (P.kv.m κ - 14)).take 7), .eqTable (r.size + 4),
      .packF x4] ++ ops) r [] = pureRun impl κ inp ops r L₀ := by
    intro ops
    simp only [List.cons_append, List.nil_append]
    rw [pr_op impl κ inp r (v := .f ρ) rfl,
      pr_op impl κ inp r (v := .af ez) (by
        simp only [evalOp, rd_app0, rd_app_left r _ hlam, List.nil_append, List.getD_cons_zero]; rfl),
      pr_op impl κ inp r (v := .af p1) (by simp only [evalOp, hpk x1 hx1]; rfl),
      pr_op impl κ inp r (v := .af (eqTab p1)) (by
        simp only [evalOp, rd_app, List.nil_append, List.append_assoc, List.cons_append,
          List.getD_cons_succ, List.getD_cons_zero]; rfl),
      pr_op impl κ inp r (v := .af p2) (by
        simp only [evalOp]
        rw [show List.take 7 (List.drop (P.kv.m κ - 14) (chals fi "S2" P.S.s2)) = x2 from rfl, hpk x2 hx2]),
      pr_op impl κ inp r (v := .af (eqTab p2)) (by
        simp only [evalOp, rd_app, List.nil_append, List.append_assoc, List.cons_append,
          List.getD_cons_succ, List.getD_cons_zero]; rfl),
      pr_op impl κ inp r (v := .af p4) (by simp only [evalOp, hpk x4 hx4]; rfl)]
    simp [hL₀]
  have e7 : List.map (reloc P.S) ([.const (fun _ => .f ρ), .eqZ lam r.size,
      .packF x1, .eqTable (r.size + 2),
      .packFK (fun κ => ((chals fi "S2" P.S.s2).drop (P.kv.m κ - 14)).take 7), .eqTable (r.size + 4),
      .packF x4] : List Op) = [.const (fun _ => .f ρ), .eqZ lam r.size,
      .packF x1, .eqTable (r.size + 2),
      .packFK (fun κ => ((chals fi "S2" P.S.s2).drop (P.kv.m κ - 14)).take 7), .eqTable (r.size + 4),
      .packF x4] := rfl
  have hL0 : L₀.length = 7 := rfl
  have hrd : ∀ t < 7, ∀ X : List Val, rd (r ++ (L₀ ++ X).toArray) (r.size + t) = L₀.getD t default :=
    fun t ht X => by rw [rd_app, List.getD_append _ _ _ _ (by rw [hL0]; omega)]
  have hwE : ∀ t (ht : t < 7) (p : Array F), L₀.getD t default = .af p → ∀ i (X : List Val),
      evalOp impl κ inp (r ++ (L₀ ++ X).toArray) (.getF (r.size + t) i) =
        .vals [.f (p.getD i 0)] true := fun t ht p hp i X => by
    simp only [evalOp, hrd t ht X, hp]; rfl
  have hR : r.size + 6 < r.size + L₀.length := by rw [hL0]; omega
  have hRv : (rd (r ++ L₀.toArray) (r.size + 6)).toAF = p4 := by
    have h6 := hrd 6 (by decide) []; rw [List.append_nil] at h6; rw [h6]; rfl
  obtain ⟨N₀, c0h, c0l, c0a, c0t⟩ := run_claimOps4 impl κ inp r P.S 0 _ (r.size + 6) p4 (rsW4 impl κ fi r P 0)
    L₀ [] hR hRv (hwE 1 (by decide) ez rfl) (fun _ => rfl)
  obtain ⟨N₁, c1h, c1l, c1a, c1t⟩ := run_claimOps4 impl κ inp r P.S 1 _ (r.size + 6) p4 (rsW4 impl κ fi r P 1)
    L₀ N₀ hR hRv (hwE 3 (by decide) (eqTab p1) rfl) (fun _ => rfl)
  obtain ⟨N₂, c2h, c2l, c2a, c2t⟩ := run_claimOps4 impl κ inp r P.S 2 _ (r.size + 6) p4 (rsW4 impl κ fi r P 2)
    L₀ (N₀ ++ N₁) hR hRv (hwE 5 (by decide) (eqTab p2) rfl) (fun _ => rfl)
  obtain ⟨N₃, c3h, c3l, c3a, c3t⟩ := run_claimOps4 impl κ inp r P.S 3 (fun i => .const (fun _ => .f (bb i)))
    (r.size + 6) p4 (rsW4 impl κ fi r P 3) L₀ (N₀ ++ N₁ ++ N₂) hR hRv (fun _ _ => rfl) (fun _ => rfl)
  simp only [List.length_append, List.length_nil, hL0, c0l, c1l, c2l, Nat.add_zero] at c0h c1h c2h c3h c0a c1a c2a c3a c0t c1t c2t c3t
  simp only [List.append_nil, List.append_assoc] at c0h c1h c2h c3h c0a c1a c2a c3a c0t c1t c2t c3t
  rw [show 1 + 128 * elemW + (1 + 128 * elemW) = 2 * (1 + 128 * elemW) by ring] at c2h
  rw [show 1 + 128 * elemW + (1 + 128 * elemW) + (1 + 128 * elemW) = 3 * (1 + 128 * elemW) by ring] at c3h
  simp only [gFinRS, List.map_append, List.append_assoc]
  rw [e7]
  rw [es, pr_app' impl κ inp r c0h, pr_app' impl κ inp r c1h, pr_app' impl κ inp r c2h,
    pr_app' impl κ inp r c3h]
  set A := 1 + 128 * elemW with hAd
  set Lc := L₀ ++ (N₀ ++ (N₁ ++ (N₂ ++ N₃)))
  have hLc : Lc.length = 7 + 4 * A := by
    simp only [Lc, List.length_append, hL0, c0l, c1l, c2l, c3l]; ring
  have pre : ∀ (P Q : List Val) (t : ℕ), t < r.size + P.length →
      rd (r ++ (P ++ Q).toArray) t = rd (r ++ P.toArray) t := fun P Q t h => rdL r h
  have rT : ∀ (P Q : List Val) (t t' : ℕ) (v : F), Lc = P ++ Q → t' < r.size + P.length → t = t' →
      (rd (r ++ P.toArray) t').toF = v → (rd (r ++ Lc.toArray) t).toF = v := by
    intro P Q t t' v hPQ ht he hv; rw [hPQ, he, pre P Q t' ht, hv]
  obtain ⟨Mt, ht, hvt⟩ := run_rsTail4 impl κ inp r P kap (r.size + 7 + A - 1)
    (r.size + 7 + 2 * A - 1) (r.size + 7 + 3 * A - 1)
    (r.size + Lc.length - 1) Lc (rsTv4 impl inp fi r P 0) (rsTv4 impl inp fi r P 1) (rsTv4 impl inp fi r P 2)
    (rsTv4 impl inp fi r P 3) (fv r kap) hkap rfl
    (by rw [hLc]; omega) (by rw [hLc]; omega) (by rw [hLc]; omega) (by rw [hLc]; omega)
    (rT (L₀ ++ N₀) (N₁ ++ (N₂ ++ N₃)) _ _ _ (by simp [Lc]) (by simp [hL0, c0l]; omega)
      (by omega) c0t)
    (rT (L₀ ++ (N₀ ++ N₁)) (N₂ ++ N₃) _ _ _ (by simp [Lc]) (by simp [hL0, c0l, c1l]; omega)
      (by omega) c1t)
    (rT (L₀ ++ (N₀ ++ (N₁ ++ N₂))) N₃ _ _ _ (by simp [Lc])
      (by simp [hL0, c0l, c1l, c2l]; omega) (by omega) c2t)
    (rT Lc [] _ _ _ (by simp) (by simp [Lc, hL0, c0l, c1l, c2l, c3l]; omega) (by omega) c3t)
  rw [← hkapd, show r.size + 7 + 4 * A = r.size + Lc.length by rw [hLc]; omega, ht]
  refine ⟨Lc ++ Mt, rfl, fun j hj => ?_, ?_⟩
  · have rA : ∀ (P Q : List Val) (t t' : ℕ) (v : F), Lc = P ++ Q → t' < r.size + P.length → t = t' →
        (rd (r ++ P.toArray) t').toF = v → (rd (r ++ (Lc ++ Mt).toArray) t).toF = v := by
      intro P Q t t' v hPQ ht' he hv
      have hlt : t < r.size + Lc.length := by rw [he, hPQ, List.length_append]; omega
      rw [pre Lc Mt t hlt]; exact rT P Q t t' v hPQ ht' he hv
    interval_cases j <;> simp only [List.range_succ, List.range_zero, List.map_append, List.map_cons,
      List.map_nil, List.nil_append, List.cons_append, List.getD_cons_zero, List.getD_cons_succ]
    · exact rA (L₀ ++ N₀) (N₁ ++ (N₂ ++ N₃)) _ _ _ (by simp [Lc]) (by simp [hL0, c0l]; omega)
        (by omega) c0a
    · exact rA (L₀ ++ (N₀ ++ N₁)) (N₂ ++ N₃) _ _ _ (by simp [Lc])
        (by simp [hL0, c0l, c1l]; omega) (by omega) c1a
    · exact rA (L₀ ++ (N₀ ++ (N₁ ++ N₂))) N₃ _ _ _ (by simp [Lc])
        (by simp [hL0, c0l, c1l, c2l]; omega) (by omega) c2a
    · exact rA Lc [] _ _ _ (by simp) (by simp [Lc, hL0, c0l, c1l, c2l, c3l]; omega) (by omega) c3a
  · simp only [nRS, List.range_succ, List.range_zero, List.map_append, List.map_cons, List.map_nil,
      List.nil_append, List.cons_append, List.getD_cons_zero, List.getD_cons_succ]
    rw [hvt]; rfl


end RS

end FR.Snd.R4
