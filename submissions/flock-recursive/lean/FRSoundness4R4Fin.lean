-- New for `flock-recursive` (BLUEPRINT revision 4.1, A.9; stage R4c).
import FRVerifierC4

/-!
# The finals' flags at `FinP` on the relocated ops (Z, Lr, E, B′)

`finOps4 P` runs `finalsOf P`'s fields relocated to `P.S`'s format (`reloc P.S`): a read of field
`f < 19` at offset `o` becomes the absolute read `fieldOffOf P.S f + o` (`evalOp_reloc`). Each lemma
here is 3.x's `flag_fin*` (`FRVIRFinals`, `FRVIRFinalsSF`) at `P`'s sizes: the relation is 3.x's
with the sizes (`P.S.z3`, `P.lrR`, `P.e2R`, `P.e4R`), the kind tables (`P.kv.m`, `P.kv.node`) and
the proof reads (`pe4 P.S`) made parameters. At 3.x's parameters each is 3.x's relation
(`relZ4_fin3P`, …: the controls).
-/

namespace FR.Snd.R4
open RecursionFast Rev4

/-! ## Relocated reads -/

/-- The F element at byte `o` of field `f` in `S`'s format. -/
def pe4 (S : Seq) (inp : Input) (f o : ℕ) : F := F.ofBytes (bytesAt inp.π (fieldOffOf S f + o) 16)

section Reloc
variable (impl : OpImpl) (κ : Kind) (inp : Input) (regs : Array Val) (S : Seq)

/-- **A relocated read** of field `f < 19` reads `fieldOffOf S f + o` absolutely. -/
theorem evalOp_reloc {f : ℕ} (hf : f < 19) (o len k : ℕ) :
    evalOp impl κ inp regs (reloc S (.piField f o len)) =
      .vals [.b (inp.π.extract (fieldOffOf S f + o) (fieldOffOf S f + o + len))] true ∧
    evalOp impl κ inp regs (reloc S (.piElem f o)) = .vals [.f (pe4 S inp f o)] true ∧
    evalOp impl κ inp regs (reloc S (.piElemK f o)) =
      .vals [.k (K.ofBytes (bytesAt inp.π (fieldOffOf S f + o) 32))] true ∧
    evalOp impl κ inp regs (reloc S (.piDigest f o)) = .vals [.d (digestAt inp.π (fieldOffOf S f + o))] true ∧
    evalOp impl κ inp regs (reloc S (.piDigestAt f o k)) =
      .vals [.d (digestAt inp.π (fieldOffOf S f + o + 32 * (rd regs k).toN))] true := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> simp only [reloc, hf, ite_true, evalOp, absOff_zero, pe4]

/-- `reloc` on a read of field `f < 19` (the simp form). -/
theorem reloc_piElem {f : ℕ} (hf : f < 19) (o : ℕ) :
    reloc S (.piElem f o) = .piElem 0 (fieldOffOf S f + o) := if_pos hf
theorem reloc_piField {f : ℕ} (hf : f < 19) (o len : ℕ) :
    reloc S (.piField f o len) = .piField 0 (fieldOffOf S f + o) len := if_pos hf
theorem reloc_piDigest {f : ℕ} (hf : f < 19) (o : ℕ) :
    reloc S (.piDigest f o) = .piDigest 0 (fieldOffOf S f + o) := if_pos hf

theorem evalOp_piElem0 (x : ℕ) :
    evalOp impl κ inp regs (.piElem 0 x) = .vals [.f (F.ofBytes (bytesAt inp.π x 16))] true := by
  simp only [evalOp, absOff_zero]
theorem evalOp_piField0 (x len : ℕ) :
    evalOp impl κ inp regs (.piField 0 x len) = .vals [.b (inp.π.extract x (x + len))] true := by
  simp only [evalOp, absOff_zero]
theorem evalOp_piDigest0 (x : ℕ) :
    evalOp impl κ inp regs (.piDigest 0 x) = .vals [.d (digestAt inp.π x)] true := by
  simp only [evalOp, absOff_zero]

end Reloc

section Flags
variable (impl : OpImpl) (κ : Kind) (inp : Input) (fi : FinIn) (r : Array Val) (P : FinP)

/-! ## `finZ` -/

/-- **`relZ` at `P`**: (i) `eq((ρ, r), r′)·â·b̂ = c_Z` over the kind's `m`, Z3's `P.S.z3`
challenges and the relocated Z-end reads; (ii) `P^z*(λ) = α_Z`. -/
def relZ4 : Bool :=
  let rr := (List.ofFn pinnedRho ++ ((coordsR fi "Z1").take (P.kv.m κ - 13)).map (fv r)).toArray
  let rr' := (((chals fi "Z3" P.S.z3).take (P.kv.m κ - 6)).map (fv r)).toArray
  (Val.f (eqPoint rr rr' * pe4 P.S inp fZend 0 * pe4 P.S inp fZend 16)).eqv (rd r (claimN fi "Z3")) &&
  (rd r ((outsOf fi "Z2").getD 2 0)).eqv (rd r (fi.zhat.getD 0 0))

theorem flag_gFinZ (hin : ∀ x ∈ coordsR fi "Z1" ++ chals fi "Z3" P.S.z3 ++
      [claimN fi "Z3", (outsOf fi "Z2").getD 2 0, fi.zhat.getD 0 0], x < r.size) :
    ∃ L, pureRun impl κ inp ((gFinZ P fi r.size).1.map (reloc P.S)) r [] =
      some (L, relZ4 κ inp fi r P) := by
  simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hin
  have h1 := fun L => map_rd_app r L ((coordsR fi "Z1").take (P.kv.m κ - 13))
    fun x hx => hin x (.inl (.inl (List.mem_of_mem_take hx)))
  have h2 := fun L => map_rd_app r L ((chals fi "Z3" P.S.z3).take (P.kv.m κ - 6))
    fun x hx => hin x (.inl (.inr (List.mem_of_mem_take hx)))
  have tf : ∀ x, (Val.f x).toF = x := fun _ => rfl
  have taf : ∀ x, (Val.af x).toAF = x := fun _ => rfl
  have hZ : fZend < 19 := by decide
  simp only [gFinZ, relZ4, pinOps, List.ofFn_succ, List.ofFn_zero, List.map_cons, List.map_nil,
    List.cons_append, List.nil_append, reloc_piElem _ hZ]
  generalize claimN fi "Z3" = cz at *
  generalize (outsOf fi "Z2").getD 2 0 = pz at *
  generalize fi.zhat.getD 0 0 = az at *
  have h5 := hin cz (.inr (.inl rfl)); have h6 := hin pz (.inr (.inr (.inl rfl)))
  have h7 := hin az (.inr (.inr (.inr rfl)))
  simp only [pureRun, reloc, evalOp, absOff_zero, tf, taf, List.nil_append, List.cons_append,
    List.map_cons, h1, h2, rd_app, rd_app0, rd_app_left _ _ h5,
    rd_app_left _ _ h6, rd_app_left _ _ h7, List.getD_cons_succ,
    List.getD_cons_zero, Option.map_some, Val.eqv, allK, Bool.not_true, Bool.false_or, Bool.true_and,
    Bool.and_true]
  exact ⟨_, rfl⟩

/-! ## `finLr` -/

/-- **`relLr` at `P`** (a node's end check over its `P.lrR` real rows, relocated Lr-end reads). -/
def relLr4 : Bool :=
  let rLr := (((coordsR fi "Lr1").take P.lrR).map (fv r)).toArray
  let rr := ((chals fi "Lr2" P.lrR).map (fv r)).toArray
  let a := pe4 P.S inp fLrEnd 0; let bb := pe4 P.S inp fLrEnd 16; let c := pe4 P.S inp fLrEnd 32
  if P.kv.node κ then (Val.f (eqPoint rLr rr * (a * bb + c))).eqv (rd r (claimN fi "Lr2")) else true

/-- `finLr`'s export `v_L` at `P`. -/
def vLv4 : F :=
  let kL := fv r ((outsOf fi "Lr3").headD 0)
  pe4 P.S inp fLrEnd 0 + kL * pe4 P.S inp fLrEnd 16 + kL * kL * pe4 P.S inp fLrEnd 32

theorem flag_gFinLr (hin : ∀ x ∈ (coordsR fi "Lr1").take P.lrR ++ chals fi "Lr2" P.lrR ++
      [(outsOf fi "Lr3").headD 0, claimN fi "Lr2"], x < r.size) :
    ∃ L, pureRun impl κ inp ((gFinLr P fi r.size).1.map (reloc P.S)) r [] =
        some (L, relLr4 κ inp fi r P) ∧
      (rd (r ++ L.toArray) ((gFinLr P fi r.size).2.getD 0 0)).toF = vLv4 inp fi r P ∧
      (rd (r ++ L.toArray) ((gFinLr P fi r.size).2.getD 1 0)).toAF =
        ((chals fi "Lr2" P.lrR).map (fv r)).toArray := by
  simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hin
  have h1 := fun L => map_rd_app r L ((coordsR fi "Lr1").take P.lrR) fun x hx => hin x (.inl (.inl hx))
  have h2 := fun L => map_rd_app r L (chals fi "Lr2" P.lrR) fun x hx => hin x (.inl (.inr hx))
  have tf : ∀ x, (Val.f x).toF = x := fun _ => rfl
  have taf : ∀ x, (Val.af x).toAF = x := fun _ => rfl
  have hL : fLrEnd < 19 := by decide
  simp only [gFinLr, relLr4, vLv4, List.map_cons, List.map_nil, reloc_piElem _ hL]
  generalize (outsOf fi "Lr3").headD 0 = kl at *
  generalize claimN fi "Lr2" = c2 at *
  have hk := hin kl (.inr (.inl rfl)); have hc2 := hin c2 (.inr (.inr rfl))
  cases hn : P.kv.node κ <;>
  simp only [hn, pureRun, reloc, evalOp, absOff_zero, tf, taf, List.nil_append, List.cons_append,
    h1, h2, rd_app, rd_app0, rd_app_left _ _ hk, rd_app_left _ _ hc2,
    List.getD_cons_succ, List.getD_cons_zero,
    Option.map_some, Bool.not_true, Bool.not_false, Bool.false_or, Bool.true_or, Bool.true_and,
    Bool.and_true, ↓reduceIte, Bool.false_eq_true] <;>
  exact ⟨_, rfl, rfl, rfl⟩

/-! ## `finE` -/

/-- **`relE` at `P`**: (ii)–(iv) for a node over its `P.e2R`/`P.e4R` real rounds, (v) (E4 end is
`f̂(r′) ‖ 0^16`, read at `S`'s E4-end offset) for every kind. -/
def relE4 : Bool :=
  let rE := (((coordsR fi "E1").take P.e2R).map (fv r)).toArray
  let r2 := ((chals fi "E2" P.e2R).map (fv r)).toArray
  let r4 := ((chals fi "E4" P.e4R).map (fv r)).toArray
  let kE := fv r ((outsOf fi "E3").headD 0)
  let kL := fv r ((outsOf fi "Lr3").headD 0)
  let a := pe4 P.S inp fEEnd 0; let bb := pe4 P.S inp fEEnd 16; let c := pe4 P.S inp fEEnd 32
  let m := impl.evalM r2 r4
  let l := impl.evalL (rd r (lrEx fi 1)).toAF r4
  let wM := m.1 + kE * m.2.1 + kE * kE * m.2.2
  let wL := l.1 + kL * l.2.1 + kL * kL * l.2.2
  let o := fieldOffOf P.S fE + (gOE4end P.S + 16)
  let e4 := (Val.f (pe4 P.S inp fE (gOE4end P.S))).eqv (rd r (fi.zhat.getD 3 0)) &&
    (inp.π.extract o (o + 16)).data.all (· == 0)
  if P.kv.node κ then
    (Val.f (eqPoint rE r2 * (a * bb + c))).eqv (rd r (claimN fi "E2")) &&
    ((Val.f (a + kE * bb + kE * kE * c + kE * kE * kE * fv r (lrEx fi 0))).eqv
      (rd r (claim0 fi "E4")) &&
    ((Val.f ((wM + kE * kE * kE * wL) * fv r (fi.zhat.getD 3 0))).eqv (rd r (claimN fi "E4")) &&
      e4))
  else e4

theorem flag_gFinE (hin : ∀ x ∈ (coordsR fi "E1").take P.e2R ++ chals fi "E2" P.e2R ++
      chals fi "E4" P.e4R ++
      [(outsOf fi "E3").headD 0, claimN fi "E2", claim0 fi "E4", claimN fi "E4",
       fi.zhat.getD 3 0, (outsOf fi "Lr3").headD 0, lrEx fi 0, lrEx fi 1], x < r.size) :
    ∃ L, pureRun impl κ inp ((gFinE P fi r.size).1.map (reloc P.S)) r [] =
        some (L, relE4 impl κ inp fi r P) ∧
      (rd (r ++ L.toArray) ((gFinE P fi r.size).2.getD 0 0)).toAF =
        ((chals fi "E4" P.e4R).map (fv r)).toArray := by
  simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hin
  have h1 := fun L => map_rd_app r L ((coordsR fi "E1").take P.e2R)
    fun x hx => hin x (.inl (.inl (.inl hx)))
  have h2 := fun L => map_rd_app r L (chals fi "E2" P.e2R) fun x hx => hin x (.inl (.inl (.inr hx)))
  have h3 := fun L => map_rd_app r L (chals fi "E4" P.e4R) fun x hx => hin x (.inl (.inr hx))
  have tf : ∀ x, (Val.f x).toF = x := fun _ => rfl
  have taf : ∀ x, (Val.af x).toAF = x := fun _ => rfl
  have hEE : fEEnd < 19 := by decide
  have hE : fE < 19 := by decide
  simp only [gFinE, relE4, List.map_cons, List.map_nil, reloc_piElem _ hEE, reloc_piElem _ hE,
    reloc_piField _ hE]
  generalize (outsOf fi "E3").headD 0 = ke at *
  generalize claimN fi "E2" = c2 at *
  generalize claim0 fi "E4" = c40 at *
  generalize claimN fi "E4" = c4 at *
  generalize fi.zhat.getD 3 0 = ze at *
  generalize (outsOf fi "Lr3").headD 0 = kl at *
  generalize lrEx fi 0 = vl at *
  generalize lrEx fi 1 = rl at *
  have hk := hin ke (.inr (.inl rfl)); have hc2 := hin c2 (.inr (.inr (.inl rfl)))
  have hc40 := hin c40 (.inr (.inr (.inr (.inl rfl))))
  have hc4 := hin c4 (.inr (.inr (.inr (.inr (.inl rfl)))))
  have hze := hin ze (.inr (.inr (.inr (.inr (.inr (.inl rfl))))))
  have hkl := hin kl (.inr (.inr (.inr (.inr (.inr (.inr (.inl rfl)))))))
  have hvl := hin vl (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl rfl))))))))
  have hrl := hin rl (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr rfl))))))))
  cases hn : P.kv.node κ <;>
  simp only [hn, pureRun, reloc, evalOp, absOff_zero, tf, taf, List.nil_append,
    List.cons_append, h1, h2, h3,
    rd_app, rd_app0, rd_app_left _ _ hk, rd_app_left _ _ hc2, rd_app_left _ _ hc40,
    rd_app_left _ _ hc4, rd_app_left _ _ hze, rd_app_left _ _ hkl, rd_app_left _ _ hvl,
    rd_app_left _ _ hrl,
    List.getD_cons_succ, List.getD_cons_zero, allK,
    Option.map_some, Bool.not_true, Bool.not_false, Bool.false_or, Bool.true_or, Bool.true_and,
    Bool.and_true, ↓reduceIte, Bool.false_eq_true, Val.isZero] <;>
  exact ⟨_, rfl, rfl⟩

/-! ## `finB′` -/

/-- `pubH` at `P`: the statement's digests read at `S`'s `stmt` offset. -/
def pubH4 (kp : F) : F :=
  let vl := dLo inp.vk; let vh := dHi inp.vk
  let c₁ := bytesAt inp.π (fieldOffOf P.S fStmt + 1) 32
  let c₂ := bytesAt inp.π (fieldOffOf P.S fStmt + 33) 32
  1 + kp * (vl + kp * (vh + kp * (dLo c₁ + kp * (dHi c₁ + kp * (vl + kp * (vh + kp * (dLo c₂ +
    kp * dHi c₂)))))))

/-- `v*` at `P`. -/
def vStar4 : F :=
  let kp := fv r ((outsOf fi "B'").headD 0)
  fv r (fi.zhat.getD nRS 0) + (if P.kv.node κ then kp * kp * pubH4 inp P kp else 0)

/-- **`relB` at `P`**: `v*` (in `K`) is P1.0's initial claim. -/
def relB4 : Bool := (Val.k (K.smulF (vStar4 κ inp fi r P) 1)).eqv (rd r (claim0 fi "P1"))

theorem flag_gFinB' (hin : ∀ x ∈ [(outsOf fi "B'").headD 0, fi.zhat.getD nRS 0, claim0 fi "P1"],
      x < r.size) :
    ∃ L, pureRun impl κ inp ((gFinB' P fi r.size).1.map (reloc P.S)) r [] =
        some (L, relB4 κ inp fi r P) ∧
      (rd (r ++ L.toArray) ((gFinB' P fi r.size).2.getD 0 0)).toF = vStar4 κ inp fi r P := by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hin
  have tf : ∀ x, (Val.f x).toF = x := fun _ => rfl
  have td : ∀ x, (Val.d x).toD = x := fun _ => rfl
  have tk : ∀ x, (Val.k x).toK = x := fun _ => rfl
  have hS : fStmt < 19 := by decide
  simp only [gFinB', relB4, vStar4, pubH4, dLo, dHi, List.map_cons, List.map_nil,
    reloc_piDigest _ hS]
  generalize (outsOf fi "B'").headD 0 = kp at *
  generalize fi.zhat.getD nRS 0 = vR at *
  generalize claim0 fi "P1" = c0 at *
  have hk := hin kp (.inl rfl); have hR := hin vR (.inr (.inl rfl))
  have hc := hin c0 (.inr (.inr rfl))
  cases hn : P.kv.node κ <;>
  simp only [hn, pureRun, reloc, evalOp, absOff_zero, tf, td, tk, List.nil_append,
    List.cons_append, rd_app, rd_app0, rd_app_left _ _ hk, rd_app_left _ _ hR, rd_app_left _ _ hc,
    List.getD_cons_succ, List.getD_cons_zero, Option.map_some, allK, Bool.not_true, Bool.false_or,
    Bool.true_and, Bool.and_true, ↓reduceIte, Bool.false_eq_true, digestAt_eq] <;>
  exact ⟨_, rfl, rfl⟩

end Flags

end FR.Snd.R4
