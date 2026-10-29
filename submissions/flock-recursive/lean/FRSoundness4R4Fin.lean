-- New for `flock-recursive` (BLUEPRINT revision 4.1, A.9; stage R4c).
import FRSoundness4RsvRun

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

/-! ## Running the flags on a reversed accumulator

`pureRun` appends each op's outputs to its accumulator, `L ++ vs`. A `simp` that keeps `L` as one
list literal pays `List.cons_append` over the whole of `L` at every op, and `List.getD_cons_succ`
up to the read at every read: quadratic in the program's length (G3 §3). The flag proofs below
keep the accumulator as `M.reverse` (`M` the outputs, newest first): an op's output is consed onto
`M` (`revAcc_app_cons`), and a read is one lookup in the literal `default :: M` (`rd_revAcc`, by
`Array.reduceGetElem?`) at the distance back from the newest output. -/

/-- Entry `k` of `M.reverse` is entry `M.length - k` of `default :: M`; the `default` stands for
every read past the end. -/
theorem getD_revAcc (M : List Val) (k : ℕ) :
    M.reverse.getD k default = (((default : Val) :: M).toArray[M.length - k]?).getD default := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_toArray]
  rcases Nat.lt_or_ge k M.length with h | h
  · rw [List.getElem?_reverse h, show M.length - k = (M.length - 1 - k) + 1 by omega]; rfl
  · rw [List.getElem?_eq_none (by simpa using h), Nat.sub_eq_zero_of_le h]; rfl

/-- A read of `r ++ M.reverse` at `r.size + k`: one lookup in the literal `default :: M`. -/
theorem rd_revAcc (r : Array Val) (M : List Val) (k : ℕ) :
    rd (r ++ M.reverse.toArray) (r.size + k) =
      (((default : Val) :: M).toArray[M.length - k]?).getD default := by
  rw [rd_app, getD_revAcc]

theorem rd_revAcc0 (r : Array Val) (M : List Val) :
    rd (r ++ M.reverse.toArray) r.size =
      (((default : Val) :: M).toArray[M.length]?).getD default := by
  simpa using rd_revAcc r M 0

/-- An op's outputs join a reversed accumulator at its head. -/
theorem revAcc_app_cons (M : List Val) (a : Val) (as : List Val) :
    M.reverse ++ a :: as = (a :: M).reverse ++ as := by simp

/-- A read at `x ≥ n = R.size` of `R ++ M.reverse` (a block's base is `c + k`, not `r.size + k`). -/
theorem rd_revAccAt (R : Array Val) (M : List Val) {n : ℕ} (hR : R.size = n) {x : ℕ} (hx : n ≤ x) :
    rd (R ++ M.reverse.toArray) x = (((default : Val) :: M).toArray[M.length - (x - n)]?).getD default := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hx
  subst hR
  rw [Nat.add_sub_cancel_left]
  exact rd_revAcc R M k

/-- A run from `[]` is a run from the empty reversed accumulator. -/
theorem pureRun_nil_rev (impl : OpImpl) (κ : Kind) (inp : Input) (ops : List Op) (r : Array Val) :
    pureRun impl κ inp ops r [] = pureRun impl κ inp ops r ([] : List Val).reverse := rfl

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
  rw [pureRun_nil_rev]
  simp only [pureRun, reloc, evalOp, absOff_zero, tf, taf, List.map_cons, h1, h2, rd_revAcc,
    rd_revAcc0, revAcc_app_cons, List.append_nil, List.length_cons, List.length_nil, Nat.reduceAdd,
    Nat.reduceSub, Array.reduceGetElem?, Option.getD_some, rd_app_left _ _ h5,
    rd_app_left _ _ h6, rd_app_left _ _ h7, Option.map_some, Val.eqv, allK, Bool.not_true,
    Bool.false_or, Bool.true_and, Bool.and_true]
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
  rw [pureRun_nil_rev]
  cases hc : P.ck <;> cases hn : P.kv.node κ <;>
  simp only [hc, Bool.cond_true, Bool.cond_false, hn, pureRun, reloc, evalOp, absOff_zero, tf, taf,
    h1, h2, rd_revAcc, rd_revAcc0, revAcc_app_cons, List.append_nil, List.length_cons,
    List.length_nil, Nat.reduceAdd, Nat.reduceSub, Array.reduceGetElem?, Option.getD_some,
    rd_app_left _ _ hk, rd_app_left _ _ hc2,
    Option.map_some, Bool.not_true, Bool.not_false, Bool.false_or, Bool.true_or, Bool.true_and,
    Bool.and_true, ↓reduceIte, Bool.false_eq_true] <;>
  refine ⟨_, rfl, ?_, ?_⟩ <;> simp only [List.getD_cons_succ, List.getD_cons_zero, rd_revAcc,
    List.length_cons, List.length_nil, Nat.reduceAdd, Nat.reduceSub, Array.reduceGetElem?,
    Option.getD_some, tf, taf] <;> rfl

/-! ## `finE` -/

/-- **`relE` at `P` without the reserve** (3.x, the segment group): (ii)–(iv) for a node over its `P.e2R`/`P.e4R` real rounds, (v) (E4 end is
`f̂(r′) ‖ 0^16`, read at `S`'s E4-end offset) for every kind. -/
def relE4o : Bool :=
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

/-- **The reserve's child claim on the registers' input** (RSV2 §2.1, revision 4.4.2): `p_x` (23),
`p_y` (25), `s` (9) from `fLrEnd` at `rsvRx`, `rsvRy`, `rsvS`. -/
def rsvPx4 (inp : Input) (P : FinP) : List F :=
  (List.range 23).map fun j => pe4 P.S inp fLrEnd (rsvRx + 16 * j)
def rsvPy4 (inp : Input) (P : FinP) : List F :=
  (List.range 25).map fun j => pe4 P.S inp fLrEnd (rsvRy + 16 * j)
def rsvS4 (inp : Input) (P : FinP) : List F :=
  (List.range 9).map fun j => pe4 P.S inp fLrEnd (rsvS + 16 * j)

/-- **`relE` at `P`**. Without the reserve (`rsvOps` off: 3.x, the segment group): (ii)–(iv) for a
node over its `P.e2R`/`P.e4R` real rounds, (v) (E4 end is `f̂(r′) ‖ 0^16`, read at `S`'s E4-end
offset) for every kind. **With the reserve** (RSV2 §2.2): (v); `fEEnd[64, 112) = 0`; where the
kind's `rsv` is off, `fLrEnd[48, 1008) = 0` and `fEEnd[48, 64) = 0`; `X₃[1] = X₃[2] = 0`; and on a node

* (ii″) `claimN(E2) = eq(τ, r_E2)(âb̂ + ĉ) + eq(p_x, r_E2)·η·(m̂* + X)`;
* (iii″) `claim0(E4) = â + κ_E b̂ + κ_E² ĉ + κ_E³ v_L + κ_E⁴ m̂*`;
* (iv″) `claimN(E4) = X^P + κ_E³·L̃·f̂`, `X^P` the **one** `evalM` at the row point
  `r_E2[<22] ‖ x̂₂₂ ‖ s^P` (32 entries) and the column point `r′[<24] ‖ ŷ₂₄` (25), with
  `s^P_{3k+m} = [k = κ.ix]·f̂·κ_E^m + κ_E⁴·eq(p_y, r′)·s_{3k+m}` and the mixed entries
  `x̂₂₂ = (r_E2 ‖ p_x[e2R, 23))[22]`, `ŷ₂₄ = (r′ ‖ p_y[e4R, 25))[24]`. -/
def relE4 : Bool :=
  let rE := (((coordsR fi "E1").take P.e2R).map (fv r)).toArray
  let r2 := ((chals fi "E2" P.e2R).map (fv r)).toArray
  let r4 := ((chals fi "E4" P.e4R).map (fv r)).toArray
  let kE := fv r ((outsOf fi "E3").headD 0)
  let kL := fv r ((outsOf fi "Lr3").headD 0)
  let a := pe4 P.S inp fEEnd 0; let bb := pe4 P.S inp fEEnd 16; let c := pe4 P.S inp fEEnd 32
  let l := impl.evalL (rd r (lrEx fi 1)).toAF r4
  let wL := l.1 + kL * l.2.1 + kL * kL * l.2.2
  let o := fieldOffOf P.S fE + (gOE4end P.S + 16)
  let e4 := (Val.f (pe4 P.S inp fE (gOE4end P.S))).eqv (rd r (fi.zhat.getD 3 0)) &&
    (inp.π.extract o (o + 16)).data.all (· == 0)
  if P.rsvOps then
    let px := rsvPx4 inp P; let py := rsvPy4 inp P; let s := rsvS4 inp P
    let X0 := pe4 P.S inp fLrEnd rsvX
    let mh := pe4 P.S inp fEEnd 48
    let eta := fv r ((coordsR fi "E1").getD 23 0)
    let fz := fv r (fi.zhat.getD 3 0)
    let w := kE * kE * (kE * kE) * eqPoint (py.take P.e4R).toArray r4
    let ind : ℕ → F := fun k => if P.kix = k then 1 else 0
    let t : ℕ → F := fun m => [fz, fz * kE, fz * (kE * kE)].getD m 0
    let sP := (List.range 9).map fun i => ind (i / 3) * t (i % 3) + w * s.getD i 0
    let x22 := ((chals fi "E2" P.e2R).map (fv r) ++ px.drop P.e2R).getD 22 (fv r 0)
    let y24 := ((chals fi "E4" P.e4R).map (fv r) ++ py.drop P.e4R).getD 24 (fv r 0)
    let XP := (impl.evalM ((((chals fi "E2" P.e2R).map (fv r)).take 22 ++ [x22] ++ sP).toArray)
      ((((chals fi "E4" P.e4R).map (fv r)).take 24 ++ [y24]).toArray)).1
    let oE := fieldOffOf P.S fEEnd; let oL := fieldOffOf P.S fLrEnd
    e4 && ((inp.π.extract (oE + 64) (oE + 64 + 48)).data.all (· == 0) &&
      ((P.rsv || (inp.π.extract (oL + 48) (oL + 48 + 960)).data.all (· == 0)) &&
      ((P.rsv || (inp.π.extract (oE + 48) (oE + 48 + 16)).data.all (· == 0)) &&
      (decide (pe4 P.S inp fLrEnd (rsvX + 16) = 0) && (decide (pe4 P.S inp fLrEnd (rsvX + 32) = 0) &&
      ((!P.kv.node κ || (Val.f (eqPoint rE r2 * (a * bb + c) +
          eqPoint (px.take P.e2R).toArray r2 * (eta * (mh + X0)))).eqv (rd r (claimN fi "E2"))) &&
      ((!P.kv.node κ || (Val.f (a + kE * bb + kE * kE * c + kE * kE * kE * fv r (lrEx fi 0) +
          kE * kE * (kE * kE) * mh)).eqv (rd r (claim0 fi "E4"))) &&
      (!P.kv.node κ || (Val.f (XP + kE * kE * kE * wL * fz)).eqv (rd r (claimN fi "E4"))))))))))
  else relE4o impl κ inp fi r P

/-- A read at a list entry is the entry of the reads (`List.getD_map`). -/
theorem rd_getD_toF (R : Array Val) (l : List Reg) (i d : ℕ) :
    (rd R (l.getD i d)).toF = (l.map fun x => (rd R x).toF).getD i (rd R d).toF := by
  rw [List.getD_map]

theorem flag_gFinE0 (hin : ∀ x ∈ (coordsR fi "E1").take P.e2R ++ chals fi "E2" P.e2R ++
      chals fi "E4" P.e4R ++
      [(outsOf fi "E3").headD 0, claimN fi "E2", claim0 fi "E4", claimN fi "E4",
       fi.zhat.getD 3 0, (outsOf fi "Lr3").headD 0, lrEx fi 0, lrEx fi 1], x < r.size) :
    ∃ L, pureRun impl κ inp ((gFinE0 P fi r.size (fun κ => P.kv.node κ) true).map (reloc P.S)) r [] =
        some (L, relE4o impl κ inp fi r P) ∧
      (rd (r ++ L.toArray) (r.size + 17)).toAF =
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
  simp only [gFinE0, relE4o, cond_true, List.cons_append, List.nil_append, List.map_append, List.map_cons, List.map_nil, reloc_piElem _ hEE, reloc_piElem _ hE,
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
  rw [pureRun_nil_rev]
  cases hc : P.ck <;> cases hn : P.kv.node κ <;>
  simp only [hc, Bool.cond_true, Bool.cond_false, hn, pureRun, reloc, evalOp, absOff_zero, tf, taf,
    h1, h2, h3, rd_revAcc, rd_revAcc0, revAcc_app_cons, List.append_nil, List.length_cons,
    List.length_nil, Nat.reduceAdd, Nat.reduceSub, Array.reduceGetElem?, Option.getD_some,
    rd_app_left _ _ hk, rd_app_left _ _ hc2, rd_app_left _ _ hc40,
    rd_app_left _ _ hc4, rd_app_left _ _ hze, rd_app_left _ _ hkl, rd_app_left _ _ hvl,
    rd_app_left _ _ hrl, allK,
    Option.map_some, Bool.not_true, Bool.not_false, Bool.false_or, Bool.true_or, Bool.true_and,
    Bool.and_true, ↓reduceIte, Bool.false_eq_true, Val.isZero] <;>
  refine ⟨_, rfl, ?_⟩ <;> simp only [List.getD_cons_zero, rd_revAcc,
    List.length_cons, List.length_nil, Nat.reduceAdd, Nat.reduceSub, Array.reduceGetElem?,
    Option.getD_some, taf]

/-- **Block A of the reserve's `finE`**: the own ops with no `evalM` and no assert
(`gFinE0 … (fun _ => false) false`): the flag is (v), and the registers the reserve's block reads. -/
theorem run_gFinE0off (hin : ∀ x ∈ (coordsR fi "E1").take P.e2R ++ chals fi "E2" P.e2R ++
      chals fi "E4" P.e4R ++
      [(outsOf fi "E3").headD 0, claimN fi "E2", claim0 fi "E4", claimN fi "E4",
       fi.zhat.getD 3 0, (outsOf fi "Lr3").headD 0, lrEx fi 0, lrEx fi 1], x < r.size) :
    ∃ L, pureRun impl κ inp ((gFinE0 P fi r.size (fun _ => false) false).map (reloc P.S)) r [] =
        some (L, (Val.f (pe4 P.S inp fE (gOE4end P.S))).eqv (rd r (fi.zhat.getD 3 0)) &&
          (inp.π.extract (fieldOffOf P.S fE + (gOE4end P.S + 16))
            (fieldOffOf P.S fE + (gOE4end P.S + 16) + 16)).data.all (· == 0)) ∧
      L.length = 38 ∧
      rd (r ++ L.toArray) (r.size + 4) = .af ((chals fi "E2" P.e2R).map (fv r)).toArray ∧
      rd (r ++ L.toArray) (r.size + 8) = .f (eqPoint (((coordsR fi "E1").take P.e2R).map (fv r)).toArray
        ((chals fi "E2" P.e2R).map (fv r)).toArray *
        (pe4 P.S inp fEEnd 0 * pe4 P.S inp fEEnd 16 + pe4 P.S inp fEEnd 32)) ∧
      rd (r ++ L.toArray) (r.size + 10) = .f (fv r ((outsOf fi "E3").headD 0) * fv r ((outsOf fi "E3").headD 0)) ∧
      rd (r ++ L.toArray) (r.size + 16) = .f (pe4 P.S inp fEEnd 0 +
        fv r ((outsOf fi "E3").headD 0) * pe4 P.S inp fEEnd 16 +
        fv r ((outsOf fi "E3").headD 0) * fv r ((outsOf fi "E3").headD 0) * pe4 P.S inp fEEnd 32 +
        fv r ((outsOf fi "E3").headD 0) * fv r ((outsOf fi "E3").headD 0) * fv r ((outsOf fi "E3").headD 0) *
          fv r (lrEx fi 0)) ∧
      rd (r ++ L.toArray) (r.size + 17) = .af ((chals fi "E4" P.e4R).map (fv r)).toArray ∧
      rd (r ++ L.toArray) (r.size + 35) = .f (fv r ((outsOf fi "E3").headD 0) * fv r ((outsOf fi "E3").headD 0) *
        fv r ((outsOf fi "E3").headD 0) *
        ((impl.evalL (rd r (lrEx fi 1)).toAF ((chals fi "E4" P.e4R).map (fv r)).toArray).1 +
          fv r ((outsOf fi "Lr3").headD 0) *
            (impl.evalL (rd r (lrEx fi 1)).toAF ((chals fi "E4" P.e4R).map (fv r)).toArray).2.1 +
          fv r ((outsOf fi "Lr3").headD 0) * fv r ((outsOf fi "Lr3").headD 0) *
            (impl.evalL (rd r (lrEx fi 1)).toAF ((chals fi "E4" P.e4R).map (fv r)).toArray).2.2) *
        fv r (fi.zhat.getD 3 0)) := by
  simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hin
  have h1 := fun L => map_rd_app r L ((coordsR fi "E1").take P.e2R)
    fun x hx => hin x (.inl (.inl (.inl hx)))
  have h2 := fun L => map_rd_app r L (chals fi "E2" P.e2R) fun x hx => hin x (.inl (.inl (.inr hx)))
  have h3 := fun L => map_rd_app r L (chals fi "E4" P.e4R) fun x hx => hin x (.inl (.inr hx))
  have tf : ∀ x, (Val.f x).toF = x := fun _ => rfl
  have taf : ∀ x, (Val.af x).toAF = x := fun _ => rfl
  have hEE : fEEnd < 19 := by decide
  have hE : fE < 19 := by decide
  simp only [gFinE0, cond_false, List.cons_append, List.nil_append, List.map_append, List.map_cons,
    List.map_nil, reloc_piElem _ hEE, reloc_piElem _ hE, reloc_piField _ hE]
  generalize (outsOf fi "E3").headD 0 = ke at *
  generalize claimN fi "E2" = c2 at *
  generalize claim0 fi "E4" = c40 at *
  generalize claimN fi "E4" = c4 at *
  generalize fi.zhat.getD 3 0 = ze at *
  generalize (outsOf fi "Lr3").headD 0 = kl at *
  generalize lrEx fi 0 = vl at *
  generalize lrEx fi 1 = rl at *
  have hk := hin ke (.inr (.inl rfl))
  have hze := hin ze (.inr (.inr (.inr (.inr (.inr (.inl rfl))))))
  have hkl := hin kl (.inr (.inr (.inr (.inr (.inr (.inr (.inl rfl)))))))
  have hvl := hin vl (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl rfl))))))))
  have hrl := hin rl (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr rfl))))))))
  rw [pureRun_nil_rev]
  cases hc : P.ck <;>
  simp only [hc, Bool.cond_true, Bool.cond_false, pureRun, reloc, evalOp, absOff_zero, tf, taf,
    h1, h2, h3, rd_revAcc, rd_revAcc0, revAcc_app_cons, List.append_nil, List.length_cons,
    List.length_nil, Nat.reduceAdd, Nat.reduceSub, Array.reduceGetElem?, Option.getD_some,
    rd_app_left _ _ hk, rd_app_left _ _ hze, rd_app_left _ _ hkl, rd_app_left _ _ hvl,
    rd_app_left _ _ hrl, allK,
    Option.map_some, Bool.not_true, Bool.not_false, Bool.false_or, Bool.true_or, Bool.true_and,
    Bool.and_true, ↓reduceIte, Bool.false_eq_true, Val.isZero] <;>
  refine ⟨_, rfl, rfl, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp only [rd_revAcc,
    List.length_cons, List.length_nil, Nat.reduceAdd, Nat.reduceSub, Array.reduceGetElem?,
    Option.getD_some, mul_zero, zero_add, add_zero, pe4, Nat.add_zero, fv]

/-- `rsvEOps`' second block (21 ops, registers `c + 60 … c + 75`): `m̂*`, the zero asserts, the
packed child points and their `eq`s, `κ_E⁴`, `w`, `f̂κ_E`, `f̂κ_E²`, the kind indicators and `1`. -/
def rsvBC (P : FinP) (fi : FinIn) (b c : ℕ) : List Op :=
  let kE := (outsOf fi "E3").headD 0
  let fz := fi.zhat.getD 3 0
  [Op.piElem fEEnd 48,
   Op.piField fEEnd 64 48, Op.assertZero (c + 61) allK,
   Op.piField fLrEnd 48 960, Op.assertZero (c + 62) (fun _ => !P.rsv),
   Op.piField fEEnd 48 16, Op.assertZero (c + 63) (fun _ => !P.rsv),
   Op.assertZero (c + 58) allK, Op.assertZero (c + 59) allK,
   Op.packFK (fun _ => ((List.range 23).map (c + ·)).take P.e2R), Op.eqPt (c + 64) (b + 4),
   Op.packFK (fun _ => ((List.range 25).map (c + 23 + ·)).take P.e4R), Op.eqPt (c + 66) (b + 17),
   Op.mulF (b + 10) (b + 10), Op.mulF (c + 68) (c + 67),
   Op.mulF fz kE, Op.mulF fz (b + 10),
   Op.const (fun _ => .f (if P.kix = 0 then 1 else 0)),
   Op.const (fun _ => .f (if P.kix = 1 then 1 else 0)),
   Op.const (fun _ => .f (if P.kix = 2 then 1 else 0)),
   Op.const (fun _ => .f 1)]

/-- `rsvEOps`' last block (21 ops from `d + 36`, `d = c + 76`): the mixed entries, the stacked call and
the three claim asserts (ii″)–(iv″). -/
def rsvTl (P : FinP) (fi : FinIn) (b c : ℕ) : List Op :=
  let eta := (coordsR fi "E1").getD 23 0
  let node : KC Bool := fun κ => P.kv.node κ
  let rx := (List.range 23).map (c + ·)
  let ry := (List.range 25).map (c + 23 + ·)
  let d := c + 76
  [Op.packFK (fun _ => [(chals fi "E2" P.e2R ++ rx.drop P.e2R).getD 22 0]), Op.getF (d + 36) 0,
   Op.mulF (c + 75) (d + 37),
   Op.packFK (fun _ => [(chals fi "E4" P.e4R ++ ry.drop P.e4R).getD 24 0]), Op.getF (d + 39) 0,
   Op.mulF (c + 75) (d + 40),
   Op.packFK (fun _ => (chals fi "E2" P.e2R).take 22 ++ [d + 38] ++ (List.range 9).map (d + 27 + ·)),
   Op.packFK (fun _ => (chals fi "E4" P.e4R).take 24 ++ [d + 41]),
   Op.evalM (d + 42) (d + 43),
   Op.addF (c + 60) (c + 57), Op.mulF eta (d + 47), Op.mulF (c + 65) (d + 48), Op.addF (b + 8) (d + 49),
   Op.assertEq (d + 50) (claimN fi "E2") node,
   Op.mulF (c + 68) (c + 60), Op.addF (b + 16) (d + 51),
   Op.assertEq (d + 52) (claim0 fi "E4") node,
   Op.addF (d + 44) (b + 35),
   Op.assertEq (d + 53) (claimN fi "E4") node]

/-- **`rsvEOps` in blocks** (fixed kind): the 60 reads of `fLrEnd` (`p_x ‖ p_y ‖ s ‖ X₃` are contiguous
from byte 48), `rsvBC`, `rsvSOps`, `rsvTl`. -/
theorem rsvEOps_split (P : FinP) (fi : FinIn) (b c : ℕ) :
    rsvEOps P fi b c = (List.range 60).map (fun j => Op.piElem fLrEnd (48 + 16 * j)) ++ rsvBC P fi b c ++
      rsvSOps (c + 72 + ·) (fun m => [fi.zhat.getD 3 0, c + 70, c + 71].getD m 0) (c + 69) (c + 75)
        (c + 48 + ·) (c + 76) ++ rsvTl P fi b c := by
  rfl

/-- **Block BC's run**, from a base `R` of size `c + 60` holding the 60 reads at `c …` and block A's
registers below `c`. -/
theorem run_rsvBC (R : Array Val) (b c : ℕ) (hR : R.size = c + 60) (hbc : b + 38 ≤ c)
    (r2 r4 : Array F) (k2 kE fz : F)
    (hb4 : rd R (b + 4) = .af r2) (hb10 : rd R (b + 10) = .f k2) (hb17 : rd R (b + 17) = .af r4)
    (hfz : fi.zhat.getD 3 0 < c ∧ (rd R (fi.zhat.getD 3 0)).toF = fz)
    (hkE : (outsOf fi "E3").headD 0 < c ∧ (rd R ((outsOf fi "E3").headD 0)).toF = kE)
    (hV : ∀ j < 60, rd R (c + j) = .f (pe4 P.S inp fLrEnd (48 + 16 * j))) :
    ∃ L, pureRun impl κ inp ((rsvBC P fi b c).map (reloc P.S)) R [] =
        some (L, (inp.π.extract (fieldOffOf P.S fEEnd + 64) (fieldOffOf P.S fEEnd + 64 + 48)).data.all (· == 0) &&
          ((P.rsv || (inp.π.extract (fieldOffOf P.S fLrEnd + 48) (fieldOffOf P.S fLrEnd + 48 + 960)).data.all
              (· == 0)) &&
          ((P.rsv || (inp.π.extract (fieldOffOf P.S fEEnd + 48) (fieldOffOf P.S fEEnd + 48 + 16)).data.all
              (· == 0)) &&
          (decide (pe4 P.S inp fLrEnd (rsvX + 16) = 0) && decide (pe4 P.S inp fLrEnd (rsvX + 32) = 0))))) ∧
      L.length = 16 ∧
      rd (R ++ L.toArray) (c + 60) = .f (pe4 P.S inp fEEnd 48) ∧
      rd (R ++ L.toArray) (c + 65) = .f (eqPoint ((rsvPx4 inp P).take P.e2R).toArray r2) ∧
      rd (R ++ L.toArray) (c + 68) = .f (k2 * k2) ∧
      rd (R ++ L.toArray) (c + 69) = .f (k2 * k2 * eqPoint ((rsvPy4 inp P).take P.e4R).toArray r4) ∧
      rd (R ++ L.toArray) (c + 70) = .f (fz * kE) ∧
      rd (R ++ L.toArray) (c + 71) = .f (fz * k2) ∧
      rd (R ++ L.toArray) (c + 72) = .f (if P.kix = 0 then 1 else 0) ∧
      rd (R ++ L.toArray) (c + 73) = .f (if P.kix = 1 then 1 else 0) ∧
      rd (R ++ L.toArray) (c + 74) = .f (if P.kix = 2 then 1 else 0) ∧
      rd (R ++ L.toArray) (c + 75) = .f 1 := by
  have hl : ∀ x, x < c + 60 → ∀ L : List Val, rd (R ++ L.toArray) x = rd R x :=
    fun x hx L => rd_app_left _ _ (by omega)
  have hpx : ∀ L : List Val, (((List.range 23).map (c + ·)).take P.e2R).map
      (fun x => (rd (R ++ L.toArray) x).toF) = (rsvPx4 inp P).take P.e2R := fun L => by
    rw [List.map_take, List.map_map]; refine congrArg (List.take P.e2R) ?_; unfold rsvPx4
    refine List.map_congr_left fun j hj => ?_
    rw [List.mem_range] at hj
    simp only [Function.comp_apply]; rw [hl (c + j) (by omega), hV j (by omega)]; rfl
  have hpy : ∀ L : List Val, (((List.range 25).map (c + 23 + ·)).take P.e4R).map
      (fun x => (rd (R ++ L.toArray) x).toF) = (rsvPy4 inp P).take P.e4R := fun L => by
    rw [List.map_take, List.map_map]; refine congrArg (List.take P.e4R) ?_; unfold rsvPy4
    refine List.map_congr_left fun j hj => ?_
    rw [List.mem_range] at hj
    simp only [Function.comp_apply]
    rw [show c + 23 + j = c + (23 + j) by omega, hl (c + (23 + j)) (by omega), hV (23 + j) (by omega)]
    show F.ofBytes (bytesAt inp.π (fieldOffOf P.S fLrEnd + (48 + 16 * (23 + j))) 16) =
      F.ofBytes (bytesAt inp.π (fieldOffOf P.S fLrEnd + (rsvRy + 16 * j)) 16)
    rw [show 48 + 16 * (23 + j) = rsvRy + 16 * j by simp only [rsvRy]; omega]
  have h4 := hl (b + 4) (by omega); have h10 := hl (b + 10) (by omega)
  have h17 := hl (b + 17) (by omega)
  have hz := hl _ (Nat.lt_of_lt_of_le hfz.1 (by omega))
  have hk := hl _ (Nat.lt_of_lt_of_le hkE.1 (by omega))
  have h58 := hl (c + 58) (by omega); have h59 := hl (c + 59) (by omega)
  have v58 := hV 58 (by norm_num); have v59 := hV 59 (by norm_num)
  have hEE : fEEnd < 19 := by decide
  have hL : fLrEnd < 19 := by decide
  have tf : ∀ x, (Val.f x).toF = x := fun _ => rfl
  have taf : ∀ x, (Val.af x).toAF = x := fun _ => rfl
  simp only [rsvBC, List.map_cons, List.map_nil, reloc_piElem _ hEE, reloc_piField _ hEE,
    reloc_piField _ hL]
  rw [pureRun_nil_rev]
  simp only [pureRun, reloc, evalOp, absOff_zero, tf, taf, rd_revAccAt R _ hR, hpx, hpy,
    revAcc_app_cons, List.append_nil, List.length_cons, List.length_nil, Nat.reduceAdd,
    Nat.reduceSub, Nat.reduceMul, Nat.add_sub_add_left, Nat.add_le_add_iff_left, Nat.reduceLeDiff,
    Array.reduceGetElem?, Option.getD_some, h4, h10, h17, hz, hk, h58, h59, v58, v59, hb4, hb10, hb17,
    hfz.2, hkE.2, allK, Option.map_some, Bool.not_true, Bool.not_false, Bool.not_not, Bool.false_or,
    Bool.true_or, Bool.true_and, Bool.and_true, Val.isZero]
  refine ⟨_, rfl, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
  simp only [rd_revAccAt R _ hR, List.length_cons, List.length_nil, Nat.reduceAdd, Nat.reduceSub,
    Nat.add_sub_add_left, Nat.add_le_add_iff_left, Nat.reduceLeDiff, Array.reduceGetElem?,
    Option.getD_some, Nat.le_refl, Nat.sub_self, le_add_iff_nonneg_right, zero_le] <;> rfl

/-- **Block E's run** (`rsvTl`), from a base `R` of size `c + 76 + 36` holding blocks A–D. -/
theorem run_rsvTl (R : Array Val) (b c : ℕ) (hR : R.size = c + 76 + 36) (hbc : b + 38 ≤ c)
    (r2l r4l sPl : List F) (x22 y24 X0 mh eta e65 v8 k4 v16 v35 : F)
    (hE2 : ∀ L : List Val, (chals fi "E2" P.e2R).map (fun x => (rd (R ++ L.toArray) x).toF) = r2l)
    (hE4 : ∀ L : List Val, (chals fi "E4" P.e4R).map (fun x => (rd (R ++ L.toArray) x).toF) = r4l)
    (hsP : ∀ L : List Val, ((List.range 9).map (c + 76 + 27 + ·)).map
      (fun x => (rd (R ++ L.toArray) x).toF) = sPl)
    (hx22 : (chals fi "E2" P.e2R ++ ((List.range 23).map (c + ·)).drop P.e2R).getD 22 0 < R.size ∧
      (rd R ((chals fi "E2" P.e2R ++ ((List.range 23).map (c + ·)).drop P.e2R).getD 22 0)).toF = x22)
    (hy24 : (chals fi "E4" P.e4R ++ ((List.range 25).map (c + 23 + ·)).drop P.e4R).getD 24 0 < R.size ∧
      (rd R ((chals fi "E4" P.e4R ++ ((List.range 25).map (c + 23 + ·)).drop P.e4R).getD 24 0)).toF = y24)
    (heta : (coordsR fi "E1").getD 23 0 < R.size ∧ (rd R ((coordsR fi "E1").getD 23 0)).toF = eta)
    (h75 : rd R (c + 75) = .f 1) (h57 : rd R (c + 57) = .f X0) (h60 : rd R (c + 60) = .f mh)
    (h65 : rd R (c + 65) = .f e65) (h68 : rd R (c + 68) = .f k4) (h8 : rd R (b + 8) = .f v8)
    (h16 : rd R (b + 16) = .f v16) (h35 : rd R (b + 35) = .f v35)
    (hcl : claimN fi "E2" < R.size ∧ claim0 fi "E4" < R.size ∧ claimN fi "E4" < R.size) :
    ∃ L, pureRun impl κ inp ((rsvTl P fi b c).map (reloc P.S)) R [] =
        some (L, (!P.kv.node κ || (Val.f (v8 + e65 * (eta * (mh + X0)))).eqv (rd R (claimN fi "E2"))) &&
          ((!P.kv.node κ || (Val.f (v16 + k4 * mh)).eqv (rd R (claim0 fi "E4"))) &&
          (!P.kv.node κ || (Val.f ((impl.evalM (r2l.take 22 ++ [x22] ++ sPl).toArray
            (r4l.take 24 ++ [y24]).toArray).1 + v35)).eqv (rd R (claimN fi "E4"))))) := by
  have hl : ∀ x, x < c + 76 + 36 → ∀ L : List Val, rd (R ++ L.toArray) x = rd R x :=
    fun x hx L => rd_app_left _ _ (by omega)
  have tf : ∀ x, (Val.f x).toF = x := fun _ => rfl
  have taf : ∀ x, (Val.af x).toAF = x := fun _ => rfl
  have hgd : ∀ a : F, ([a].toArray).getD 0 0 = a := fun _ => rfl
  have g75 := hl (c + 75) (by omega); have g57 := hl (c + 57) (by omega)
  have g60 := hl (c + 60) (by omega); have g65 := hl (c + 65) (by omega)
  have g68 := hl (c + 68) (by omega); have g8 := hl (b + 8) (by omega)
  have g16 := hl (b + 16) (by omega); have g35 := hl (b + 35) (by omega)
  have gx := fun L => rd_app_left R L hx22.1
  have gy := fun L => rd_app_left R L hy24.1
  have ge := fun L => rd_app_left R L heta.1
  have gc1 := fun L => rd_app_left R L hcl.1
  have gc2 := fun L => rd_app_left R L hcl.2.1
  have gc3 := fun L => rd_app_left R L hcl.2.2
  simp only [rsvTl, List.map_cons, List.map_nil]
  rw [pureRun_nil_rev]
  simp only [pureRun, reloc, evalOp, tf, taf, rd_revAccAt R _ hR, List.map_append, List.map_take, hE2, hE4,
    hsP, revAcc_app_cons, List.append_nil, List.length_cons, List.length_nil, Nat.reduceAdd,
    Nat.reduceSub, Nat.add_sub_add_left, Nat.add_le_add_iff_left, Nat.reduceLeDiff,
    Array.reduceGetElem?, Option.getD_some, g75, g57, g60, g65, g68, g8, g16, g35, gx, gy, ge, gc1, gc2,
    gc3, h75, h57, h60, h65, h68, h8, h16, h35, hx22.2, hy24.2, heta.2, hgd, Option.map_some,
    Bool.true_and, Bool.and_true, List.map_cons, List.map_nil, one_mul]
  exact ⟨_, rfl⟩

theorem rsvSOps_reloc (S : Seq) (ind t : ℕ → Reg) (w one : Reg) (s : ℕ → Reg) (d : ℕ) :
    (rsvSOps ind t w one s d).map (reloc S) = rsvSOps ind t w one s d := by
  simp only [rsvSOps, List.map_append, List.map_map]; rfl

theorem getD_lt' {N : ℕ} (hN : 0 < N) {l : List ℕ} (h : ∀ x ∈ l, x < N) (n : ℕ) : l.getD n 0 < N := by
  rw [List.getD_eq_getElem?_getD]
  rcases hl : l[n]? with _ | z
  · exact hN
  · exact h z (List.mem_of_getElem? hl)

/-- **`finE`'s flag with the reserve** (`rsvOps`): blocks A (`run_gFinE0off`), the 60 reads,
`rsvBC`, `rsvSOps`, `rsvTl`, joined by `pureRun_seq`. -/
theorem flag_gFinE1 (hr : P.rsvOps = true) (hin : ∀ x ∈ (coordsR fi "E1").take P.e2R ++ chals fi "E2" P.e2R ++
      chals fi "E4" P.e4R ++
      [(outsOf fi "E3").headD 0, claimN fi "E2", claim0 fi "E4", claimN fi "E4",
       fi.zhat.getD 3 0, (outsOf fi "Lr3").headD 0, lrEx fi 0, lrEx fi 1, (coordsR fi "E1").getD 23 0, 0],
      x < r.size) :
    ∃ L, pureRun impl κ inp ((gFinE P fi r.size).1.map (reloc P.S)) r [] =
        some (L, relE4 impl κ inp fi r P) ∧
      (rd (r ++ L.toArray) ((gFinE P fi r.size).2.getD 0 0)).toAF =
        ((chals fi "E4" P.e4R).map (fv r)).toArray ∧
      ∀ i < rsvN, P.rsvOps = true → rd (r ++ L.toArray) (((gFinE P fi r.size).2.drop 1).getD i 0) =
        .f (pe4 P.S inp fLrEnd (48 + 16 * i)) := by
  simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hin
  obtain ⟨LA, hA, hlA, a4, a8, a10, a16, a17, a35⟩ := run_gFinE0off impl κ inp fi r P fun x hx => hin x (by
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with ((h | h) | h) | h | h | h | h | h | h | h | h
    exacts [.inl (.inl (.inl h)), .inl (.inl (.inr h)), .inl (.inr h), .inr (.inl h),
      .inr (.inr (.inl h)), .inr (.inr (.inr (.inl h))), .inr (.inr (.inr (.inr (.inl h)))),
      .inr (.inr (.inr (.inr (.inr (.inl h))))), .inr (.inr (.inr (.inr (.inr (.inr (.inl h)))))),
      .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl h))))))),
      .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl h))))))))])
  have hpos : 0 < r.size := hin 0 (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr rfl))))))))))
  have hkE := hin _ (.inr (.inl rfl))
  have hfz := hin _ (.inr (.inr (.inr (.inr (.inr (.inl rfl))))))
  have heta := hin _ (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl rfl))))))))))
  have hc2 := hin _ (.inr (.inr (.inl rfl)))
  have hc40 := hin _ (.inr (.inr (.inr (.inl rfl))))
  have hc4 := hin _ (.inr (.inr (.inr (.inr (.inl rfl)))))
  have hE2r : ∀ x ∈ chals fi "E2" P.e2R, x < r.size := fun x hx => hin x (.inl (.inl (.inr hx)))
  have hE4r : ∀ x ∈ chals fi "E4" P.e4R, x < r.size := fun x hx => hin x (.inl (.inr hx))
  -- the bases
  have hEE : fLrEnd < 19 := by decide
  have e1 : ExtA r (r ++ LA.toArray) := ExtA.app r LA
  have s1 : (r ++ LA.toArray).size = r.size + 38 := by simp [hlA]
  -- B1: the 60 reads
  have hB1 : pureRun impl κ inp (((List.range 60).map fun j => Op.piElem fLrEnd (48 + 16 * j)).map
      (reloc P.S)) (r ++ LA.toArray) [] =
      some ((List.range 60).map fun j => Val.f (pe4 P.S inp fLrEnd (48 + 16 * j)), true) := by
    rw [List.map_map]
    have := pureRun_mapRange impl κ inp (r ++ LA.toArray) (reloc P.S ∘ fun j => Op.piElem fLrEnd (48 + 16 * j))
      (fun j => Val.f (pe4 P.S inp fLrEnd (48 + 16 * j))) [] 60 (fun i _ L => by
        simp only [Function.comp_apply, reloc_piElem _ hEE, evalOp, absOff_zero]; rfl)
    simpa using this
  generalize hV60 : ((List.range 60).map fun j => Val.f (pe4 P.S inp fLrEnd (48 + 16 * j))) = V60 at hB1
  have hlV : V60.length = 60 := by rw [← hV60]; simp
  have e2 : ExtA (r ++ LA.toArray) (r ++ LA.toArray ++ V60.toArray) := ExtA.app _ V60
  have s2 : (r ++ LA.toArray ++ V60.toArray).size = r.size + 38 + 60 := by simp [hlA, hlV]
  have e02 := e1.trans e2
  have hV : ∀ j < 60, rd (r ++ LA.toArray ++ V60.toArray) (r.size + 38 + j) =
      .f (pe4 P.S inp fLrEnd (48 + 16 * j)) := fun j hj => by
    rw [← s1, rd_app, ← hV60, getD_mapRange _ _ hj]
  -- BC
  obtain ⟨LBC, hBC, hlBC, f60, f65, f68, f69, f70, f71, f72, f73, f74, f75⟩ :=
    run_rsvBC impl κ inp fi P (r ++ LA.toArray ++ V60.toArray) r.size (r.size + 38) s2 le_rfl
      ((chals fi "E2" P.e2R).map (fv r)).toArray ((chals fi "E4" P.e4R).map (fv r)).toArray
      (fv r ((outsOf fi "E3").headD 0) * fv r ((outsOf fi "E3").headD 0)) (fv r ((outsOf fi "E3").headD 0))
      (fv r (fi.zhat.getD 3 0))
      (by rw [e2.rd (by omega), a4]) (by rw [e2.rd (by omega), a10]) (by rw [e2.rd (by omega), a17])
      ⟨Nat.lt_of_lt_of_le hfz (by omega), by rw [e02.rd (Nat.lt_of_lt_of_le hfz (by omega))]⟩
      ⟨Nat.lt_of_lt_of_le hkE (by omega), by rw [e02.rd (Nat.lt_of_lt_of_le hkE (by omega))]⟩ hV
  generalize hR3 : r ++ LA.toArray ++ V60.toArray ++ LBC.toArray = R3 at *
  have e3 : ExtA (r ++ LA.toArray ++ V60.toArray) R3 := hR3 ▸ ExtA.app _ LBC
  have s3 : R3.size = r.size + 38 + 76 := by rw [← hR3]; simp [hlA, hlV, hlBC]
  have e03 := e02.trans e3
  -- D
  have hD := run_rsvSOps impl κ inp R3 (r.size + 38 + 76) s3 (r.size + 38 + 72 + ·)
    (fun m => [fi.zhat.getD 3 0, r.size + 38 + 70, r.size + 38 + 71].getD m 0) (r.size + 38 + 69) (r.size + 38 + 75)
    (r.size + 38 + 48 + ·) (fun k => if P.kix = k then 1 else 0)
    (fun m => [fv r (fi.zhat.getD 3 0), fv r (fi.zhat.getD 3 0) * fv r ((outsOf fi "E3").headD 0),
      fv r (fi.zhat.getD 3 0) * (fv r ((outsOf fi "E3").headD 0) * fv r ((outsOf fi "E3").headD 0))].getD m 0)
    (fun i => pe4 P.S inp fLrEnd (48 + 16 * (48 + i)))
    (fv r ((outsOf fi "E3").headD 0) * fv r ((outsOf fi "E3").headD 0) *
      (fv r ((outsOf fi "E3").headD 0) * fv r ((outsOf fi "E3").headD 0)) *
      eqPoint ((rsvPy4 inp P).take P.e4R).toArray ((chals fi "E4" P.e4R).map (fv r)).toArray) 1
    (fun k hk => by
      refine ⟨show (r.size + 38 + 72 + k : ℕ) < r.size + 38 + 76 by omega, ?_⟩
      interval_cases k
      · rw [f72]; rfl
      · rw [show r.size + 38 + 72 + 1 = r.size + 38 + 73 by omega, f73]; rfl
      · rw [show r.size + 38 + 72 + 2 = r.size + 38 + 74 by omega, f74]; rfl)
    (fun m hm => by
      interval_cases m
      · exact ⟨Nat.lt_of_lt_of_le hfz (by omega), by
          simp only [List.getD_cons_zero]; rw [e03.rd (Nat.lt_of_lt_of_le hfz (by omega))]⟩
      · exact ⟨show r.size + 38 + 70 < r.size + 38 + 76 by omega, by
          simp only [List.getD_cons_succ, List.getD_cons_zero]; rw [f70]; rfl⟩
      · exact ⟨show r.size + 38 + 71 < r.size + 38 + 76 by omega, by
          simp only [List.getD_cons_succ, List.getD_cons_zero]; rw [f71]; rfl⟩)
    ⟨show (r.size + 38 + 69 : ℕ) < r.size + 38 + 76 by omega, by rw [f69]; rfl⟩
    ⟨show (r.size + 38 + 75 : ℕ) < r.size + 38 + 76 by omega, by rw [f75]; rfl⟩
    (fun i hi => ⟨show (r.size + 38 + 48 + i : ℕ) < r.size + 38 + 76 by omega, by
      rw [e3.rd (by omega), show r.size + 38 + 48 + i = r.size + 38 + (48 + i) by omega, hV _ (by omega)]; rfl⟩)
  generalize hLD : (List.range 9).map _ ++ (List.range 9).map _ ++ (List.range 9).map _ ++
    (List.range 9).map _ = LD at hD
  generalize hR4 : R3 ++ LD.toArray = R4
  have e4 : ExtA R3 R4 := hR4 ▸ ExtA.app _ LD
  have s4 : R4.size = r.size + 38 + 76 + 36 := by
    rw [← hR4, Array.size_append, s3, List.size_toArray, ← hLD]; simp
  have e04 := e03.trans e4
  have e24 := e3.trans e4
  -- reads of the 60 values from any extension of the read block
  have hVx : ∀ R', ExtA (r ++ LA.toArray ++ V60.toArray) R' → ∀ j < 60,
      (rd R' (r.size + 38 + j)).toF = pe4 P.S inp fLrEnd (48 + 16 * j) := fun R' e j hj => by
    rw [e.rd (by rw [s2]; omega), hV j hj]; rfl
  have hfr : ∀ R', ExtA r R' → ∀ l : List Reg, (∀ x ∈ l, x < r.size) →
      l.map (fun x => (rd R' x).toF) = l.map (fv r) := fun R' e l hl =>
    List.map_congr_left fun x hx => by rw [e.rd (hl x hx)]
  let kE := fv r ((outsOf fi "E3").headD 0)
  let fz := fv r (fi.zhat.getD 3 0)
  have hsP : ∀ L : List Val, ((List.range 9).map (r.size + 38 + 76 + 27 + ·)).map
      (fun x => (rd (R4 ++ L.toArray) x).toF) =
      (List.range 9).map fun i => (if P.kix = i / 3 then 1 else 0) *
        [fz, fz * kE, fz * (kE * kE)].getD (i % 3) 0 +
        kE * kE * (kE * kE) * eqPoint ((rsvPy4 inp P).take P.e4R).toArray
          ((chals fi "E4" P.e4R).map (fv r)).toArray * (rsvS4 inp P).getD i 0 := fun L => by
    rw [List.map_map]
    refine List.map_congr_left fun i hi => ?_
    rw [List.mem_range] at hi
    simp only [Function.comp_apply]
    rw [rd_app_left _ _ (show r.size + 38 + 76 + 27 + i < R4.size by omega), ← hR4,
      rd_appAt R3 LD s3 (show r.size + 38 + 76 ≤ r.size + 38 + 76 + 27 + i by omega),
      show r.size + 38 + 76 + 27 + i - (r.size + 38 + 76) = 27 + i by omega, ← hLD,
      List.getD_append_right _ _ _ _ (by simp), List.length_append, List.length_append,
      length_mapRange, length_mapRange, length_mapRange, show 27 + i - (9 + 9 + 9) = i by omega,
      getD_mapRange _ _ hi, rsvS4, getD_mapRange _ _ hi]
    simp only [one_mul, Val.toF]
    rw [show 48 + 16 * (48 + i) = rsvS + 16 * i by simp only [rsvS]; omega]
  have hrx : ∀ R', ExtA (r ++ LA.toArray ++ V60.toArray) R' →
      ((List.range 23).map (r.size + 38 + ·)).map (fun x => (rd R' x).toF) = rsvPx4 inp P := fun R' e => by
    rw [List.map_map]; unfold rsvPx4
    refine List.map_congr_left fun j hj => ?_
    rw [List.mem_range] at hj
    simp only [Function.comp_apply]; rw [hVx R' e j (by omega)]; rfl
  have hry : ∀ R', ExtA (r ++ LA.toArray ++ V60.toArray) R' →
      ((List.range 25).map (r.size + 38 + 23 + ·)).map (fun x => (rd R' x).toF) = rsvPy4 inp P := fun R' e => by
    rw [List.map_map]; unfold rsvPy4
    refine List.map_congr_left fun j hj => ?_
    rw [List.mem_range] at hj
    simp only [Function.comp_apply]
    rw [show r.size + 38 + 23 + j = r.size + 38 + (23 + j) by omega, hVx R' e (23 + j) (by omega),
      show 48 + 16 * (23 + j) = rsvRy + 16 * j by simp only [rsvRy]; omega]
  have hlt4 : ∀ x, x < r.size → x < R4.size := fun x hx => Nat.lt_of_lt_of_le hx e04.1
  have h0 : (rd R4 0).toF = fv r 0 := by rw [e04.rd hpos]
  have e14 : ExtA (r ++ LA.toArray) R4 := e2.trans e24
  obtain ⟨LE, hE⟩ := run_rsvTl impl κ inp fi P R4 r.size (r.size + 38) s4 le_rfl
    ((chals fi "E2" P.e2R).map (fv r)) ((chals fi "E4" P.e4R).map (fv r)) _
    (((chals fi "E2" P.e2R).map (fv r) ++ (rsvPx4 inp P).drop P.e2R).getD 22 (fv r 0))
    (((chals fi "E4" P.e4R).map (fv r) ++ (rsvPy4 inp P).drop P.e4R).getD 24 (fv r 0))
    (pe4 P.S inp fLrEnd rsvX) (pe4 P.S inp fEEnd 48) (fv r ((coordsR fi "E1").getD 23 0))
    (eqPoint ((rsvPx4 inp P).take P.e2R).toArray ((chals fi "E2" P.e2R).map (fv r)).toArray)
    (eqPoint (((coordsR fi "E1").take P.e2R).map (fv r)).toArray ((chals fi "E2" P.e2R).map (fv r)).toArray *
      (pe4 P.S inp fEEnd 0 * pe4 P.S inp fEEnd 16 + pe4 P.S inp fEEnd 32))
    (kE * kE * (kE * kE))
    (pe4 P.S inp fEEnd 0 + kE * pe4 P.S inp fEEnd 16 + kE * kE * pe4 P.S inp fEEnd 32 +
      kE * kE * kE * fv r (lrEx fi 0))
    (kE * kE * kE *
        ((impl.evalL (rd r (lrEx fi 1)).toAF ((chals fi "E4" P.e4R).map (fv r)).toArray).1 +
          fv r ((outsOf fi "Lr3").headD 0) *
            (impl.evalL (rd r (lrEx fi 1)).toAF ((chals fi "E4" P.e4R).map (fv r)).toArray).2.1 +
          fv r ((outsOf fi "Lr3").headD 0) * fv r ((outsOf fi "Lr3").headD 0) *
            (impl.evalL (rd r (lrEx fi 1)).toAF ((chals fi "E4" P.e4R).map (fv r)).toArray).2.2) * fz)
    (fun L => hfr _ (e04.trans (ExtA.app _ L)) _ hE2r) (fun L => hfr _ (e04.trans (ExtA.app _ L)) _ hE4r)
    hsP
    ⟨getD_lt' (Nat.lt_of_lt_of_le hpos e04.1) (fun x hx => by
        rcases List.mem_append.1 hx with hx | hx
        · exact hlt4 x (hE2r x hx)
        · obtain ⟨j, hj, rfl⟩ := List.mem_map.1 (List.mem_of_mem_drop hx)
          rw [List.mem_range] at hj; rw [s4]; omega) 22,
      by rw [rd_getD_toF, List.map_append, hfr _ e04 _ hE2r, List.map_drop, hrx _ e24, h0]⟩
    ⟨getD_lt' (Nat.lt_of_lt_of_le hpos e04.1) (fun x hx => by
        rcases List.mem_append.1 hx with hx | hx
        · exact hlt4 x (hE4r x hx)
        · obtain ⟨j, hj, rfl⟩ := List.mem_map.1 (List.mem_of_mem_drop hx)
          rw [List.mem_range] at hj; rw [s4]; omega) 24,
      by rw [rd_getD_toF, List.map_append, hfr _ e04 _ hE4r, List.map_drop, hry _ e24, h0]⟩
    ⟨hlt4 _ heta, by rw [e04.rd heta]⟩
    (by rw [e4.rd (by rw [s3]; omega), f75])
    (by rw [e24.rd (by rw [s2]; omega), hV 57 (by norm_num)]; rfl)
    (by rw [e4.rd (by rw [s3]; omega), f60]) (by rw [e4.rd (by rw [s3]; omega), f65])
    (by rw [e4.rd (by rw [s3]; omega), f68])
    (by rw [e14.rd (by rw [s1]; omega), a8]) (by rw [e14.rd (by rw [s1]; omega), a16])
    (by rw [e14.rd (by rw [s1]; omega), a35])
    ⟨hlt4 _ hc2, hlt4 _ hc40, hlt4 _ hc4⟩
  subst hR4 hR3
  refine ⟨LA ++ (V60 ++ (LBC ++ (LD ++ LE))), ?_, ?_, ?_⟩
  · simp only [gFinE, hr, Bool.cond_true, List.map_append, rsvEOps_split, rsvSOps_reloc, List.append_assoc]
    rw [pureRun_seq impl κ inp hA (pureRun_seq impl κ inp hB1 (pureRun_seq impl κ inp hBC
      (pureRun_seq impl κ inp hD hE)))]
    rw [e04.rd hc2, e04.rd hc40, e04.rd hc4]
    simp only [relE4, hr, ↓reduceIte, Bool.true_and, Bool.and_assoc]
    rfl
  · simp only [gFinE, hr, Bool.cond_true, List.getD_cons_zero]
    rw [← app_app, rd_app_left _ _ (by rw [s1]; omega), a17]; rfl
  · intro i hi _
    simp only [gFinE, hr, Bool.cond_true, List.drop_succ_cons, List.drop_zero]
    have hi' : i < 60 := hi
    rw [getD_mapRange _ _ hi, ← app_app, ← app_app, rd_app_left _ _ (by rw [s2]; omega), hV i hi']
/-- **`finE`'s flag** (revision 4.4.2): without the reserve it is `relE4o` (`flag_gFinE0`). With the
reserve (`rsvOps`) the op list is `gFinE0 … (fun _ => false) false ++ rsvEOps …` (RSV2 §2.2) and the
flag is `relE4`'s first branch (`flag_gFinE1`, block by block). -/
theorem flag_gFinE (hin : ∀ x ∈ (coordsR fi "E1").take P.e2R ++ chals fi "E2" P.e2R ++
      chals fi "E4" P.e4R ++
      [(outsOf fi "E3").headD 0, claimN fi "E2", claim0 fi "E4", claimN fi "E4",
       fi.zhat.getD 3 0, (outsOf fi "Lr3").headD 0, lrEx fi 0, lrEx fi 1, (coordsR fi "E1").getD 23 0, 0],
      x < r.size) :
    ∃ L, pureRun impl κ inp ((gFinE P fi r.size).1.map (reloc P.S)) r [] =
        some (L, relE4 impl κ inp fi r P) ∧
      (rd (r ++ L.toArray) ((gFinE P fi r.size).2.getD 0 0)).toAF =
        ((chals fi "E4" P.e4R).map (fv r)).toArray ∧
      ∀ i < rsvN, P.rsvOps = true → rd (r ++ L.toArray) (((gFinE P fi r.size).2.drop 1).getD i 0) =
        .f (pe4 P.S inp fLrEnd (48 + 16 * i)) := by
  rcases Bool.eq_false_or_eq_true P.rsvOps with hr | hr
  rotate_left
  · have h := flag_gFinE0 impl κ inp fi r P fun x hx => hin x (by
      simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hx ⊢
      rcases hx with ((h | h) | h) | h | h | h | h | h | h | h | h
      exacts [.inl (.inl (.inl h)), .inl (.inl (.inr h)), .inl (.inr h), .inr (.inl h),
        .inr (.inr (.inl h)), .inr (.inr (.inr (.inl h))), .inr (.inr (.inr (.inr (.inl h)))),
        .inr (.inr (.inr (.inr (.inr (.inl h))))), .inr (.inr (.inr (.inr (.inr (.inr (.inl h)))))),
        .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl h))))))),
        .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl h))))))))])
    simp only [gFinE, relE4, hr, cond_false, Bool.false_eq_true, ↓reduceIte, List.getD_cons_zero]
    obtain ⟨L, h1, h2⟩ := h
    exact ⟨L, h1, h2, fun _ _ h => h.elim⟩
  · exact flag_gFinE1 impl κ inp fi r P hr hin

/-! ## `finB′` -/

/-- `pubH` at `P`: the statement's digests read at `S`'s `stmt` offset. -/
def pubH4 (kp : F) : F :=
  let vl := dLo inp.vk; let vh := dHi inp.vk
  let c₁ := bytesAt inp.π (fieldOffOf P.S fStmt + 1) 32
  let c₂ := bytesAt inp.π (fieldOffOf P.S fStmt + 33) 32
  1 + kp * (vl + kp * (vh + kp * (dLo c₁ + kp * (dHi c₁ + kp * (vl + kp * (vh + kp * (dLo c₂ +
    kp * dHi c₂)))))))

/-- `v*` at `P` without the reserve: `v_RS + [node] κ′²·pubH(κ′)` (`finB′`'s export). -/
def vStar4o : F :=
  let kp := fv r ((outsOf fi "B'").headD 0)
  fv r (fi.zhat.getD nRS 0) + (if P.kv.node κ then kp * kp * pubH4 inp P kp else 0)

/-- **`v*` at `P`** (revision 4.4.2, RSV2 §2.2): with the reserve on the kind (`rsvOps ∧ rsv`), the
child claim's 60 values `v_i` (`finE`'s exports after `r′`) at `κ′^{11} … κ′^{70}`:
`v*₀ + κ′^{11}·Σ_{i<60} κ′^i v_i`. -/
def vStar4 : F :=
  let kp := fv r ((outsOf fi "B'").headD 0)
  if P.rsvOps && P.rsv then
    vStar4o κ inp fi r P + kp ^ 11 * ∑ i ∈ Finset.range rsvN,
      kp ^ i * fv r (((fi.ex.getD exE []).drop 1).getD i 0)
  else vStar4o κ inp fi r P

/-- **`relB` at `P`**: `v*` (in `K`) is P1.0's initial claim. -/
def relB4 : Bool := (Val.k (K.smulF (vStar4 κ inp fi r P) 1)).eqv (rd r (claim0 fi "P1"))

theorem flag_gFinB'o (hr : P.rsvOps = false) (hin : ∀ x ∈ [(outsOf fi "B'").headD 0, fi.zhat.getD nRS 0, claim0 fi "P1"],
      x < r.size) :
    ∃ L, pureRun impl κ inp ((gFinB' P fi r.size).1.map (reloc P.S)) r [] =
        some (L, relB4 κ inp fi r P) ∧
      (rd (r ++ L.toArray) ((gFinB' P fi r.size).2.getD 0 0)).toF = vStar4o κ inp fi r P := by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hin
  have tf : ∀ x, (Val.f x).toF = x := fun _ => rfl
  have td : ∀ x, (Val.d x).toD = x := fun _ => rfl
  have tk : ∀ x, (Val.k x).toK = x := fun _ => rfl
  have hS : fStmt < 19 := by decide
  simp only [gFinB', relB4, vStar4, vStar4o, pubH4, dLo, dHi, List.map_cons, List.map_nil,
    reloc_piDigest _ hS, hr, cond_false, Bool.false_and, Bool.false_eq_true, ↓reduceIte, List.append_nil]
  generalize (outsOf fi "B'").headD 0 = kp at *
  generalize fi.zhat.getD nRS 0 = vR at *
  generalize claim0 fi "P1" = c0 at *
  have hk := hin kp (.inl rfl); have hR := hin vR (.inr (.inl rfl))
  have hc := hin c0 (.inr (.inr rfl))
  rw [pureRun_nil_rev]
  cases hn : P.kv.node κ <;>
  simp only [hn, pureRun, reloc, evalOp, absOff_zero, tf, td, tk, rd_revAcc, rd_revAcc0,
    revAcc_app_cons, List.append_nil, List.length_cons, List.length_nil, Nat.reduceAdd,
    Nat.reduceSub, Array.reduceGetElem?, Option.getD_some, rd_app_left _ _ hk, rd_app_left _ _ hR,
    rd_app_left _ _ hc, Option.map_some, allK, Bool.not_true, Bool.false_or,
    Bool.true_and, Bool.and_true, ↓reduceIte, Bool.false_eq_true, digestAt_eq] <;>
  refine ⟨_, rfl, ?_⟩ <;> simp only [List.getD_cons_zero, rd_revAcc,
    List.length_cons, List.length_nil, Nat.reduceAdd, Nat.reduceSub, Array.reduceGetElem?,
    Option.getD_some, tf]

/-- `finB′`'s own ops (33 outputs from `b`), its assert gated by `g`. -/
def gB0 (P : FinP) (fi : FinIn) (b : ℕ) (g : KC Bool) : List Op :=
  let kp := (outsOf fi "B'").headD 0
  let vRS := fi.zhat.getD nRS 0
  [.input 0, .splitDigest b, .piDigest fStmt 1, .splitDigest (b + 3), .piDigest fStmt 33,
    .splitDigest (b + 6), .const (fun _ => .f 1),
    .mulF kp (b + 8), .addF (b + 7) (b + 10), .mulF kp (b + 11), .addF (b + 2) (b + 12),
    .mulF kp (b + 13), .addF (b + 1) (b + 14), .mulF kp (b + 15), .addF (b + 5) (b + 16),
    .mulF kp (b + 17), .addF (b + 4) (b + 18), .mulF kp (b + 19), .addF (b + 2) (b + 20),
    .mulF kp (b + 21), .addF (b + 1) (b + 22), .mulF kp (b + 23), .addF (b + 9) (b + 24),
    .mulF kp kp, .mulF (b + 26) (b + 25), .const (fun _ => .f 0),
    .keep (fun κ => P.kv.node κ) (b + 27) (b + 28),
    .addF vRS (b + 29),
    .const (fun _ => .k 1), .mulKF (b + 31) (b + 30),
    .assertEq (b + 32) (claim0 fi "P1") g]

/-- `rsvBOps`' tail (9 ops from `e = d + 118`): `κ′^{11}`, the claim, its assert. -/
def rsvBTl (fi : FinIn) (kp k2 s9 vRS one e : ℕ) (rsv : KC Bool) : List Op :=
  [Op.mulF k2 k2, Op.mulF e e, Op.mulF (e + 1) k2, Op.mulF (e + 2) kp,
   Op.mulF (e + 3) (e - 1), Op.addF s9 (e + 4), Op.addF vRS (e + 5), Op.mulKF one (e + 6),
   Op.assertEq (e + 7) (claim0 fi "P1") rsv]

theorem gFinB'_rsv (hr : P.rsvOps = true) (b : ℕ) : (gFinB' P fi b).1 =
    gB0 P fi b (fun _ => !P.rsv) ++
      (((List.range 59).flatMap fun k =>
        [Op.mulF ((outsOf fi "B'").headD 0)
          (if k = 0 then ((fi.ex.getD exE []).drop 1).getD 59 0 else b + 33 + 2 * k - 1),
         Op.addF (((fi.ex.getD exE []).drop 1).getD (58 - k) 0) (b + 33 + 2 * k)]) ++
      rsvBTl fi ((outsOf fi "B'").headD 0) (b + 26) (b + 29) (fi.zhat.getD nRS 0) (b + 31) (b + 33 + 118)
        (fun _ => P.rsv)) := by
  simp only [gFinB', hr, Bool.cond_true]; rfl

/-- **Block A of the reserve's `finB′`**: the own ops with the assert gated `¬rsv`. -/
theorem run_gB0 (hin : ∀ x ∈ [(outsOf fi "B'").headD 0, fi.zhat.getD nRS 0, claim0 fi "P1"], x < r.size) :
    ∃ L, pureRun impl κ inp ((gB0 P fi r.size (fun _ => !P.rsv)).map (reloc P.S)) r [] =
        some (L, P.rsv || (Val.k (K.smulF (vStar4o κ inp fi r P) 1)).eqv (rd r (claim0 fi "P1"))) ∧
      L.length = 33 ∧
      rd (r ++ L.toArray) (r.size + 26) = .f (fv r ((outsOf fi "B'").headD 0) * fv r ((outsOf fi "B'").headD 0)) ∧
      rd (r ++ L.toArray) (r.size + 29) = .f (if P.kv.node κ then
        fv r ((outsOf fi "B'").headD 0) * fv r ((outsOf fi "B'").headD 0) *
          pubH4 inp P (fv r ((outsOf fi "B'").headD 0)) else 0) ∧
      rd (r ++ L.toArray) (r.size + 31) = .k 1 ∧
      (rd (r ++ L.toArray) (r.size + 30)).toF = vStar4o κ inp fi r P := by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hin
  have tf : ∀ x, (Val.f x).toF = x := fun _ => rfl
  have td : ∀ x, (Val.d x).toD = x := fun _ => rfl
  have tk : ∀ x, (Val.k x).toK = x := fun _ => rfl
  have hS : fStmt < 19 := by decide
  simp only [gB0, vStar4o, pubH4, dLo, dHi, List.map_cons, List.map_nil, reloc_piDigest _ hS]
  generalize (outsOf fi "B'").headD 0 = kp at *
  generalize fi.zhat.getD nRS 0 = vR at *
  generalize claim0 fi "P1" = c0 at *
  have hk := hin kp (.inl rfl); have hR := hin vR (.inr (.inl rfl))
  have hc := hin c0 (.inr (.inr rfl))
  rw [pureRun_nil_rev]
  cases hn : P.kv.node κ <;>
  simp only [hn, pureRun, reloc, evalOp, absOff_zero, tf, td, tk, rd_revAcc, rd_revAcc0,
    revAcc_app_cons, List.append_nil, List.length_cons, List.length_nil, Nat.reduceAdd,
    Nat.reduceSub, Array.reduceGetElem?, Option.getD_some, rd_app_left _ _ hk, rd_app_left _ _ hR,
    rd_app_left _ _ hc, Option.map_some, allK, Bool.not_true, Bool.false_or,
    Bool.true_and, Bool.and_true, ↓reduceIte, Bool.false_eq_true, digestAt_eq, Bool.not_not] <;>
  refine ⟨_, rfl, rfl, ?_, ?_, ?_, ?_⟩ <;> simp only [rd_revAcc,
    List.length_cons, List.length_nil, Nat.reduceAdd, Nat.reduceSub, Array.reduceGetElem?,
    Option.getD_some, tf]

/-- **`finB′`'s flag with the reserve** (`rsvOps`): the own block (`run_gB0`), the Horner chain
(`run_rsvHorner`) and the tail. Reads the 60 exports of `finE` (`hex`). -/
theorem flag_gFinB'1 (hr : P.rsvOps = true)
    (hin : ∀ x ∈ [(outsOf fi "B'").headD 0, fi.zhat.getD nRS 0, claim0 fi "P1"], x < r.size)
    (hex : ∀ x ∈ (fi.ex.getD exE []).drop 1, x < r.size) :
    ∃ L, pureRun impl κ inp ((gFinB' P fi r.size).1.map (reloc P.S)) r [] =
        some (L, relB4 κ inp fi r P) ∧
      (rd (r ++ L.toArray) ((gFinB' P fi r.size).2.getD 0 0)).toF = vStar4o κ inp fi r P := by
  obtain ⟨LA, hA, hlA, a26, a29, a31, a30⟩ := run_gB0 impl κ inp fi r P hin
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hin
  have hk := hin _ (.inl rfl); have hR := hin _ (.inr (.inl rfl)); have hc := hin _ (.inr (.inr rfl))
  have hpos : 0 < r.size := Nat.lt_of_le_of_lt (Nat.zero_le _) hk
  have hvs : ∀ j, ((fi.ex.getD exE []).drop 1).getD j 0 < r.size := fun j => getD_lt' hpos hex j
  have s1 : (r ++ LA.toArray).size = r.size + 33 := by simp [hlA]
  have e1 : ExtA r (r ++ LA.toArray) := ExtA.app r LA
  obtain ⟨MH, hH, hlH, hvH⟩ := run_rsvHorner impl κ inp (r ++ LA.toArray) (r.size + 33) s1
    ((outsOf fi "B'").headD 0) (((fi.ex.getD exE []).drop 1).getD 59 0)
    (fun k => ((fi.ex.getD exE []).drop 1).getD (58 - k) 0)
    (fv r ((outsOf fi "B'").headD 0)) (fv r (((fi.ex.getD exE []).drop 1).getD 59 0))
    (fun k => fv r (((fi.ex.getD exE []).drop 1).getD (58 - k) 0))
    ⟨Nat.lt_of_lt_of_le hk (by omega), by rw [e1.rd hk]⟩
    ⟨Nat.lt_of_lt_of_le (hvs 59) (by omega), by rw [e1.rd (hvs 59)]⟩
    (fun k => ⟨Nat.lt_of_lt_of_le (hvs _) (by omega), by rw [e1.rd (hvs _)]⟩) 59
  have s2 : (r ++ LA.toArray ++ MH.toArray).size = r.size + 33 + 118 := by simp [hlA, hlH]
  have e2 : ExtA (r ++ LA.toArray) (r ++ LA.toArray ++ MH.toArray) := ExtA.app _ MH
  have e02 := e1.trans e2
  have g : ∀ x, x < r.size + 33 → ∀ L : List Val,
      rd (r ++ LA.toArray ++ MH.toArray ++ L.toArray) x = rd (r ++ LA.toArray) x := fun x hx L => by
    rw [rd_app_left _ _ (by rw [s2]; omega), e2.rd (by rw [s1]; exact hx)]
  have g0 : ∀ x, x < r.size → ∀ L : List Val,
      rd (r ++ LA.toArray ++ MH.toArray ++ L.toArray) x = rd r x := fun x hx L => by
    rw [g x (by omega) L, e1.rd hx]
  have gH : ∀ L : List Val, rd (r ++ LA.toArray ++ MH.toArray ++ L.toArray) (r.size + 33 + 118 - 1) =
      .f (hornerV (fv r ((outsOf fi "B'").headD 0)) (fv r (((fi.ex.getD exE []).drop 1).getD 59 0))
        (fun k => fv r (((fi.ex.getD exE []).drop 1).getD (58 - k) 0)) 59) := fun L => by
    rw [rd_app_left _ _ (by rw [s2]; omega), show r.size + 33 + 118 - 1 = r.size + 33 + 2 * 58 + 1 by omega,
      hvH 58 (by norm_num)]
  have g26 := g (r.size + 26) (by omega); have g29 := g (r.size + 29) (by omega)
  have g30 := g (r.size + 30) (by omega); have g31 := g (r.size + 31) (by omega)
  have gk := g0 _ hk; have gR := g0 _ hR; have gc := g0 _ hc
  have tf : ∀ x, (Val.f x).toF = x := fun _ => rfl
  have tk : ∀ x, (Val.k x).toK = x := fun _ => rfl
  have hsum := hornerV_eq_sum (fv r ((outsOf fi "B'").headD 0))
    (fun j => fv r (((fi.ex.getD exE []).drop 1).getD j 0)) 59 59 le_rfl
  simp only [Nat.reduceSub, Nat.sub_self, zero_add, Nat.reduceAdd] at hsum
  have hT : ∃ LT fT, pureRun impl κ inp ((rsvBTl fi ((outsOf fi "B'").headD 0) (r.size + 26) (r.size + 29)
      (fi.zhat.getD nRS 0) (r.size + 31) (r.size + 33 + 118) (fun _ => P.rsv)).map (reloc P.S))
      (r ++ LA.toArray ++ MH.toArray) [] = some (LT, fT) ∧ fT = (!P.rsv || (Val.k (K.smulF (vStar4o κ inp fi r P +
        fv r ((outsOf fi "B'").headD 0) ^ 11 * ∑ i ∈ Finset.range rsvN,
          fv r ((outsOf fi "B'").headD 0) ^ i * fv r (((fi.ex.getD exE []).drop 1).getD i 0)) 1)).eqv
        (rd r (claim0 fi "P1"))) := by
    simp only [rsvBTl, List.map_cons, List.map_nil]
    rw [pureRun_nil_rev]
    simp only [pureRun, reloc, evalOp, tf, tk, rd_revAccAt _ _ s2, revAcc_app_cons, List.append_nil,
      List.length_cons, List.length_nil, Nat.reduceAdd, Nat.reduceSub, Nat.add_sub_cancel_left,
      Nat.le_add_right, le_refl, Nat.sub_self, Array.reduceGetElem?, Option.getD_some, g26, g29,
      g31, gk, gR, gc, gH, a26, a29, a31, Option.map_some, Bool.true_and, Bool.and_true, hsum]
    refine ⟨_, _, rfl, ?_⟩
    simp only [vStar4o, rsvN]
    congr 4
    ring

  obtain ⟨LT, fT, hT, rfl⟩ := hT
  refine ⟨LA ++ (MH ++ LT), ?_, ?_⟩
  · rw [gFinB'_rsv (fi := fi) (P := P) hr, List.map_append, List.map_append]
    have hHr : ((List.range 59).flatMap fun k =>
        [Op.mulF ((outsOf fi "B'").headD 0)
          (if k = 0 then ((fi.ex.getD exE []).drop 1).getD 59 0 else r.size + 33 + 2 * k - 1),
         Op.addF (((fi.ex.getD exE []).drop 1).getD (58 - k) 0) (r.size + 33 + 2 * k)]).map (reloc P.S) =
        (List.range 59).flatMap fun k =>
        [Op.mulF ((outsOf fi "B'").headD 0)
          (if k = 0 then ((fi.ex.getD exE []).drop 1).getD 59 0 else r.size + 33 + 2 * k - 1),
         Op.addF (((fi.ex.getD exE []).drop 1).getD (58 - k) 0) (r.size + 33 + 2 * k)] := by
      simp only [List.map_flatMap, List.map_cons, List.map_nil, reloc]
    rw [hHr, pureRun_seq impl κ inp hA (pureRun_seq impl κ inp hH hT)]
    cases hrs : P.rsv <;> simp [relB4, vStar4, hr, hrs]
  · simp only [gFinB', List.getD_cons_zero]
    rw [← app_app, rd_app_left _ _ (by rw [s1]; omega), a30]

/-- **`finB′`'s flag** (revision 4.4.2). Without the reserve, `flag_gFinB'o`. With it, B′'s own
assert is gated `¬rsv` and `rsvBOps` (Horner over the 60 exports, RSV2 §2.2) asserts `v*` where
`rsv` (`flag_gFinB'1`; `hex`: `finE`'s exports are registers of the file). The export is `v*₀`
(`vStar4o`) in both cases. -/
theorem flag_gFinB' (hin : ∀ x ∈ [(outsOf fi "B'").headD 0, fi.zhat.getD nRS 0, claim0 fi "P1"],
      x < r.size) (hex : ∀ x ∈ (fi.ex.getD exE []).drop 1, x < r.size) :
    ∃ L, pureRun impl κ inp ((gFinB' P fi r.size).1.map (reloc P.S)) r [] =
        some (L, relB4 κ inp fi r P) ∧
      (rd (r ++ L.toArray) ((gFinB' P fi r.size).2.getD 0 0)).toF = vStar4o κ inp fi r P := by
  cases hr : P.rsvOps
  · exact flag_gFinB'o impl κ inp fi r P hr hin
  · exact flag_gFinB'1 impl κ inp fi r P hr hin hex

end Flags

end FR.Snd.R4
