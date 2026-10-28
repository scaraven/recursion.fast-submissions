-- New for `flock-recursive` (BLUEPRINT §7, A.9; stage S-0 fix pass, S-0-M1).
import FRVIRSpec
import FRSkip

/-!
# The phase-final checks (`Finals`, A.9) and `gen`

`Finals` has one field per phase. A field sees the phases' outputs (`GCtx.outs`), the values ring
switching certifies (`finRS`'s exports `α₁ … α₄`: `ẑ_Z`, Lc's claim, Sh's claim, E4's
`f̂(r′)`; then `v_RS`; revision 3.13), and the exports of the fields run before it (`FinIn.ex`:
`finLr`'s `v_L`, `r_Lr` are read by `finE`); it returns ops (asking nothing) and its own
exports. `gen fin mode` is the skeleton, then the fields in the order `finRS, finZ, finLc, finSh,
finLr, finE, finB′, finP 0 … 4, finPf`, then `accept`.

Owners (A.9): **S-0** `finZ`, `finLc`, `finSh`, `finLr` (here, with `flag_finZ` …: the flag of each
is A.9's relation over the register values); **S-F** `finRS`, `finE`, `finB′`; **S-G** `finP`,
`finPf` (stated as fields; `s0Finals` takes them as arguments; the dump marks them pending).

The proofs run the ops with `pureRun` (registers kept as `r ++ L`, the normal form of
`FRVIRSpec.exec_app`; `exec_pureRun` carries them into `exec`).
-/

namespace FR
open RecursionFast

/-! ## Running ops that ask nothing -/

/-- Run ops that ask nothing from registers `r ++ L`: the appended values and the flag (`none` if
an op asks). -/
def pureRun (impl : OpImpl) (κ : Kind) (inp : Input) : List Op → Array Val → List Val →
    Option (List Val × Bool)
  | [], _, L => some (L, true)
  | op :: ops, r, L =>
    match evalOp impl κ inp (r ++ L.toArray) op with
    | .vals vs ok => (pureRun impl κ inp ops r (L ++ vs)).map fun p => (p.1, ok && p.2)
    | .ask _ => none

theorem exec_pureRun (impl : OpImpl) (κ : Kind) (inp : Input) (o₁ ops : List Op) (r : Array Val)
    (L L' : List Val) (f ok : Bool) (tr : Trace) (h : pureRun impl κ inp o₁ r L = some (L', f)) :
    exec impl κ inp (o₁ ++ ops) ⟨r ++ L.toArray, ok⟩ tr =
      exec impl κ inp ops ⟨r ++ L'.toArray, ok && f⟩ tr := by
  induction o₁ generalizing L L' f ok with
  | nil => simp [pureRun] at h; obtain ⟨rfl, rfl⟩ := h; simp
  | cons op o ih =>
    rw [List.cons_append, exec_app]
    simp only [pureRun] at h
    split at h
    · next vs ok' hv =>
      simp only [Option.map_eq_some_iff] at h
      obtain ⟨⟨L₂, f₂⟩, h₂, he⟩ := h
      simp only [Prod.mk.injEq] at he; obtain ⟨rfl, rfl⟩ := he
      simp only [hv]
      rw [ih _ _ _ _ h₂]; simp [Bool.and_assoc]
    · cases h

/-- A field's ops on the trace: its flag joins the run's (the bridge from `flag_fin*` to `exec`). -/
theorem exec_field (impl : OpImpl) (κ : Kind) (inp : Input) (o₁ ops : List Op) (r : Array Val)
    (L : List Val) (f ok : Bool) (tr : Trace) (h : pureRun impl κ inp o₁ r [] = some (L, f)) :
    exec impl κ inp (o₁ ++ ops) ⟨r, ok⟩ tr = exec impl κ inp ops ⟨r ++ L.toArray, ok && f⟩ tr := by
  simpa using exec_pureRun impl κ inp o₁ ops r [] L f ok tr h

/-! ## The typed `Finals` (A.9) -/

/-- What a final field sees. -/
structure FinIn where
  /-- The phases' outputs (`GCtx.outs`, by phase number). -/
  outs : Array (List Reg)
  /-- `finRS`'s exports: `α₁ … α₄` (`ẑ_Z`, Lc's claim, Sh's claim, E4's `f̂(r′)`), then `v_RS`
  (revision 3.13, `J_z = 4`). -/
  zhat : List Reg
  /-- The exports of the fields run before, in run order. -/
  ex : Array (List Reg)

/-- A final field: ops from the next free register, and the registers it exports. -/
abbrev FinField := FinIn → ℕ → List Op × List Reg

/-- **The phase-final checks** (A.9), one field per phase. -/
structure Finals where
  finRS : FinField
  finZ : FinField
  finLc : FinField
  finSh : FinField
  finLr : FinField
  finE : FinField
  finB' : FinField
  finP : ℕ → FinField
  finPf : FinField

/-- The fields after `finRS`, in run order. -/
def Finals.rest (fin : Finals) : List FinField :=
  [fin.finZ, fin.finLc, fin.finSh, fin.finLr, fin.finE, fin.finB'] ++
    (List.range nLevels).map fin.finP ++ [fin.finPf]

/-- The finals' ops: `finRS`, then the rest with `finRS`'s exports as `zhat`. -/
def Finals.ops (fin : Finals) : FinOps := fun outs b =>
  let rs := fin.finRS ⟨outs, [], #[]⟩ b
  let step := fun (acc : List Op × ℕ × Array (List Reg)) (f : FinField) =>
    let x := f ⟨outs, rs.2, acc.2.2⟩ acc.2.1
    (acc.1 ++ x.1, acc.2.1 + opsOut x.1, acc.2.2.push x.2)
  rs.1 ++ (fin.rest.foldl step ([], b + opsOut rs.1, #[rs.2])).1

/-- **`gen fin mode`**: the verifier program with every phase-final check. -/
def gen (fin : Finals) (mode : Mode) : VProg := genWith fin.ops mode

/-- A pending field (S-F's, S-G's until delivered): no ops, no exports. -/
def pending : FinField := fun _ _ => ([], [])

/-- `finLr`'s place in `FinIn.ex` (run order: `finRS` 0, then `rest`: `finZ`, `finLc`, `finSh`,
`finLr`). -/
def exLr : ℕ := 4

/-- Control: `rest`'s entry `exLr − 1` is `finLr`, so its exports are `ex[exLr]` for the later
fields. -/
theorem rest_exLr (fin : Finals) : fin.rest[exLr - 1]? = some fin.finLr := rfl

/-- `finLr`'s exports as `finE` sees them: `v_L` (index 0) and the point `r_Lr` (index 1). -/
def lrEx (fi : FinIn) (j : ℕ) : Reg := (fi.ex.getD exLr []).getD j 0

/-! ## S-0's fields -/

/-- Phase `name`'s outputs. -/
def outsOf (fi : FinIn) (name : String) : List Reg := fi.outs.getD (phaseIx name) []

/-- A rounds phase's challenges (`claim₀ :: rᵢ … ++ [final]`). -/
def chals (fi : FinIn) (name : String) (k : ℕ) : List Reg := ((outsOf fi name).drop 1).take k

/-- A rounds phase's first and last claims. -/
def claim0 (fi : FinIn) (name : String) : Reg := (outsOf fi name).headD 0
def claimN (fi : FinIn) (name : String) : Reg := (outsOf fi name).getLastD 0

/-- A squeeze phase's coordinates (after the packed array). -/
def coordsR (fi : FinIn) (name : String) : List Reg := (outsOf fi name).drop 1

/-- The pinned coordinates `ρ₁ … ρ₇` (A.1, `FRSkip.pinnedRho`) as seven constant registers. -/
def pinOps : List Op := (List.ofFn pinnedRho).map fun x => .const fun _ => .f x

/-- **`finZ`** (A.9, revisions 3.8–3.9, skip-c): `eq((ρ, r), r′)·â·b̂ = c_Z` by `eqPt` (the pinned
`ρ₁ … ρ₇` are the point's variables `0 … 6`, then Z1's free coordinates). Exports `â`, `b̂` and Z2's
`P^z*(λ)`, the value of RS claim 1 (`ẑ(r, λ)`). -/
def finZ : FinField := fun fi b =>
  let co := coordsR fi "Z1"; let rs := chals fi "Z3" 26
  (pinOps ++
   [.packFK (fun κ => [b, b + 1, b + 2, b + 3, b + 4, b + 5, b + 6] ++ co.take (κ.m - 13)),
    .packFK (fun κ => rs.take (κ.m - 6)), .eqPt (b + 7) (b + 8),
    .piElem fZend 0, .piElem fZend 16, .mulF (b + 9) (b + 10), .mulF (b + 12) (b + 11),
    .assertEq (b + 13) (claimN fi "Z3") allK],
   [b + 10, b + 11, (outsOf fi "Z2").getD 2 0])

/-- `v_β = Σ_{i<8} β^i v_i` by Horner from `v₇` (register `b + 13`), the `v_i` at `b + 6 + i`, into
`b + 23 … b + 36` (closed-form register numbers). -/
def hornerOps (beta b : ℕ) : List Op := (List.range 7).flatMap fun i =>
  [.mulF beta (if i = 0 then b + 13 else b + (22 + 2 * i)), .addF (b + (12 - i)) (b + (23 + 2 * i))]

/-- **`finLc`** (A.9, revision 3.8.2): (i) `c₀ = â + α b̂`; (ii) `c_Lc = Â(rowW′, eq(r_k,·)) + α
B̂(rowW′, eq(r_k,·))` with `rowW′ = maskRows v rowW` (9 entries in `blockKinds` order: the leaf's
`v₀` at `chain`, a node's 8 `v` at the other kinds, `free` included); (iii) `Σ_{i<8} β^i v_i = α₂`
(RS claim 2). Exports `v_β`. -/
def finLc : FinField := fun fi b =>
  let α := (outsOf fi "L1").headD 0; let β := (outsOf fi "L3β").headD 0
  let oL3 := phaseOff (phaseIx "L3") fL2
  let v := (List.range 8).map fun i => b + (6 + i)
  ([.piElem fZend 0, .piElem fZend 16, .mulF α (b + 1), .addF b (b + 2),
    .assertEq (b + 3) (claim0 fi "L2") allK,
    .packFK (fun _ => (chals fi "Z3" 26).take 8), .rowW ((outsOf fi "Z2").headD 0) (b + 4)] ++
   (List.range 8).map (fun i => .piElem fL2 (oL3 + 16 * i)) ++
   [.const (fun _ => .f 0),
    .packFK (fun κ => if κ.isNode then (b + 14) :: v else (b + 6) :: List.replicate 8 (b + 14)),
    .maskRows (b + 15) (b + 5), .packF (chals fi "L2" 14), .eqTable (b + 17),
    .walkAB (b + 16) (b + 18), .mulF α (b + 20), .addF (b + 19) (b + 21),
    .assertEq (b + 22) (claimN fi "L2") allK] ++
   hornerOps β b ++
   [.assertEq (b + 36) (fi.zhat.getD 1 0) allK],
   [b + 36])

/-- The link families of the Sh phase (A.6, revision 3.5: at most 8). -/
def nLinkFam : ℕ := 8

/-- Family `f`'s term `κ_s^(f+2)·linkW τ f r` added to the running sum, 4 registers from
`b + 16 + 4f` (closed-form register numbers; the sum starts at `b + 14`, the power at `b + 15`). -/
def linkOps (tau r ks b : ℕ) : List Op := (List.range nLinkFam).flatMap fun f =>
  [.linkW tau f r, .mulF (if f = 0 then b + 15 else b + (16 + 4 * f - 1)) (b + (16 + 4 * f)),
   .addF (if f = 0 then b + 14 else b + (16 + 4 * f - 2)) (b + (16 + 4 * f + 1)),
   .mulF (if f = 0 then b + 15 else b + (16 + 4 * f - 1)) ks]

/-- The 32-byte chaining value `h0` of BLAKE2s-256 (`FRBlockLayout.h0`, little-endian words). -/
def h0Bytes : ByteArray := bytesOf [0x47, 0xE6, 0x08, 0x6B, 0x85, 0xAE, 0x67, 0xBB, 0x72, 0xF3,
  0x6E, 0x3C, 0x3A, 0xF5, 0x4F, 0xA5, 0x7F, 0x52, 0x0E, 0x51, 0x8C, 0x68, 0x05, 0x9B, 0xAB, 0xD9,
  0x83, 0x1F, 0x19, 0xCD, 0xE0, 0x5B]

/-- `h0`'s two F elements. -/
def h0lo : F := F.ofBytes (bytesAt h0Bytes 0 16)
def h0hi : F := F.ofBytes (bytesAt h0Bytes 16 16)

/-- **The shift's boundary values** (A.8 `shiftTarget … bnd`, revision 3.9), 7 registers from `b`:
a leaf's `s` (`hdr`'s `pub`, bytes 16–47) and `h` (`stmt` bytes 1–32), two elements each; a node's
`h0` twice. The array is register `b + 6`. -/
def bndOps (b : ℕ) : List Op :=
  [.piElem fHdr 16, .piElem fHdr 32, .piElem fStmt 1, .piElem fStmt 17,
   .const (fun _ => .f h0lo), .const (fun _ => .f h0hi),
   .packFK (fun κ => if κ.isNode then [b + 4, b + 5, b + 4, b + 5] else [b, b + 1, b + 2, b + 3])]

/-- **`finSh`** (A.9): the boundary values (`bndOps`, registers `b … b + 6`), then (i)
`c₀ = shiftTarget τ θ bnd`; (ii) `c_Sh = w_out ẑ_out + w_in ẑ_in`,
`w_out = eq(τ, r_blk)·slotW 0 θ r_pos`, `w_in = (shift(τ, r_blk) + κ_s eq(0, r_blk))·slotW 1 θ
r_pos + Σ_f κ_s^(f+2) linkW τ f r_blk` (`τ` S1's coordinates `0 …`, `θ` 18–27, `κ_s` 28; `r` S2's
challenges, `r_blk` the first `m − 14`, `r_pos` the next 10). Exports `w_out`, `w_in`. -/
def finSh : FinField := fun fi b₀ =>
  let co := coordsR fi "S1"; let rs := chals fi "S2" 28; let ks := co.getD 28 0
  let b := b₀ + 7
  (bndOps b₀ ++
   [.packFK (fun κ => co.take (κ.m - 14)), .packF ((co.drop 18).take 10), .shiftTarget b (b + 1) (b₀ + 6) ks,
    .assertEq (b + 2) (claim0 fi "S2") allK,
    .packFK (fun κ => rs.take (κ.m - 14)), .packFK (fun κ => (rs.drop (κ.m - 14)).take 10),
    .eqPt b (b + 3), .slotW 0 (b + 1) (b + 4), .mulF (b + 5) (b + 6),
    .shiftEq b (b + 3), .const (fun κ => .af (Array.replicate (κ.m - 14) 0)), .eqPt (b + 9) (b + 3),
    .mulF ks (b + 10), .addF (b + 8) (b + 11), .slotW 1 (b + 1) (b + 4), .mulF (b + 12) (b + 13),
    .mulF ks ks] ++
   linkOps b (b + 3) ks b ++
   [.addF (b + 7) (b + 46), .mulF (b + 48) (fi.zhat.getD 2 0),
    .assertEq (b + 49) (claimN fi "S2") allK],
   [b + 7, b + 46])

/-- **`finLr`** (A.9, revision 3.13; node only): `â_L, b̂_L, ĉ_L` from the Lr-end absorb (A.3 row
7′); (ii) `c_Lr2 = eq(r_Lr, r)·(â_L b̂_L + ĉ_L)` (`r_Lr` Lr1's 15 coordinates, `r` Lr2's
challenges); (i) `c₀^{Lr2} = 0` holds by `initClaim`; (iii) exports **`v_L = â_L + κ_L b̂_L + κ_L²
ĉ_L`** and Lr2's point `r` (the row point of `evalL`, as `r_{E2}` is `evalM`'s) to `finE`, whose E4
lincheck carries Lr's (Lr4 is withdrawn: S-G1j defect 2). A leaf's Lr-end message is asserted
zero by `gen`, so its `v_L` is `0`. -/
def finLr : FinField := fun fi b =>
  let kL := (outsOf fi "Lr3").headD 0
  ([.piElem fLrEnd 0, .piElem fLrEnd 16, .piElem fLrEnd 32,
    .packF ((coordsR fi "Lr1").take 15), .packF (chals fi "Lr2" 15), .eqPt (b + 3) (b + 4),
    .mulF b (b + 1), .addF (b + 6) (b + 2), .mulF (b + 5) (b + 7),
    .assertEq (b + 8) (claimN fi "Lr2") Kind.isNode,
    .mulF kL (b + 1), .mulF kL kL, .mulF (b + 10) (b + 2), .addF b (b + 9), .addF (b + 12) (b + 11)],
   [b + 13, b + 4])

/-- **The finals with S-0's fields** and the other owners' fields as arguments. -/
def s0Finals (rs e b' : FinField) (p : ℕ → FinField) (pf : FinField) : Finals :=
  ⟨rs, finZ, finLc, finSh, finLr, e, b', p, pf⟩

/-! ## The flags of S-0's fields (A.9's relations) -/

section Flags
variable (impl : OpImpl) (κ : Kind) (inp : Input) (fi : FinIn) (r : Array Val)

/-- The F value of register `x`. -/
abbrev fv (x : Reg) : F := (rd r x).toF

theorem map_rd_app (L : List Val) (xs : List Reg) (h : ∀ x ∈ xs, x < r.size) :
    xs.map (fun x => (rd (r ++ L.toArray) x).toF) = xs.map (fv r) :=
  List.map_congr_left fun x hx => by rw [rd_app_left _ _ (h x hx)]

/-- **`flag_finZ`**: `finZ` asks nothing, and its flag is A.9's relation (rev 3.8, skip-c). -/
theorem flag_finZ (hin : ∀ x ∈ coordsR fi "Z1" ++ chals fi "Z3" 26 ++ [claimN fi "Z3"], x < r.size) :
    ∃ L, pureRun impl κ inp (finZ fi r.size).1 r [] = some (L,
      let rr := (List.ofFn pinnedRho ++ ((coordsR fi "Z1").take (κ.m - 13)).map (fv r)).toArray
      let rr' := (((chals fi "Z3" 26).take (κ.m - 6)).map (fv r)).toArray
      (Val.f (eqPoint rr rr' * F.ofBytes (bytesAt inp.π (absOff fZend 0) 16) *
        F.ofBytes (bytesAt inp.π (absOff fZend 16) 16))).eqv (rd r (claimN fi "Z3"))) := by
  simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hin
  have h1 := fun L => map_rd_app r L ((coordsR fi "Z1").take (κ.m - 13))
    fun x hx => hin x (.inl (.inl (List.mem_of_mem_take hx)))
  have h2 := fun L => map_rd_app r L ((chals fi "Z3" 26).take (κ.m - 6))
    fun x hx => hin x (.inl (.inr (List.mem_of_mem_take hx)))
  have tf : ∀ x, (Val.f x).toF = x := fun _ => rfl
  have taf : ∀ x, (Val.af x).toAF = x := fun _ => rfl
  simp only [finZ, pinOps, List.ofFn_succ, List.ofFn_zero, List.map_cons, List.map_nil]
  generalize claimN fi "Z3" = cz at *
  have h5 := hin cz (.inr rfl)
  simp only [pureRun, evalOp, tf, taf, List.nil_append, List.cons_append, List.map_append,
    List.map_cons, List.map_nil, h1, h2, rd_app, rd_app0, rd_app_left _ _ h5, List.getD_cons_succ,
    List.getD_cons_zero, Option.map_some, Val.eqv, allK, Bool.not_true, Bool.false_or, Bool.true_and,
    Bool.and_true]
  exact ⟨_, rfl⟩

/-- The F element at byte `o` of field `f`. -/
abbrev pe (f o : ℕ) : F := F.ofBytes (bytesAt inp.π (absOff f o) 16)

/-- **A.9's `finLc` relation** over the register values. -/
def relLc : Bool :=
  let α := fv r ((outsOf fi "L1").headD 0); let β := fv r ((outsOf fi "L3β").headD 0)
  let oL3 := phaseOff (phaseIx "L3") fL2
  let v := (List.range 8).map fun i => pe inp fL2 (oL3 + 16 * i)
  let vk : List F := if κ.isNode then 0 :: v else v.headD 0 :: List.replicate 8 0
  let rw := maskRows vk.toArray (impl.rowW (fv r ((outsOf fi "Z2").headD 0))
    (((chals fi "Z3" 26).take 8).map (fv r)).toArray)
  let cw := eqTab ((chals fi "L2" 14).map (fv r)).toArray
  let vβ := (v.reverse.drop 1).foldl (fun acc x => x + β * acc) (v.getD 7 0)
  (Val.f (pe inp fZend 0 + α * pe inp fZend 16)).eqv (rd r (claim0 fi "L2")) &&
  ((Val.f ((impl.walkAB rw cw).1 + α * (impl.walkAB rw cw).2)).eqv (rd r (claimN fi "L2")) &&
  (Val.f vβ).eqv (rd r (fi.zhat.getD 1 0)))


theorem flag_finLc (hin : ∀ x ∈ (chals fi "Z3" 26).take 8 ++ chals fi "L2" 14 ++
      [(outsOf fi "L1").headD 0, (outsOf fi "L3β").headD 0, (outsOf fi "Z2").headD 0,
       claim0 fi "L2", claimN fi "L2", fi.zhat.getD 1 0], x < r.size) :
    ∃ L, pureRun impl κ inp (finLc fi r.size).1 r [] = some (L, relLc impl κ inp fi r) := by
  simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hin
  have h1 := fun L => map_rd_app r L ((chals fi "Z3" 26).take 8) fun x hx => hin x (.inl (.inl hx))
  have h2 := fun L => map_rd_app r L (chals fi "L2" 14) fun x hx => hin x (.inl (.inr hx))
  have tf : ∀ x, (Val.f x).toF = x := fun _ => rfl
  have taf : ∀ x, (Val.af x).toAF = x := fun _ => rfl
  simp only [finLc, relLc]
  generalize (outsOf fi "L1").headD 0 = a at *
  generalize (outsOf fi "L3β").headD 0 = be at *
  generalize (outsOf fi "Z2").headD 0 = l at *
  generalize claim0 fi "L2" = c0 at *
  generalize claimN fi "L2" = cN at *
  generalize fi.zhat.getD 1 0 = zh at *
  generalize phaseOff (phaseIx "L3") fL2 = oL3
  have ha := hin a (.inr (.inl rfl)); have hb := hin be (.inr (.inr (.inl rfl)))
  have hl := hin l (.inr (.inr (.inr (.inl rfl)))); have hc0 := hin c0 (.inr (.inr (.inr (.inr (.inl rfl)))))
  have hcN := hin cN (.inr (.inr (.inr (.inr (.inr (.inl rfl))))))
  have hz := hin zh (.inr (.inr (.inr (.inr (.inr (.inr rfl))))))
  cases hk : κ.isNode <;>
  simp only [hk, pureRun, evalOp, tf, taf, List.nil_append, List.cons_append, h1, h2, hornerOps,
    rd_app, rd_app0, rd_app_left _ _ ha, rd_app_left _ _ hb, rd_app_left _ _ hl,
    rd_app_left _ _ hc0, rd_app_left _ _ hcN, rd_app_left _ _ hz, List.range_succ, List.range_zero,
    List.map_cons, List.map_nil, List.map_append, List.reverse_cons, List.reverse_nil,
    List.getD_eq_getElem?_getD, List.getElem?_cons_succ, List.getElem?_cons_zero, Option.getD_some,
    Option.map_some, allK, Bool.not_true, Bool.false_or, Bool.true_and, Bool.and_true,
    List.drop_succ_cons, List.drop_zero, List.foldl_cons, List.foldl_nil,
    List.replicate_succ, List.replicate_zero, ite_true, ite_false, Bool.false_eq_true,
    List.headD_cons, List.flatMap_append, List.flatMap_cons, List.flatMap_nil, ↓reduceIte, Nat.reduceEqDiff, Nat.reduceAdd,
    Nat.reduceMul, Nat.reduceSub] <;>
  exact ⟨_, rfl⟩

/-- The link families' sum `acc + Σ_f κ_s^(f+2) linkW τ f r` (as `linkOps`). -/
def linkSum (τ r : Array F) (ks : F) : ℕ → F → F → F
  | 0, acc, _ => acc
  | n + 1, acc, pow =>
    linkSum τ r ks n (acc + pow * impl.linkW κ τ (nLinkFam - (n + 1)) r) (pow * ks)

/-- **A.9's `finSh` relation** over the register values. -/
def relSh : Bool :=
  let co := coordsR fi "S1"; let rs := chals fi "S2" 28; let ks := fv r (co.getD 28 0)
  let τ := ((co.take (κ.m - 14)).map (fv r)).toArray
  let θ := (((co.drop 18).take 10).map (fv r)).toArray
  let rb := ((rs.take (κ.m - 14)).map (fv r)).toArray
  let rp := (((rs.drop (κ.m - 14)).take 10).map (fv r)).toArray
  let wout := eqPoint τ rb * impl.slotW κ 0 θ rp
  let win := linkSum impl κ τ rb ks nLinkFam
    ((impl.shiftEq τ rb + ks * eqPoint (Array.replicate (κ.m - 14) 0) rb) * impl.slotW κ 1 θ rp)
    (ks * ks)
  let bnd : Array F := if κ.isNode then #[h0lo, h0hi, h0lo, h0hi]
    else #[pe inp fHdr 16, pe inp fHdr 32, pe inp fStmt 1, pe inp fStmt 17]
  (Val.f (impl.shiftTarget ks τ θ bnd)).eqv (rd r (claim0 fi "S2")) &&
  (Val.f ((wout + win) * fv r (fi.zhat.getD 2 0))).eqv
    (rd r (claimN fi "S2"))

theorem flag_finSh (hin : ∀ x ∈ coordsR fi "S1" ++ chals fi "S2" 28 ++
      [claim0 fi "S2", claimN fi "S2", fi.zhat.getD 2 0, fi.zhat.getD 2 0,
       (coordsR fi "S1").getD 28 0], x < r.size) :
    ∃ L, pureRun impl κ inp (finSh fi r.size).1 r [] = some (L, relSh impl κ inp fi r) := by
  simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hin
  have hco : ∀ x ∈ coordsR fi "S1", x < r.size := fun x hx => hin x (.inl (.inl hx))
  have hrs : ∀ x ∈ chals fi "S2" 28, x < r.size := fun x hx => hin x (.inl (.inr hx))
  have h1 := fun L => map_rd_app r L ((coordsR fi "S1").take (κ.m - 14))
    fun x hx => hco x (List.mem_of_mem_take hx)
  have h2 := fun L => map_rd_app r L (((coordsR fi "S1").drop 18).take 10)
    fun x hx => hco x (List.mem_of_mem_drop (List.mem_of_mem_take hx))
  have h3 := fun L => map_rd_app r L ((chals fi "S2" 28).take (κ.m - 14))
    fun x hx => hrs x (List.mem_of_mem_take hx)
  have h4 := fun L => map_rd_app r L (((chals fi "S2" 28).drop (κ.m - 14)).take 10)
    fun x hx => hrs x (List.mem_of_mem_drop (List.mem_of_mem_take hx))
  have hks : (coordsR fi "S1").getD 28 0 < r.size ∨ (coordsR fi "S1").getD 28 0 = 0 := by
    rcases Nat.lt_or_ge 28 (coordsR fi "S1").length with h | h
    · exact .inl (hco _ (by rw [List.getD_eq_getElem _ _ h]; exact List.getElem_mem h))
    · exact .inr (List.getD_eq_default _ _ h)
  have tf : ∀ x, (Val.f x).toF = x := fun _ => rfl
  have taf : ∀ x, (Val.af x).toAF = x := fun _ => rfl
  simp only [finSh, relSh, bndOps]
  generalize claim0 fi "S2" = c0 at *
  generalize claimN fi "S2" = cN at *
  generalize fi.zhat.getD 2 0 = zo at *
  generalize (coordsR fi "S1").getD 28 0 = ks at *
  have hc0 := hin c0 (.inr (.inl rfl)); have hcN := hin cN (.inr (.inr (.inl rfl)))
  have hzo := hin zo (.inr (.inr (.inr (.inl rfl))))
  have hk := hin ks (.inr (.inr (.inr (.inr (.inr rfl)))))
  cases hκ : κ.isNode <;>
  simp only [hκ, ite_true, ite_false, Bool.false_eq_true, Nat.add_assoc, List.map_cons, List.map_nil,
    pureRun, evalOp, tf, taf, List.nil_append, List.cons_append, h1, h2, h3, h4, linkOps,
    nLinkFam, linkSum, List.range_succ, List.range_zero, List.flatMap_append, List.flatMap_cons,
    List.flatMap_nil, ↓reduceIte, Nat.reduceEqDiff, Nat.reduceAdd, Nat.reduceMul, Nat.reduceSub,
    rd_app, rd_app0, rd_app_left _ _ hc0, rd_app_left _ _ hcN,
    rd_app_left _ _ hzo, rd_app_left _ _ hk,
    List.getD_cons_succ, List.getD_cons_zero,
    Option.map_some, allK, Bool.not_true, Bool.false_or, Bool.true_and, Bool.and_true] <;>
  exact ⟨_, rfl⟩

/-- **A.9's `finLr` relation** (node only, revision 3.13: the end check (ii)) over the register
values. -/
def relLr : Bool :=
  let rLr := (((coordsR fi "Lr1").take 15).map (fv r)).toArray
  let rr := ((chals fi "Lr2" 15).map (fv r)).toArray
  let a := pe inp fLrEnd 0; let bb := pe inp fLrEnd 16; let c := pe inp fLrEnd 32
  if κ.isNode then (Val.f (eqPoint rLr rr * (a * bb + c))).eqv (rd r (claimN fi "Lr2")) else true

/-- `finLr`'s first export, **`v_L = â_L + κ_L b̂_L + κ_L² ĉ_L`** (A.9 (iii), revision 3.13). -/
def vLv : F :=
  let kL := fv r ((outsOf fi "Lr3").headD 0)
  pe inp fLrEnd 0 + kL * pe inp fLrEnd 16 + kL * kL * pe inp fLrEnd 32

/-- **`flag_finLr`**: `finLr` asks nothing; its flag is `relLr`; its exports are `v_L` and Lr2's
point. -/
theorem flag_finLr (hin : ∀ x ∈ (coordsR fi "Lr1").take 15 ++ chals fi "Lr2" 15 ++
      [(outsOf fi "Lr3").headD 0, claimN fi "Lr2"], x < r.size) :
    ∃ L, pureRun impl κ inp (finLr fi r.size).1 r [] = some (L, relLr κ inp fi r) ∧
      (rd (r ++ L.toArray) ((finLr fi r.size).2.getD 0 0)).toF = vLv inp fi r ∧
      (rd (r ++ L.toArray) ((finLr fi r.size).2.getD 1 0)).toAF =
        ((chals fi "Lr2" 15).map (fv r)).toArray := by
  simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hin
  have h1 := fun L => map_rd_app r L ((coordsR fi "Lr1").take 15) fun x hx => hin x (.inl (.inl hx))
  have h2 := fun L => map_rd_app r L (chals fi "Lr2" 15) fun x hx => hin x (.inl (.inr hx))
  have tf : ∀ x, (Val.f x).toF = x := fun _ => rfl
  have taf : ∀ x, (Val.af x).toAF = x := fun _ => rfl
  simp only [finLr, relLr, vLv]
  generalize (outsOf fi "Lr3").headD 0 = kl at *
  generalize claimN fi "Lr2" = c2 at *
  have hk := hin kl (.inr (.inl rfl)); have hc2 := hin c2 (.inr (.inr rfl))
  cases hn : κ.isNode <;>
  simp only [hn, pureRun, evalOp, tf, taf, List.nil_append, List.cons_append, h1, h2,
    rd_app, rd_app0, rd_app_left _ _ hk, rd_app_left _ _ hc2,
    List.getD_cons_succ, List.getD_cons_zero,
    Option.map_some, Bool.not_true, Bool.not_false, Bool.false_or, Bool.true_or, Bool.true_and,
    Bool.and_true, ↓reduceIte, Bool.false_eq_true] <;>
  exact ⟨_, rfl, rfl, rfl⟩

end Flags

end FR
