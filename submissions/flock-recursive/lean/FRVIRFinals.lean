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

/-! ## The run kit (moved here from `FRVIRFinalsSF`/`FRVIRFinalsSG` by INT-5 for `finLc`) -/

section Kit
variable (impl : OpImpl) (κ : Kind) (inp : Input) (r : Array Val)

theorem pureRun_append (o₁ o₂ : List Op) (L : List Val) :
    pureRun impl κ inp (o₁ ++ o₂) r L = (pureRun impl κ inp o₁ r L).bind fun p =>
      (pureRun impl κ inp o₂ r p.1).map fun q => (q.1, p.2 && q.2) := by
  induction o₁ generalizing L with
  | nil => simp only [List.nil_append, pureRun, Option.bind_some, Bool.true_and]; simp
  | cons op o ih =>
    simp only [List.cons_append, pureRun]
    split
    · rw [ih]
      cases pureRun impl κ inp o r _ with
      | none => rfl
      | some p => simp [Option.map_map, Function.comp_def, Bool.and_assoc]
    · rfl

end Kit

section Rebase
variable (impl : OpImpl) (κ : Kind) (inp : Input)

/-- **Rebase**: running from `r` with `L ++ M` appended is running from `r ++ L` with `M`. -/
theorem pureRun_rebase (os : List Op) (r : Array Val) (L : List Val) : ∀ M : List Val,
    pureRun impl κ inp os r (L ++ M) =
      (pureRun impl κ inp os (r ++ L.toArray) M).map fun p => (L ++ p.1, p.2) := by
  induction os with
  | nil => intro M; simp [pureRun]
  | cons op os ih =>
    intro M
    have e : r ++ (L ++ M).toArray = r ++ L.toArray ++ M.toArray := by simp [Array.append_assoc]
    simp only [pureRun, e]
    rcases evalOp impl κ inp (r ++ L.toArray ++ M.toArray) op with ⟨vs, ok⟩ | q
    · simp only [List.append_assoc, ih, Option.map_map]; rfl
    · rfl

/-- Two blocks from base registers: the second runs from the first's registers. -/
theorem pureRun_seq {A B : List Op} {R : Array Val} {M M' : List Val} {f g : Bool}
    (hA : pureRun impl κ inp A R [] = some (M, f))
    (hB : pureRun impl κ inp B (R ++ M.toArray) [] = some (M', g)) :
    pureRun impl κ inp (A ++ B) R [] = some (M ++ M', f && g) := by
  rw [pureRun_append, hA, Option.bind_some]
  have := pureRun_rebase impl κ inp B R M []
  simp only [List.append_nil] at this
  rw [this, hB]; rfl

end Rebase

/-! ## The 64-term sum of `finLc` (ii)'s `free` term (revision 3.16, R-V-M2) -/

/-- `a0 + Σ_{s<n} X[s]·Y[s]`, summed in order (`dotOps`' running sum). -/
def dotAcc (a0 : F) (X Y : Array F) : ℕ → F
  | 0 => a0
  | n + 1 => dotAcc a0 X Y n + X.getD n 0 * Y.getD n 0

/-- **`Σ_{s<n} X[s]·Y[s]`** (`X`, `Y` the arrays of registers `x`, `y`; the sum starts at register
`z`'s value): per term `X[s]`, `Y[s]`, their product and the running sum, four ops from register
`c + 4s`; the sum ends at `c + 4n − 1`. -/
def dotOps (x y z c : ℕ) : ℕ → List Op
  | 0 => []
  | n + 1 => dotOps x y z c n ++
      [.getF x n, .getF y n, .mulF (c + 4 * n) (c + 4 * n + 1),
       .addF (if n = 0 then z else c + 4 * n - 1) (c + 4 * n + 2)]

/-- The values `dotOps` appends. -/
def dotVals (a0 : F) (X Y : Array F) : ℕ → List Val
  | 0 => []
  | n + 1 => dotVals a0 X Y n ++ [.f (X.getD n 0), .f (Y.getD n 0), .f (X.getD n 0 * Y.getD n 0),
      .f (dotAcc a0 X Y (n + 1))]

theorem dotVals_length (a0 : F) (X Y : Array F) (n : ℕ) : (dotVals a0 X Y n).length = 4 * n := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [dotVals, List.length_append, ih, List.length_cons, List.length_nil]; ring

theorem dotVals_last (a0 : F) (X Y : Array F) (n : ℕ) :
    (dotVals a0 X Y (n + 1)).getD (4 * n + 3) default = .f (dotAcc a0 X Y (n + 1)) := by
  rw [dotVals, List.getD_eq_getElem?_getD,
    List.getElem?_append_right (by rw [dotVals_length]; omega), dotVals_length]
  simp

theorem rd_len (R : Array Val) (L M : List Val) (t : ℕ) :
    rd (R ++ (L ++ M).toArray) (R.size + L.length + t) = M.getD t default := by
  rw [Nat.add_assoc, rd_app]; simp [List.getElem?_append_right]

theorem pureRun_cons_val {impl : OpImpl} {κ : Kind} {inp : Input} {R : Array Val} {op : Op}
    {ops : List Op} {L : List Val} {v : Val}
    (h : evalOp impl κ inp (R ++ L.toArray) op = .vals [v] true) :
    pureRun impl κ inp (op :: ops) R L = pureRun impl κ inp ops R (L ++ [v]) := by
  simp only [pureRun, h, Bool.true_and]; cases pureRun impl κ inp ops R (L ++ [v]) <;> rfl

/-- **`dotOps` runs to its sum**: from base registers `R` (holding `x`, `y`, `z`), the appended
values are `dotVals`, the last the sum `dotAcc`. -/
theorem run_dotOps (impl : OpImpl) (κ : Kind) (inp : Input) (R : Array Val) (x y z : ℕ)
    (hx : x < R.size) (hy : y < R.size) (hz : z < R.size) : ∀ n,
    pureRun impl κ inp (dotOps x y z R.size n) R [] =
      some (dotVals (rd R z).toF (rd R x).toAF (rd R y).toAF n, true)
  | 0 => rfl
  | n + 1 => by
    rw [dotOps, pureRun_append, run_dotOps impl κ inp R x y z hx hy hz n, Option.bind_some]
    set X := (rd R x).toAF
    set Y := (rd R y).toAF
    set D := dotVals (rd R z).toF X Y n with hDdef
    have hD : D.length = 4 * n := dotVals_length _ _ _ n
    have r0 : ∀ (M : List Val) (t : ℕ), rd (R ++ (D ++ M).toArray) (R.size + 4 * n + t) =
        M.getD t default := fun M t ↦ by rw [← hD]; exact rd_len R D M t
    have hacc : ∀ (M : List Val), (rd (R ++ (D ++ M).toArray)
        (if n = 0 then z else R.size + 4 * n - 1)).toF = dotAcc (rd R z).toF X Y n := by
      intro M
      rcases n with _ | k
      · rw [if_pos rfl, rd_app_left R _ hz]; rfl
      · rw [if_neg (by omega), show R.size + 4 * (k + 1) - 1 = R.size + (4 * k + 3) by omega,
          rd_app, List.getD_eq_getElem?_getD,
          List.getElem?_append_left (by rw [hD]; omega), ← List.getD_eq_getElem?_getD,
          hDdef, dotVals_last]; rfl
    have r00 : ∀ M : List Val, rd (R ++ (D ++ M).toArray) (R.size + 4 * n) = M.getD 0 default :=
      fun M ↦ by simpa using r0 M 0
    have hxL : ∀ M : List Val, rd (R ++ (D ++ M).toArray) x = rd R x := fun M ↦
      rd_app_left R _ hx
    have hyL : ∀ M : List Val, rd (R ++ (D ++ M).toArray) y = rd R y := fun M ↦
      rd_app_left R _ hy
    rw [pureRun_cons_val (v := .f (X.getD n 0)) (by
          rw [show D = D ++ [] by simp]; simp only [evalOp, hxL]; rfl),
      pureRun_cons_val (v := .f (Y.getD n 0)) (by simp only [evalOp, hyL]; rfl),
      pureRun_cons_val (v := .f (X.getD n 0 * Y.getD n 0)) (by
          simp only [evalOp, List.append_assoc, List.singleton_append, List.cons_append, r0, r00]
          rfl),
      pureRun_cons_val (v := .f (dotAcc (rd R z).toF X Y (n + 1))) (by
          simp only [evalOp, List.append_assoc, List.singleton_append, List.cons_append, r0, hacc]
          rfl)]
    simp [pureRun, dotVals, hDdef]


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
`ρ₁ … ρ₇` are the point's variables `0 … 6`, then Z1's free coordinates); **the c-claim** (INT-4,
S-G6 finding 1): Z2's `P^z*(λ)` equals `α_Z = fi.zhat[0]`, RS claim 1's value `ẑ(r, λ)` as ring
switching computes it, for every kind. Exports `â`, `b̂` and `P^z*(λ)`. -/
def finZ : FinField := fun fi b =>
  let co := coordsR fi "Z1"; let rs := chals fi "Z3" 26
  (pinOps ++
   [.packFK (fun κ => [b, b + 1, b + 2, b + 3, b + 4, b + 5, b + 6] ++ co.take (κ.m - 13)),
    .packFK (fun κ => rs.take (κ.m - 6)), .eqPt (b + 7) (b + 8),
    .piElem fZend 0, .piElem fZend 16, .mulF (b + 9) (b + 10), .mulF (b + 12) (b + 11),
    .assertEq (b + 13) (claimN fi "Z3") allK,
    .assertEq ((outsOf fi "Z2").getD 2 0) (fi.zhat.getD 0 0) allK],
   [b + 10, b + 11, (outsOf fi "Z2").getD 2 0])

/-- `v_β = Σ_{i<8} β^i v_i` by Horner from `v₇` (register `b + 13`), the `v_i` at `b + 6 + i`, into
`b + 23 … b + 36` (closed-form register numbers). -/
def hornerOps (beta b : ℕ) : List Op := (List.range 7).flatMap fun i =>
  [.mulF beta (if i = 0 then b + 13 else b + (22 + 2 * i)), .addF (b + (12 - i)) (b + (23 + 2 * i))]

/-- `dotOps` asks nothing. -/
theorem dotOps_noAsk (x y z c n : ℕ) : (dotOps x y z c n).filterMap Op.item? = [] := by
  induction n with
  | zero => rfl
  | succ n ih => simp [dotOps, List.filterMap_append, ih, Op.item?]

/-- `finLc`'s registers `b … b + 40` (A.9, revisions 3.8.2, 3.16): (i) `c₀ = â + α b̂`; the walk
`Â(rowW′, eq(r_k,·)) + α B̂(rowW′, eq(r_k,·))` (at `b + 22`) with `rowW′ = maskRows w rowW`, `w` in
`blockKinds` order: a leaf's `v₀` at `chain`; a node's `v₀ … v₆` at `stream … w43` and **`0` at
`free`** (R-V-M2: `nodeKindW`); `v_β = Σ_{i<8} β^i v_i` (`b + 36`) and (iii) `v_β = α₂` (RS claim
2); then the `free` term's inputs: `v_free` (`b + 37`: a node's `v₇`, a leaf's `0`), `L_s(λ)` for
`s < 64` (`eqZ λ 0`, `b + 38`) and `eq(r_k[0..5], ·)` (`b + 40`). -/
def lcHead (fi : FinIn) (b : ℕ) : List Op :=
  let α := (outsOf fi "L1").headD 0; let β := (outsOf fi "L3β").headD 0
  let oL3 := phaseOff (phaseIx "L3") fL2
  let v := (List.range 8).map fun i => b + (6 + i)
  [.piElem fZend 0, .piElem fZend 16, .mulF α (b + 1), .addF b (b + 2),
    .assertEq (b + 3) (claim0 fi "L2") allK,
    .packFK (fun _ => (chals fi "Z3" 26).take 8), .rowW ((outsOf fi "Z2").headD 0) (b + 4)] ++
   (List.range 8).map (fun i => .piElem fL2 (oL3 + 16 * i)) ++
   [.const (fun _ => .f 0),
    .packFK (fun κ => if κ.isNode then (b + 14) :: (v.take 7 ++ [b + 14])
      else (b + 6) :: List.replicate 8 (b + 14)),
    .maskRows (b + 15) (b + 5), .packF (chals fi "L2" 14), .eqTable (b + 17),
    .walkAB (b + 16) (b + 18), .mulF α (b + 20), .addF (b + 19) (b + 21)] ++
   hornerOps β b ++
   [.assertEq (b + 36) (fi.zhat.getD 1 0) allK,
    .keep Kind.isNode (b + 13) (b + 14), .eqZ ((outsOf fi "Z2").headD 0) (b + 14),
    .packF ((chals fi "L2" 14).take 6), .eqTable (b + 39)]

/-- `finLc`'s last ops, own registers from `d` (`= b + 297`; the 64-term sum `Σ_s L_s(λ)
eq(r_k[0..5], s)` is at `b + 296`): `eq(r′_hi, r_k[6..13])`, `X = sum · eq`, `Y = v_free·X`, the
check (ii) `c_Lc = walk + Y + α Y` (R-V-M2: `(1 + α)·v_free·⟨rowW, eq(r_k,·)⟩`, `linM_free_mle`). -/
def lcTail (fi : FinIn) (b d : ℕ) : List Op :=
  let α := (outsOf fi "L1").headD 0
  [.packF ((chals fi "L2" 14).drop 6), .eqPt (b + 4) d, .mulF (b + 296) (d + 1),
   .mulF (b + 37) (d + 2), .mulF α (d + 3), .addF (d + 3) (d + 4), .addF (b + 22) (d + 5),
   .assertEq (d + 6) (claimN fi "L2") allK]

/-- **`finLc`** (A.9, revision 3.16): `lcHead`, the 64-term sum (`dotOps`, registers
`b + 41 … b + 296`), `lcTail` (registers `b + 297 … b + 303`). Exports `v_β`. -/
def finLc : FinField := fun fi b =>
  (lcHead fi b ++ dotOps (b + 38) (b + 40) (b + 14) (b + 41) 64 ++ lcTail fi b (b + 297), [b + 36])

/-- The link families of the Sh phase (A.6, revision 3.5: at most 8). -/
def nLinkFam : ℕ := 8

/-- Family `f`'s term `κ_s^(f+2)·W_f` added to the running sum, 4 registers from `b + 27 + 4f`
(`W_f` read by `getF` from `linkWAll`'s register `b + 25`; the sum starts at `b + 22`, the power
at `b + 26`; revision 3.14). -/
def linkOps (ks b : ℕ) : List Op := (List.range nLinkFam).flatMap fun f =>
  [.getF (b + 25) f, .mulF (b + (26 + 4 * f)) (b + (27 + 4 * f)),
   .addF (if f = 0 then b + 22 else b + (25 + 4 * f)) (b + (28 + 4 * f)),
   .mulF (b + (26 + 4 * f)) ks]

/-- **The shift's boundary values** (A.8 `shiftTarget … bnd`, revision 3.9), 7 registers from `b`:
a leaf's `s` (`hdr`'s `pub`, bytes 16–47) and `h` (`stmt` bytes 1–32), two elements each; a node's
are zero (revision 3.14: the chain-masked Sh has no end term, and its start term
`κ_s(In(0) + In(chainBase_2))` has target `κ_s(h̃0 + h̃0) = 0` in characteristic two; the starts'
`h_in = h0` is `streamStart`'s pin). Revision 3.15 (`τ` of 18 coordinates, INT-4): the array
(register `b + 7`) is followed by the kind's last block `1^(m−14) ‖ 0^(32−m)` (`b + 6` holds `1`,
`b + 4` holds `0`), 22 entries. -/
def bndOps (b : ℕ) : List Op :=
  [.piElem fHdr 16, .piElem fHdr 32, .piElem fStmt 1, .piElem fStmt 17,
   .const (fun _ => .f 0), .const (fun _ => .f 0), .const (fun _ => .f 1),
   .packFK (fun κ => (if κ.isNode then [b + 4, b + 5, b + 4, b + 5] else [b, b + 1, b + 2, b + 3]) ++
     (List.replicate (κ.m - 14) (b + 6) ++ List.replicate (32 - κ.m) (b + 4)))]

/-- **A block point of 18 coordinates** (revision 3.15, ruling (c)): the first `m − 14` registers
of `xs`, then `32 − m` copies of the zero register `z` (P30/N30: coordinates 16–17). -/
def padB (κ : Kind) (xs : List Reg) (z : Reg) : List Reg :=
  xs.take (κ.m - 14) ++ List.replicate (32 - κ.m) z

/-- **`finSh`** (A.9, revision 3.14): the boundary values (`bndOps`, registers `b … b + 6`), then
(i) `c₀ = shiftTarget τ θ bnd`; (ii) `c_Sh = w_out ẑ_out + w_in ẑ_in` with
`w_out = E·slotW 0 θ r_pos`, `w_in = (Sh + κ_s E₀)·slotW_in θ r_pos + Σ_f κ_s^(f+2) W_f`
(`τ` S1's coordinates `0 …`, `θ` 18–27, `κ_s` 28; `r` S2's challenges, `r_blk` the first `m − 14`,
`r_pos` the next 10; revision 3.15: `τ`, `r_blk` and `E₀`'s zero point have 18 coordinates for
every kind, P30/N30 zero-padded (`padB`), and `bnd` carries the kind's last block). A leaf: `E = eq(τ, r_blk)`, `Sh = shift(τ, r_blk)`, `E₀ = eq(0, r_blk)`,
`slotW_in` the `d` slot (map 1), `W_f = 0`. A node (**chain-masked**, `shiftMask`): `E`, `Sh` the
sums over the blocks with an in-chain successor, `E₀ = eq(0, r_blk) + eq(chainBase_2, r_blk)`,
`slotW_in` the `h_in` slot (map 2, base 0), `W_f` the 8 families of `linkWAll (τ ‖ θ)
(r_blk ‖ r_pos)` (`getF`). Exports `w_out`, `w_in`. -/
def finSh : FinField := fun fi b₀ =>
  let co := coordsR fi "S1"; let rs := chals fi "S2" 28; let ks := co.getD 28 0
  let b := b₀ + 8
  (bndOps b₀ ++
   [.packFK (fun κ => padB κ co (b₀ + 4)), .packF ((co.drop 18).take 10),
    .shiftTarget b (b + 1) (b₀ + 7) ks,
    .assertEq (b + 2) (claim0 fi "S2") allK,
    .packFK (fun κ => padB κ rs (b₀ + 4)), .packFK (fun κ => (rs.drop (κ.m - 14)).take 10),
    .eqPt b (b + 3), .shiftEq b (b + 3), .const (fun _ => .af (Array.replicate 18 0)),
    .eqPt (b + 7) (b + 3), .shiftMask b (b + 3),
    .keep Kind.isNode (b + 9) (b + 5), .keep Kind.isNode (b + 10) (b + 6),
    .keep Kind.isNode (b + 11) (b + 8),
    .slotW 0 (b + 1) (b + 4), .mulF (b + 12) (b + 15),
    .mulF ks (b + 14), .addF (b + 13) (b + 17),
    .slotW 1 (b + 1) (b + 4), .slotW 2 (b + 1) (b + 4), .keep Kind.isNode (b + 20) (b + 19),
    .mulF (b + 18) (b + 21),
    .packFK (fun κ => co.take (κ.m - 14) ++ (co.drop 18).take 10),
    .packFK (fun κ => rs.take (κ.m - 14) ++ (rs.drop (κ.m - 14)).take 10),
    .linkWAll (b + 23) (b + 24), .mulF ks ks] ++
   linkOps ks b ++
   [.addF (b + 16) (b + 57), .mulF (b + 59) (fi.zhat.getD 2 0),
    .assertEq (b + 60) (claimN fi "S2") allK],
   [b + 16, b + 57])

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

/-- The F element at byte `o` of field `f`. -/
abbrev pe (f o : ℕ) : F := F.ofBytes (bytesAt inp.π (absOff f o) 16)

/-- **A.9's `finZ` relation** over the register values: (i) `eq((ρ, r), r′)·â·b̂ = c_Z`; (ii) the
c-claim `P^z*(λ) = α_Z` (Z2's output 2 against RS claim 1's value, INT-4). -/
def relZ : Bool :=
  let rr := (List.ofFn pinnedRho ++ ((coordsR fi "Z1").take (κ.m - 13)).map (fv r)).toArray
  let rr' := (((chals fi "Z3" 26).take (κ.m - 6)).map (fv r)).toArray
  (Val.f (eqPoint rr rr' * pe inp fZend 0 * pe inp fZend 16)).eqv (rd r (claimN fi "Z3")) &&
  (rd r ((outsOf fi "Z2").getD 2 0)).eqv (rd r (fi.zhat.getD 0 0))

/-- **`flag_finZ`**: `finZ` asks nothing, and its flag is A.9's relation `relZ` (rev 3.8, skip-c;
INT-4: with the c-claim). -/
theorem flag_finZ (hin : ∀ x ∈ coordsR fi "Z1" ++ chals fi "Z3" 26 ++
      [claimN fi "Z3", (outsOf fi "Z2").getD 2 0, fi.zhat.getD 0 0], x < r.size) :
    ∃ L, pureRun impl κ inp (finZ fi r.size).1 r [] = some (L, relZ κ inp fi r) := by
  simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hin
  have h1 := fun L => map_rd_app r L ((coordsR fi "Z1").take (κ.m - 13))
    fun x hx => hin x (.inl (.inl (List.mem_of_mem_take hx)))
  have h2 := fun L => map_rd_app r L ((chals fi "Z3" 26).take (κ.m - 6))
    fun x hx => hin x (.inl (.inr (List.mem_of_mem_take hx)))
  have tf : ∀ x, (Val.f x).toF = x := fun _ => rfl
  have taf : ∀ x, (Val.af x).toAF = x := fun _ => rfl
  simp only [finZ, relZ, pinOps, List.ofFn_succ, List.ofFn_zero, List.map_cons, List.map_nil]
  generalize claimN fi "Z3" = cz at *
  generalize (outsOf fi "Z2").getD 2 0 = pz at *
  generalize fi.zhat.getD 0 0 = az at *
  have h5 := hin cz (.inr (.inl rfl)); have h6 := hin pz (.inr (.inr (.inl rfl)))
  have h7 := hin az (.inr (.inr (.inr rfl)))
  simp only [pureRun, evalOp, tf, taf, List.nil_append, List.cons_append, List.map_append,
    List.map_cons, List.map_nil, h1, h2, rd_app, rd_app0, rd_app_left _ _ h5, rd_app_left _ _ h6,
    rd_app_left _ _ h7, List.getD_cons_succ,
    List.getD_cons_zero, Option.map_some, Val.eqv, allK, Bool.not_true, Bool.false_or, Bool.true_and,
    Bool.and_true]
  exact ⟨_, rfl⟩

/-- **`relZ` binds RS claim 1** (INT-4): when `P^z*(λ)` and `α_Z` are F values, an accepting
`finZ` has `eq·â·b̂ = c_Z` and `P^z*(λ) = α_Z`. -/
theorem relZ_iff {p a : F} (hp : rd r ((outsOf fi "Z2").getD 2 0) = .f p)
    (ha : rd r (fi.zhat.getD 0 0) = .f a) :
    relZ κ inp fi r = true ↔
      (Val.f (eqPoint (List.ofFn pinnedRho ++ ((coordsR fi "Z1").take (κ.m - 13)).map (fv r)).toArray
          (((chals fi "Z3" 26).take (κ.m - 6)).map (fv r)).toArray * pe inp fZend 0 *
          pe inp fZend 16)).eqv (rd r (claimN fi "Z3")) = true ∧ p = a := by
  simp only [relZ, hp, ha, Val.eqv, Bool.and_eq_true, decide_eq_true_eq]

/-- (−) **A run with `α_Z ≠ P^z*(λ)` is rejected** (INT-4; S-G6 finding 1): `finZ`'s flag is
`false` whatever the other check gives. Before INT-4 no op read `α_Z`. -/
theorem finZ_rejects (hin : ∀ x ∈ coordsR fi "Z1" ++ chals fi "Z3" 26 ++
      [claimN fi "Z3", (outsOf fi "Z2").getD 2 0, fi.zhat.getD 0 0], x < r.size)
    {p a : F} (hp : rd r ((outsOf fi "Z2").getD 2 0) = .f p)
    (ha : rd r (fi.zhat.getD 0 0) = .f a) (hne : p ≠ a) :
    ∃ L, pureRun impl κ inp (finZ fi r.size).1 r [] = some (L, false) := by
  obtain ⟨L, hL⟩ := flag_finZ impl κ inp fi r hin
  refine ⟨L, hL.trans ?_⟩
  have : relZ κ inp fi r ≠ true := fun h => hne ((relZ_iff κ inp fi r hp ha).1 h).2
  simpa using this

/-- (+) … and with `α_Z = P^z*(λ)` and the first check true, `finZ` accepts. -/
theorem finZ_accepts (hin : ∀ x ∈ coordsR fi "Z1" ++ chals fi "Z3" 26 ++
      [claimN fi "Z3", (outsOf fi "Z2").getD 2 0, fi.zhat.getD 0 0], x < r.size)
    {p : F} (hp : rd r ((outsOf fi "Z2").getD 2 0) = .f p) (ha : rd r (fi.zhat.getD 0 0) = .f p)
    (h1 : (Val.f (eqPoint (List.ofFn pinnedRho ++ ((coordsR fi "Z1").take (κ.m - 13)).map (fv r)).toArray
          (((chals fi "Z3" 26).take (κ.m - 6)).map (fv r)).toArray * pe inp fZend 0 *
          pe inp fZend 16)).eqv (rd r (claimN fi "Z3")) = true) :
    ∃ L, pureRun impl κ inp (finZ fi r.size).1 r [] = some (L, true) := by
  obtain ⟨L, hL⟩ := flag_finZ impl κ inp fi r hin
  exact ⟨L, hL.trans (by rw [(relZ_iff κ inp fi r hp ha).2 ⟨h1, rfl⟩])⟩

/-- `finLc`'s claims `v_0 … v_7` (L3's message). -/
def lcV : List F := (List.range 8).map fun i => pe inp fL2 (phaseOff (phaseIx "L3") fL2 + 16 * i)

/-- `r′_hi`: Z3's first 8 challenges. -/
def lcRhi : Array F := (((chals fi "Z3" 26).take 8).map (fv r)).toArray

/-- `r_k`: L2's 14 challenges. -/
def lcRk : List F := (chals fi "L2" 14).map (fv r)

/-- **The walk** `Â + α B̂` at `rowW′ = maskRows w rowW` and `eq(r_k, ·)`; `w` = a node's
`nodeKindW v` (`free` weight 0, revision 3.16), a leaf's `v₀ :: 0^8`. -/
def lcWalk : F :=
  let α := fv r ((outsOf fi "L1").headD 0)
  let w : List F := if κ.isNode then nodeKindW (lcV inp) else (lcV inp).headD 0 :: List.replicate 8 0
  let rw := maskRows w.toArray (impl.rowW (fv r ((outsOf fi "Z2").headD 0)) (lcRhi fi r))
  let cw := eqTab (lcRk fi r).toArray
  (impl.walkAB rw cw).1 + α * (impl.walkAB rw cw).2

/-- `v_free`: a node's `v₇`, a leaf's `0`. -/
def lcVf : F := if κ.isNode then pe inp fL2 (phaseOff (phaseIx "L3") fL2 + 16 * 7) else 0

/-- **`free`'s term without `(1 + α)`** (revision 3.16, R-V-M2): `v_free · (Σ_{s<64} L_s(λ)
eq(r_k[0..5], s)) · eq(r′_hi, r_k[6..13])` (`L_s(λ)` = `eqZ(λ, 0)[s]`); its spec is
`FRSpartan.linM_free_mle`, `⟨rowW, eq(r_k, ·)⟩` in closed form. -/
def lcFree : F :=
  lcVf κ inp * (dotAcc 0 (impl.eqZ (fv r ((outsOf fi "Z2").headD 0)) 0)
    (eqTab (((chals fi "L2" 14).take 6).map (fv r)).toArray) 64 * eqPoint (lcRhi fi r) (((chals fi "L2" 14).drop 6).map (fv r)).toArray)

/-- `dotAcc` is the sum `a0 + Σ_{s<n} X[s]·Y[s]` (`lcFree`'s 64-term sum is `Σ_{s<64} L_s(λ)
eq(r_k[0..5], s)`). -/
theorem dotAcc_eq (a0 : F) (X Y : Array F) (n : ℕ) :
    dotAcc a0 X Y n = a0 + ∑ s ∈ Finset.range n, X.getD s 0 * Y.getD s 0 := by
  induction n with
  | zero => simp [dotAcc]
  | succ n ih => rw [dotAcc, ih, Finset.sum_range_succ, add_assoc]

/-- (+) **A leaf's `free` term is `0`**: `lcVf` is `0`, so a leaf's (ii) is the 3.15 walk. -/
theorem lcFree_leaf (h : κ.isNode = false) : lcFree impl κ inp fi r = 0 := by
  simp [lcFree, lcVf, h]

/-- **A.9's `finLc` relation** over the register values (revision 3.16): (i) `c₀ = â + α b̂`,
(iii) `Σ_{i<8} β^i v_i = α₂`, (ii) `c_Lc = walk + (1 + α)·lcFree` (as `Y + α Y`). -/
def relLc : Bool :=
  let α := fv r ((outsOf fi "L1").headD 0); let β := fv r ((outsOf fi "L3β").headD 0)
  let v := lcV inp
  let vβ := (v.reverse.drop 1).foldl (fun acc x => x + β * acc) (v.getD 7 0)
  let y := lcFree impl κ inp fi r
  ((Val.f (pe inp fZend 0 + α * pe inp fZend 16)).eqv (rd r (claim0 fi "L2")) &&
    (Val.f vβ).eqv (rd r (fi.zhat.getD 1 0))) &&
  (Val.f (lcWalk impl κ inp fi r + (y + α * y))).eqv (rd r (claimN fi "L2"))

theorem map_rd_app' (R : Array Val) (hR : ∀ i < r.size, ∀ L : List Val, rd (R ++ L.toArray) i = rd r i)
    (L : List Val) (xs : List Reg) (h : ∀ x ∈ xs, x < r.size) :
    xs.map (fun x => (rd (R ++ L.toArray) x).toF) = xs.map (fv r) :=
  List.map_congr_left fun x hx => by rw [hR x (h x hx)]

set_option maxRecDepth 4096 in
/-- **`flag_finLc`**: `finLc` asks nothing, and its flag is A.9's relation `relLc` (revision 3.16). -/
theorem flag_finLc (hin : ∀ x ∈ (chals fi "Z3" 26).take 8 ++ chals fi "L2" 14 ++
      [(outsOf fi "L1").headD 0, (outsOf fi "L3β").headD 0, (outsOf fi "Z2").headD 0,
       claim0 fi "L2", claimN fi "L2", fi.zhat.getD 1 0], x < r.size) :
    ∃ L, pureRun impl κ inp (finLc fi r.size).1 r [] = some (L, relLc impl κ inp fi r) := by
  simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hin
  have h1 := fun L => map_rd_app r L ((chals fi "Z3" 26).take 8) fun x hx => hin x (.inl (.inl hx))
  have h2 := fun L => map_rd_app r L (chals fi "L2" 14) fun x hx => hin x (.inl (.inr hx))
  have h2a := fun L => map_rd_app r L ((chals fi "L2" 14).take 6)
    fun x hx => hin x (.inl (.inr (List.mem_of_mem_take hx)))
  have tf : ∀ x, (Val.f x).toF = x := fun _ => rfl
  have taf : ∀ x, (Val.af x).toAF = x := fun _ => rfl
  have ha := hin _ (.inr (.inl rfl)); have hb := hin _ (.inr (.inr (.inl rfl)))
  have hl := hin _ (.inr (.inr (.inr (.inl rfl))))
  have hc0 := hin _ (.inr (.inr (.inr (.inr (.inl rfl)))))
  have hcN := hin _ (.inr (.inr (.inr (.inr (.inr (.inl rfl))))))
  have hz := hin _ (.inr (.inr (.inr (.inr (.inr (.inr rfl))))))
  -- the head: registers `b … b + 40`
  obtain ⟨V1, f1, hA, hlen, hf1, g4, g14, g22, g37, g38, g40⟩ : ∃ V1 f1,
      pureRun impl κ inp (lcHead fi r.size) r [] = some (V1, f1) ∧ V1.length = 41 ∧
      f1 = ((Val.f (pe inp fZend 0 + fv r ((outsOf fi "L1").headD 0) * pe inp fZend 16)).eqv
          (rd r (claim0 fi "L2")) &&
        (Val.f (((lcV inp).reverse.drop 1).foldl
          (fun acc x => x + fv r ((outsOf fi "L3β").headD 0) * acc) ((lcV inp).getD 7 0))).eqv
          (rd r (fi.zhat.getD 1 0))) ∧
      V1.getD 4 default = .af (lcRhi fi r) ∧ V1.getD 14 default = .f 0 ∧
      V1.getD 22 default = .f (lcWalk impl κ inp fi r) ∧ V1.getD 37 default = .f (lcVf κ inp) ∧
      V1.getD 38 default = .af (impl.eqZ (fv r ((outsOf fi "Z2").headD 0)) 0) ∧
      V1.getD 40 default = .af (eqTab (((chals fi "L2" 14).take 6).map (fv r)).toArray) := by
    cases hk : κ.isNode
    all_goals
      apply Exists.intro
      apply Exists.intro
      refine ⟨?run, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      case run =>
        simp only [lcHead, hk, pureRun, evalOp, tf, taf, List.nil_append, List.cons_append, h1, h2,
            h2a, hornerOps, rd_app, rd_app0, rd_app_left _ _ ha, rd_app_left _ _ hb,
            rd_app_left _ _ hl, rd_app_left _ _ hc0, rd_app_left _ _ hz, List.range_succ,
            List.range_zero, List.map_cons, List.map_nil, List.map_append,
            List.getD_cons_succ, List.getD_cons_zero,
            Option.getD_some, Option.map_some, allK, Bool.not_true, Bool.false_or, Bool.true_and,
            Bool.and_true, List.take_succ_cons, List.take_zero, List.replicate_succ,
            List.replicate_zero, ite_true, ite_false, Bool.false_eq_true, List.flatMap_append,
            List.flatMap_cons, List.flatMap_nil, ↓reduceIte, Nat.reduceEqDiff, Nat.reduceAdd,
            Nat.reduceMul, Nat.reduceSub]
        rfl
      all_goals
        try simp only [lcWalk, lcV, lcRhi, lcRk, lcVf, nodeKindW, hk, ite_true, ite_false,
          Bool.false_eq_true, List.range_succ, List.range_zero, List.map_cons, List.map_nil,
          List.map_append, List.nil_append, List.cons_append, List.getD_cons_succ,
          List.getD_cons_zero, List.take_succ_cons, List.take_zero, List.headD_cons,
          List.replicate_succ, List.replicate_zero, List.length_cons, List.length_nil,
          List.reverse_cons, List.reverse_nil, List.drop_succ_cons, List.drop_zero,
          List.foldl_cons, List.foldl_nil, List.getD_eq_getElem?_getD, List.getElem?_cons_succ,
          List.getElem?_cons_zero, Option.getD_some, Nat.reduceMul, Nat.reduceAdd]
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
      some (V3, (Val.f (lcWalk impl κ inp fi r + (lcFree impl κ inp fi r +
        fv r ((outsOf fi "L1").headD 0) * lcFree impl κ inp fi r))).eqv (rd r (claimN fi "L2"))) := by
    simp only [lcTail, pureRun, evalOp, tf, taf, List.nil_append, List.cons_append, h2b, rd_app,
      rd_app0, rv 4 (by norm_num), rv 22 (by norm_num), rv 37 (by norm_num), rs, g4, g22, g37,
      rr _ ha, rr _ hb, rr _ hcN, List.getD_cons_succ, List.getD_cons_zero, Option.map_some,
      allK, Bool.not_true, Bool.false_or, Bool.true_and, Bool.and_true]
    exact ⟨_, rfl⟩
  have e : (finLc fi r.size).1 =
      (lcHead fi r.size ++ dotOps (r.size + 38) (r.size + 40) (r.size + 14) (r.size + 41) 64) ++
        lcTail fi r.size R2.size := by rw [hR2]; rfl
  rw [e, pureRun_seq impl κ inp (pureRun_seq impl κ inp hA hD) hC, hf1]
  exact ⟨_, by simp only [relLc, Bool.and_true]; rfl⟩

/-- The link families' sum `acc + Σ_f κ_s^(f+2) W_f` (as `linkOps`; `W` is `linkWAll`'s array). -/
def linkSum (W : Array F) (ks : F) : ℕ → F → F → F
  | 0, acc, _ => acc
  | n + 1, acc, pow => linkSum W ks n (acc + pow * W.getD (nLinkFam - (n + 1)) 0) (pow * ks)

/-- **A.9's `finSh` relation** over the register values (revision 3.14: a node's weights are the
chain-masked `shiftMask`, its In slot map 2, its link families `linkWAll`'s; revision 3.15: `τ`,
`r_blk` of 18 coordinates, zero-padded, and `bnd`'s last block). -/
def relSh : Bool :=
  let co := coordsR fi "S1"; let rs := chals fi "S2" 28; let ks := fv r (co.getD 28 0)
  let τ := ((co.take (κ.m - 14)).map (fv r) ++ List.replicate (32 - κ.m) 0).toArray
  let θ := (((co.drop 18).take 10).map (fv r)).toArray
  let rb := ((rs.take (κ.m - 14)).map (fv r) ++ List.replicate (32 - κ.m) 0).toArray
  let rp := (((rs.drop (κ.m - 14)).take 10).map (fv r)).toArray
  let tt := ((co.take (κ.m - 14) ++ (co.drop 18).take 10).map (fv r)).toArray
  let rr := ((rs.take (κ.m - 14) ++ (rs.drop (κ.m - 14)).take 10).map (fv r)).toArray
  let sm := impl.shiftMask τ rb
  let e := if κ.isNode then sm.1 else eqPoint τ rb
  let sh := if κ.isNode then sm.2.1 else impl.shiftEq τ rb
  let e0 := if κ.isNode then sm.2.2 else eqPoint (Array.replicate 18 0) rb
  let sIn := if κ.isNode then impl.slotW κ 2 θ rp else impl.slotW κ 1 θ rp
  let wout := e * impl.slotW κ 0 θ rp
  let win := linkSum (impl.linkWAll κ tt rr) ks nLinkFam ((sh + ks * e0) * sIn) (ks * ks)
  let bnd : Array F := ((if κ.isNode then [0, 0, 0, 0]
    else [pe inp fHdr 16, pe inp fHdr 32, pe inp fStmt 1, pe inp fStmt 17]) ++
    (List.replicate (κ.m - 14) 1 ++ List.replicate (32 - κ.m) 0)).toArray
  (Val.f (impl.shiftTarget ks τ θ bnd)).eqv (rd r (claim0 fi "S2")) &&
  (Val.f ((wout + win) * fv r (fi.zhat.getD 2 0))).eqv
    (rd r (claimN fi "S2"))

set_option maxRecDepth 8192 in
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
  have h5 := fun L => map_rd_app r L ((coordsR fi "S1").take (κ.m - 14) ++
    ((coordsR fi "S1").drop 18).take 10) fun x hx => by
      rcases List.mem_append.1 hx with hx | hx
      · exact hco x (List.mem_of_mem_take hx)
      · exact hco x (List.mem_of_mem_drop (List.mem_of_mem_take hx))
  have h6 := fun L => map_rd_app r L ((chals fi "S2" 28).take (κ.m - 14) ++
    ((chals fi "S2" 28).drop (κ.m - 14)).take 10) fun x hx => by
      rcases List.mem_append.1 hx with hx | hx
      · exact hrs x (List.mem_of_mem_take hx)
      · exact hrs x (List.mem_of_mem_drop (List.mem_of_mem_take hx))
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
    pureRun, evalOp, tf, taf, List.nil_append, List.cons_append, h1, h2, h3, h4, h5, h6, linkOps,
    padB, List.map_append, List.map_replicate,
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
