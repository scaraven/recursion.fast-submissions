-- New for `flock-recursive` (BLUEPRINT §10 changes 27 (B) step 4; stage RET-3): the declarations of
-- the 3.x verifier-shape modules that the revision 4 certificate reads, moved here verbatim (same
-- names, statements and proofs) from `FRVIRFinals` (56), `FRVIRFinalsSF` (32). Content: the phase-
-- final checks revision 4 reads: `Finals`, `pureRun`, `finZ`, `finLc`, `finSh`, `finLr`, `finRS`,
-- `finE`, `finB'` (definitions over `OpImpl`) and their run lemmas. The 3.x modules import this
-- one.
import FRSkip
import FRVIRSpecCore

/-! ## From `FRVIRFinals` (56 declarations) -/

section

namespace FR

open RecursionFast

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
      ([.getF x n, .getF y n, .mulF (c + 4 * n) (c + 4 * n + 1),
       .addF (if n = 0 then z else c + 4 * n - 1) (c + 4 * n + 2)] : List Op)

/-- The values `dotOps` appends. -/
def dotVals (a0 : F) (X Y : Array F) : ℕ → List Val
  | 0 => []
  | n + 1 => dotVals a0 X Y n ++ ([.f (X.getD n 0), .f (Y.getD n 0), .f (X.getD n 0 * Y.getD n 0),
      .f (dotAcc a0 X Y (n + 1))] : List Val)

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

/-- `finLr`'s place in `FinIn.ex` (run order: `finRS` 0, then `rest`: `finZ`, `finLc`, `finSh`,
`finLr`). -/
def exLr : ℕ := 4

/-- `finLr`'s exports as `finE` sees them: `v_L` (index 0) and the point `r_Lr` (index 1). -/
def lrEx (fi : FinIn) (j : ℕ) : Reg := (fi.ex.getD exLr []).getD j 0

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
   ([.packFK (fun κ => [b, b + 1, b + 2, b + 3, b + 4, b + 5, b + 6] ++ co.take (κ.m - 13)),
    .packFK (fun κ => rs.take (κ.m - 6)), .eqPt (b + 7) (b + 8),
    .piElem fZend 0, .piElem fZend 16, .mulF (b + 9) (b + 10), .mulF (b + 12) (b + 11),
    .assertEq (b + 13) (claimN fi "Z3") allK,
    .assertEq ((outsOf fi "Z2").getD 2 0) (fi.zhat.getD 0 0) allK] : List Op),
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
  ([.piElem fZend 0, .piElem fZend 16, .mulF α (b + 1), .addF b (b + 2),
    .assertEq (b + 3) (claim0 fi "L2") allK,
    .packFK (fun _ => (chals fi "Z3" 26).take 8),
    .rowW ((outsOf fi "Z2").headD 0) (b + 4)] : List Op) ++
   ((List.range 8).map (fun i => .piElem fL2 (oL3 + 16 * i)) : List Op) ++
   ([.const (fun _ => .f 0),
    .packFK (fun κ => if κ.isNode then (b + 14) :: (v.take 7 ++ [b + 14])
      else (b + 6) :: List.replicate 8 (b + 14)),
    .maskRows (b + 15) (b + 5), .packF (chals fi "L2" 14), .eqTable (b + 17),
    .walkAB (b + 16) (b + 18), .mulF α (b + 20), .addF (b + 19) (b + 21)] : List Op) ++
   hornerOps β b ++
   ([.assertEq (b + 36) (fi.zhat.getD 1 0) allK,
    .keep Kind.isNode (b + 13) (b + 14), .eqZ ((outsOf fi "Z2").headD 0) (b + 14),
    .packF ((chals fi "L2" 14).take 6), .eqTable (b + 39)] : List Op)

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
   ([.packFK (fun κ => padB κ co (b₀ + 4)), .packF ((co.drop 18).take 10),
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
    .linkWAll (b + 23) (b + 24), .mulF ks ks] : List Op) ++
   linkOps ks b ++
   ([.addF (b + 16) (b + 57), .mulF (b + 59) (fi.zhat.getD 2 0),
    .assertEq (b + 60) (claimN fi "S2") allK] : List Op),
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

/-- The link families' sum `acc + Σ_f κ_s^(f+2) W_f` (as `linkOps`; `W` is `linkWAll`'s array). -/
def linkSum (W : Array F) (ks : F) : ℕ → F → F → F
  | 0, acc, _ => acc
  | n + 1, acc, pow => linkSum W ks n (acc + pow * W.getD (nLinkFam - (n + 1)) 0) (pow * ks)

/-- **A.9's `finLr` relation** (node only, revision 3.13: the end check (ii)) over the register
values. -/
def relLr : Bool :=
  let rLr := (((coordsR fi "Lr1").take 15).map (fv r)).toArray
  let rr := ((chals fi "Lr2" 15).map (fv r)).toArray
  let a := pe inp fLrEnd 0; let bb := pe inp fLrEnd 16; let c := pe inp fLrEnd 32
  if κ.isNode then (Val.f (eqPoint rLr rr * (a * bb + c))).eqv (rd r (claimN fi "Lr2")) else true

end Flags

end FR

end

/-! ## From `FRVIRFinalsSF` (32 declarations) -/

section

namespace FR

open RecursionFast

section Kit

variable (impl : OpImpl) (κ : Kind) (inp : Input) (r : Array Val)

/-- One op appending one value with no assertion. -/
theorem pr_op {op : Op} {ops : List Op} {L : List Val} {v : Val}
    (h : evalOp impl κ inp (r ++ L.toArray) op = .vals [v] true) :
    pureRun impl κ inp (op :: ops) r L = pureRun impl κ inp ops r (L ++ [v]) := by
  simp only [pureRun, h, Bool.true_and]; cases pureRun impl κ inp ops r (L ++ [v]) <;> rfl

theorem rd_pre {L M : List Val} {x : ℕ} (h : x < r.size + L.length) :
    rd (r ++ (L ++ M).toArray) x = rd (r ++ L.toArray) x := by
  rw [← app_app]; exact rd_append_left (by simpa using h)

theorem rd_new (L : List Val) (v : Val) (M : List Val) :
    rd (r ++ (L ++ v :: M).toArray) (r.size + L.length) = v := by
  rw [rd_app]; simp

theorem rd_new1 (L : List Val) (v : Val) : rd (r ++ (L ++ [v]).toArray) (r.size + L.length) = v :=
  rd_new r L v []

end Kit

/-- The packing basis element of index `i` (`bitBasis`, A.7). -/
def bb (i : ℕ) : F := bitBasis ⟨i % 128, Nat.mod_lt _ (by decide)⟩

/-- Slice value `i` of RS claim `j` (RS0's message: claim-major, 16 bytes each). -/
def rsOff (j i : ℕ) : ℕ := 16 * (128 * j + i)

/-- One slice value of claim `j` (8 registers): `s`, its inner weight `c` (`wop i`), `c·s` into the
claim value, `Φ_{r″}(s)` (`phiRS`, `r″` in register `R`), `bitBasis i · Φ(s)` into the switched
claim. -/
def elemOps (j i : ℕ) (wop : ℕ → Op) (R aA aT b : ℕ) : List Op :=
  [.piElem fRS0 (rsOff j i), wop i, .mulF (b + 1) b, .addF aA (b + 2), .phiRS R b,
   .const (fun _ => .f (bb i)), .mulF (b + 5) (b + 4), .addF aT (b + 6)]

/-- The width of `elemOps`. -/
def elemW : ℕ := 8

/-- Slice values `i … i + n − 1` of claim `j`. -/
def elemsOps (j : ℕ) (wop : ℕ → Op) (R : Reg) : ℕ → ℕ → Reg → Reg → ℕ → List Op
  | 0, _, _, _, _ => []
  | n + 1, i, aA, aT, b =>
    elemOps j i wop R aA aT b ++ elemsOps j wop R n (i + 1) (b + 3) (b + elemW - 1) (b + elemW)

/-- The skip node `x_j` (`S` is the first 64 nodes). -/
def xS (j : ℕ) : F := skipNode ⟨j % 128, Nat.mod_lt _ (by decide)⟩

section Run

variable (impl : OpImpl) (κ : Kind) (inp : Input) (r : Array Val)

theorem pr_app {o₁ o₂ : List Op} {L M : List Val}
    (h : pureRun impl κ inp o₁ r L = some (L ++ M, true)) :
    pureRun impl κ inp (o₁ ++ o₂) r L = pureRun impl κ inp o₂ r (L ++ M) := by
  rw [pureRun_append, h, Option.bind_some]; cases pureRun impl κ inp o₂ r (L ++ M) <;> simp

theorem pr_app' {o₁ o₂ : List Op} {L L' : List Val}
    (h : pureRun impl κ inp o₁ r L = some (L', true)) :
    pureRun impl κ inp (o₁ ++ o₂) r L = pureRun impl κ inp o₂ r L' := by
  rw [pureRun_append, h, Option.bind_some]; cases pureRun impl κ inp o₂ r L' <;> simp

theorem rdX (L X : List Val) (t : ℕ) :
    rd (r ++ (L ++ X).toArray) (r.size + L.length + t) = X.getD t default := by
  rw [Nat.add_assoc, rd_app]; simp [List.getElem?_append_right]

theorem rdL {L X : List Val} {y : ℕ} (h : y < r.size + L.length) :
    rd (r ++ (L ++ X).toArray) y = rd (r ++ L.toArray) y := rd_pre r h

theorem rdX0 (L X : List Val) : rd (r ++ (L ++ X).toArray) (r.size + L.length) = X.getD 0 default := by
  simpa using rdX r L X 0

/-- One claim: a zero, then its 128 slice values (width `1 + 128 · elemW`). -/
def claimOps (j : ℕ) (wop : ℕ → Op) (R : Reg) (b : ℕ) : List Op :=
  .const (fun _ => .f 0) :: elemsOps j wop R 128 0 b b (b + 1)

end Run

/-- `v_RS` by Horner in `κ` from the switched claims `T₀ … T₃` (registers `t₀ … t₃`; a leaf's
`T₃` replaced by `0`), from register `d`; then a leaf's zero check of claim 3's slice values
(revision 3.13: claim 3 is E4's `f̂(r′)`, node only). -/
def rsTail (kap t₀ t₁ t₂ t₃ d : ℕ) : List Op :=
  [.const (fun _ => .f 0), .addF t₃ d, .keep Kind.isNode (d + 1) d,
   .mulF kap (d + 2), .addF t₂ (d + 3), .mulF kap (d + 4), .addF t₁ (d + 5), .mulF kap (d + 6),
   .addF t₀ (d + 7), .piField fRS0 (rsOff 3 0) 2048, .assertZero (d + 9) (fun κ => !κ.isNode)]

/-- RS1's `r″ = f₀ … f₆` (coordinates 0–6). -/
def rsFsRegs (fi : FinIn) : List Reg := (List.range 7).map fun p => (coordsR fi "RS1").getD p 0

/-- **`finRS`** (A.9 revisions 3.9, 3.13, `J_z = 4`): the claim values `α_Z, α_Lc, α_Sh, α_E` and
`v_RS` (exports, in this order). Registers from `b`: `ρ₁` (A.1's first pinned coordinate),
`eqZ λ ρ₁`, the two `eq` tables (Lc, Sh) after their points, `r″`; the claims from `b + 7`,
`1 + 128 · 8` each (claim 3, E4's `f̂(r′)`, weighted by the packing basis `bb i`: `f̂(r′) =
Σ_i b_i s_{3,i}`); then `rsTail`. -/
def finRS : FinField := fun fi b =>
  let kap := (coordsR fi "RS1").getD 7 0
  let lam := (outsOf fi "Z2").headD 0
  let c₀ := b + 7
  let cw := 1 + 128 * elemW
  let d := c₀ + 4 * cw
  (([.const (fun _ => .f (pinnedRho 0)), .eqZ lam b,
    .packF ((chals fi "L2" 14).take 7), .eqTable (b + 2),
    .packFK (fun κ => ((chals fi "S2" 28).drop (κ.m - 14)).take 7), .eqTable (b + 4),
    .packF (rsFsRegs fi)] : List Op) ++
   claimOps 0 (fun i => .getF (b + 1) i) (b + 6) c₀ ++
   claimOps 1 (fun i => .getF (b + 3) i) (b + 6) (c₀ + cw) ++
   claimOps 2 (fun i => .getF (b + 5) i) (b + 6) (c₀ + 2 * cw) ++
   claimOps 3 (fun i => .const (fun _ => .f (bb i))) (b + 6) (c₀ + 3 * cw) ++
   rsTail kap (c₀ + cw - 1) (c₀ + 2 * cw - 1) (c₀ + 3 * cw - 1) (c₀ + 4 * cw - 1) d,
   (List.range 4).map (fun j => c₀ + j * cw + 127 * elemW + 4) ++ [d + 8])

/-- `finRS`'s export index of `v_RS` (after the `J_z = 4` claim values). -/
def nRS : ℕ := 4

section RS

variable (impl : OpImpl) (κ : Kind) (inp : Input) (fi : FinIn) (r : Array Val)

/-- The F values of registers, as an array. -/
def ptF (xs : List Reg) : Array F := (xs.map (fv r)).toArray

end RS

/-- E4 end's message (`f̂(r′) ‖ 0^16`, 32 bytes) inside the E field (A.3 row 9: after E2's and
E4's rounds). -/
def oE4end : ℕ := phaseOff (phaseIx "E4end") fE

/-- **`finE`** (A.9 revision 3.13; checks (ii)–(iv) node only): `â_M, b̂_M, ĉ_M` from the E-end
absorb (A.3 row 9′); (ii) `c_{E2} = eq(r_E, r_{E2})·(â_M b̂_M + ĉ_M)` (`r_E` E1's 21 coordinates,
`r_{E2}` E2's challenges); (iii) `c₀^{E4} = â_M + κ_E b̂_M + κ_E² ĉ_M + κ_E³ v_L`, binding the
lincheck's free initial claim (`v_L`, `r_Lr`: `finLr`'s exports, `lrEx`); (iv) `c_{E4} = (W_M +
κ_E³ W_L)·f̂(r′)` with `W_M = (Ã_M + κ_E B̃_M + κ_E² C̃_M)(r_{E2}, r′)` (`evalM`) and `W_L = (Ã_L +
κ_L B̃_L + κ_L² C̃_L)(r_Lr, r′)` (`evalL`), both at the F point `r′` (E4's 23 challenges: every
cell coordinate, S-G1j defect 2), `f̂(r′)` RS claim 4 (`zhat` 3); (v) E4 end's absorbed value is
`f̂(r′)` and its last 16 bytes are zero (every kind: a leaf's claim-4 slices are zero, so its
message must be). `c₀^{E2} = 0`
holds by `initClaim`. Exports the point `r′`. -/
def finE : FinField := fun fi b =>
  let kE := (outsOf fi "E3").headD 0
  let kL := (outsOf fi "Lr3").headD 0
  let fz := fi.zhat.getD 3 0
  ([.piElem fEEnd 0, .piElem fEEnd 16, .piElem fEEnd 32,
    .packF ((coordsR fi "E1").take 21), .packF (chals fi "E2" 21), .eqPt (b + 3) (b + 4),
    .mulF b (b + 1), .addF (b + 6) (b + 2), .mulF (b + 5) (b + 7),
    .assertEq (b + 8) (claimN fi "E2") Kind.isNode,
    .mulF kE (b + 1), .mulF kE kE, .mulF (b + 10) (b + 2), .addF b (b + 9), .addF (b + 12) (b + 11),
    .mulF (b + 10) kE, .mulF (b + 14) (lrEx fi 0), .addF (b + 13) (b + 15),
    .assertEq (b + 16) (claim0 fi "E4") Kind.isNode,
    .packF (chals fi "E4" 23), .evalM (b + 4) (b + 17), .mulF kE (b + 19), .mulF (b + 10) (b + 20),
    .addF (b + 18) (b + 21), .addF (b + 23) (b + 22),
    .evalL (lrEx fi 1) (b + 17), .mulF kL (b + 26), .mulF kL kL, .mulF (b + 29) (b + 27),
    .addF (b + 25) (b + 28), .addF (b + 31) (b + 30),
    .mulF (b + 14) (b + 32), .addF (b + 24) (b + 33), .mulF (b + 34) fz,
    .assertEq (b + 35) (claimN fi "E4") Kind.isNode,
    .piElem fE oE4end, .assertEq (b + 36) fz allK, .piField fE (oE4end + 16) 16,
    .assertZero (b + 37) allK],
   [b + 17])

/-- The F halves of a digest (`splitDigest`). -/
def dLo (x : Digest) : F := F.ofBytes (Vector.ofFn fun i : Fin 16 => x[i.1])

def dHi (x : Digest) : F := F.ofBytes (Vector.ofFn fun i : Fin 16 => x[16 + i.1])

/-- **`finB′`** (A.9, revisions 3.6, 3.12): `v* = v_RS + Σ_k κ′^(k+2) pub_k` equals P1.0's initial
claim (in `K`); E is batched into `v_RS` as RS claim 4 (3.13), so `v*` has no `v_E` term
(stage-review changes 18). A node's public point claims, in order: M's `one` cell `1`; slot 0's
`vk`, `c₁`; slot 1's `vk`, `c₂` (each digest as its two halves): nine cells, `J_f = 9`, no padding
cells (revision 3.14). A leaf kind has none (`keep`). `v_RS` is `finRS`'s export `nRS`. Exports `v*`. -/
def finB' : FinField := fun fi b =>
  let kp := (outsOf fi "B'").headD 0
  let vRS := fi.zhat.getD nRS 0
  ([.input 0, .splitDigest b, .piDigest fStmt 1, .splitDigest (b + 3), .piDigest fStmt 33,
    .splitDigest (b + 6), .const (fun _ => .f 1),
    .mulF kp (b + 8), .addF (b + 7) (b + 10), .mulF kp (b + 11), .addF (b + 2) (b + 12),
    .mulF kp (b + 13), .addF (b + 1) (b + 14), .mulF kp (b + 15), .addF (b + 5) (b + 16),
    .mulF kp (b + 17), .addF (b + 4) (b + 18), .mulF kp (b + 19), .addF (b + 2) (b + 20),
    .mulF kp (b + 21), .addF (b + 1) (b + 22), .mulF kp (b + 23), .addF (b + 9) (b + 24),
    .mulF kp kp, .mulF (b + 26) (b + 25), .const (fun _ => .f 0), .keep Kind.isNode (b + 27) (b + 28),
    .addF vRS (b + 29),
    .const (fun _ => .k 1), .mulKF (b + 31) (b + 30), .assertEq (b + 32) (claim0 fi "P1") allK],
   [b + 30])

section EB

variable (impl : OpImpl) (κ : Kind) (inp : Input) (fi : FinIn) (r : Array Val)

/-- The public point claims' Horner sum `Σ_k κ′^k pub_k` (A.9 `finB′`, the order of `finB'`). -/
def pubH (kp : F) : F :=
  let vl := dLo inp.vk; let vh := dHi inp.vk
  let c₁ := bytesAt inp.π (absOff fStmt 1) 32; let c₂ := bytesAt inp.π (absOff fStmt 33) 32
  1 + kp * (vl + kp * (vh + kp * (dLo c₁ + kp * (dHi c₁ + kp * (vl + kp * (vh + kp * (dLo c₂ +
    kp * dHi c₂)))))))

/-- **`v*`** (A.9 `finB′`) from the register values of `κ′` and `v_RS`. -/
def vStar : F :=
  let kp := fv r ((outsOf fi "B'").headD 0)
  fv r (fi.zhat.getD nRS 0) + (if κ.isNode then kp * kp * pubH inp kp else 0)

/-- **A.9's `finB′` relation**: `v*` (in `K`) is P1.0's initial claim. -/
def relB : Bool := (Val.k (K.smulF (vStar κ inp fi r) 1)).eqv (rd r (claim0 fi "P1"))

end EB

theorem noAsk_elemsOps (j : ℕ) (wop : ℕ → Op) (hw : ∀ i, (wop i).item? = none) (R : ℕ) :
    ∀ n i aA aT b, (elemsOps j wop R n i aA aT b).filterMap Op.item? = []
  | 0, _, _, _, _ => rfl
  | n + 1, i, aA, aT, b => by
    simp only [elemsOps, elemOps, List.filterMap_append, List.filterMap_cons, hw i,
      noAsk_elemsOps j wop hw R n, List.filterMap_nil, List.append_nil]
    rfl

theorem noAsk_claimOps (j : ℕ) (wop : ℕ → Op) (hw : ∀ i, (wop i).item? = none) (R b : ℕ) :
    (claimOps j wop R b).filterMap Op.item? = [] := by
  simp only [claimOps, List.filterMap_cons, noAsk_elemsOps j wop hw]; rfl

/-- **The finals with S-0's and S-F's fields**; S-G's `finP`, `finPf` as arguments. -/
def sfFinals (p : ℕ → FinField) (pf : FinField) : Finals := s0Finals finRS finE finB' p pf

end FR

end
