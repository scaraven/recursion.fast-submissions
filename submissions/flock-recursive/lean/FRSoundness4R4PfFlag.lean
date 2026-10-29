-- New for `flock-recursive` (BLUEPRINT revision 4.1, A.9 `finPf`; revision 4.3's uniform `finPf`,
-- INT-8; track R4h). The 3.x template is `FRVIRFinalsSG.flag_finPf`.
import FRSoundness4R4PfRun

/-!
# The flag of INT-8's relocated `finPf` (`flag_gFinPf4`)

For a fixed-kind program (`Q := fun _ => P`) with kind-table cells (`P.ck`), the relocated
`gFinPf P` asks nothing and its flag is **`relPf4`**: `claimN(Pf) = Ŵ₄(P₄)·pad·final̂(sf)`, with

* the kind's points by the tables: slot `s` (tails `P₁ … P₄`, then `P₀`) is point `slotIx P κ s` of
  `gPfPts` (`m*`'s if `selA`, else family `famI`'s);
* `Ŵ₀(P₀) = rsWeight(r″, the kind's claim points (ptIx), κ, β, P₀)` plus, on a node, the cells' sum
  over `nc` coordinates (`w0V4`); the four level steps are 3.x's `lvsV` (`wV4`);
* the kind's pad (`padV4`: `1` for `m*`, else its family's `padF4`) and `final̂` over the relocated
  final elements (`finHat4`);

and the tails' flag `tailOk4` (the final message's exact zero tail of the kind).
-/

namespace FR.Snd.R4
open RecursionFast Rev4 Finset

/-! ## The kind's points -/

/-- Family `i`'s candidate point for slot `s` (`pfCand`'s index into `gPfPts`). -/
def candIx (P : FinP) (i s : ℕ) : ℕ :=
  if s < 4 then 7 + 3 * P.fams.length + P.e4s.length + 4 * i + s else 8 + 7 * P.fams.length + P.e4s.length + i

/-- The `m*` family's (`pfCandA`'s index). -/
def candAIx (P : FinP) (s : ℕ) : ℕ :=
  if s < 4 then 3 + 3 * P.fams.length + P.e4s.length + s else 7 + 7 * P.fams.length + P.e4s.length

/-- The kind's family among `fams` (the one `selOps` leaves). -/
def famI (P : FinP) (κ : Kind) : ℕ := selI (fun i => decide (P.kv.fsel κ = i)) (P.fams.length - 1)

/-- **Slot `s`'s point** (tails `s < 4`, `P₀` at `4`) for kind `κ`. -/
def slotIx (P : FinP) (κ : Kind) (s : ℕ) : ℕ := if P.kv.selA κ then candAIx P s else candIx P (famI P κ) s

theorem pfCand_eq (P : FinP) (Pp : ℕ → ℕ) (i s : ℕ) : pfCand P Pp i s = Pp (candIx P i s) := by
  unfold pfCand candIx; split_ifs <;> rfl

theorem pfCandA_eq (P : FinP) (Pp : ℕ → ℕ) (s : ℕ) : pfCandA P Pp s = Pp (candAIx P s) := by
  unfold pfCandA candAIx; split_ifs <;> rfl

theorem gPfPts_length (P : FinP) (fi : FinIn) :
    (gPfPts P fi).length = 8 + 8 * P.fams.length + P.e4s.length := by
  simp only [gPfPts, List.length_append, List.length_cons, List.length_nil, List.length_map,
    List.length_range, List.length_flatMap]
  simp only [List.map_const', List.sum_replicate, smul_eq_mul]
  ring

theorem candIx_lt (P : FinP) (fi : FinIn) {i : ℕ} (hi : i < P.fams.length) (s : ℕ) :
    candIx P i s < (gPfPts P fi).length := by
  rw [gPfPts_length, candIx]; split_ifs <;> omega

theorem candAIx_lt (P : FinP) (fi : FinIn) (s : ℕ) : candAIx P s < (gPfPts P fi).length := by
  rw [gPfPts_length, candAIx]; split_ifs <;> omega

theorem famI_lt (P : FinP) (κ : Kind) (hnf : 0 < P.fams.length) : famI P κ < P.fams.length :=
  lt_of_le_of_lt (selI_le _ _) (by omega)

theorem slotIx_lt (P : FinP) (κ : Kind) (fi : FinIn) (hnf : 0 < P.fams.length) (s : ℕ) :
    slotIx P κ s < (gPfPts P fi).length := by
  unfold slotIx; split_ifs
  · exact candAIx_lt P fi s
  · exact candIx_lt P fi (famI_lt P κ hnf) s

/-! ## The relocated op list -/

/-- **INT-8's `finPf` relocated** (fixed kind, `ck`): `gFinPf`'s blocks, the final message's reads
(`fhOps`, `gTailOps`) relocated to `P.S`'s format. -/
def gFinPfR (P : FinP) (fi : FinIn) (b : ℕ) : List Op :=
  let S := P.S; let nc := P.nc; let nf := P.fams.length
  let one := b
  let cu := b + 1
  let z0 := b + 2
  let pts := gPfPts P fi
  let Pp := ptsOut pts (b + 3)
  let pb := b + 3 + ptsW pts
  let sb := pb + 5 * (nf - 1)
  let wb := sb + 5
  let rs1 := coordsR fi "RS1"
  let kp := (outsOf fi "B'").headD 0
  let cb := wb + (2 + 2 * nc)
  let c9 := cb + 1 + (2 * nc + 3) * P.ncell
  let acc9 := gCellsAccK nc P.ncell z0 (cb + 1)
  let cr := c9 + (2 * nc + 3) * P.nrcell
  let ce := cond P.rsvOps (cr + 1) c9
  let lb := ce + 2
  let fb := lb + lvsW fi [1, 2, 3, 4]
  let pd := fb + 2 + 4 * 2 ^ S.pf
  let sf := chals fi "Pf" S.pf
  let pe := pd + (P.fams.map (padW S.pf)).sum
  let sel : ℕ → KC Bool := fun i κ => decide (P.kv.fsel κ = i)
  let selA : KC Bool := fun κ => P.kv.selA κ
  let node : KC Bool := fun κ => P.kv.node κ
  ([.const (fun _ => .k 1), .const (fun _ => .k (1 + K.u)), .const (fun _ => .k 0)] : List Op) ++
   ptsOps one z0 pts (b + 3) ++
   (List.range 5).flatMap (fun s => selOps sel (fun i => pfCand P Pp i s) nf (pb + s * (nf - 1))) ++
   (List.range 5).map (fun s =>
     .keep selA (pfCandA P Pp s) (selOut (fun i => pfCand P Pp i s) nf (pb + s * (nf - 1)))) ++
   ([.packF ((List.range 7).map fun p => rs1.getD p 0),
    .rsWeight wb (fun κ => (P.kv.ptIx κ).map Pp) (rs1.getD 7 0) ((outsOf fi "L3β").headD 0)
      node (sb + 4)] : List Op) ++
   ((List.range nc).map (fun v => .getK (sb + 4) v) : List Op) ++
   ((List.range nc).map (fun v => .addK one (wb + 2 + v)) : List Op) ++
   ([.mulF kp kp] : List Op) ++
   (gCellsOpsK nc one (wb + 2) (wb + (nc + 2)) kp (fun j _ => P.cells.getD j 0) P.ncell 0 z0 cb (cb + 1) ++
     cond P.rsvOps (gCellsOpsK nc one (wb + 2) (wb + (nc + 2)) kp (fun j _ => P.rcells.getD j 0)
       P.nrcell 0 acc9 (c9 - 1) c9 ++ [.keep (fun _ => P.rsv) (gCellsAccK nc P.nrcell acc9 c9) acc9]) []) ++
   ([.keep node (cond P.rsvOps cr acc9) z0, .addK (wb + 1) ce] : List Op) ++
   gLvsOps S fi one cu sb [1, 2, 3, 4] (ce + 1) lb ++
   ([.packK sf, .eqTableK fb] : List Op) ++ (fhOps (fb + 1) (List.range (2 ^ S.pf)) z0 (fb + 2)).map (reloc S) ++
   padsOps one sf S.pf P.fams pd ++
   selOps sel (padsReg one S.pf P.fams pd) nf pe ++
   ([.keep selA one (selOut (padsReg one S.pf P.fams pd) nf pe),
    .mulK (lvsOut fi [1, 2, 3, 4] (ce + 1) lb) (pe + (nf - 1)),
    .mulK (pe + nf) (fhOut (List.range (2 ^ S.pf)) z0 (fb + 2)),
    .assertEq (pe + nf + 1) (claimN fi "Pf") allK] : List Op) ++
   (gTailOps (fun _ => P) S.pf P.tails (pe + nf + 2)).map (reloc S)

theorem map_reloc_of (S : Seq) {l : List Op} (h : ∀ op ∈ l, reloc S op = op) : l.map (reloc S) = l := by
  conv_rhs => rw [← List.map_id l]
  exact List.map_congr_left h

theorem map_cond {α β : Type} (f : α → β) (c : Bool) (l l' : List α) :
    (cond c l l').map f = cond c (l.map f) (l'.map f) := by cases c <;> rfl

theorem gFinPf_reloc (P : FinP) (hck : P.ck = true) (fi : FinIn) (b : ℕ) :
    (gFinPf P fi b).1.map (reloc P.S) = gFinPfR P fi b := by
  delta gFinPfR
  simp only [gFinPf, hck, cond_true, List.map_append, map_cond, ptsOps_reloc, selOps_reloc,
    gCellsOpsK_reloc, gLvsOps_reloc, padsOps_reloc, List.map_flatMap]
  rw [map_reloc_of P.S (l := [.const (fun _ => .k 1), .const (fun _ => .k (1 + K.u)), .const (fun _ => .k 0)])
    (List.forall_mem_cons.2 ⟨rfl, List.forall_mem_cons.2 ⟨rfl, List.forall_mem_cons.2 ⟨rfl, fun _ h => absurd h (List.not_mem_nil)⟩⟩⟩)]
  simp only [List.map_map, List.map_cons, List.map_nil]
  rfl

/-! ## The relation -/

section Val
variable (impl : OpImpl) (κ : Kind) (inp : Input) (fi : FinIn) (r : Array Val) (P : FinP)

/-- Point `j` of `gPfPts`. -/
def ptPf (j : ℕ) : Array K := ptV r ((gPfPts P fi).getD j [])

/-- The kind's tail `Pₖ[1..]` (`k = 1 … 4`). -/
def tl4 (k : ℕ) : Array K := ptPf fi r P (slotIx P κ (k - 1))

/-- The kind's `P₀`. -/
def rho4 : Array K := ptPf fi r P (slotIx P κ 4)

/-- The `κ′` register's value. -/
def kp4 : F := fv r ((outsOf fi "B'").headD 0)

/-- The public cells' sum `Σ_{k < ncell} κ′^{k+2}·eq(cell_k, P₀)` (`finPf`'s first chain). -/
def cv4 : K := cellsVal4 P.nc (rho4 κ fi r P) (kp4 fi r) (fun j => P.cells.getD j 0) P.ncell 0
  (kp4 fi r * kp4 fi r) 0

/-- **`Ŵ₀(P₀)`** (INT-8's): `rsWeight` at the kind's claim points, and on a node the cells' sum; with
the reserve on (`rsvOps ∧ rsv`, revision 4.4.2) the second chain continues it over the reserve's
cells, `Σ_{i < nrcell} κ′^{2+ncell+i}·eq(rcell_i, P₀)`. -/
def w0V4 : K :=
  impl.rsWeight (ptF r ((List.range 7).map fun p => (coordsR fi "RS1").getD p 0))
      ((P.kv.ptIx κ).map (ptPf fi r P)) (fv r ((coordsR fi "RS1").getD 7 0))
      (if P.kv.node κ then fv r ((outsOf fi "L3β").headD 0) else 1) (rho4 κ fi r P) +
    (if P.kv.node κ then
      (if (P.rsvOps && P.rsv) = true then cellsVal4 P.nc (rho4 κ fi r P) (kp4 fi r)
        (fun j => P.rcells.getD j 0) P.nrcell 0 (kp4 fi r * kp4 fi r * kp4 fi r ^ P.ncell) (cv4 κ fi r P)
       else cv4 κ fi r P) else 0)

/-- **`Ŵ₄(P₄)`**: 3.x's four level steps at the kind's tails. -/
def wV4 : K := lvsV impl fi (rd r) (tl4 κ fi r P) [1, 2, 3, 4] (w0V4 impl κ fi r P)

/-- Pf's challenge `v`. -/
def sfv4 (v : ℕ) : K := (rd r ((chals fi "Pf" P.S.pf).getD v 0)).toK

/-- **The kind's pad**: `1` for `m*`, else its family's. -/
def padV4 : K := if P.kv.selA κ then 1 else padF4 (sfv4 fi r P) P.S.pf (P.fams.getD (famI P κ) 0)

/-- `final̂(sf)` over the relocated final elements. -/
def finHat4 : K :=
  fhVal4 P.S inp (eqTab ((chals fi "Pf" P.S.pf).map fun x => (rd r x).toK).toArray) (List.range (2 ^ P.S.pf)) 0

/-- **INT-8's `finPf` relation**: `claimN(Pf) = Ŵ₄(P₄)·pad·final̂(sf)`, and the kind's exact tail. -/
def relPf4 : Bool :=
  (Val.k (wV4 impl κ fi r P * padV4 κ fi r P * finHat4 inp fi r P)).eqv (rd r (claimN fi "Pf")) &&
    tailOk4 P κ inp

end Val

/-! ## The run -/

section Run
variable (impl : OpImpl) (κ : Kind) (inp : Input)

/-- Two blocks, the second from the first's registers, flags joined. -/
theorem pr_seq2 {A B : List Op} {R : Array Val} {M M' : List Val} {f g : Bool}
    (hA : pureRun impl κ inp A R [] = some (M, f))
    (hB : pureRun impl κ inp B (R ++ M.toArray) [] = some (M', g)) :
    pureRun impl κ inp (A ++ B) R [] = some (M ++ M', f && g) := by
  rw [pureRun_append, hA, Option.bind_some]
  have := pureRun_rebase impl κ inp B R M []
  simp only [List.append_nil] at this
  rw [this, hB]; rfl

/-- A run from `M` on, seen from the file `R ++ M`. -/
theorem pr_rebase {os : List Op} {R : Array Val} {M M' : List Val} {f : Bool}
    (h : pureRun impl κ inp os R M = some (M ++ M', f)) :
    pureRun impl κ inp os (R ++ M.toArray) [] = some (M', f) := by
  have e := pureRun_rebase impl κ inp os R M []
  rw [List.append_nil] at e
  rw [e] at h
  cases h' : pureRun impl κ inp os (R ++ M.toArray) [] with
  | none => rw [h'] at h; cases h
  | some p =>
    rw [h'] at h
    obtain ⟨p1, p2⟩ := p
    simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq, List.append_cancel_left_eq] at h
    rw [h.1, h.2]

/-- **The reserve's cell chain** (`finPf`'s second chain, revision 4.4.2): gated by `o` (`rsvOps`),
`n` more cells from the first chain's accumulator `acc` (value `A`) and last power (the register just
below, value `Pw`), then a `keep` by `sv` (`rsv`) between the continued sum and `A`. -/
theorem run_rsvChain (nc one g h kp : ℕ) (cells : ℕ → KC ℕ) (ρ : Array K) (kpv : F)
    (r : Array Val) (h1 : one < r.size) (hv1 : rd r one = .k 1) (hk : kp < r.size) (hkv : (rd r kp).toF = kpv)
    (hg0 : ∀ v < nc, g + v < r.size ∧ rd r (g + v) = .k (ρ.getD v 0))
    (hh0 : ∀ v < nc, h + v < r.size ∧ rd r (h + v) = .k (1 + ρ.getD v 0)) (hnc : 0 < nc)
    (o : Bool) (sv : KC Bool) (n acc : ℕ) (A : K) (Pw : F) (L : List Val)
    (hacc : acc < r.size + L.length) (hA : rd (r ++ L.toArray) acc = .k A)
    (hpw : 0 < r.size + L.length) (hP : (rd (r ++ L.toArray) (r.size + L.length - 1)).toF = Pw) :
    ∃ M, pureRun impl κ inp (cond o (gCellsOpsK nc one g h kp cells n 0 acc (r.size + L.length - 1)
        (r.size + L.length) ++ [.keep sv (gCellsAccK nc n acc (r.size + L.length)) acc]) [])
        (r ++ L.toArray) [] = some (M, true) ∧
      M.length = cond o ((2 * nc + 3) * n + 1) 0 ∧
      rd (r ++ L.toArray ++ M.toArray) (cond o (r.size + L.length + (2 * nc + 3) * n) acc) =
        .k (if (o && sv κ) = true then cellsVal4 nc ρ kpv (fun j => cells j κ) n 0 Pw A else A) := by
  cases o with
  | false => exact ⟨[], rfl, rfl, by simpa using hA⟩
  | true =>
    obtain ⟨M, hM, hl, hv, -⟩ := run_gCellsOpsK impl κ inp nc one g h kp cells ρ kpv r h1 hv1 hk hkv hg0 hh0
      hnc n 0 acc (r.size + L.length - 1) A Pw L hacc hA (by omega) hP
    set w : Val := if sv κ then .k (cellsVal4 nc ρ kpv (fun j => cells j κ) n 0 Pw A) else .k A
    have hkeep : evalOp impl κ inp (r ++ (L ++ M).toArray)
        (.keep sv (gCellsAccK nc n acc (r.size + L.length)) acc) = .vals [w] true := by
      simp only [evalOp, hv, FR.rd_pre r (M := M) hacc, hA, w]
    have hrun : pureRun impl κ inp (gCellsOpsK nc one g h kp cells n 0 acc (r.size + L.length - 1)
        (r.size + L.length) ++ [.keep sv (gCellsAccK nc n acc (r.size + L.length)) acc]) r L =
        some (L ++ (M ++ [w]), true) := by
      rw [pr_app impl κ inp r hM, pr_op impl κ inp r hkeep]; simp [pureRun]
    refine ⟨M ++ [w], pr_rebase impl κ inp hrun, by simp [hl], ?_⟩
    rw [show r ++ L.toArray ++ (M ++ [w]).toArray = r ++ (L ++ M ++ [w]).toArray by
        simp [Array.append_assoc],
      show cond true (r.size + L.length + (2 * nc + 3) * n) acc = r.size + (L ++ M).length by
        simp [hl]; omega, rd_new1 r (L ++ M) w]
    simp only [Bool.true_and, w]; split <;> rfl

/-- **The slots' selections** (`selOps` for slots `0 … T − 1`, each from the previous' registers). -/
theorem run_selSlots (sel : ℕ → KC Bool) (cand : ℕ → ℕ → Reg) (n : ℕ) (R : Array Val)
    (hc : ∀ s i, i < n → cand s i < R.size) : ∀ T, ∃ M,
    pureRun impl κ inp ((List.range T).flatMap fun s => selOps sel (cand s) n (R.size + s * (n - 1))) R [] =
      some (M, true) ∧ M.length = T * (n - 1) ∧ ∀ s < T, 0 < n →
        selOut (cand s) n (R.size + s * (n - 1)) < R.size + M.length ∧
        rd (R ++ M.toArray) (selOut (cand s) n (R.size + s * (n - 1))) =
          rd R (cand s (selI (fun i => sel i κ) (n - 1)))
  | 0 => ⟨[], rfl, by simp, fun s hs => absurd hs (Nat.not_lt_zero _)⟩
  | T + 1 => by
    obtain ⟨M, hM, hl, hv⟩ := run_selSlots sel cand n R hc T
    have hsz : (R ++ M.toArray).size = R.size + T * (n - 1) := by simp [hl]
    obtain ⟨M', hM', hl', hv'⟩ := run_selOps impl κ inp sel (cand T) n (R ++ M.toArray)
      (fun i hi => Nat.lt_of_lt_of_le (hc T i hi) (by simp))
    rw [hsz] at hM' hv'
    refine ⟨M ++ M', ?_, by simp [hl, hl']; ring, fun s hs hn => ?_⟩
    · rw [List.range_succ, List.flatMap_append, List.flatMap_singleton]
      exact pr_seq impl κ inp hM hM'
    · rcases Nat.lt_succ_iff_lt_or_eq.1 hs with hs | rfl
      · obtain ⟨hb, hr⟩ := hv s hs hn
        refine ⟨Nat.lt_of_lt_of_le hb (by simp), ?_⟩
        rw [show R ++ (M ++ M').toArray = R ++ M.toArray ++ M'.toArray by simp [Array.append_assoc],
          rd_append_left (by simpa using hb), hr]
      · obtain ⟨hb, hr⟩ := hv' hn
        refine ⟨by rw [List.length_append, hl, ← Nat.add_assoc]; exact hb, ?_⟩
        rw [show R ++ (M ++ M').toArray = R ++ M.toArray ++ M'.toArray by simp [Array.append_assoc], hr,
          rd_append_left (hc s _ (lt_of_le_of_lt (selI_le _ _) (by omega)))]

/-- **`finPf` from the level steps on** (blocks 11–17): from a file `R` holding the constants, the
kind's tails at `sb …` and `Ŵ₀(P₀)` at `ce + 1`. -/
theorem flag_pfTail4 (r R : Array Val) (P : FinP) (hS : P.S = seq4) (hnf : 0 < P.fams.length) (fi : FinIn)
    (b sb ce : ℕ) (w0 : K) (hpos : 0 < r.size) (hO : ∀ n, ∀ x ∈ fi.outs.getD n [], x < r.size)
    (hlv : ∀ k ∈ [1, 2, 3, 4], ∀ x ∈ lvRefs fi k, x < r.size) (eR : ExtA r R) (hR : R.size = ce + 2)
    (hb : b + 2 < R.size) (r1one : rd R b = .k 1) (r1cu : rd R (b + 1) = .k (1 + K.u))
    (r1z : rd R (b + 2) = .k 0)
    (hT : ∀ k ∈ [1, 2, 3, 4], sb + (k - 1) < R.size ∧ rd R (sb + (k - 1)) = .ak (tl4 κ fi r P k))
    (hW : rd R (ce + 1) = .k w0) :
    ∃ L, pureRun impl κ inp
      (lvsOps fi b (b + 1) sb [1, 2, 3, 4] (ce + 1) (ce + 2) ++
       ([.packK (chals fi "Pf" P.S.pf), .eqTableK (ce + 2 + lvsW fi [1, 2, 3, 4])] ++
       ((fhOps (ce + 2 + lvsW fi [1, 2, 3, 4] + 1) (List.range (2 ^ P.S.pf)) (b + 2)
          (ce + 2 + lvsW fi [1, 2, 3, 4] + 2)).map (reloc P.S) ++
       (padsOps b (chals fi "Pf" P.S.pf) P.S.pf P.fams (ce + 2 + lvsW fi [1, 2, 3, 4] + 2 + 4 * 2 ^ P.S.pf) ++
       (selOps (fun i κ => decide (P.kv.fsel κ = i))
          (padsReg b P.S.pf P.fams (ce + 2 + lvsW fi [1, 2, 3, 4] + 2 + 4 * 2 ^ P.S.pf)) P.fams.length
          (ce + 2 + lvsW fi [1, 2, 3, 4] + 2 + 4 * 2 ^ P.S.pf + (P.fams.map (padW P.S.pf)).sum) ++
       ([.keep (fun κ => P.kv.selA κ) b (selOut (padsReg b P.S.pf P.fams
            (ce + 2 + lvsW fi [1, 2, 3, 4] + 2 + 4 * 2 ^ P.S.pf)) P.fams.length
            (ce + 2 + lvsW fi [1, 2, 3, 4] + 2 + 4 * 2 ^ P.S.pf + (P.fams.map (padW P.S.pf)).sum)),
         .mulK (lvsOut fi [1, 2, 3, 4] (ce + 1) (ce + 2))
           (ce + 2 + lvsW fi [1, 2, 3, 4] + 2 + 4 * 2 ^ P.S.pf + (P.fams.map (padW P.S.pf)).sum +
             (P.fams.length - 1)),
         .mulK (ce + 2 + lvsW fi [1, 2, 3, 4] + 2 + 4 * 2 ^ P.S.pf + (P.fams.map (padW P.S.pf)).sum +
             P.fams.length) (fhOut (List.range (2 ^ P.S.pf)) (b + 2) (ce + 2 + lvsW fi [1, 2, 3, 4] + 2)),
         .assertEq (ce + 2 + lvsW fi [1, 2, 3, 4] + 2 + 4 * 2 ^ P.S.pf + (P.fams.map (padW P.S.pf)).sum +
             P.fams.length + 1) (claimN fi "Pf") allK] ++
       (gTailOps (fun _ => P) P.S.pf P.tails (ce + 2 + lvsW fi [1, 2, 3, 4] + 2 + 4 * 2 ^ P.S.pf +
          (P.fams.map (padW P.S.pf)).sum + P.fams.length + 2)).map (reloc P.S)))))))
      R [] = some (L, (Val.k (lvsV impl fi (rd r) (tl4 κ fi r P) [1, 2, 3, 4] w0 * padV4 κ fi r P *
        finHat4 inp fi r P)).eqv (rd r (claimN fi "Pf")) && tailOk4 P κ inp) := by
  have app0 : ∀ X : Array Val, X ++ ([] : List Val).toArray = X := fun X => by simp
  have hcNr : claimN fi "Pf" < r.size := getLastD_lt (outsOf_lt hpos hO "Pf") hpos
  have hsfm : ∀ x ∈ chals fi "Pf" P.S.pf, x < r.size := chals_lt hpos hO "Pf" _
  have hsf : ∀ v, (chals fi "Pf" P.S.pf).getD v 0 < r.size := getD_lt hpos hsfm
  generalize hlw : lvsW fi [1, 2, 3, 4] = lw
  -- B11: the levels
  obtain ⟨M11, hB11, hl11, hv11⟩ := run_lvsOps impl κ inp fi b (b + 1) sb (tl4 κ fi r P) R
    (by omega) r1one (by omega) r1cu [1, 2, 3, 4] (ce + 1) w0 R le_rfl (fun _ _ => rfl)
    (fun k hk => ⟨fun x hx => Nat.lt_of_lt_of_le (hlv k hk x hx) eR.1, hT k hk⟩) (by omega) hW
  rw [hR] at hB11 hv11
  rw [lvsV_congr impl fi (tl4 κ fi r P) r.size (fun x hx => eR.rd hx) [1, 2, 3, 4] _ hlv] at hv11
  set R11 := R ++ M11.toArray with hR11
  have sR11 : R11.size = ce + 2 + lw := by simp [R11, hR, hl11, hlw]
  have e011 : ExtA r R11 := eR.trans (ExtA.app R M11)
  have eR11 : ExtA R R11 := ExtA.app R M11
  -- B12: `sf` and `eq(sf, ·)`
  set sfV := ((chals fi "Pf" P.S.pf).map fun x => (rd r x).toK).toArray
  set V12 : List Val := [.ak sfV, .ak (eqTab sfV)]
  have hB12 : pureRun impl κ inp [.packK (chals fi "Pf" P.S.pf), .eqTableK (ce + 2 + lw)] R11 [] =
      some (V12, true) := by
    have hm : (chals fi "Pf" P.S.pf).map (fun x => (rd R11 x).toK) =
        (chals fi "Pf" P.S.pf).map (fun x => (rd r x).toK) :=
      List.map_congr_left fun x hx => by rw [e011.rd (hsfm x hx)]
    rw [← sR11]
    simp only [pureRun, evalOp, List.nil_append, app0, rd_app0, hm, Option.map_some, Bool.and_true]
    rfl
  set R12 := R11 ++ V12.toArray with hR12
  have sR12 : R12.size = ce + 2 + lw + 2 := by simp [R12, sR11, V12]
  have eR12 : ExtA R R12 := eR11.trans (ExtA.app R11 V12)
  -- B13: `final̂(sf)`
  obtain ⟨M13, hB13, hl13, hv13⟩ := run_fhOps4 impl κ inp P.S R12 (ce + 2 + lw + 1) (eqTab sfV)
    (by rw [sR12]; omega) (by rw [hR12, ← sR11, rd_app]; rfl) (List.range (2 ^ P.S.pf)) (b + 2) 0 []
    (by rw [List.length_nil, Nat.add_zero, sR12]; omega)
    (by rw [app0, eR12.rd (by omega), r1z])
  simp only [List.length_nil, Nat.add_zero, List.nil_append, sR12, List.length_range] at hB13 hv13 hl13
  set R13 := R12 ++ M13.toArray with hR13
  have sR13 : R13.size = ce + 2 + lw + 2 + 4 * 2 ^ P.S.pf := by simp [R13, sR12, hl13]
  have eR13 : ExtA R R13 := eR12.trans (ExtA.app R12 M13)
  have e013 : ExtA r R13 := eR.trans eR13
  -- B14: the pad chains
  obtain ⟨M14, hB14, hl14, hv14⟩ := run_padsOps impl κ inp b (chals fi "Pf" P.S.pf) (sfv4 fi r P) P.S.pf
    P.fams R13 (Nat.lt_of_lt_of_le (by omega : b < R.size) eR13.1)
    (by rw [eR13.rd (by clear * - hb; omega), r1one])
    (fun v _ => ⟨Nat.lt_of_lt_of_le (hsf v) e013.1, by rw [e013.rd (hsf v)]; rfl⟩)
  rw [sR13] at hB14 hv14
  set R14 := R13 ++ M14.toArray with hR14
  have sR14 : R14.size = ce + 2 + lw + 2 + 4 * 2 ^ P.S.pf + (P.fams.map (padW P.S.pf)).sum := by
    simp [R14, sR13, hl14]
  have e1314 : ExtA R13 R14 := ExtA.app R13 M14
  -- B15: the kind's pad
  have hv14' : ∀ i < P.fams.length, padsReg b P.S.pf P.fams (ce + 2 + lw + 2 + 4 * 2 ^ P.S.pf) i < R14.size ∧
      rd R14 (padsReg b P.S.pf P.fams (ce + 2 + lw + 2 + 4 * 2 ^ P.S.pf) i) =
        .k (padF4 (sfv4 fi r P) P.S.pf (P.fams.getD i 0)) := fun i hi => by
    obtain ⟨h1, h2⟩ := hv14 i hi
    exact ⟨by rw [sR14, ← hl14]; exact h1, h2⟩
  obtain ⟨M15, hB15, hl15, hv15⟩ := run_selOps impl κ inp (fun i κ => decide (P.kv.fsel κ = i))
    (padsReg b P.S.pf P.fams (ce + 2 + lw + 2 + 4 * 2 ^ P.S.pf)) P.fams.length R14
    (fun i hi => (hv14' i hi).1)
  rw [sR14] at hB15 hv15
  obtain ⟨-, hr15⟩ := hv15 hnf
  set pe := ce + 2 + lw + 2 + 4 * 2 ^ P.S.pf + (P.fams.map (padW P.S.pf)).sum with hpe
  set R15 := R14 ++ M15.toArray with hR15
  have sR15 : R15.size = pe + (P.fams.length - 1) := by simp [R15, sR14, hl15, hpe]
  have e1415 : ExtA R14 R15 := ExtA.app R14 M15
  have eR15 : ExtA R R15 := eR13.trans (e1314.trans e1415)
  have r15pad : rd R15 (selOut (padsReg b P.S.pf P.fams (ce + 2 + lw + 2 + 4 * 2 ^ P.S.pf)) P.fams.length pe) =
      .k (padF4 (sfv4 fi r P) P.S.pf (P.fams.getD (famI P κ) 0)) := by
    rw [hr15]; exact (hv14' _ (famI_lt P κ hnf)).2
  have hWo : lvsOut fi [1, 2, 3, 4] (ce + 1) (ce + 2) < R11.size := by
    by_contra hc'
    have h0 := hv11; rw [rd, Array.getElem?_eq_none (by simpa [R11] using hc')] at h0; cases h0
  have hFo : fhOut (List.range (2 ^ P.S.pf)) (b + 2) (ce + 2 + lw + 2) < R13.size := by
    by_contra hc'
    have h0 := hv13; rw [rd, Array.getElem?_eq_none (by simpa [R13] using hc')] at h0; cases h0
  have e1115 : ExtA R11 R15 := (ExtA.app R11 V12).trans ((ExtA.app R12 M13).trans (e1314.trans e1415))
  have e1315 : ExtA R13 R15 := e1314.trans e1415
  have r15W : rd R15 (lvsOut fi [1, 2, 3, 4] (ce + 1) (ce + 2)) =
      .k (lvsV impl fi (rd r) (tl4 κ fi r P) [1, 2, 3, 4] w0) := by rw [e1115.rd hWo, hv11]
  have r15F : rd R15 (fhOut (List.range (2 ^ P.S.pf)) (b + 2) (ce + 2 + lw + 2)) = .k (finHat4 inp fi r P) := by
    rw [e1315.rd hFo, hv13]; rfl
  have r15one : rd R15 b = .k 1 := by rw [eR15.rd (by clear * - hb; omega), r1one]
  have hsel : selOut (padsReg b P.S.pf P.fams (ce + 2 + lw + 2 + 4 * 2 ^ P.S.pf)) P.fams.length pe < R15.size := by
    by_contra hc'
    have h0 := r15pad; rw [rd, Array.getElem?_eq_none (by simpa using hc')] at h0; cases h0
  obtain ⟨V16, hB16⟩ : ∃ V16, pureRun impl κ inp
      [.keep (fun κ => P.kv.selA κ) b (selOut (padsReg b P.S.pf P.fams
          (ce + 2 + lw + 2 + 4 * 2 ^ P.S.pf)) P.fams.length pe),
       .mulK (lvsOut fi [1, 2, 3, 4] (ce + 1) (ce + 2)) (pe + (P.fams.length - 1)),
       .mulK (pe + P.fams.length) (fhOut (List.range (2 ^ P.S.pf)) (b + 2) (ce + 2 + lw + 2)),
       .assertEq (pe + P.fams.length + 1) (claimN fi "Pf") allK] R15 [] =
      some (V16, (Val.k (lvsV impl fi (rd r) (tl4 κ fi r P) [1, 2, 3, 4] w0 * padV4 κ fi r P *
        finHat4 inp fi r P)).eqv (rd r (claimN fi "Pf"))) := by
    rw [show pe + P.fams.length + 1 = R15.size + 2 by rw [sR15]; clear * - hnf; omega,
      show pe + P.fams.length = R15.size + 1 by rw [sR15]; clear * - hnf; omega,
      show pe + (P.fams.length - 1) = R15.size from sR15.symm]
    simp only [pureRun, evalOp, List.nil_append, List.cons_append, app0, rd_app, rd_app0,
      rd_app_left _ _ (show b < R15.size by have := eR15.1; clear * - this hb; omega), r15one,
      rd_app_left _ _ hsel, r15pad,
      rd_app_left _ _ (Nat.lt_of_lt_of_le hcNr (eR.trans eR15).1), (eR.trans eR15).rd hcNr,
      rd_app_left _ _ (Nat.lt_of_lt_of_le hWo e1115.1), rd_app_left _ _ (Nat.lt_of_lt_of_le hFo e1315.1),
      r15W, r15F, List.getD_cons_succ, List.getD_cons_zero, Option.map_some, allK, Bool.not_true,
      Bool.false_or, Bool.true_and, Bool.and_true]
    refine ex_some ?_
    refine congrArg (fun z : K => (Val.k z).eqv (rd r (claimN fi "Pf"))) ?_
    simp only [padV4]
    split_ifs <;> simp [toK_k]
  set R16 := R15 ++ V16.toArray with hR16
  obtain ⟨M17, hB17⟩ := run_gTailOps impl κ inp P.S P P.tails R16
  have hl16 : V16.length = 3 := by
    have := pureRun_len impl κ inp R15 _ [] V16 _ hB16; simpa [opsOut, Op.outs] using this
  have sR16 : R16.size = pe + P.fams.length + 2 := by
    simp [R16, sR15, hl16]; clear * - hnf; omega
  rw [sR16] at hB17
  exact ⟨_, pr_seq impl κ inp hB11 (pr_seq impl κ inp hB12 (pr_seq impl κ inp hB13
    (pr_seq impl κ inp hB14 (pr_seq impl κ inp hB15 (pr_seq2 impl κ inp hB16 hB17)))))⟩


set_option maxHeartbeats 1000000 in
/-- **`flag_gFinPf4`** (3.x's `flag_finPf` at INT-8's uniform `finPf`): the relocated field of a
fixed-kind program with kind-table cells asks nothing; its flag is `relPf4`. -/
theorem flag_gFinPf4 (r : Array Val) (P : FinP) (hS : P.S = seq4) (hnc : 0 < P.nc)
    (hnf : 0 < P.fams.length) (fi : FinIn) (hpos : 0 < r.size)
    (hO : ∀ n, ∀ x ∈ fi.outs.getD n [], x < r.size)
    (hpts : ∀ s ∈ gPfPts P fi, ∀ x ∈ s, x.Ok r.size)
    (hix : ∀ j ∈ P.kv.ptIx κ, j < (gPfPts P fi).length)
    (hlv : ∀ k ∈ [1, 2, 3, 4], ∀ x ∈ lvRefs fi k, x < r.size) :
    ∃ L, pureRun impl κ inp (gFinPfR P fi r.size) r [] = some (L, relPf4 impl κ inp fi r P) := by
  have app0 : ∀ X : Array Val, X ++ ([] : List Val).toArray = X := fun X => by simp
  have hrs : ∀ p, (coordsR fi "RS1").getD p 0 < r.size := getD_lt hpos (coordsR_lt hpos hO "RS1")
  have hkpr : (outsOf fi "B'").headD 0 < r.size := headD_lt (outsOf_lt hpos hO "B'") hpos
  have hcNr : claimN fi "Pf" < r.size := getLastD_lt (outsOf_lt hpos hO "Pf") hpos
  have hβr : (outsOf fi "L3β").headD 0 < r.size := headD_lt (outsOf_lt hpos hO "L3β") hpos
  have hsfm : ∀ x ∈ chals fi "Pf" P.S.pf, x < r.size := chals_lt hpos hO "Pf" _
  have hsf : ∀ v, (chals fi "Pf" P.S.pf).getD v 0 < r.size := getD_lt hpos hsfm
  have hlvs : ∀ (one cu Ts W b' : ℕ), gLvsOps P.S fi one cu Ts [1, 2, 3, 4] W b' =
      lvsOps fi one cu Ts [1, 2, 3, 4] W b' := fun _ _ _ _ _ => by rw [hS, gLvsOps_4]
  delta gFinPfR
  simp only [hlvs, List.append_assoc]
  generalize hpw : ptsW (gPfPts P fi) = pw
  set b := r.size with hb
  set kp := (outsOf fi "B'").headD 0 with hkp
  set kpv := kp4 fi r with hkpv
  set Pp := ptsOut (gPfPts P fi) (b + 3)
  -- B1: the constants
  set V1 : List Val := [.k 1, .k (1 + K.u), .k 0]
  have hB1 : pureRun impl κ inp [Op.const fun _ => Val.k 1, Op.const fun _ => Val.k (1 + K.u),
      Op.const fun _ => Val.k 0] r [] = some (V1, true) := rfl
  set R1 := r ++ V1.toArray with hR1
  have sR1 : R1.size = b + 3 := by simp [R1, V1, hb]
  have r1one : rd R1 b = .k 1 := by rw [hR1, hb, rd_app0]; rfl
  have r1cu : rd R1 (b + 1) = .k (1 + K.u) := by rw [hR1, hb, rd_app]; rfl
  have r1z : rd R1 (b + 2) = .k 0 := by rw [hR1, hb, rd_app]; rfl
  have e01 : ExtA r R1 := ExtA.app r V1
  -- B2: the points
  obtain ⟨M2, hB2, hl2, hv2⟩ := run_ptsOps impl κ inp R1 b (b + 2) (by omega) r1one (by omega) r1z
    (gPfPts P fi) [] (fun s hs x hx => by
      have := hpts s hs x hx
      cases x with
      | f y => exact Nat.lt_of_lt_of_le this e01.1
      | k y => exact Nat.lt_of_lt_of_le this e01.1
      | c v => trivial)
  simp only [List.length_nil, Nat.add_zero, List.nil_append, sR1] at hB2 hv2
  set R2 := R1 ++ M2.toArray with hR2
  have sR2 : R2.size = b + 3 + pw := by simp [R2, sR1, hl2, hpw]
  have e12 : ExtA R1 R2 := ExtA.app R1 M2
  have hPv : ∀ j < (gPfPts P fi).length, rd R2 (Pp j) = .ak (ptPf fi r P j) ∧ Pp j < R2.size := by
    intro j hj
    refine ⟨?_, ?_⟩
    · rw [hv2 j hj, hR1, ptV_app r V1 _ (hpts _ (by
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj]; exact List.getElem_mem _))]; rfl
    · rw [sR2, ← hpw]; exact ptsOut_lt _ _ _ hj
  -- B3: the families' selections
  obtain ⟨M3, hB3, hl3, hv3⟩ := run_selSlots impl κ inp (fun i κ => decide (P.kv.fsel κ = i))
    (fun s i => pfCand P Pp i s) P.fams.length R2
    (fun s i hi => by rw [pfCand_eq]; exact (hPv _ (candIx_lt P fi hi s)).2) 5
  rw [sR2] at hB3 hv3
  set R3 := R2 ++ M3.toArray with hR3
  have sR3 : R3.size = b + 3 + pw + 5 * (P.fams.length - 1) := by simp [R3, sR2, hl3]
  have e23 : ExtA R2 R3 := ExtA.app R2 M3
  have r3sel : ∀ s < 5, selOut (fun i => pfCand P Pp i s) P.fams.length (b + 3 + pw + s * (P.fams.length - 1)) < R3.size ∧
      rd R3 (selOut (fun i => pfCand P Pp i s) P.fams.length (b + 3 + pw + s * (P.fams.length - 1))) =
        .ak (ptPf fi r P (candIx P (famI P κ) s)) := by
    intro s hs
    obtain ⟨hb3, hr3⟩ := hv3 s hs hnf
    refine ⟨by rw [sR3]; simpa [hl3] using hb3, ?_⟩
    rw [hr3, pfCand_eq]; exact (hPv _ (candIx_lt P fi (famI_lt P κ hnf) s)).1
  -- B4: the kind's slots
  have hB4 := run_base impl κ inp R3 ((List.range 5).map fun s =>
      Op.keep (fun κ => P.kv.selA κ) (pfCandA P Pp s)
        (selOut (fun i => pfCand P Pp i s) P.fams.length (b + 3 + pw + s * (P.fams.length - 1)))) []
    (fun op hop Y => by
      obtain ⟨s, hs, rfl⟩ := List.mem_map.mp hop
      have hs' := List.mem_range.mp hs
      have hA : pfCandA P Pp s < R3.size := by
        rw [pfCandA_eq]; exact Nat.lt_of_lt_of_le (hPv _ (candAIx_lt P fi s)).2 e23.1
      simp only [evalOp, rd_app_left _ _ hA, rd_app_left _ _ (r3sel s hs').1])
    (fun op hop => by obtain ⟨s, -, rfl⟩ := List.mem_map.mp hop; exact ⟨_, rfl⟩)
  set V4 : List Val := (List.range 5).map fun s => .ak (ptPf fi r P (slotIx P κ s))
  have hV4 : ((List.range 5).map fun s =>
      Op.keep (fun κ => P.kv.selA κ) (pfCandA P Pp s)
        (selOut (fun i => pfCand P Pp i s) P.fams.length (b + 3 + pw + s * (P.fams.length - 1)))).map (baseVal impl κ inp R3) = V4 := by
    simp only [List.map_map, V4]
    refine List.map_congr_left fun s hs => ?_
    have hs' := List.mem_range.mp hs
    simp only [Function.comp_apply, baseVal, evalOp, (r3sel s hs').2, slotIx]
    rw [pfCandA_eq, e23.rd (hPv _ (candAIx_lt P fi s)).2, (hPv _ (candAIx_lt P fi s)).1]
    split_ifs <;> rfl
  rw [hV4, List.nil_append] at hB4
  set sb := b + 3 + pw + 5 * (P.fams.length - 1) with hsb
  set R4 := R3 ++ V4.toArray with hR4
  have sR4 : R4.size = sb + 5 := by simp [R4, sR3, V4]
  have e34 : ExtA R3 R4 := ExtA.app R3 V4
  have r4T : ∀ s < 5, rd R4 (sb + s) = .ak (ptPf fi r P (slotIx P κ s)) := by
    intro s hs; rw [hR4, ← sR3, rd_app]; simp [V4, hs]
  -- B5: `rsWeight`
  have e03 : ExtA r R3 := e01.trans (e12.trans e23)
  have e04 : ExtA r R4 := e03.trans e34
  have rr : ∀ x < r.size, ∀ L : List Val, rd (R4 ++ L.toArray) x = rd r x := fun x hx L => by
    rw [rd_app_left R4 L (Nat.lt_of_lt_of_le hx e04.1), e04.rd hx]
  have hPr : ∀ j ∈ P.kv.ptIx κ, Pp j < R4.size := fun j hj =>
    Nat.lt_of_lt_of_le (hPv j (hix j hj)).2 (e23.trans e34).1
  have hptsL : ∀ L : List Val, (P.kv.ptIx κ).map (fun x => (rd (R4 ++ L.toArray) (Pp x)).toAK) =
      (P.kv.ptIx κ).map (ptPf fi r P) := fun L => List.map_congr_left fun j hj => by
    rw [rd_app_left _ _ (hPr j hj), (e23.trans e34).rd (hPv j (hix j hj)).2, (hPv j (hix j hj)).1]; rfl
  have hP4 : sb + 4 < R4.size := by rw [sR4]; omega
  have r4P : rd R4 (sb + 4) = .ak (rho4 κ fi r P) := r4T 4 (by omega)
  set rsW := impl.rsWeight (ptF r ((List.range 7).map fun p => (coordsR fi "RS1").getD p 0))
      ((P.kv.ptIx κ).map (ptPf fi r P)) (fv r ((coordsR fi "RS1").getD 7 0))
      (if P.kv.node κ then fv r ((outsOf fi "L3β").headD 0) else 1) (rho4 κ fi r P)
  set V5 : List Val := [.af (ptF r ((List.range 7).map fun p => (coordsR fi "RS1").getD p 0)), .k rsW]
  have hB5 : pureRun impl κ inp
      [.packF ((List.range 7).map fun p => (coordsR fi "RS1").getD p 0),
       .rsWeight (sb + 5) (fun κ => (P.kv.ptIx κ).map Pp) ((coordsR fi "RS1").getD 7 0)
         ((outsOf fi "L3β").headD 0) (fun κ => P.kv.node κ) (sb + 4)] R4 [] = some (V5, true) := by
    have hrpp : (List.range 7).map (fun x => (rd R4 ((coordsR fi "RS1").getD x 0)).toF) =
        (List.range 7).map (fun x => fv r ((coordsR fi "RS1").getD x 0)) :=
      List.map_congr_left fun p _ => by rw [e04.rd (hrs p)]
    rw [show sb + 5 = R4.size from sR4.symm]
    simp only [pureRun, evalOp, List.nil_append, List.cons_append, rd_app, rd_app0,
      rd_app_left _ _ hP4, r4P, List.map_map, Function.comp_def, hptsL,
      rr _ (hrs 7), rr _ hβr, List.getD_cons_succ, List.getD_cons_zero, Option.map_some, Bool.and_true,
      Array.append_empty, hrpp]
    rfl
  set R5 := R4 ++ V5.toArray with hR5
  have sR5 : R5.size = sb + 5 + 2 := by simp [R5, sR4, V5]
  have e45 : ExtA R4 R5 := ExtA.app R4 V5
  -- B6, B7: `ρ_v` and `1 + ρ_v`
  have hB6 := run_base impl κ inp R5 ((List.range P.nc).map fun v => Op.getK (sb + 4) v) []
    (fun op hop Y => by
      obtain ⟨v, -, rfl⟩ := List.mem_map.mp hop
      simp only [evalOp, rd_app_left _ _ (show sb + 4 < R5.size by rw [sR5]; omega)])
    (fun op hop => by obtain ⟨v, -, rfl⟩ := List.mem_map.mp hop; exact ⟨_, rfl⟩)
  set V6 : List Val := (List.range P.nc).map fun v => .k ((rho4 κ fi r P).getD v 0)
  have hV6 : ((List.range P.nc).map fun v => Op.getK (sb + 4) v).map (baseVal impl κ inp R5) = V6 := by
    simp only [List.map_map, V6]
    refine List.map_congr_left fun v _ => ?_
    simp only [Function.comp_apply, baseVal, evalOp, e45.rd hP4, r4P, Val.toAK]
  rw [hV6, List.nil_append] at hB6
  set R6 := R5 ++ V6.toArray with hR6
  have sR6 : R6.size = sb + 5 + 2 + P.nc := by simp [R6, sR5, V6]
  have e56 : ExtA R5 R6 := ExtA.app R5 V6
  have r6 : ∀ v < P.nc, rd R6 (sb + 5 + 2 + v) = .k ((rho4 κ fi r P).getD v 0) := fun v hv => by
    rw [hR6, ← sR5, rd_app]; simp [V6, hv]
  have e16 : ExtA R1 R6 := e12.trans (e23.trans (e34.trans (e45.trans e56)))
  have r6one : rd R6 b = .k 1 := by rw [e16.rd (by rw [sR1]; omega), r1one]
  have hB7 := run_base impl κ inp R6 ((List.range P.nc).map fun v => Op.addK b (sb + 5 + 2 + v)) []
    (fun op hop Y => by
      obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hop
      have : sb + 5 + 2 + v < R6.size := by rw [sR6]; simp at hv; omega
      simp only [evalOp, rd_app_left _ _ this, rd_app_left _ _ (show b < R6.size by rw [sR6]; omega)])
    (fun op hop => by obtain ⟨v, -, rfl⟩ := List.mem_map.mp hop; exact ⟨_, rfl⟩)
  set V7 : List Val := (List.range P.nc).map fun v => .k (1 + (rho4 κ fi r P).getD v 0)
  have hV7 : ((List.range P.nc).map fun v => Op.addK b (sb + 5 + 2 + v)).map (baseVal impl κ inp R6) = V7 := by
    simp only [List.map_map, V7]
    refine List.map_congr_left fun v hv => ?_
    simp only [Function.comp_apply, baseVal, evalOp, r6one, r6 v (List.mem_range.mp hv), toK_k]
  rw [hV7, List.nil_append] at hB7
  set R7 := R6 ++ V7.toArray with hR7
  have sR7 : R7.size = sb + 5 + (2 + 2 * P.nc) := by simp [R7, sR6, V7]; omega
  have e67 : ExtA R6 R7 := ExtA.app R6 V7
  -- B8: `κ′²`
  have e07 : ExtA r R7 := e04.trans (e45.trans (e56.trans e67))
  have hB8 : pureRun impl κ inp [.mulF kp kp] R7 [] = some ([.f (kpv * kpv)], true) := by
    simp only [pureRun, evalOp, List.nil_append, Array.append_empty, e07.rd hkpr]; rfl
  set R8 := R7 ++ [Val.f (kpv * kpv)].toArray with hR8
  have sR8 : R8.size = sb + 5 + (2 + 2 * P.nc) + 1 := by simp [R8, sR7]
  have e78 : ExtA R7 R8 := ExtA.app R7 _
  -- B9: the cells
  have e18 : ExtA R1 R8 := e16.trans (e67.trans e78)
  have e58 : ExtA R5 R8 := e56.trans (e67.trans e78)
  have h8one : b < R8.size := by rw [sR8]; omega
  have r8one : rd R8 b = .k 1 := by rw [e18.rd (by rw [sR1]; omega), r1one]
  have h8kp : kp < R8.size := Nat.lt_of_lt_of_le hkpr (e07.trans e78).1
  have r8kp : (rd R8 kp).toF = kpv := by rw [(e07.trans e78).rd hkpr]; rfl
  have r8g : ∀ v < P.nc, sb + 5 + 2 + v < R8.size ∧ rd R8 (sb + 5 + 2 + v) = .k ((rho4 κ fi r P).getD v 0) :=
    fun v hv => ⟨by rw [sR8]; clear * - hv; omega,
      by rw [(e67.trans e78).rd (by rw [sR6]; clear * - hv; omega), r6 v hv]⟩
  have r8h : ∀ v < P.nc, sb + 5 + (P.nc + 2) + v < R8.size ∧
      rd R8 (sb + 5 + (P.nc + 2) + v) = .k (1 + (rho4 κ fi r P).getD v 0) :=
    fun v hv => ⟨by rw [sR8]; clear * - hv; omega, by
      rw [show sb + 5 + (P.nc + 2) + v = R6.size + v by rw [sR6]; clear * -; omega,
        e78.rd (by rw [sR7, sR6]; clear * - hv; omega), hR7, rd_app]; simp [V7, hv]⟩
  obtain ⟨M9, hB9, hl9, hv9, hp9⟩ := run_gCellsOpsK impl κ inp P.nc b (sb + 5 + 2) (sb + 5 + (P.nc + 2)) kp
    (fun j _ => P.cells.getD j 0) (rho4 κ fi r P) kpv R8 h8one r8one h8kp r8kp r8g r8h hnc
    P.ncell 0 (b + 2) (sb + 5 + (2 + 2 * P.nc)) 0 (kpv * kpv) []
    (by rw [List.length_nil, Nat.add_zero, sR8, hsb]; clear * -; omega)
    (by rw [app0, e18.rd (by rw [sR1]; omega), r1z])
    (by rw [List.length_nil, Nat.add_zero, sR8, hsb]; clear * -; omega)
    (by rw [app0, hR8, ← sR7, rd_app0]; rfl)
  simp only [List.length_nil, Nat.add_zero, List.nil_append, sR8] at hB9 hv9 hp9
  rw [gCellsPwK_eq] at hp9
  set R9 := R8 ++ M9.toArray with hR9
  set c9 := sb + 5 + (2 + 2 * P.nc) + 1 + (2 * P.nc + 3) * P.ncell with hc9
  have sR9 : R9.size = c9 := by simp [R9, sR8, hl9, hc9]
  have hsz9 : R8.size + M9.length = c9 := by rw [sR8, hl9]
  have e89 : ExtA R8 R9 := ExtA.app R8 M9
  set cv := cellsVal4 P.nc (rho4 κ fi r P) kpv (fun j => P.cells.getD j 0) P.ncell 0 (kpv * kpv) 0
  set acc9 := gCellsAccK P.nc P.ncell (b + 2) (sb + 5 + (2 + 2 * P.nc) + 1) with hacc9
  have hca : acc9 < R9.size := by
    by_contra hc'
    have h0 := hv9; rw [rd, Array.getElem?_eq_none (by simpa using hc')] at h0; cases h0
  -- B9′: the reserve's chain (revision 4.4.2), gated by `rsvOps`, kept by `rsv`
  obtain ⟨Mr, hBr, hlr, hvr⟩ := run_rsvChain impl κ inp P.nc b (sb + 5 + 2) (sb + 5 + (P.nc + 2)) kp
    (fun j _ => P.rcells.getD j 0) (rho4 κ fi r P) kpv R8 h8one r8one h8kp r8kp r8g r8h hnc
    P.rsvOps (fun _ => P.rsv) P.nrcell acc9 cv (kpv * kpv * kpv ^ P.ncell) M9
    (by rw [hsz9, ← sR9]; exact hca) hv9 (by rw [hsz9]; omega) (by rw [hsz9]; exact hp9)
  rw [hsz9] at hBr hvr
  set ce := cond P.rsvOps (c9 + (2 * P.nc + 3) * P.nrcell + 1) c9 with hce
  set R9r := R9 ++ Mr.toArray with hR9r
  have sR9r : R9r.size = ce := by
    simp only [R9r, Array.size_append, List.size_toArray, hlr, sR9, hce]
    cases P.rsvOps <;> simp only [cond_true, cond_false] <;> omega
  have hc9ce : c9 ≤ ce := by rw [hce]; cases P.rsvOps <;> simp only [cond_true, cond_false] <;> omega
  have e99 : ExtA R9 R9r := ExtA.app R9 Mr
  -- B10: `Ŵ₀(P₀)`
  have e59 : ExtA R5 R9r := (e58.trans e89).trans e99
  have r9w : rd R9r (sb + 5 + 1) = .k rsW := by
    rw [e59.rd (by rw [sR5]; omega), hR5, ← sR4, rd_app]; rfl
  have r9z : rd R9r (b + 2) = .k 0 := by rw [((e18.trans e89).trans e99).rd (by rw [sR1]; omega), r1z]
  set cvT : K := if (P.rsvOps && P.rsv) = true then cellsVal4 P.nc (rho4 κ fi r P) kpv
    (fun j => P.rcells.getD j 0) P.nrcell 0 (kpv * kpv * kpv ^ P.ncell) cv else cv with hcvT
  have hcr : cond P.rsvOps (c9 + (2 * P.nc + 3) * P.nrcell) acc9 < R9r.size := by
    by_contra hc'
    have h0 := hvr; rw [rd, Array.getElem?_eq_none (by simpa using hc')] at h0; cases h0
  set V10 : List Val := [if P.kv.node κ then .k cvT else .k 0, .k (w0V4 impl κ fi r P)]
  have hB10 : pureRun impl κ inp
      [.keep (fun κ => P.kv.node κ) (cond P.rsvOps (c9 + (2 * P.nc + 3) * P.nrcell) acc9) (b + 2),
       .addK (sb + 5 + 1) ce] R9r [] = some (V10, true) := by
    rw [← sR9r]
    simp only [pureRun, evalOp, List.nil_append, List.cons_append, rd_app, rd_app0, app0,
      rd_app_left _ _ (show sb + 5 + 1 < R9r.size by rw [sR9r]; have := hc9ce; clear * - this hc9; omega),
      rd_app_left _ _ (show b + 2 < R9r.size by rw [sR9r]; have := hc9ce; clear * - this hc9 hsb; omega),
      rd_app_left _ _ hcr, r9w, r9z, hvr,
      List.getD_cons_succ, List.getD_cons_zero, Option.map_some, Bool.and_true]
    simp only [V10, w0V4, cv4, cv, cvT, toK_k, rsW, kpv, kp4]
    cases P.kv.node κ <;> simp <;> rfl
  set R10 := R9r ++ V10.toArray with hR10
  have sR10 : R10.size = ce + 2 := by simp [R10, sR9r, V10]
  have e910 : ExtA R9r R10 := ExtA.app R9r V10
  have r10w : rd R10 (ce + 1) = .k (w0V4 impl κ fi r P) := by rw [hR10, ← sR9r, rd_app]; rfl
  have e010 : ExtA r R10 := e07.trans (e78.trans (e89.trans (e99.trans e910)))
  have e410 : ExtA R4 R10 := e45.trans (e59.trans e910)
  have e110 : ExtA R1 R10 := e18.trans (e89.trans (e99.trans e910))
  obtain ⟨LT, hT⟩ := flag_pfTail4 impl κ inp r R10 P hS hnf fi b sb ce (w0V4 impl κ fi r P) hpos hO hlv
    e010 sR10 (by have := e110.1; rw [sR1] at this; exact this)
    (by rw [e110.rd (by rw [sR1]; omega), r1one])
    (by rw [e110.rd (by rw [sR1]; omega), r1cu]) (by rw [e110.rd (by rw [sR1]; omega), r1z])
    (fun k hk => by
      have hk' : k - 1 < 5 := by simp at hk; omega
      refine ⟨by rw [sR10]; have := hc9ce; clear * - hk' this hc9; omega, ?_⟩
      rw [e410.rd (by rw [sR4]; omega), r4T (k - 1) hk']; rfl) r10w
  exact ⟨_, pr_seq impl κ inp hB1 (pr_seq impl κ inp hB2 (pr_seq impl κ inp hB3
    (pr_seq impl κ inp hB4 (pr_seq impl κ inp hB5 (pr_seq impl κ inp hB6 (pr_seq impl κ inp hB7
    (pr_seq impl κ inp hB8 (pr_seq impl κ inp hB9 (pr_seq impl κ inp hBr (pr_seq impl κ inp hB10 hT))))))))))⟩

end Run

end FR.Snd.R4
