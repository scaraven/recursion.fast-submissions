-- G6: this module also holds the former modules `FRNodeRun4FE` (one section each, in import order).
import FRNodeRun4CT
import FRNodeRows4RepF

section G6_FRNodeRun4FE

-- New for `flock-recursive` (stage FEL, design `FEL.md`): the `felems` auxiliary cells from `PfCells`
-- (the `dotKF` column cells are arena₁'s, `FRNodeRows4Defs.colA`), hence `Gaps4`.

/-!
# The `felems` cells, and `Gaps4`

Since FEL a `dotKF`'s column cells are the arena₁ cells of the elements of its column's 16-byte windows
(`colA`, read through `tplExt4A`), and a `dotKF` whose column is not a `piField`'s bytes with every window an
element is refused (an import, which the closure fails). So the `felems` auxiliary facts follow from
`PfCells` alone, at every run:

* **`aux_colW`** (generic in the window map and the cell base): a column's cells evaluate to the register's
  `F` elements;
* **`xof_felemsA`**: a `felems` entry of the compile is a `dotKF`'s, its cells `colA π col n`, `col` an
  existing register;
* **`felems_of_pf`**: every non-`bits` auxiliary entry of `protoCS π` holds on an answer-driven run, given
  `PfCells`; hence **`slotRunF_of_pf`**;
* **`gaps4_fel`**: `Sub4.Gaps4` (`gaps4_of_runF`, `pfCells_of_rows`).
-/

namespace FR
namespace N4s
open RecursionFast Rev4 Circ TEval W4 Tpl

/-! ## The table -/

theorem colTab_lookup {ca : List ((ℕ × ℕ) × Option (List (Option ℕ)))} {pv : List (ℕ × ℕ × ℕ × ℕ)}
    {win : ℕ → Option ℕ} : ∀ {cols : List ℕ} {col : ℕ} {r : Option (List (Option ℕ))},
      (colTab ca pv win cols).lookup col = some r → r = colEWC ca pv win col
  | [], _, _, h => by simp [colTab] at h
  | c :: cs, col, r, h => by
    simp only [colTab, List.map_cons, List.lookup_cons] at h
    split at h
    · rename_i hc
      have : col = c := by simpa using hc
      subst this
      exact (Option.some.inj h).symm
    · exact colTab_lookup h

theorem esCache_lookup {pv : List (ℕ × ℕ × ℕ × ℕ)} {win : ℕ → Option ℕ} {sz : ℕ} :
    ∀ {cols : List ℕ} {k : ℕ × ℕ} {r : Option (List (Option ℕ))},
      (esCache pv win sz cols).lookup k = some r → r = colEs win sz k.1 k.2
  | [], _, _, h => by simp [esCache] at h
  | c :: cs, k, r, h => by
    simp only [esCache, List.filterMap_cons] at h
    cases hp : provOf pv c with
    | none => rw [hp] at h; exact esCache_lookup h
    | some p =>
      rw [hp] at h
      simp only [Option.map_some, List.lookup_cons] at h
      split at h
      · rename_i hc
        have : k = (absOff p.1 p.2.1, p.2.2) := by simpa using hc
        subst this
        exact (Option.some.inj h).symm
      · exact esCache_lookup h

/-- **The cache changes nothing** where its entries are `colEs`'s. -/
theorem colEWC_eq {ca : List ((ℕ × ℕ) × Option (List (Option ℕ)))} {pv : List (ℕ × ℕ × ℕ × ℕ)}
    {win : ℕ → Option ℕ} (hca : ∀ k r, ca.lookup k = some r → r = colEs win (piSizeOf seq4) k.1 k.2)
    (col : ℕ) : colEWC ca pv win col = colEW pv win col := by
  unfold colEWC colEW
  split
  · split
    · rename_i r hr; exact hca _ _ hr
    · rfl
  · rfl

theorem pvP_of_ne {π : ℕ} (h : π ≠ 0) : pvP π = pvP 1 := by
  unfold pvP protoProg
  rw [if_neg h, if_neg Nat.one_ne_zero]

/-- **The prototype's table holds `colEW`'s elements.** -/
theorem colTP_lookup {π col : ℕ} {r : Option (List (Option ℕ))} (h : (colTP π).lookup col = some r) :
    r = colEW (pvP π) winE col := by
  have hca : ∀ k r, esC0.lookup k = some r → r = colEs winE (piSizeOf seq4) k.1 k.2 :=
    fun _ _ h => esCache_lookup (cols := dotCols (protoProg 0).ops) h
  unfold colTP at h
  by_cases h0 : π = 0
  · subst h0
    rw [if_pos rfl] at h
    rw [← colEWC_eq hca]
    exact colTab_lookup (cols := dotCols (protoProg 0).ops) h
  · rw [if_neg h0] at h
    rw [pvP_of_ne h0, ← colEWC_eq hca]
    exact colTab_lookup (cols := dotCols (protoProg 1).ops) h

/-- **What the alias gives**: the column register is a `piField f o len`'s, its windows' elements `es`, and
the cells are `colCells` of them on region `π`'s arena₁. -/
theorem colA_some {π col n : ℕ} {cells : List Lin} (h : colA π col n = some cells) :
    ∃ f o len es, provOf (pvP π) col = some (f, o, len) ∧ colEs winE (piSizeOf seq4) (absOff f o) len = some es ∧
      cells = colCells (π * slotM4 + arA1) n es := by
  unfold colA at h
  obtain ⟨r, hr, h2⟩ := Option.bind_eq_some_iff.1 h
  obtain ⟨es, hes, rfl⟩ := Option.map_eq_some_iff.1 h2
  rw [colTP_lookup hr] at hes
  unfold colEW at hes
  split at hes
  · rename_i f o len hp
    exact ⟨f, o, len, es, hp, hes, rfl⟩
  · cases hes

/-! ## The cells' values -/

/-- **A column's cells hold the register's `F` elements** (generic: the window map `win` and the cell base
`base`; `hpc` is `PfCells` for them): the register holds the proof bytes `[x, x + len)`. -/
theorem aux_colW {regs : Array Val} {w : Asg} {inp : Input} {win : ℕ → Option ℕ} {base sz x len r n m : ℕ}
    {es : List (Option ℕ)}
    (hpc : ∀ o e, win o = some e → w (base + e) = F.ofBytes (bytesAt inp.π o 16))
    (hes : colEs win sz x len = some es) (hsz : sz ≤ inp.π.size)
    (hreg : regs[r]? = some (.b (inp.π.extract x (x + len)))) (hrs : r < m) :
    (colCells base n es).map (Lin.ev w) = (AuxK.felems n).val (rd (regs.extract 0 m) r) := by
  have hrd : rd (regs.extract 0 m) r = .b (inp.π.extract x (x + len)) := by
    rw [rd_extract hrs, rd, hreg]; rfl
  rw [hrd]
  unfold colEs at hes
  dsimp only at hes
  split_ifs at hes with hc
  obtain ⟨hl, hb, hall⟩ := hc
  cases hes
  rw [List.all_eq_true] at hall
  have hsize : (inp.π.extract x (x + len)).size = len := by
    simp [ByteArray.size_extract]; omega
  refine List.ext_getElem (by simp [AuxK.val, colCells]) fun b h1 h2 => ?_
  simp only [colCells, List.length_map, List.length_range] at h1
  simp only [colCells, List.getElem_map, AuxK.val, List.getElem_range, Val.toB]
  rw [felems, Array.getD_eq_getD_getElem?, Array.getElem?_map, Array.getElem?_range, hsize]
  by_cases hb' : b < len / 16
  · have hg : ((List.range (len / 16)).map fun t => win (x + 16 * t)).getD b none = win (x + 16 * b) := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hb']; rfl
    obtain ⟨e, he⟩ := Option.isSome_iff_exists.1
      (hall _ (List.mem_map.2 ⟨b, List.mem_range.2 hb', rfl⟩))
    rw [hg, he]
    simp only [Lin.ev_cell]
    rw [hpc _ _ he, if_pos hb', Option.map_some, Option.getD_some]
    refine congrArg F.ofBytes (Vector.ext fun t ht => ?_)
    simp only [bytesAt, Vector.getElem_ofFn]
    rw [byteAt_extract _ _ _ (by omega), Nat.add_assoc]
  · have hg : ((List.range (len / 16)).map fun t => win (x + 16 * t)).getD b none = none := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_none (by simpa using hb')]; rfl
    rw [hg, if_neg hb']
    rfl

/-! ## The compile's `felems` entries -/

/-- **A `felems` entry of prototype `π`'s compile is an aliased `dotKF`'s.** -/
theorem xof_felemsA {π : ℕ} {P : Params} {cs : CS} {op : Op} {a : List Lin × ℕ × AuxK}
    (ha : a ∈ (stepOut (Xof π) P cs op).aux) {n : ℕ} (hn : a.2.2 = .felems n) :
    a.2.1 < cs.slots.size ∧ colA π a.2.1 n = some a.1 := by
  by_cases hd : ∃ w col, op = .dotKF w col
  · obtain ⟨w, col, rfl⟩ := hd
    simp only [stepOut] at ha
    cases hx : Xof π P cs (.dotKF w col) with
    | none => rw [hx, Option.getD_none, opOut_aux] at ha; cases ha
    | some o =>
      rw [hx, Option.getD_some] at ha
      rw [xof_dk] at hx
      obtain ⟨n', cells, hc, hlt, hau, -⟩ := dkA_some hx
      rw [hau, List.mem_singleton] at ha
      subst ha
      cases hn
      exact ⟨hlt, hc⟩
  · exfalso
    have h := xof_felems ha hn
    cases op <;> simp only [isDotKF, Bool.false_eq_true] at h
    exact hd ⟨_, _, rfl⟩

/-- **The `felems` auxiliary facts from `PfCells`** (prototype `π`, any answer-driven run of its program on
an input with a proof of the format's size). -/
theorem felems_of_pf {impl : OpImpl} {ι : Kind} {inp : Input} {tr : Trace} {s : St} {w : Asg} {π : ℕ}
    (hpc : PfCells w π inp) (hsz : inp.π.size = piSizeOf seq4)
    (he : execA impl ι inp (protoProg π).ops St.init tr = some (s, [])) :
    ∀ a ∈ (protoCS π).aux, isBitsA a = false →
      a.1.1.map (Lin.ev w) = a.1.2.2.val (rd (s.regs.extract 0 a.2) a.1.2.1) := by
  intro a ha hb
  rcases trail_aux (Xof π) (protoP π) AT.none _ _ none 0 ha with h0 | ⟨c, -, -, op, hcs, hm, -⟩
  · cases h0
  obtain ⟨⟨cells, r, kd⟩, m⟩ := a
  cases kd with
  | bits _ => cases hb
  | felems n =>
    obtain ⟨hlt, hcol⟩ := xof_felemsA hm rfl
    obtain ⟨f, o, len, es, hpr, hes, rfl⟩ := colA_some hcol
    have hreg : s.regs[r]? = some (.b (inp.π.extract (absOff f o) (absOff f o + len))) :=
      execA_prov _ _ _ he (by rw [← provLT_eq]; exact provOf_mem hpr)
    exact aux_colW hpc hes hsz.ge hreg (by rw [← hcs]; exact hlt)

/-- **`SlotRunF` from `PfCells`.** -/
theorem slotRunF_of_pf {impl : OpImpl} {π : ℕ} {ι : Kind} {inp : Input} {tr : Trace} {w : Asg}
    (hpc : PfCells w π inp) (hsz : inp.π.size = piSizeOf seq4) : SlotRunF impl π ι inp tr w :=
  fun _ he => felems_of_pf hpc hsz he

/-- **`Gaps4`** (FEL): `gaps4_of_runF`, with `SlotRunF` at every active slot from `PfCells`, which the
node's rows give (`pfCells_of_rows`). -/
theorem gaps4_fel : Sub4.Gaps4 :=
  gaps4_of_runF fun _ κ w _ _ _ hS v hv _ _ =>
    slotRunF_of_pf (pfCells_of_rows hS.1 hv) (by rw [slotIn_π, slotπ_size])

/-! ## Controls -/

namespace FelCtl

/-- (+) **`colEs`**: a 32-byte field at offset 32 of a 1000-byte proof, every window an element (`x / 16`),
gives its two elements; (−) a length not a multiple of 16, a field past the proof's end, a window that is
no element give `none`. -/
theorem colEs_ctl :
    colEs (fun x => some (x / 16)) 1000 32 32 = some [some 2, some 3] ∧
    colEs (fun x => some (x / 16)) 1000 32 40 = none ∧
    colEs (fun x => some (x / 16)) 50 32 32 = none ∧
    colEs (fun x => if x = 48 then none else some (x / 16)) 1000 32 32 = none := by
  refine ⟨rfl, rfl, rfl, rfl⟩

/-- (+) **`colCells`**: three cells of a two-window column at base 100 are the two elements' cells, then
the zero form. -/
theorem colCells_ctl : colCells 100 3 [some 2, some 3] = [Lin.cell 102, Lin.cell 103, []] := rfl

/-- (+) **The table**: a column in it gets its entry; (−) one not in it gets nothing (`colA` refuses). -/
theorem lookup_ctl :
    ([(7, some [some 2]), (9, none)] : List (ℕ × Option (List (Option ℕ)))).lookup 7 = some (some [some 2]) ∧
    ([(7, some [some 2]), (9, none)] : List (ℕ × Option (List (Option ℕ)))).lookup 8 = none := by
  refine ⟨rfl, rfl⟩

end FelCtl

end N4s
end FR

end G6_FRNodeRun4FE

section G6_FRSubmission4Fin

-- New for `flock-recursive` (BLUEPRINT revision 4.1, §5; stage S-H4, pass 11, item 5: the plug,
-- coordinator's ruling of 2026-10-29). The certificate of `sub4` from `Gaps4` alone.

/-!
# `certificate_sub4F`: the certificate of `sub4` from `Gaps4`; `Gaps4` holds (FEL)

With S-H4's node branch `nd` (`FRXNd4`: decode law `nodeDec4_nd`, links `LinksD4`, witness
`readW4 sigH`) and S-L4's `links4_sigH` (`Links4 nd D` from `Gaps4` for every decoder whose links
contain `LinksD4` and whose witness is `readW4 sigH`), `Open4`'s `dec` follows from its `gap`. What
the certificate still assumes is

**`Open4F := Gaps4`**: on every witness of the node statement with the reserve `StmtN4R` (SRA:
was `StmtN4`; the accepted run gives the reserve's cells and the true child claim), the slots'
circuit gap `Gap4R.imp` at the proof decoder `pf4` (S-E13a's residual; B4 closed `aggChk`; owners B3,
IMP, C1, SRA, ASK-P). `gap4Imp_of_rsv` (`FRNodeRsvLink`) reduces it further.

**Closed** (stage FEL): `open4F_holds : Open4F` (`N4s.gaps4_fel`), so `certificate_sub4'` and the challenge's
`certified` take no hypothesis.
-/

namespace FR.Sub4
open RecursionFast FR.Rev4 FR.X.X4

/-- **What the certificate of `sub4` still assumes**: the circuit's gaps. -/
def Open4F : Prop := Gaps4

/-- **`Open4` from `Open4F`**: `dec` is `links4_sigH` at S-H4's decoder. -/
theorem open4_of_F (h : Open4F) : Open4 := ⟨h, links4_sigH nodeDec4_nd (fun _ _ _ _ _ h => h) rfl h⟩

/-- **The contract's `Certificate` of `sub4`, given `Open4F`.** -/
theorem certificate_sub4F (h : Open4F) : Certificate sub4 := certificate_sub4 (open4_of_F h)

/-- **The certificate against a declared claim**, given `Open4F`. -/
theorem certificateR_sub4F (D : Declared) (hb : boundsOK D) (h : Open4F) : CertificateR D sub4 :=
  ⟨certificate_sub4F h, hb⟩

/-- **`Open4F` holds** (stage FEL): `Gaps4` is `N4s.gaps4_fel` (the `felems` cells aliased to arena₁, after
SEG-R2's `gaps4_of_runF`). -/
theorem open4F_holds : Open4F := N4s.gaps4_fel

/-- **The contract's `Certificate` of `sub4`** (FEL: unconditional). -/
theorem certificate_sub4' : Certificate sub4 := certificate_sub4F open4F_holds

/-! ## Controls -/

/-- (+) The decoder's links are exactly `LinksD4` and its witness `readW4 sigH` (the two side
conditions of `links4_sigH` hold by `rfl`). -/
theorem nodeDec4_nd_parts : nodeDec4_nd.Links = X.LinksD4 ∧ nodeDec4_nd.readW = X.readW4 X.sigH := ⟨rfl, rfl⟩

/-- (−) **The submission's node branch is not the empty one**: `sub4.ext` runs `nd`, not `ndNone`. -/
theorem sub4_ext_ne_none : sub4.ext = ext4With nd ∧ nd ≠ ndNone := ⟨rfl, nd_ne_ndNone⟩

end FR.Sub4

end G6_FRSubmission4Fin
