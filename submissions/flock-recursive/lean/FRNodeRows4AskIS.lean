-- New for `flock-recursive` (PACK-4.4.1 §1.3, §4.3; IMP-RESULT §5.3; track IMPC): `ATImp` for the
-- import-class generator `impcTG` (static proof reads, challenge conversions), and `imp` with it.
import FRNodeRows4AskTH
import FRNodeRows4AskB

/-!
# The import classes are sound (`atImp_impc`), and `imp` with them (`gap4Imp_of_impc`)

* **The tables** (`itOffA_getD`, `itemsA_getD`, `phIxA_getD`, `mem_pSegs`) are `itOff`, `itAt`, `phIx`
  and the fields' phase parts.
* **`pfLoc_spec`** (`reassemble4`'s positional spec, inverted): if `pfLoc o = some (k, q)`, proof byte
  `o` of `reassemble4 seq4 tr` is query byte `q` of trace entry `k`, for every trace.
* **`winE_spec`**, **`win_slot`**: at an active slot, a window `winE` accepts is the H cell of its
  element (`slot_qelem`), inside arena₁'s range.
* **`PfCells w π inp`**: arena₁'s cells of region `π` hold the windows of `inp.π`;
  **`pfCells_of_rows`**: the node's rows give it at every active slot (`a1_slot`, `win_slot`).
* **`atImp_impc`**: given `PfCells`, `impcTG X π` meets `ATImp`: a covered proof read's components are
  its windows' elements, a challenge conversion's are its answer's halves (from `InvK`).
* **`gap4Imp_of_impc`**: SRA's `gap4Imp_of_rsv` with `impcTG` beside the reserve (`withImpc`): what
  remains per slot is the ask template's `ATOk` and `SlotRunA` with `impcTG`'s classes out of the
  residual imports.
-/

namespace FR
namespace N4s
open RecursionFast Rev4 Circ TEval W4

/-! ## The tables -/

theorem scanl_getD (l : List ℕ) {k : ℕ} (hk : k ≤ l.length) :
    (l.scanl (· + ·) 0).toArray.getD k 0 = (l.take k).sum := by
  rw [Array.getD_eq_getD_getElem?, List.getElem?_toArray, List.getElem?_scanl, if_pos hk, Option.getD_some,
    List.sum_eq_foldl]

theorem itOffA_getD {k : ℕ} (hk : k ≤ (itemsOf seq4).length) : itOffA.getD k 0 = itOff k := by
  rw [itOffA, scanl_getD _ (by simpa using hk), itOff, List.map_take]

theorem itemsA_getD (k : ℕ) : itemsA.getD k .seed = itAt k := by
  rw [itemsA, itAt, Array.getD_eq_getD_getElem?, List.getElem?_toArray, List.getD_eq_getElem?_getD]

theorem itemsA_size : itemsA.size = (itemsOf seq4).length := by simp [itemsA]

theorem phIxA_getD {n : ℕ} (hn : n ≤ (phasesOf seq4).length) : phIxA.getD n 0 = X.phIx seq4 n := by
  rw [phIxA, scanl_getD _ (by simpa using hn), X.phIx, List.map_take]

theorem phasesA_getD {n : ℕ} (hn : n < (phasesOf seq4).length) :
    phasesA.getD n ("", .seed) = (phasesOf seq4)[n] := by
  rw [phasesA, Array.getD_eq_getD_getElem?, List.getElem?_toArray, List.getElem?_eq_getElem hn, Option.getD_some]

/-- **A phase part of `pSegs`** is field `f`'s bytes of phase `n`. -/
theorem mem_pSegs {s : PSeg} (h : s ∈ pSegs) : s.f < nFields4 ∧ ∃ hn : s.n < (phasesOf seq4).length,
    s.st = fieldOffOf seq4 s.f + phaseOffOf seq4 s.n s.f ∧ s.len = ((phasesOf seq4)[s.n]).2.bytesToL seq4.lv s.f := by
  simp only [pSegs, List.mem_flatMap, List.mem_range, List.mem_filterMap] at h
  obtain ⟨f, hf, n, hn, hs⟩ := h
  split_ifs at hs
  cases hs
  refine ⟨hf, hn, rfl, ?_⟩
  dsimp only
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hn, Option.getD_some]

/-! ## Where a proof byte comes from -/

theorem items_lt {n r : ℕ} (hn : n < (phasesOf seq4).length)
    (hr : r < (((phasesOf seq4)[n]).2.itemsL seq4.lv).length) : X.phIx seq4 n + r < (itemsOf seq4).length := by
  have h := X.itemsOf_phIx seq4 hn hr
  rw [List.getElem?_eq_getElem hr] at h
  by_contra hc
  rw [List.getElem?_eq_none (by omega)] at h
  exact absurd h (by simp)

/-- **`pfLoc`'s spec**: proof byte `o` of `reassemble4 seq4 tr` is query byte `q` of the trace's entry
`k`, for every trace `tr`. -/
theorem pfLoc_spec (tr : Trace) {o k q : ℕ} (h : pfLoc o = some (k, q)) :
    k < (itemsOf seq4).length ∧
      byteAt (X.reassemble4 seq4 tr) o = byteAt (tr.toArray.getD k (ByteArray.empty, 0)).1 q := by
  unfold pfLoc at h
  split at h
  · rename_i s hs
    have hmem := List.mem_of_find?_eq_some hs
    have hin : s.st ≤ o ∧ o < s.st + s.len := by simpa using List.find?_some hs
    obtain ⟨hf, hn, hst, hlen⟩ := mem_pSegs hmem
    rw [phasesA_getD hn, phIxA_getD (le_of_lt hn)] at h
    obtain ⟨⟨r, q'⟩, hr, he⟩ := Option.map_eq_some_iff.1 h
    simp only [Prod.mk.injEq] at he
    obtain ⟨rfl, rfl⟩ := he
    have ho : o = fieldOffOf seq4 s.f + phaseOffOf seq4 s.n s.f + (o - s.st) := by omega
    have hj : o - s.st < ((phasesOf seq4)[s.n]).2.bytesToL seq4.lv s.f := by omega
    rw [ho, X.reassemble4_byte seq4 tr hf hn hj]
    have hk := fun {r} => @items_lt s.n r hn
    generalize (phasesOf seq4)[s.n].2 = sh at hr hj hk
    generalize o - s.st = j at hr hj
    cases sh with
    | seed =>
      simp only [phItem] at hr
      split_ifs at hr with hfh
      cases hr
      simp only [Sh.bytesToL, if_pos hfh] at hj
      rw [hfh]
      exact ⟨by simpa using hk (r := 0) (by simp [Sh.itemsL]), X.ctb4_seed _ _ _ _ _ hj⟩
    | absorb g len =>
      simp only [phItem] at hr
      split_ifs at hr with hfg
      cases hr
      simp only [Sh.bytesToL, if_pos hfg] at hj
      subst hfg
      exact ⟨by simpa using hk (r := 0) (by simp [Sh.itemsL]), X.ctb4_absorb _ _ _ _ _ hj⟩
    | uni g =>
      simp only [phItem] at hr
      split_ifs at hr with hfg
      cases hr
      simp only [Sh.bytesToL, if_pos hfg] at hj
      subst hfg
      exact ⟨by simpa using hk (r := 0) (by simp [Sh.itemsL]), X.ctb4_uni _ _ _ _ _ hj⟩
    | rounds g n d inK =>
      simp only [phItem] at hr
      split_ifs at hr with hfg
      cases hr
      simp only [Sh.bytesToL, if_pos hfg] at hj
      subst hfg
      have hrb : 0 < roundBytes inK := by unfold roundBytes; split <;> norm_num
      have hp : j / roundBytes inK < n := Nat.div_lt_of_lt_mul (by rwa [Nat.mul_comm])
      have ht : j % roundBytes inK < roundBytes inK := Nat.mod_lt _ hrb
      have hjd : j = j / roundBytes inK * roundBytes inK + j % roundBytes inK := (Nat.div_add_mod' j _).symm
      refine ⟨hk (by simp [Sh.itemsL, List.length_flatten, List.sum_replicate]; omega), ?_⟩
      rw [hjd, X.ctb4_rounds _ _ _ _ _ hp ht, ← hjd]
    | queries i =>
      simp only [phItem] at hr
      split_ifs at hr with hfc
      cases hr
      simp only [Sh.bytesToL, if_pos hfc] at hj
      rw [hfc]
      have hcb : 0 < colBytes i := Nat.pos_of_ne_zero fun h0 => by simp [h0] at hj
      have hp : j / colBytes i < (seq4.lv i).t := Nat.div_lt_of_lt_mul (by rwa [Nat.mul_comm])
      have ht : j % colBytes i < colBytes i := Nat.mod_lt _ hcb
      have hjd : j = j / colBytes i * colBytes i + j % colBytes i := (Nat.div_add_mod' j _).symm
      refine ⟨hk ?_, ?_⟩
      · have hl : ((Sh.queries i).itemsL seq4.lv).length = (seq4.lv i).t * (1 + (seq4.lv i).sib) := by
          simp only [Sh.itemsL, posItemsL, List.length_flatten, List.map_replicate, List.length_cons,
            List.length_map, List.length_range, List.sum_replicate, smul_eq_mul]
          ring
        have : (1 + (seq4.lv i).sib) * (j / colBytes i) < (1 + (seq4.lv i).sib) * (seq4.lv i).t :=
          Nat.mul_lt_mul_of_pos_left hp (by omega)
        rw [hl, Nat.mul_comm (seq4.lv i).t]; exact this
      · rw [hjd, X.ctb4_cols _ _ _ _ _ hp ht, ← hjd]
    | squeezes n ch => simp [phItem] at hr
  · cases h

/-- **`winE`'s spec**: the window is query bytes `[q, q + 16)` of item `k`, on an element boundary, not in
the last block. -/
theorem winE_spec {o e : ℕ} (h : winE o = some e) : ∃ k q, k < (itemsOf seq4).length ∧
    q + 16 ≤ (itAt k).qlen ∧ (1 + itOff k + 8 + q) % 16 = 0 ∧ 1 + itOff k + (itAt k).slen + 64 ≤ N4c.segB ∧
    e = (1 + itOff k + 8 + q) / 16 ∧ ∀ t < 16, pfLoc (o + t) = some (k, q + t) := by
  unfold winE at h
  split at h
  · rename_i k q _
    dsimp only at h
    split_ifs at h with hc
    cases h
    obtain ⟨hal, hk, hq, hb, hall⟩ := hc
    rw [itemsA_size] at hk
    simp only [itOffA_getD (le_of_lt hk), itemsA_getD] at hal hq hb ⊢
    refine ⟨k, q, hk, hq, hal, hb, rfl, fun t ht => ?_⟩
    have := List.all_eq_true.1 hall t (List.mem_range.2 ht)
    simpa using this
  · cases h

/-- **A window `winE` accepts is its element's H cell** at an active slot (and the element is in
arena₁'s range). -/
theorem win_slot {κ : NodeKind} {w : Asg} {v : ℕ} (hv : N4c.Active4 (rd4 X.pf4) κ w v) {o e : ℕ}
    (h : winE o = some e) :
    F.ofBytes (bytesAt ((rd4 X.pf4).slotπ κ v w) o 16) = w (sCell (slotB0 κ v) e) ∧ e < arN := by
  obtain ⟨k, q, hk, hq, hal, hb, rfl, hall⟩ := winE_spec h
  have he := slotTr4_getElem? κ v w k
  rw [itAt_eq hk, Option.map_some] at he
  have hsl : (itAt k).slen = 8 + (itAt k).qlen + 32 := rfl
  refine ⟨?_, elem_arN (by omega)⟩
  rw [← slot_qelem hv hk he hb hq hal]
  refine congrArg F.ofBytes (Vector.ext fun r hr => ?_)
  rw [bytesAt, Vector.getElem_ofFn, Vector.getElem_ofFn, X.slotπ_byte]
  rw [show X.pf4 = X.reassemble4 seq4 from rfl, (pfLoc_spec _ (hall r hr)).2, Array.getD_eq_getD_getElem?,
    List.getElem?_toArray, he, Option.getD_some]

/-! ## The cells -/

/-- **Arena₁'s cells of region `π` hold the proof's element windows** (every window `winE` accepts). -/
def PfCells (w : Asg) (π : ℕ) (inp : Input) : Prop :=
  ∀ o e, winE o = some e → w (π * slotM4 + arA1 + e) = F.ofBytes (bytesAt inp.π o 16)

theorem slotIn_π (rd : N4c.Read4) (κ : NodeKind) (vk c₁ : Digest) (w : Asg) (v : ℕ) :
    (N4c.slotIn rd κ vk c₁ w v).π = rd.slotπ κ v w := by
  unfold N4c.slotIn; split <;> rfl

/-- **The node's rows give `PfCells`** at every active slot. -/
theorem pfCells_of_rows {κ : NodeKind} {vk c₁ c₂ : Digest} {w : Asg}
    (hS : N4c.StmtN4 κ (lRows4 κ) (nodeIRows4 κ) vk c₁ c₂ w) {v : ℕ} (hv : N4c.Active4 (rd4 X.pf4) κ w v) :
    PfCells (slotAsg κ v w) (protoOf κ v) (N4c.slotIn (rd4 X.pf4) κ vk c₁ w v) := by
  intro o e h
  obtain ⟨h1, h2⟩ := win_slot hv h
  rw [slotIn_π, h1, a1_slot (one_of_pubCells hS.2.2.2.2) hS.2.2.2.1 (active_lt X.pf4 hv) h2]

/-! ## The values -/

theorem bytesAt_lo (q : ByteArray) (o : ℕ) :
    (Vector.ofFn fun i : Fin 16 => (bytesAt q o 32)[i.1]) = bytesAt q o 16 :=
  Vector.ext fun i hi => by simp [bytesAt]

theorem bytesAt_hi (q : ByteArray) (o : ℕ) :
    (Vector.ofFn fun i : Fin 16 => (bytesAt q o 32)[16 + i.1]) = bytesAt q (o + 16) 16 :=
  Vector.ext fun i hi => by simp [bytesAt]; ring_nf

theorem chF_lo (x : Digest) : chF x 0 = dlo x :=
  congrArg F.ofBytes (Vector.ext fun i hi => by
    simp [digestBytes, Array.getD_eq_getD_getElem?, show i < 32 by omega])

theorem chF_hi (x : Digest) : chF x 1 = dhi x :=
  congrArg F.ofBytes (Vector.ext fun i hi => by
    simp [digestBytes, Array.getD_eq_getD_getElem?, show 16 + i < 32 by omega])

theorem map_eq_of_zip {α β γ : Type} {f : α → γ} {g : β → γ} : ∀ {l₁ : List α} {l₂ : List β},
    l₁.length = l₂.length → (∀ p ∈ l₁.zip l₂, f p.1 = g p.2) → l₁.map f = l₂.map g
  | [], [], _, _ => rfl
  | a :: l₁, b :: l₂, hl, h => by
    rw [List.map_cons, List.map_cons, h (a, b) List.mem_cons_self,
      map_eq_of_zip (by simpa using hl) fun p hp => h p (List.mem_cons_of_mem _ hp)]

theorem failRT_not {P : Params} {w : Asg} (hone : P.one.ev w = 1) : ¬ (failRT P).Holds w := by
  simp [failRT, Row.Holds, hone]

/-- **A proof read's rows**: with `PfCells`, its slot is `[some (t, ls)]` and `ls` carries the windows'
values. -/
theorem pfRows_ev {P : Params} {π : ℕ} {w : Asg} {inp : Input} (hone : P.one.ev w = 1)
    (hc : PfCells w π inp) {sl : List Slot} {t : Ty} {os : List ℕ} (hr : ∀ r ∈ pfRows P π sl t os, r.Holds w) :
    ∃ ls, sl = [some (t, ls)] ∧ ls.map (Lin.ev w) = os.map fun o => F.ofBytes (bytesAt inp.π o 16) := by
  unfold pfRows at hr
  split at hr
  · rename_i t' ls
    split_ifs at hr with ht
    · obtain ⟨rfl, hl⟩ := ht
      refine ⟨ls, rfl, map_eq_of_zip hl fun p hp => ?_⟩
      have hr' : ∀ r ∈ (match winE p.2 with | some e => [a1Row P π p.1 e] | none => [failRT P]), r.Holds w :=
        fun r hr0 => hr r (List.mem_flatMap.2 ⟨p, hp, hr0⟩)
      split at hr'
      · rename_i e he
        have := hr' _ List.mem_cons_self
        simp only [a1Row, Row.Holds, Lin.ev_sub, Lin.ev_cell, hone, one_mul, Lin.ev_nil] at this
        rw [sub_eq_zero.1 this, hc _ _ he]
      · exact absurd (hr' _ List.mem_cons_self) (failRT_not hone)
    · exact absurd (hr _ List.mem_cons_self) (failRT_not hone)
  · exact absurd (hr _ List.mem_cons_self) (failRT_not hone)

/-- **A challenge conversion's rows**: its slot is `[some (t, ls)]` and `ls` carries the answer's halves
(`c = 0`: `dlo`, else `dhi`). -/
theorem chRows_ev {P : Params} {w : Asg} {cs : CS} {regs : Array Val} {κ : Kind} (hone : P.one.ev w = 1)
    (hinv : InvK w cs regs κ) {a : ℕ} {sl : List Slot} {t : Ty} {cc : List ℕ}
    (hr : ∀ r ∈ chRows P cs a sl t cc, r.Holds w) :
    ∃ x ls, rd regs a = .d x ∧ sl = [some (t, ls)] ∧
      ls.map (Lin.ev w) = cc.map fun c => if c = 0 then dlo x else dhi x := by
  unfold chRows at hr
  split at hr
  · rename_i a₀ a₁ t' ls hlk hsa
    split_ifs at hr with ht
    · obtain ⟨rfl, hl⟩ := ht
      have hrep := rep_of_invK hinv a
      rw [CS.slotK, hlk, hsa] at hrep
      obtain ⟨hty, hev⟩ := hrep
      generalize rd regs a = y at hty hev
      cases y <;> simp only [tyOf, reduceCtorEq, Option.some.injEq] at hty
      rename_i x
      simp only [List.map_cons, List.map_nil, encV, List.cons.injEq, and_true] at hev
      refine ⟨x, ls, rfl, rfl, map_eq_of_zip hl fun p hp => ?_⟩
      have := hr _ (List.mem_map.2 ⟨p, hp, rfl⟩)
      simp only [eqLRow, Row.Holds, Lin.ev_sub, hone, one_mul, Lin.ev_nil] at this
      rw [sub_eq_zero.1 this]
      split_ifs
      · exact hev.1
      · exact hev.2
    · exact absurd (hr _ List.mem_cons_self) (failRT_not hone)
  · exact absurd (hr _ List.mem_cons_self) (failRT_not hone)

/-! ## `ATImp` -/

/-- **The import classes are sound** where arena₁ holds the proof's windows (`PfCells`): a covered
proof read's components are its windows' values, a challenge conversion's its answer's halves. -/
theorem atImp_impc {impl : OpImpl} {X : Ext} {π : ℕ} {pv : List (ℕ × ℕ × ℕ × ℕ)} {κ : Kind} {inp : Input}
    {w : Asg} (h : PfCells w π inp) : ATImp impl X (impcTG X π pv).toAT κ inp w := by
  intro P cs pre op k regs vs ok hcov hc hev himp
  obtain ⟨hsel, hinv, -, hrows⟩ := hc
  have hr : ∀ r ∈ impcRows X π pv P cs op, r.Holds w := hrows
  have hone := hsel.1
  cases op with
  | piElem f o =>
    simp only [evalOp, Res.vals.injEq] at hev
    obtain ⟨rfl, -⟩ := hev
    obtain ⟨ls, hsl, hls⟩ := pfRows_ev hone h hr
    rw [hsl]
    exact .cons ⟨rfl, by rw [hls]; rfl⟩ .nil
  | piElemK f o =>
    simp only [evalOp, Res.vals.injEq] at hev
    obtain ⟨rfl, -⟩ := hev
    obtain ⟨ls, hsl, hls⟩ := pfRows_ev hone h hr
    rw [hsl]
    refine .cons ⟨rfl, ?_⟩ .nil
    rw [hls]
    simp only [List.map_cons, List.map_nil, encV, encK, K.ofBytes, bytesAt_lo, bytesAt_hi]
  | piDigest f o =>
    simp only [evalOp, Res.vals.injEq] at hev
    obtain ⟨rfl, -⟩ := hev
    obtain ⟨ls, hsl, hls⟩ := pfRows_ev hone h hr
    rw [hsl]
    refine .cons ⟨rfl, ?_⟩ .nil
    rw [hls]
    simp only [List.map_cons, List.map_nil, encV, digestAt_eq, dlo, dhi, bytesAt_lo, bytesAt_hi]
  | chF a c =>
    simp only [evalOp, Res.vals.injEq] at hev
    obtain ⟨rfl, -⟩ := hev
    obtain ⟨x, ls, hx, hsl, hls⟩ := chRows_ev hone hinv hr
    have hc2 : c < 2 := by simpa [TG.toAT, impcTG, impcCov] using hcov
    rw [hsl]
    refine .cons ⟨rfl, ?_⟩ .nil
    rw [hls, hx]
    rcases (by omega : c = 0 ∨ c = 1) with rfl | rfl
    · simp only [List.map_cons, List.map_nil, encV, Val.toD, chF_lo, ite_true]
    · simp only [List.map_cons, List.map_nil, one_ne_zero, ite_false, encV, Val.toD, chF_hi]
  | chK a =>
    simp only [evalOp, Res.vals.injEq] at hev
    obtain ⟨rfl, -⟩ := hev
    obtain ⟨x, ls, hx, hsl, hls⟩ := chRows_ev hone hinv hr
    rw [hsl]
    refine .cons ⟨rfl, ?_⟩ .nil
    rw [hls, hx]
    simp only [List.map_cons, List.map_nil, one_ne_zero, ite_false, ite_true, encV, encK, Val.toD, chK, K.ofBytes,
      dlo, dhi]
  | assertZero a act =>
    simp only [impcRows, himp, if_true] at hr
    exact absurd (hr _ List.mem_cons_self) (failRT_not hone)
  | _ => simp [TG.toAT, impcTG, impcCov] at hcov

/-- **The column-word generator meets `ATImp`** (it covers `dotKF` only, as a non-import). -/
theorem atImp_col {impl : OpImpl} {X : Ext} {π : ℕ} {pv : List (ℕ × ℕ × ℕ × ℕ)} {κ : Kind} {inp : Input}
    {w : Asg} : ATImp impl X (colTG X π pv).toAT κ inp w := by
  intro P cs pre op k regs vs ok hcov hc _ himp
  have hcov' : isDotKF op = true := hcov
  have hr : ∀ r ∈ (colTG X π pv).rows P cs pre op k, r.Holds w := hc.2.2.2
  simp only [colTG, hcov', himp, if_true] at hr
  exact absurd (hr _ List.mem_cons_self) (failRT_not hc.1.1)

/-! ## `imp` with the import classes -/

/-- Prototype `π`'s template: SRA's `withRsv` (the ask template `Aq π`, `input`, the reserve), then the
import classes. -/
def withImpc (Aq : ℕ → AT) (π : ℕ) : AT := (withRsv Aq π).add (impcTG (Xof π) π (provLT 0 (protoProg π).ops)).toAT

/-- **`imp` with the import classes discharged** (SRA's `gap4Imp_of_rsv` plus `atImp_impc`): what remains
per active slot and selectable index is the ask template's `ATOk` and the residual run facts, whose
imports no longer include the static proof reads and the challenge conversions. -/
theorem gap4Imp_of_impc {rt : ℕ → RT} {Aq : ℕ → AT} {impl₀ : OpImpl} {base : NodeKind → OpImpl}
    (hT₀ : ImplT impl₀) (hT : ∀ ν, ImplT (base ν)) (hok : RepOk rt impl₀ base) (hpf : PfHdr X.pf4)
    (hpv : PfView X.pf4) {κ : NodeKind} {vk c₁ c₂ : Digest} {w : Asg} {ch : List F} {b : ℕ}
    (hfoldR : ∀ v < κ.vslots, ∀ p ∈ repIRows4 rt κ v, p ∈ nodeIRows4 κ)
    (hfoldA : ∀ v < κ.vslots, ∀ p ∈ askIRows4 (withImpc Aq) κ v b, p ∈ nodeIRows4 κ)
    (hS : N4c.StmtN4R κ (lRows4 κ) (nodeIRows4 κ) vk c₁ c₂ w ch)
    (h : ∀ v, N4c.Active4 (rd4 X.pf4) κ w v → ∀ ι, SelOk (slotAsg κ v w) (protoP (protoOf κ v)) ι →
      ATOk (implP impl₀ base (protoOf κ v) ι) (Xof (protoOf κ v)) (Aq (protoOf κ v)) ι
          (N4c.slotIn (rd4 X.pf4) κ vk c₁ w v) (slotAsg κ v w) ((rd4 X.pf4).slotTr κ v w) ∧
        SlotRunA (rt (protoOf κ v)) (withImpc Aq (protoOf κ v)) (implP impl₀ base (protoOf κ v) ι)
          (protoOf κ v) ι (N4c.slotIn (rd4 X.pf4) κ vk c₁ w v) ((rd4 X.pf4).slotTr κ v w) (slotAsg κ v w)) :
    ∀ v, N4c.Active4 (rd4 X.pf4) κ w v →
      SlotImp impl₀ base κ v w (N4c.slotIn (rd4 X.pf4) κ vk c₁ w v) ((rd4 X.pf4).slotTr κ v w) :=
  gap4Imp_of_runS hT₀ hT hok hpf hpv hfoldR hfoldA hS.1 fun v hv ι hι =>
    ⟨atOk_add (atOk_add (atOk_add (h v hv ι hι).1 (atImp_inp (inpCells_of_rows hpv hpf hS.1 v hv ι hι)))
      (atImp_rsv_slot hS.2.1 hS.2.2 v ι _)) (atImp_impc (pfCells_of_rows hS.1 hv)), (h v hv ι hι).2⟩

/-! ## Controls -/

/-- The node's generator with the import classes (`askTG`, which now folds `impcTG`: ASK-T). -/
def askTGI (π : ℕ) : TG :=
  (((askTGT (XofT π) π).add (inpTG (XofT π) π)).add (rsvTG (XofT π) π)).add
    (impcTG (XofT π) π (provLT 0 (protoProg π).ops))

/-- (+) **The edit composes**: today's template (ASK-T's ask template `askAq` with the import classes)
has `askTGI`'s fields, so `askFold`'s hypothesis holds by `rfl`. -/
theorem withImpc_askT (π : ℕ) :
    (withImpc askAq π).cov = (askTGI π).cov ∧ (withImpc askAq π).rows = (askTGI π).rows :=
  ⟨rfl, rfl⟩

/-- (+) The generator covers the challenge conversions; (−) not a third challenge coordinate or an
`input`. -/
theorem impcCov_ctl : impcCov (.chF 0 0) = true ∧ impcCov (.chK 3) = true ∧ impcCov (.chF 0 2) = false ∧
    impcCov (.input 0) = false := by
  decide

/-- (+) **A challenge conversion's row**: on an answer register with a digest slot (the same at every
kind), `chF a 0`'s cell is tied to its first half; (−) on an untracked register the row fails. -/
theorem chRows_ctl (P : Params) :
    chRows P { CS.init 0 with slots := #[some (.d, [Lin.cell 0, Lin.cell 1])] } 0 [some (.f, [Lin.cell 2])] .f [0] =
      [eqLRow P (Lin.cell 2) (Lin.cell 0)] ∧
    chRows P (CS.init 0) 0 [some (.f, [Lin.cell 2])] .f [0] = [failRT P] := ⟨rfl, rfl⟩

/-- (−) **`PfCells` is load-bearing**: a covered window's row ties the import cell to arena₁'s cell, so
an assignment where that cell differs from the window breaks the row (one = 1, import cell 1, arena
cell 0). -/
theorem a1Row_neg (π e : ℕ) : ¬ (a1Row ⟨Lin.cell 0, fun _ => []⟩ π (Lin.cell 1) e).Holds
    (fun c => if c = 0 ∨ c = 1 then 1 else 0) := by
  have h : π * slotM4 + arA1 + e ≠ 0 ∧ π * slotM4 + arA1 + e ≠ 1 := by
    constructor <;> (unfold arA1; omega)
  simp only [a1Row, Row.Holds, Lin.ev_sub, Lin.ev_cell, Lin.ev_nil, h.1, h.2, or_self, if_false, true_or,
    if_true, one_mul, sub_zero]
  exact one_ne_zero

end N4s
end FR
