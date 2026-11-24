-- New for lvm6 (WP ST-5, STARTUP). The deployed program built by the fast builder: `progQ6F lay`, with
-- `progQ6F_eq : progQ6F lay = progQ6 lay`. Additive: `famQ6`, `progQ6` and every gadget are unchanged.
import Lvm6BuildF
import Lvm6NodeDeploy
import Lvm6NodeMbFG

/-!
# `progQ6F` (WP ST-5)

GST timed `progQ6 lay` at ≈ 3 s, CC's part (`ccGo`) at 2.2–2.6 s. The cost is `BM`'s `bind` (module doc of
`Lvm6BuildF`) at the gadgets whose left operand is large: `mapB` over the positions (`valsGenW`, `valsGen`,
`fpGen`; `t = 110` at level 0), the left-recursive loops of `posGen` (`boolsG`, `lanesG`, `posCells`), the
claim batch `wBatchG` (53 gadgets) and the four nested `glueGW` around it, and the family spine itself.

Each twin below is its gadget's text in `FM`, with `lift` at the leaves (gadgets whose own cost is small) and
the twins in place of the hot gadgets. Its `rep_…` lemma is the gadget's `Rep`, from `Lvm6BuildF`'s
homomorphism lemmas only (`rep_bind`, `rep_lift`, `rep_pure`, `rep_mapB`, `rep_forU`, `rep_leftAcc`): no gadget
semantics is reproved and no statement changes. **`progQ6F_eq`** is the only bridge to `progQ6`.
-/

set_option autoImplicit false

namespace Lvm6.BF

open Lvm Lvm.Loop Lvm.Loop.Build Lvm.Q2 Lvm.Typed Lvm6 Lvm6.QC Lvm6.Node Lvm6.Node.Dep

/-! ## Positions (`posGen`) -/

/-- `boolsG` as a loop. -/
def boolsGF (B : ℕ) (gate : Cell) (n : ℕ) : FM Unit := forUF (fun i ↦ lift (boolG (kc (B + i)) gate)) n

theorem rep_boolsG (B : ℕ) (gate : Cell) (n : ℕ) : Rep (boolsGF B gate n) (boolsG B gate n) :=
  rep_forU rfl (fun _ ↦ rfl) (fun _ ↦ rep_lift _) n

/-- `lanesG` as a loop. -/
def lanesGF (B : ℕ) (gate : Cell) (dd : ℕ → C2) (n : ℕ) : FM Unit :=
  forUF (fun i ↦ lift (laneG B (128 * i) (dd i).re gate >>= fun _ ↦ laneG B (128 * i + 64) (dd i).im gate)) n

theorem rep_lanesG (B : ℕ) (gate : Cell) (dd : ℕ → C2) (n : ℕ) :
    Rep (lanesGF B gate dd n) (lanesG B gate dd n) :=
  rep_forU rfl (fun _ ↦ rfl) (fun _ ↦ rep_lift _) n

/-- `posCells` as `mapB` over the range, in `FM`. -/
def posCellsF (B h c t : ℕ) : FM (List Cell) :=
  mapBF (fun k ↦ lift (posCell B (128 * (k / c) + h * (k % c)) h)) (List.range t)

theorem rep_posCells (B h c t : ℕ) : Rep (posCellsF B h c t) (posCells B h c t) :=
  rep_leftAcc rfl (fun _ ↦ rfl) (fun _ ↦ rep_lift _) t

/-- **`posGen`'s twin.** -/
def posGenF (B h c kq t : ℕ) (ds : Fin (kq + 1) → C2) (gate : Cell) : FM (List Cell) :=
  boolsGF B gate (128 * (kq + 1)) >>= fun _ ↦ lanesGF B gate (dsAt ds) (kq + 1) >>= fun _ ↦ posCellsF B h c t

theorem rep_posGen (B h c kq t : ℕ) (ds : Fin (kq + 1) → C2) (gate : Cell) :
    Rep (posGenF B h c kq t ds gate) (posGen B h c kq t ds gate) :=
  rep_bind (rep_boolsG _ _ _) fun _ ↦ rep_bind (rep_lanesG _ _ _ _) fun _ ↦ rep_posCells _ _ _ _

/-! ## The class constants, once per process -/

section Consts

open LeanVM.Parameters LeanVM.Protocol.Whir

/-- The diagonal `W_i(e_i)`, `i = i₀ … i₀ + k − 1`, carrying the table row `r = wRow n i` (one `wStep` a level). -/
def wDiagGo (n : ℕ) : ℕ → ℕ → List K → List K → List K
  | 0, _, _, acc => acc.reverse
  | k + 1, i, r, acc => wDiagGo n k (i + 1) (wStep i r) (r.getD i 0 :: acc)

theorem wDiagGo_eq (n : ℕ) : ∀ (k i : ℕ) (acc : List K),
    wDiagGo n k i (wRow n i) acc = acc.reverse ++ (List.range k).map fun j ↦ (wRow n (i + j)).getD (i + j) 0
  | 0, i, acc => by simp [wDiagGo]
  | k + 1, i, acc => by
    have e : wStep i (wRow n i) = wRow n (i + 1) := rfl
    rw [wDiagGo, e, wDiagGo_eq n k (i + 1), List.range_succ_eq_map]
    simp only [List.reverse_cons, List.append_assoc, List.singleton_append, List.map_cons, List.map_map,
      Nat.add_zero]
    congr 2
    refine List.map_congr_left fun j _ ↦ ?_
    have h : i + 1 + j = i + j.succ := by omega
    simp only [Function.comp_apply, h]

/-- **The diagonal is `cW`** (`n²` field products instead of `Σ i²` per call). -/
theorem wDiag_eq (n : ℕ) : wDiagGo n n 0 (wRow n 0) [] = (List.range n).map cW := by
  rw [wDiagGo_eq]
  simp only [List.reverse_nil, List.nil_append, Nat.zero_add]
  refine List.map_congr_left fun i hi ↦ ?_
  have hi' := List.mem_range.mp hi
  rw [wRow_getD n i (by omega) i hi', cW_eq]

/-- The table size: every call site has `n ≤ 20` (levels `max (ko + 2) ℓ` = 20, 16, 12, 8; final 8, 4). -/
def cWN : ℕ := 20

/-- `W_i(e_i)⁻¹` for `i < cWN` as data (printed by the ST-5 probe from `(cW i)⁻¹`). Untrusted: `invChk`
keeps an entry only if its product with `W_i(e_i)` is `1` (one product instead of an inversion, ≈ 1.9 ms). -/
def cWInvLit : List ℕ :=
  [1, 9223372036854775803, 16566595158504539616, 12911735938760240710, 2125028155691853901,
    4204569583749220094, 6707278589741703265, 1511496419735272010, 8683548997371710969, 120515905832802472,
    10797586625038654684, 5944514742312431224, 18149037763096777334, 15307119890373185988,
    18218058313307988331, 14663487748577323313, 4781568082007774283, 7330356837328886549,
    13911455371512638823, 16617999719419028343]

/-- `c⁻¹` from a candidate `d`: `d` if `c·d = 1`, else computed. -/
def invChk (c d : K) : K := if c * d == 1 then d else c⁻¹

theorem invChk_eq (c d : K) : invChk c d = c⁻¹ := by
  unfold invChk
  split
  · rename_i h
    exact (inv_eq_of_mul_eq_one_right (eq_of_beq h)).symm
  · rfl

/-- **`W_i(e_i)` and its inverse for `i < cWN`**: a closed constant, evaluated once at initialisation. -/
def cWTab : List (K × K) :=
  (wDiagGo cWN cWN 0 (wRow cWN 0) []).mapIdx fun i c ↦ (c, invChk c (K.ofBits (cWInvLit.getD i 0)))

/-- `(W_i(e_i), W_i(e_i)⁻¹)`: the table's entry, or computed past its end. -/
def cWP (i : ℕ) : K × K := if h : i < cWTab.length then cWTab[i] else (cW i, (cW i)⁻¹)

theorem cWP_eq (i : ℕ) : cWP i = (cW i, (cW i)⁻¹) := by
  unfold cWP
  split
  · rename_i h
    simp only [cWTab, wDiag_eq, List.getElem_mapIdx, List.getElem_map, List.getElem_range, invChk_eq]
  · rfl

end Consts

/-- **`wConsts`' twin**, from the table. -/
def wConstsF (z : C2) (n : ℕ) : FM (List C2 × List C2) :=
  mapBF (fun i ↦ lift (kConst (cWP i).1 z)) (List.range n) >>= fun cs ↦
    mapBF (fun i ↦ lift (kConst (cWP i).2 z)) (List.range n) >>= fun ci ↦ pure (cs, ci)

theorem rep_wConsts (z : C2) (n : ℕ) : Rep (wConstsF z n) (wConsts z n) :=
  rep_bind (rep_mapB (fun i ↦ by simp only [cWP_eq]; exact rep_lift _) _) fun _ ↦
    rep_bind (rep_mapB (fun i ↦ by simp only [cWP_eq]; exact rep_lift _) _) fun _ ↦ rep_pure _

/-- **`valsPre`'s twin.** -/
def valsPreF (κ ℓ : ℕ) (gate : Cell) : FM (C2 × C2 × (List C2 × List C2)) :=
  lift (g2Zero ⟨gate, gate⟩) >>= fun z ↦ lift (g2Const 1 z) >>= fun one ↦ wConstsF z (max (κ + 1) ℓ) >>= fun k ↦
    pure (z, one, k)

theorem rep_valsPre (κ ℓ : ℕ) (gate : Cell) : Rep (valsPreF κ ℓ gate) (valsPre κ ℓ gate) :=
  rep_bind (rep_lift _) fun _ ↦ rep_bind (rep_lift _) fun _ ↦ rep_bind (rep_wConsts _ _) fun _ ↦ rep_pure _

/-- **`fpPre`'s twin.** -/
def fpPreF (κ ℓ : ℕ) (gate : Cell) : FM (C2 × C2 × (List C2 × List C2)) :=
  lift (g2Zero ⟨gate, gate⟩) >>= fun z ↦ lift (g2Const 1 z) >>= fun one ↦ wConstsF z (fpN κ ℓ) >>= fun k ↦
    pure (z, one, k)

theorem rep_fpPre (κ ℓ : ℕ) (gate : Cell) : Rep (fpPreF κ ℓ gate) (fpPre κ ℓ gate) :=
  rep_bind (rep_lift _) fun _ ↦ rep_bind (rep_lift _) fun _ ↦ rep_bind (rep_wConsts _ _) fun _ ↦ rep_pure _

/-! ## Values (`valsGenW`, `valsGen`/`fvGen`, `fpGen`) -/

/-- **`foldG`'s twin** (the round's `mapB` as a loop). -/
def foldGF (z x : C2) : ℕ → List RndC → List C2 → FM C2
  | 0, _, ls => pure (ls.getD 0 z)
  | j + 1, rc, ls => lift (g2Mul (rc.headD (zR z)).β x (rc.headD (zR z)).α) >>= fun cc ↦
      mapBF (fun u ↦ lift (g2Mul cc (ls.getD (2 * u) z) (ls.getD (2 * u + 1) z))) (List.range (2 ^ j)) >>=
        fun ls' ↦ foldGF z x j rc.tail ls'

theorem rep_foldG (z x : C2) : ∀ (j : ℕ) (rc : List RndC) (ls : List C2), Rep (foldGF z x j rc ls) (foldG z x j rc ls)
  | 0, _, _ => rep_pure _
  | j + 1, _, _ => rep_bind (rep_lift _) fun _ ↦ rep_bind (rep_mapB (fun _ ↦ rep_lift _) _) fun _ ↦
      rep_foldG z x j _ _

/-- **`valAtW`'s twin** (one position). -/
def valAtWF (z one : C2) (k : List C2 × List C2) (zz : Bool) (ℓ κ : ℕ) (rc : List RndC)
    (hi : List C2) (pc : Cell) (r : List (Option ℕ)) : FM (C2 × List C2) :=
  lift (vChain z k.1 (max (κ + 1) ℓ - 1) 0 ⟨pc, z.re⟩) >>= fun ws ↦
  mapBF (fun i ↦ lift (nStep z (k.2.getD i z) (ws.getD i z))) (List.range (max (κ + 1) ℓ)) >>= fun nws ↦
  mapBF (fun s ↦ lift (novG z one nws s)) (List.range ℓ) >>= fun novs ↦
  lift (g2Dot z ((List.range ℓ).map fun s ↦ (hi.getD s z, novs.getD s z))) >>= fun d ↦
  lift (g2Mul (nws.getD κ z) d z) >>= fun hv ↦
  foldGF z ⟨pc, z.re⟩ ℓ rc (lanesC zz z.re ℓ r) >>= fun fv ↦
  lift (g2Add fv hv) >>= fun o ↦ pure (o, nws)

theorem rep_valAtW (z one : C2) (k : List C2 × List C2) (zz : Bool) (ℓ κ : ℕ) (rc : List RndC)
    (hi : List C2) (pc : Cell) (r : List (Option ℕ)) :
    Rep (valAtWF z one k zz ℓ κ rc hi pc r) (valAtW z one k zz ℓ κ rc hi pc r) :=
  rep_bind (rep_lift _) fun _ ↦ rep_bind (rep_mapB (fun _ ↦ rep_lift _) _) fun _ ↦
    rep_bind (rep_mapB (fun _ ↦ rep_lift _) _) fun _ ↦ rep_bind (rep_lift _) fun _ ↦
    rep_bind (rep_lift _) fun _ ↦ rep_bind (rep_foldG _ _ _ _ _) fun _ ↦ rep_bind (rep_lift _) fun _ ↦
    rep_pure _

/-- **`valAt`'s twin** (one position, CCV). -/
def valAtF (z one : C2) (k : List C2 × List C2) (zz : Bool) (ℓ κ : ℕ) (rc : List RndC) (hi : List C2)
    (pc : Cell) (r : List (Option ℕ)) : FM C2 :=
  lift (vChain z k.1 (max (κ + 1) ℓ - 1) 0 ⟨pc, z.re⟩) >>= fun ws ↦
  mapBF (fun i ↦ lift (nStep z (k.2.getD i z) (ws.getD i z))) (List.range (max (κ + 1) ℓ)) >>= fun nws ↦
  mapBF (fun s ↦ lift (novG z one nws s)) (List.range ℓ) >>= fun novs ↦
  lift (g2Dot z ((List.range ℓ).map fun s ↦ (hi.getD s z, novs.getD s z))) >>= fun d ↦
  lift (g2Mul (nws.getD κ z) d z) >>= fun hv ↦
  foldGF z ⟨pc, z.re⟩ ℓ rc (lanesC zz z.re ℓ r) >>= fun fv ↦
  lift (g2Add fv hv)

theorem rep_valAt (z one : C2) (k : List C2 × List C2) (zz : Bool) (ℓ κ : ℕ) (rc : List RndC)
    (hi : List C2) (pc : Cell) (r : List (Option ℕ)) :
    Rep (valAtF z one k zz ℓ κ rc hi pc r) (valAt z one k zz ℓ κ rc hi pc r) :=
  rep_bind (rep_lift _) fun _ ↦ rep_bind (rep_mapB (fun _ ↦ rep_lift _) _) fun _ ↦
    rep_bind (rep_mapB (fun _ ↦ rep_lift _) _) fun _ ↦ rep_bind (rep_lift _) fun _ ↦
    rep_bind (rep_lift _) fun _ ↦ rep_bind (rep_foldG _ _ _ _ _) fun _ ↦ rep_lift _

/-- **`valsGenW`'s twin.** -/
def valsGenWF (zz : Bool) (h ℓ κ : ℕ) (rc : List RndC) (hi : List C2) (ps : List Cell)
    (rows : List (List (Option ℕ))) (gate : Cell) : FM (List C2 × List (List C2)) :=
  valsPreF κ ℓ gate >>= fun e ↦
    mapBF (fun k ↦ valAtWF e.1 e.2.1 e.2.2 zz ℓ κ rc hi (ps.getD k gate) (rows.getD k []))
      (List.range ps.length) >>= fun prs ↦ pure (prs.map Prod.fst, prs.map Prod.snd)

theorem rep_valsGenW (zz : Bool) (h ℓ κ : ℕ) (rc : List RndC) (hi : List C2) (ps : List Cell)
    (rows : List (List (Option ℕ))) (gate : Cell) :
    Rep (valsGenWF zz h ℓ κ rc hi ps rows gate) (valsGenW zz h ℓ κ rc hi ps rows gate) :=
  rep_bind (rep_valsPre _ _ _) fun _ ↦ rep_bind (rep_mapB (fun _ ↦ rep_valAtW _ _ _ _ _ _ _ _ _ _) _) fun _ ↦
    rep_pure _

/-- **`fvGen`'s twin** (`valsGen false … []`). -/
def fvGenF (h ℓ κ : ℕ) (rc : List RndC) (ps : List Cell) (rows : List (List (Option ℕ))) (gate : Cell) :
    FM (List C2) :=
  valsPreF κ ℓ gate >>= fun e ↦
    mapBF (fun k ↦ valAtF e.1 e.2.1 e.2.2 false ℓ κ rc [] (ps.getD k gate) (rows.getD k []))
      (List.range ps.length)

theorem rep_fvGen (h ℓ κ : ℕ) (rc : List RndC) (ps : List Cell) (rows : List (List (Option ℕ)))
    (gate : Cell) : Rep (fvGenF h ℓ κ rc ps rows gate) (fvGen h ℓ κ rc ps rows gate) :=
  rep_bind (rep_valsPre _ _ _) fun _ ↦ rep_mapB (fun _ ↦ rep_valAt _ _ _ _ _ _ _ _ _ _) _

/-- **`fpGen`'s twin.** -/
def fpGenF (κ ℓ : ℕ) (sc : List C2) (ps : List Cell) (gate : Cell) : FM (List C2) :=
  fpPreF κ ℓ gate >>= fun e ↦
    mapBF (fun k ↦ lift (fpAt e.1 e.2.1 e.2.2 ℓ κ sc (ps.getD k gate))) (List.range ps.length)

theorem rep_fpGen (κ ℓ : ℕ) (sc : List C2) (ps : List Cell) (gate : Cell) :
    Rep (fpGenF κ ℓ sc ps gate) (fpGen κ ℓ sc ps gate) :=
  rep_bind (rep_fpPre _ _ _) fun _ ↦ rep_mapB (fun _ ↦ rep_lift _) _

/-! ## Levels -/

/-- **`levelGenW`'s twin**, over twins of its two gadget arguments. -/
def levelGenWF {kq : ℕ} (nh ko t : ℕ) (posG : (Fin (kq + 1) → C2) → Cell → FM (List Cell))
    (valsGW : List RndC → List C2 → List Cell → List (List (Option ℕ)) → Cell →
      FM (List C2 × List (List C2)))
    (g ℓ : ℕ) (lev : Level) (wdI lvN a : ℕ) (gate : Cell) :
    FM (List RndC × TailOutC × List (List C2)) :=
  lift (roundsGen g ℓ a gate) >>= fun rc ↦
  posG (fun j ↦ ansAt (a + 27 * ℓ + 2 * nh + 4 * 2 ^ lvN + 9 + 10 + 9 * ko + 2 * 1) j) gate >>= fun ps ↦
  valsGW rc ((List.range nh).map fun j ↦ ld2 (a + 27 * ℓ + 2 * j)) ps
    (openRows lev wdI (tailOpenAt nh ko kq lvN (a + 27 * ℓ) - 4) t) gate >>= fun r ↦
  pure (rc, ⟨(List.range nh).map fun j ↦ ld2 (a + 27 * ℓ + 2 * j),
    List.ofFn (fun j : Fin (ko + 1) ↦ ansAt (a + 27 * ℓ + 2 * nh + 4 * 2 ^ lvN + 9) j),
    ld2 (a + 27 * ℓ + 2 * nh + 4 * 2 ^ lvN + 9 + 10 + 9 * ko), ps,
    ansAt (a + 27 * ℓ + 2 * nh + 4 * 2 ^ lvN + 9 + 10 + 9 * ko + 2 * 1) (kq + 1), r.1⟩, r.2)

theorem rep_levelGenW {kq : ℕ} (nh ko t : ℕ) {posGF : (Fin (kq + 1) → C2) → Cell → FM (List Cell)}
    {posG : (Fin (kq + 1) → C2) → Cell → BM (List Cell)}
    {valsGWF : List RndC → List C2 → List Cell → List (List (Option ℕ)) → Cell →
      FM (List C2 × List (List C2))}
    {valsGW : List RndC → List C2 → List Cell → List (List (Option ℕ)) → Cell →
      BM (List C2 × List (List C2))}
    (hpos : ∀ ds gate, Rep (posGF ds gate) (posG ds gate))
    (hvals : ∀ rc hi ps rows gate, Rep (valsGWF rc hi ps rows gate) (valsGW rc hi ps rows gate))
    (g ℓ : ℕ) (lev : Level) (wdI lvN a : ℕ) (gate : Cell) :
    Rep (levelGenWF nh ko t posGF valsGWF g ℓ lev wdI lvN a gate)
      (levelGenW nh ko t posG valsGW g ℓ lev wdI lvN a gate) :=
  rep_bind (rep_lift _) fun _ ↦ rep_bind (hpos _ _) fun _ ↦ rep_bind (hvals _ _ _ _ _) fun _ ↦ rep_pure _

/-- **`levCall`'s twin.** -/
def levCallF (I : Inp) (B j : ℕ) (gate : Cell) : FM (List RndC × TailOutC × List (List C2)) :=
  let q := lp j
  levelGenWF q.ℓ q.ko q.t (posGenF (bOf B j) q.h q.c q.kq q.t) (valsGenWF (j == 0) q.h q.ℓ (q.ko + 1)) 10 q.ℓ
    (P17.lvl j) (wdOf j) (P17.lvl (j + 1)).lv (I.aL j) gate

theorem rep_levCall (I : Inp) (B j : ℕ) (gate : Cell) : Rep (levCallF I B j gate) (levCall I B j gate) := by
  unfold levCallF levCall
  try dsimp only
  exact rep_levelGenW _ _ _ (fun _ _ ↦ rep_posGen _ _ _ _ _ _ _) (fun _ _ _ _ _ ↦ rep_valsGenW _ _ _ _ _ _ _ _ _)
    _ _ _ _ _ _ _

/-! ## The weight cell (`wBatchG`, `glueGW`) and the final level -/

/-- **`wBatchG`'s twin.** -/
def wBatchGF (Gs : List (List C2 → Cell → BM C2)) (lc : C2) (rc : List RndC) (τ : List C2) (gate : Cell) :
    FM C2 :=
  mapBF (fun G ↦ lift (G (τ ++ rc.map (·.α)) gate)) Gs >>= fun ws ↦ lift (g2Zero lc) >>= fun z ↦
    lift (Lvm6.QC.hornerG z lc ws)

theorem rep_wBatchG (Gs : List (List C2 → Cell → BM C2)) (lc : C2) (rc : List RndC) (τ : List C2)
    (gate : Cell) : Rep (wBatchGF Gs lc rc τ gate) (wBatchG Gs lc rc τ gate) :=
  rep_bind (rep_mapB (fun _ ↦ rep_lift _) _) fun _ ↦ rep_bind (rep_lift _) fun _ ↦ rep_lift _

/-- **`glueGW`'s twin**, over a twin of the previous weight gadget. -/
def glueGWF (wGp : List RndC → List C2 → Cell → FM C2) (rcP : List RndC) (oc : TailOutC)
    (wss : List (List C2)) (rc : List RndC) (τ : List C2) (gate : Cell) : FM C2 :=
  let y := rc.map (·.α) ++ τ
  wGp rcP y gate >>= fun pv ↦
  lift (g2Zero oc.lam) >>= fun z ↦ lift (g2Const 1 z) >>= fun one ↦
  lift (prodFG z one (eqFac z one oc.z) oc.z.length y) >>= fun ev ↦
  lift (g2Mul oc.lam ev pv) >>= fun acc ↦
  lift (colsGW z one oc.lam y oc.z.length wss oc.lam acc)

theorem rep_glueGW {wGpF : List RndC → List C2 → Cell → FM C2} {wGp : List RndC → List C2 → Cell → BM C2}
    (hw : ∀ rcP y gate, Rep (wGpF rcP y gate) (wGp rcP y gate)) (rcP : List RndC) (oc : TailOutC)
    (wss : List (List C2)) (rc : List RndC) (τ : List C2) (gate : Cell) :
    Rep (glueGWF wGpF rcP oc wss rc τ gate) (glueGW wGp rcP oc wss rc τ gate) :=
  rep_bind (hw _ _ _) fun _ ↦ rep_bind (rep_lift _) fun _ ↦ rep_bind (rep_lift _) fun _ ↦
    rep_bind (rep_lift _) fun _ ↦ rep_bind (rep_lift _) fun _ ↦ rep_lift _

/-- **`finGen`'s twin**, over twins of its four gadget arguments. -/
def finGenF {kq : ℕ} (nf t : ℕ) (posG : (Fin (kq + 1) → C2) → Cell → FM (List Cell))
    (fvG : List RndC → List Cell → List (List (Option ℕ)) → Cell → FM (List C2))
    (fpG : List C2 → List Cell → Cell → FM (List C2)) (wG : List RndC → List C2 → Cell → FM C2)
    (_g _gT κ ℓ : ℕ) (lev : Level) (wdI a : ℕ) (σc : C2) (gate : Cell) : FM FinOutC :=
  let rc := roundsCells ℓ a
  let sc := (List.range nf).map fun j ↦ ld2 (a + 27 * ℓ + 2 * j)
  let ao := finOpenAt nf kq ℓ a
  posG (fun j ↦ ansAt (a + 27 * ℓ + 2 * nf) j) gate >>= fun ps ↦
  fvG rc ps (openRows lev wdI (ao - 4) t) gate >>= fun fs ↦
  fpG sc ps gate >>= fun es ↦
  lift (chkEqsG fs es gate) >>= fun _ ↦
  lift (foldsCG σc rc) >>= fun σf ↦
  lift (sc2 κ (ao + t * openStride lev) σf) >>= fun sr ↦
  lift (g2Zero σc) >>= fun z ↦
  lift (Lvm6.QC.mleG z κ sc sr.1) >>= fun mv ↦
  wG rc sr.1 gate >>= fun wv ↦
  lift (g2Mul wv mv sr.2) >>= fun e ↦
  lift (g2Assert e gate) >>= fun _ ↦
  pure ⟨rc, sc, ps, sr.1⟩

theorem rep_finGen {kq : ℕ} (nf t : ℕ) {posGF : (Fin (kq + 1) → C2) → Cell → FM (List Cell)}
    {posG : (Fin (kq + 1) → C2) → Cell → BM (List Cell)}
    {fvGF : List RndC → List Cell → List (List (Option ℕ)) → Cell → FM (List C2)}
    {fvG : List RndC → List Cell → List (List (Option ℕ)) → Cell → BM (List C2)}
    {fpGF : List C2 → List Cell → Cell → FM (List C2)} {fpG : List C2 → List Cell → Cell → BM (List C2)}
    {wGF : List RndC → List C2 → Cell → FM C2} {wG : List RndC → List C2 → Cell → BM C2}
    (hpos : ∀ ds gate, Rep (posGF ds gate) (posG ds gate))
    (hfv : ∀ rc ps rows gate, Rep (fvGF rc ps rows gate) (fvG rc ps rows gate))
    (hfp : ∀ sc ps gate, Rep (fpGF sc ps gate) (fpG sc ps gate))
    (hw : ∀ rc y gate, Rep (wGF rc y gate) (wG rc y gate))
    (g gT κ ℓ : ℕ) (lev : Level) (wdI a : ℕ) (σc : C2) (gate : Cell) :
    Rep (finGenF nf t posGF fvGF fpGF wGF g gT κ ℓ lev wdI a σc gate)
      (finGen nf t posG fvG fpG wG g gT κ ℓ lev wdI a σc gate) :=
  rep_bind (hpos _ _) fun _ ↦ rep_bind (hfv _ _ _ _) fun _ ↦ rep_bind (hfp _ _ _) fun _ ↦
    rep_bind (rep_lift _) fun _ ↦ rep_bind (rep_lift _) fun _ ↦ rep_bind (rep_lift _) fun _ ↦
    rep_bind (rep_lift _) fun _ ↦ rep_bind (rep_lift _) fun _ ↦ rep_bind (hw _ _ _) fun _ ↦
    rep_bind (rep_lift _) fun _ ↦ rep_bind (rep_lift _) fun _ ↦ rep_pure _

/-! ## The node families (`node6E`): one `lift` per part -/

section Node

open LeanVM.Parameters LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open Lvm.Har Lvm.E2V Lvm6.K Lvm6.KPack Lvm6.QK
open Lvm6 (Item rep rnd)

/-- **`treeG6`'s twin.** -/
def treeG6F (κ a : ℕ) (gate : Cell) : FM TreeOutC :=
  let q1 := layEnd (headItems κ) a
  let q2 := layEnd (rep 12 (P18.layer κ)) q1
  lift (treeHeadG κ a) >>= fun hd ↦
  lift (layers6G κ q1 (claim0 hd.value hd.mu (hd.u :: hd.ρ) hd.sl) gate) >>= fun cl ↦
  lift (treeMidG 8 q2 hd.cst (hd.sl.headD default) hd.lanes gate) >>= fun om ↦
  lift (En.treeEndG κ (layEnd midItems q2) cl gate) >>= fun en ↦
  pure ⟨hd.δ, hd.ρ, hd.dd, hd.u, om.1, om.2, en.2.1, en.2.2⟩

theorem rep_treeG6 (κ a : ℕ) (gate : Cell) : Rep (treeG6F κ a gate) (treeG6 κ a gate) :=
  rep_bind (rep_lift _) fun _ ↦ rep_bind (rep_lift _) fun _ ↦ rep_bind (rep_lift _) fun _ ↦
    rep_bind (rep_lift _) fun _ ↦ rep_pure _

/-- **`spG6`'s twin.** -/
def spG6F (h a : ℕ) (gate : Cell) : FM SpOutC :=
  let q1 := layEnd (spHeadItems h) a
  let q2 := layEnd (rep 12 (P18.layer h)) q1
  lift (spHeadG h a) >>= fun hd ↦
  lift (layers6G h q1 (claim0 hd.value hd.mu hd.r hd.sl) gate) >>= fun cl ↦
  lift (treeMidG 25 q2 hd.cst (hd.sl.headD default) hd.lanes gate) >>= fun om ↦
  lift (En.spEndG h (layEnd midItems q2) cl gate) >>= fun en ↦
  pure ⟨hd.r, hd.v, om.1, om.2, en.2.1, en.2.2⟩

theorem rep_spG6 (h a : ℕ) (gate : Cell) : Rep (spG6F h a gate) (spG6 h a gate) :=
  rep_bind (rep_lift _) fun _ ↦ rep_bind (rep_lift _) fun _ ↦ rep_bind (rep_lift _) fun _ ↦
    rep_bind (rep_lift _) fun _ ↦ rep_pure _

/-- **`node6E`'s twin.** -/
def node6EF (Ti : Lvm6.Ty.TInst6) (pubC : ℕ → Cell) (ain : List C2) (yIn : C2) (own : List C2) (ownY : C2)
    (gate : Cell) : FM NodeOutE :=
  treeG6F 18 aTree gate >>= fun t ↦ spG6F 13 aSp gate >>= fun s ↦
    lift (ksLinkG6 13 10 3816 7567 8032 aLink gate) >>= fun l ↦
      lift (Lvm6.QD.ty6 Ti pubC ain yIn own ownY aTy gate) >>= fun y ↦ pure ⟨t, s, l, y⟩

theorem rep_node6E (Ti : Lvm6.Ty.TInst6) (pubC : ℕ → Cell) (ain : List C2) (yIn : C2) (own : List C2)
    (ownY : C2) (gate : Cell) :
    Rep (node6EF Ti pubC ain yIn own ownY gate) (node6E Ti pubC ain yIn own ownY gate) :=
  rep_bind (rep_treeG6 _ _ _) fun _ ↦ rep_bind (rep_spG6 _ _ _) fun _ ↦ rep_bind (rep_lift _) fun _ ↦
    rep_bind (rep_lift _) fun _ ↦ rep_pure _

end Node

/-! ## CC and the families -/

/-- **`ccGI`'s twin.** -/
def ccGIF (I : Inp) (B : ℕ) (gate : Cell) : FM Unit :=
  lift (ringPhaseGen 17 I.svT I.svS I.vs I.aRing gate) >>= fun rp ↦
  levCallF I B 0 gate >>= fun l0 ↦ levCallF I B 1 gate >>= fun l1 ↦ levCallF I B 2 gate >>= fun l2 ↦
  levCallF I B 3 gate >>= fun l3 ↦
  lift (claimGlueG rp.val l0.1 l0.2.1) >>= fun s1 ↦ lift (claimGlueG s1 l1.1 l1.2.1) >>= fun s2 ↦
  lift (claimGlueG s2 l2.1 l2.2.1) >>= fun s3 ↦ lift (claimGlueG s3 l3.1 l3.2.1) >>= fun s4 ↦
  let w0 := wBatchGF (claimGs I rp) rp.lam
  let w4 := glueGWF (glueGWF (glueGWF (glueGWF w0 l0.1 l0.2.1 l0.2.2) l1.1 l1.2.1 l1.2.2) l2.1 l2.2.1 l2.2.2)
    l3.1 l3.2.1 l3.2.2
  finGenF 8 18 (posGenF (bOf B 4) 16 8 2 18) (fun rc ↦ fvGenF 16 4 2 rc) (fpGenF 2 4) w4 10 2 2 4
    (P17.lvl 4) 32 (I.aL 4) s4 gate >>= fun _ ↦ pure ()

theorem rep_ccGI (I : Inp) (B : ℕ) (gate : Cell) : Rep (ccGIF I B gate) (ccGI I B gate) :=
  rep_bind (rep_lift _) fun _ ↦ rep_bind (rep_levCall _ _ _ _) fun _ ↦ rep_bind (rep_levCall _ _ _ _) fun _ ↦
    rep_bind (rep_levCall _ _ _ _) fun _ ↦ rep_bind (rep_levCall _ _ _ _) fun _ ↦
    rep_bind (rep_lift _) fun _ ↦ rep_bind (rep_lift _) fun _ ↦ rep_bind (rep_lift _) fun _ ↦
    rep_bind (rep_lift _) fun _ ↦
    rep_bind (rep_finGen _ _ (fun _ _ ↦ rep_posGen _ _ _ _ _ _ _) (fun _ _ _ _ ↦ rep_fvGen _ _ _ _ _ _ _)
      (fun _ _ _ ↦ rep_fpGen _ _ _ _ _)
      (fun _ _ _ ↦ rep_glueGW (fun _ _ _ ↦ rep_glueGW (fun _ _ _ ↦ rep_glueGW (fun _ _ _ ↦
        rep_glueGW (fun _ _ _ ↦ rep_wBatchG _ _ _ _ _) _ _ _ _ _ _) _ _ _ _ _ _) _ _ _ _ _ _) _ _ _ _ _ _)
      _ _ _ _ _ _ _ _ _) fun _ ↦ rep_pure _

/-- **`ccGo`'s twin** (G0 merge fix: MBS added the tables `tabs` and `mbPre` to `ccGo`). -/
def ccGoF (o : NodeOutE) (lay : Lay) (tabs : List Lvm.M3.Tab) (B : ℕ) (gate : Cell) : FM Unit :=
  lift (ccPre o) >>= fun pr ↦ lift (mbPre tabs o gate) >>= fun mo ↦
    ccGIF (inpReal o lay pr.1 pr.2.1 pr.2.2 mo) B gate

theorem rep_ccGo (o : NodeOutE) (lay : Lay) (tabs : List Lvm.M3.Tab) (B : ℕ) (gate : Cell) :
    Rep (ccGoF o lay tabs B gate) (ccGo o lay tabs B gate) :=
  rep_bind (rep_lift _) fun _ ↦ rep_bind (rep_lift _) fun _ ↦ rep_ccGI _ _ _

/-- **`famQ6`'s twin, at given tables `T`** (G0: `famQ6` reads `mbTD lay`; a caller passes a fast equal value). -/
def famQ6FT (lay : Lay) (T : List Lvm.M3.Tab) : FM Unit :=
  node6EF (tiOf lay) (pubCOf lay) ainC yInC ownC ownYC gateC >>= fun o ↦ lift famR >>= fun _ ↦
    ccGoF o lay T ccbC gateC

/-- **`famQ6`'s twin.** -/
def famQ6F (lay : Lay) : FM Unit := famQ6FT lay (mbTD lay)

theorem rep_famQ6 (lay : Lay) : Rep (famQ6F lay) (famQ6 lay) :=
  rep_bind (rep_node6E _ _ _ _ _ _ _) fun _ ↦ rep_bind (rep_lift _) fun _ ↦ rep_ccGo _ _ _ _ _

/-- **The deployed program, built fast.** -/
def progQ6F (lay : Lay) : Program := toProgramB nK 0 (famQ6F lay)

/-- **It is the deployed program**, for every layout. -/
theorem progQ6F_eq (lay : Lay) : progQ6F lay = progQ6 lay :=
  toProgramB_eq (rep_famQ6 lay) nK 0

/-! ## The start-up path's fast builds (NODE3 wiring: ST-5 + MBF) -/

/-- **`progR`'s twin**: the families before CC, built fast. -/
def progRF (lay : Lay) : Program :=
  toProgramB nK 0 (node6EF (tiOf lay) (pubCOf lay) ainC yInC ownC ownYC gateC >>= fun _ ↦ lift famR)

theorem progRF_eq (lay : Lay) : progRF lay = progR lay :=
  toProgramB_eq (rep_bind (rep_node6E _ _ _ _ _ _ _) fun _ ↦ rep_lift _) nK 0

/-- **The deployed mini-bus tables, fast**: MBF's linear cap-cell pass (`mbTLF`) on the fast prefix build. -/
def mbTDQ (lay : Lay) : List Lvm.M3.Tab := Lvm6.Node.Mb.mbTLF (mbPar6 lay) (progRF lay) lay

theorem mbTDQ_eq (lay : Lay) : mbTDQ lay = mbTD lay := by
  rw [mbTDQ, progRF_eq, Lvm6.Node.Mb.mbTLF_eq]
  rfl

/-- **The deployed program, built fast, with fast tables.** -/
def progQ6Q (lay : Lay) : Program := toProgramB nK 0 (famQ6FT lay (mbTDQ lay))

theorem progQ6Q_eq (lay : Lay) : progQ6Q lay = progQ6 lay := by
  rw [progQ6Q, mbTDQ_eq]
  exact progQ6F_eq lay

end Lvm6.BF
