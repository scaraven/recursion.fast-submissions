-- New for lvm6 (WP CC8, second slice). The `Ŵ` cells shared between a level's values and its glue
-- (PHI-decision §3.2: no second `W_i(a)` chain), and the claim chain `gluedC` that feeds the final
-- level's claim cell. Statements first (frozen before the proofs), then the gadgets.
import Lvm6QCFinE

/-!
# Shared `Ŵ` cells and the claim chain (CC8, second slice)

**Statements** (Category A, CC8):
* `WsRep M ps wss n`: the cells `wss` hold `Ŵ_i(K(x))`, `i < n`, for each position cell `x` of `ps`.
* `ValsWAt c M vals n G`: `ValsAt`'s values, and `WsRep` of the second output.
* **`LevelHarWStmt L G n`** (CC-4 with the shared cells): `G posG valsGW g ℓ lev wdI lvN a gate`
  re-executes `levelP`; Rep: `LevelRep` and `WsRep` of the positions' `Ŵ` cells.
* **`WGlueWStmt G`** (CC-8g with the shared cells): the glue step reads `Ŵ` cells `wss` (`n ≥ ko + 1`)
  on memories where `WsRep M oc.ps wss n` holds, instead of calling a `Ŵ` gadget.
* **`ClaimGlueStmt G`** (CC-8c): from cells of a level's claim, rounds and interface, the next
  level's claim `gluedC (foldsC ℓ rs σ) y λ c`.

**Gadgets and proofs**: `valAtW` (CCV's `valAt`, handing out its `Ŵ_i(a)` cells), `valsGenW`,
`valsGenW_ok`; `levelGenW`, **`levelHarW`**; `colsGW`, `glueGW`, **`glueHarW`**; `psumG`,
`claimGlueG`, **`claimGlueHar`**. Each gadget is one call per instance, no instance constant.
-/

set_option autoImplicit false

namespace Lvm6.QC

open LeanVM.Parameters LeanVM.Protocol.Compile LeanVM.Protocol.Verifier LeanVM.Protocol.Whir
open Lvm Lvm.Loop Lvm.Loop.Build Lvm.Q2 Lvm.Har Lvm.E2V Lvm6.QK
open Lvm6 (Item Level)

variable {c : Ctx} {M : Mem}

/-! ## Statements -/

/-- **The `Ŵ` cells of the positions**: list `k` holds `Ŵ_i(K(x_k))`, `i < n`. -/
def WsRep (M : Mem) (ps : List Cell) (wss : List (List C2)) (n : ℕ) : Prop :=
  wss.map (·.map (ev2 M)) =
    ps.map fun x ↦ (List.range n).map fun i ↦ algebraMap K E2 (normVanishingAt i (kv M x))

/-- **A value gadget with `Ŵ` cells** (at a memory): `ValsAt`'s values, and the positions' `Ŵ`. -/
def ValsWAt {n t : ℕ} (c : Ctx) (M : Mem)
    (vals : List E2 → (Fin t → Fin n) → List (List K) → Fin t → E2) (nw : ℕ)
    (G : List C2 → List Cell → List (List (Option ℕ)) → Cell → BM (List C2 × List (List C2))) :
    Prop :=
  ∀ (hi : List C2) (ps : List Cell) (rows : List (List (Option ℕ))) (gate : Cell), gate.val M = 1 →
    HsA c M (G hi ps rows gate) fun r ↦ (∀ p : Fin t → Fin n,
      posOf M ps = List.ofFn (fun k ↦ (p k : ℕ)) →
        r.1.map (ev2 M) = List.ofFn (vals (hi.map (ev2 M)) p (rowsOf M rows))) ∧ WsRep M ps r.2 nw

/-- **CC-4 with the shared `Ŵ` cells** (statement). -/
def LevelHarWStmt {n n' m' : ℕ} (L : Whir.TailIface E2 n n' m') (nw : ℕ)
    (G : ((Fin (L.kq + 1) → C2) → Cell → BM (List Cell)) →
      (List RndC → List C2 → List Cell → List (List (Option ℕ)) → Cell →
        BM (List C2 × List (List C2))) →
      ℕ → ℕ → Level → ℕ → ℕ → ℕ → Cell → BM (List RndC × TailOutC × List (List C2))) : Prop :=
  ∀ (vals : List (Whir.Rnd E2) → List E2 → (Fin L.t → Fin n) → List (List K) → Fin L.t → E2)
    posG valsGW, PosOK L.pos posG →
    (∀ c M rc rs, RndsRep M rc rs → ValsWAt c M (vals rs) nw (valsGW rc)) →
    ∀ (g ht wd i gO gQ ℓ : ℕ), g ≤ 64 → gO ≤ 64 → gQ ≤ 64 →
    ∀ (lev : Level) (wdI lvN a : ℕ) (gate : Cell),
      HarO gate (G posG valsGW g ℓ lev wdI lvN a gate)
        (Whir.levelP Whir.chalE2 L g gO gQ ht wd i ℓ vals)
        (layRounds g ℓ a ++ layTail L.nh L.ko L.kq L.t lev wdI ht wd lvN gO gQ (a + 27 * ℓ))
        fun M o out ↦ LevelRep M (o.1, o.2.1) out ∧ WsRep M o.2.1.ps o.2.2 nw

/-- **CC-8g with the shared `Ŵ` cells** (statement). -/
def WGlueWStmt (G : (List RndC → List C2 → Cell → BM C2) → List RndC → TailOutC →
    List (List C2) → List RndC → List C2 → Cell → BM C2) : Prop :=
  ∀ (κ' ℓ' ko t h ℓ nw : ℕ), 0 + ℓ' + κ' = ko + 1 → ko + 1 ≤ nw →
    ∀ (w : Whir.WtE.Wt (0 + ℓ)) (Pre : Mem → Prop) wGp, Whir.wokE (ko + 1) ℓ w → WAt Pre w wGp →
    ∀ (rcP : List RndC) (rs : List (Whir.Rnd E2)) (oc : TailOutC) (o : Whir.TailOut E2 ko t (2 ^ h))
      (wss : List (List C2)), rs.length = ℓ →
      WAt (ℓ := ℓ') (fun M ↦ Pre M ∧ RndsRep M rcP rs ∧ TailRep M oc o ∧ WsRep M oc.ps wss nw)
        (Whir.wGlueE κ' ℓ' ko t h (Whir.wFolds Whir.WtE ℓ rs w) o) (G wGp rcP oc wss)

/-- **CC-8c, the claim chain** (statement): `G σc rc oc` is the next level's claim
`gluedC (foldsC ℓ rs σ) y λ c` when `σc` holds `σ` and the cells represent the rounds and interface. -/
def ClaimGlueStmt (G : C2 → List RndC → TailOutC → BM C2) : Prop :=
  ∀ (c : Ctx) (M : Mem) (σc : C2) (rc : List RndC) (rs : List (Whir.Rnd E2)) (oc : TailOutC)
    {ko t n : ℕ} (o : Whir.TailOut E2 ko t n), RndsRep M rc rs → TailRep M oc o →
    HsA c M (G σc rc oc) fun s ↦
      ev2 M s = Whir.gluedC (Whir.foldsC rs.length rs (ev2 M σc)) o.y o.lam o.c

/-! ## `mapB` with any output -/

theorem hs_mapB2 {α β γ : Type} (f : α → BM β) (F : α → γ) (g : β → γ)
    (hf : ∀ a, Hs c M (f a) fun r ↦ g r = F a) :
    ∀ l : List α, Hs c M (mapB f l) fun rs ↦ rs.map g = l.map F
  | [] => hs_pure rfl
  | a :: l => hs_bind (hf a) fun r hr ↦ hs_bind (hs_mapB2 f F g hf l) fun rs hrs ↦
    hs_pure (by rw [List.map_cons, List.map_cons, hr, hrs])

theorem map_range_getD {α β : Type} (G : α → β) (l : List α) (d : α) :
    (List.range l.length).map (fun k ↦ G (l.getD k d)) = l.map G := by
  apply List.ext_getElem
  · simp
  intro k h1 _
  simp only [List.getElem_map, List.getElem_range]
  rw [List.getD_eq_getElem _ _ (by simpa using h1)]

/-! ## The value gadget handing out its `Ŵ` cells -/

/-- **CCV's `valAt`, with its `Ŵ_i(a)` cells** (`i < max (κ + 1) ℓ`) as a second output. -/
def valAtW (z one : C2) (k : List C2 × List C2) (zz : Bool) (ℓ κ : ℕ) (rc : List RndC)
    (hi : List C2) (pc : Cell) (r : List (Option ℕ)) : BM (C2 × List C2) :=
  vChain z k.1 (max (κ + 1) ℓ - 1) 0 ⟨pc, z.re⟩ >>= fun ws ↦
  mapB (fun i ↦ nStep z (k.2.getD i z) (ws.getD i z)) (List.range (max (κ + 1) ℓ)) >>= fun nws ↦
  mapB (novG z one nws) (List.range ℓ) >>= fun novs ↦
  g2Dot z ((List.range ℓ).map fun s ↦ (hi.getD s z, novs.getD s z)) >>= fun d ↦
  g2Mul (nws.getD κ z) d z >>= fun hv ↦
  foldG z ⟨pc, z.re⟩ ℓ rc (lanesC zz z.re ℓ r) >>= fun fv ↦
  g2Add fv hv >>= fun o ↦ pure (o, nws)

theorem hs_valAtW {z one : C2} (hz : ev2 M z = 0) (hone : ev2 M one = 1) (k : List C2 × List C2)
    (zz : Bool) (ℓ κ : ℕ) (hk : ConstsOK M z (max (κ + 1) ℓ) k)
    {rc : List RndC} {rs : List (Whir.Rnd E2)} (hrep : RndsRep M rc rs) (hi : List C2) (pc : Cell)
    (r : List (Option ℕ)) :
    Hs c M (valAtW z one k zz ℓ κ rc hi pc r) fun o ↦
      (ev2 M o.1, o.2.map (ev2 M)) = (valOf rs zz ℓ κ (hi.map (ev2 M)) (kv M pc) (r.map (lw M)),
        (List.range (max (κ + 1) ℓ)).map fun i ↦ algebraMap K E2 (normVanishingAt i (kv M pc))) := by
  have hzk := kv_re_zero hz
  have hx : ev2 M ⟨pc, z.re⟩ = algebraMap K E2 (kv M pc) := by rw [ev2_mk, hzk]; rfl
  have hx0 : ev2 M ⟨pc, z.re⟩ = algebraMap K E2 (vanishingAt 0 (kv M pc)) := by
    rw [hx, vanishingAt_zero_idx]
  have hn1 : 0 + (max (κ + 1) ℓ - 1) ≤ max (κ + 1) ℓ := by omega
  refine hs_bind (hs_vChain hz k.1 _ (fun i hi ↦ (hk i hi).1) (kv M pc) _ 0 _ hn1 hx0) fun ws hws ↦
    hs_bind (hs2_mapB _ (fun i ↦ algebraMap K E2 (normVanishingAt i (kv M pc))) _ fun i hi ↦
      hs_nStep hz i _ _ _ (hk i (List.mem_range.mp hi)).2 (by
        have := List.mem_range.mp hi
        rw [hws i (by omega), zero_add])) fun nws hnws ↦ ?_
  have hn : ∀ i < max (κ + 1) ℓ, ev2 M (nws.getD i z) =
      algebraMap K E2 (normVanishingAt i (kv M pc)) := fun i hi ↦ by
    rw [ev2_getDz hnws hz, getD_range_map _ _ hi]
  refine hs_bind (hs2_mapB _ (fun s ↦ algebraMap K E2 (novelAt s (kv M pc))) _ fun s hs ↦
    hs_novG hz hone _ nws hn s (lt_of_lt_of_le (List.mem_range.mp hs) (le_max_right _ _)))
    fun novs hnovs ↦ hs_bind (hs2_dot z _) fun d hd ↦ hs_bind (hs2_mul _ d z) fun hv hhv ↦
    hs_bind (hs_foldG hz _ ℓ rc rs hrep _ (Whir.laneVal zz (r.map (lw M))) fun s hs ↦ ?_)
    fun fv hfv ↦ hs_bind (hs2_add fv hv) fun o ho ↦ hs_pure ?_
  · rw [lanesC, getD_range_map _ _ hs, ev2_laneC hzk]
  · have hL : ((List.range ℓ).map fun s ↦ (hi.getD s z, novs.getD s z)).map
        (fun e ↦ ev2 M e.1 * ev2 M e.2) = (List.range ℓ).map fun s ↦
          (hi.map (ev2 M)).getD s 0 * algebraMap K E2 (novelAt s (kv M pc)) := by
      rw [List.map_map]
      refine List.map_congr_left fun s hs ↦ ?_
      simp only [Function.comp_apply]
      rw [ev2_getDz (l := hi) rfl hz, ev2_getDz hnovs hz, getD_range_map _ _ (List.mem_range.mp hs)]
    refine Prod.ext ?_ hnws
    show ev2 M o = _
    rw [ho, hfv, hhv, hz, add_zero, hd, hz, zero_add, hn κ (by omega), hx, hL]
    rfl

/-- **The value gadget with `Ŵ` cells**: CCV's prelude, then one `valAtW` instance per position. -/
def valsGenW (zz : Bool) (_h ℓ κ : ℕ) (rc : List RndC) (hi : List C2) (ps : List Cell)
    (rows : List (List (Option ℕ))) (gate : Cell) : BM (List C2 × List (List C2)) :=
  valsPre κ ℓ gate >>= fun e ↦
    mapB (fun k ↦ valAtW e.1 e.2.1 e.2.2 zz ℓ κ rc hi (ps.getD k gate) (rows.getD k []))
      (List.range ps.length) >>= fun prs ↦ pure (prs.map Prod.fst, prs.map Prod.snd)

/-- **`ValsWAt` for W1's mid-level values**, `Ŵ_i` for `i < max (κ + 1) ℓ`. -/
theorem valsGenW_ok (zz : Bool) (h ℓ κ : ℕ) (hh : h ≤ 64) (t : ℕ) (c : Ctx) (M : Mem)
    (rc : List RndC) (rs : List (Whir.Rnd E2)) (hrep : RndsRep M rc rs) :
    ValsWAt (t := t) c M (Whir.valsE zz h ℓ κ hh rs) (max (κ + 1) ℓ) (valsGenW zz h ℓ κ rc) := by
  intro hi ps rows gate _
  refine hsA_of_hs (hs_bind (hs_valsPre κ ℓ gate) fun e he ↦ ?_)
  obtain ⟨hz, hone, hk⟩ := he
  refine hs_bind (hs_mapB2 _ (fun k ↦ (valOf rs zz ℓ κ (hi.map (ev2 M)) (kv M (ps.getD k gate))
      ((rows.getD k []).map (lw M)), (List.range (max (κ + 1) ℓ)).map fun i ↦
        algebraMap K E2 (normVanishingAt i (kv M (ps.getD k gate)))))
    (fun o ↦ (ev2 M o.1, o.2.map (ev2 M)))
    (fun k ↦ hs_valAtW hz hone e.2.2 zz ℓ κ hk hrep hi _ _) _) fun prs hprs ↦ hs_pure ⟨?_, ?_⟩
  · intro p hp
    have hcs : (prs.map Prod.fst).map (ev2 M) = (List.range ps.length).map fun k ↦
        valOf rs zz ℓ κ (hi.map (ev2 M)) (kv M (ps.getD k gate)) ((rows.getD k []).map (lw M)) := by
      have := congrArg (List.map Prod.fst) hprs
      rw [List.map_map, List.map_map] at this
      rw [List.map_map]
      exact this
    have hlen : ps.length = t := by simpa [posOf] using congrArg List.length hp
    rw [hcs]
    apply List.ext_getElem
    · simp [hlen]
    intro k h1 _
    have hk' : k < t := by simpa [hlen] using h1
    have hpk : kToNat (kv M ps[k]) = (p ⟨k, hk'⟩ : ℕ) := by
      have e := congrArg (fun l ↦ l[k]?) hp
      simp only [posOf, List.getElem?_map, List.getElem?_eq_getElem (by omega : k < ps.length),
        List.getElem?_ofFn, Option.map_some] at e
      simp only [hk', ↓reduceDIte] at e
      exact Option.some.inj e
    simp only [List.getElem_map, List.getElem_range, List.getElem_ofFn]
    rw [valsE_eq, ← hpk, ofBits_kToNat, List.getD_eq_getElem?_getD,
      List.getElem?_eq_getElem (by omega : k < ps.length), Option.getD_some]
    congr 1
    show _ = (rows.map (·.map (lw M))).getD k []
    rw [show ([] : List K) = (([] : List (Option ℕ)).map (lw M)) from rfl, List.getD_map]
  · show (prs.map Prod.snd).map (·.map (ev2 M)) = _
    have := congrArg (List.map Prod.snd) hprs
    simp only [List.map_map] at this
    rw [List.map_map, ← map_range_getD _ ps gate]
    exact this

/-! ## One level with the shared cells -/

/-- **One level's cells with the positions' `Ŵ` cells**: `ℓ` rounds, then CC-3's interface cells
(as `tailGen`), the value gadget `valsGW rc` handing out the `Ŵ` cells. -/
def levelGenW {kq : ℕ} (nh ko t : ℕ) (posG : (Fin (kq + 1) → C2) → Cell → BM (List Cell))
    (valsGW : List RndC → List C2 → List Cell → List (List (Option ℕ)) → Cell →
      BM (List C2 × List (List C2)))
    (g ℓ : ℕ) (lev : Level) (wdI lvN a : ℕ) (gate : Cell) :
    BM (List RndC × TailOutC × List (List C2)) :=
  roundsGen g ℓ a gate >>= fun rc ↦
  posG (fun j ↦ ansAt (a + 27 * ℓ + 2 * nh + 4 * 2 ^ lvN + 9 + 10 + 9 * ko + 2 * 1) j) gate >>= fun ps ↦
  valsGW rc ((List.range nh).map fun j ↦ ld2 (a + 27 * ℓ + 2 * j)) ps
    (openRows lev wdI (tailOpenAt nh ko kq lvN (a + 27 * ℓ) - 4) t) gate >>= fun r ↦
  pure (rc, ⟨(List.range nh).map fun j ↦ ld2 (a + 27 * ℓ + 2 * j),
    List.ofFn (fun j : Fin (ko + 1) ↦ ansAt (a + 27 * ℓ + 2 * nh + 4 * 2 ^ lvN + 9) j),
    ld2 (a + 27 * ℓ + 2 * nh + 4 * 2 ^ lvN + 9 + 10 + 9 * ko), ps,
    ansAt (a + 27 * ℓ + 2 * nh + 4 * 2 ^ lvN + 9 + 10 + 9 * ko + 2 * 1) (kq + 1), r.1⟩, r.2)

/-- **CC-4 with the shared `Ŵ` cells proved.** -/
theorem levelHarW {n n' m' : ℕ} (L : Whir.TailIface E2 n n' m') (nw : ℕ) :
    LevelHarWStmt L nw (levelGenW L.nh L.ko L.t) := by
  intro vals posG valsGW hpos hvals g ht wd i gO gQ ℓ hg hgO hgQ lev wdI lvN a gate c M hgate
  unfold levelGenW
  rw [roundsGen_eq]
  refine hsA_bind (hsA_pure (P := fun rc ↦ rc = roundsCells ℓ a) rfl) fun rc hrc ↦ ?_
  subst hrc
  refine hsA_bind (hpos c M _ gate hgate) fun ps hps ↦ ?_
  refine hsA_bind (hsA_pi fun rs ↦ hsA_pi fun (hr : RndsRep M (roundsCells ℓ a) rs) ↦
    hvals c M _ rs hr _ ps _ gate hgate) fun r hr ↦ hsA_pure ?_
  exact runsO_of_eq (by rw [List.append_nil]) (runsO_bind (runsO_roundsP M hg ℓ a) fun rs hrs ↦
    runsO_bind (runsO_tailP L M (vals rs) hgO hgQ lev wdI lvN (a + 27 * ℓ) ps r.1 hps (hr rs hrs).1)
      fun o' ho' ↦ runsO_pure ⟨⟨hrs, ho'⟩, (hr rs hrs).2⟩)

/-! ## The glue step reading the shared cells -/

theorem colL_eqW (κ n x : ℕ) (hκ : κ ≤ n) (wl : List E2)
    (hw : wl = (List.range n).map fun i ↦ algebraMap K E2 (normVanishingAt i (K.ofBits x)))
    (y : List E2) :
    Whir.colL κ x y = Whir.prodL (fun i X ↦ 1 + (X * wl.getD i 0 + X)) κ y := by
  refine prodL_congr κ _ _ y fun i hi X ↦ ?_
  rw [hw, List.getD_eq_getElem _ _ (by simp; omega), List.getElem_map, List.getElem_range]
  linear_combination (-X) * two_E2

/-- **The query terms from the shared cells**, one instance per position's `Ŵ` list. -/
def colsGW (z one lam : C2) (y : List C2) (ν : ℕ) : List (List C2) → C2 → C2 → BM C2
  | [], _, acc => pure acc
  | ws :: wss, pw, acc => g2Mul pw lam z >>= fun pw' ↦
      prodFG z one (colFac z one ws) ν y >>= fun cv ↦ g2Mul pw' cv acc >>= fun acc' ↦
        colsGW z one lam y ν wss pw' acc'

theorem hsA_colsGW {z one : C2} (hz : z.val M = 0) (hone : ev2 M one = 1) (lam : C2)
    (y : List C2) {ν nw : ℕ} (hν : ν ≤ nw) : ∀ (xs : List Cell) (wss : List (List C2)) (m : ℕ)
      (pw acc : C2), WsRep M xs wss nw → ev2 M pw = ev2 M lam ^ (m + 1) →
      HsA c M (colsGW z one lam y ν wss pw acc) fun r ↦ ev2 M r = ev2 M acc +
        colsV (ev2 M lam) (fun x ↦ Whir.colL ν x (y.map (ev2 M))) (xs.map fun x ↦ kToNat (kv M x)) m
  | [], [], _, _, _, _, _ => hsA_pure (by simp [colsV])
  | [], _ :: _, _, _, _, h, _ => absurd h (by simp [WsRep])
  | _ :: _, [], _, _, _, h, _ => absurd h (by simp [WsRep])
  | x :: xs, ws :: wss, m, pw, acc, hw, hpw => by
    simp only [WsRep, List.map_cons, List.cons.injEq] at hw
    have hp1 : ev2 M (pw) * ev2 M lam = ev2 M lam ^ (m + 2) := by rw [hpw]; ring
    refine hsA_bind (hsA_of_hs (hs_g2Mul pw lam z)) fun pw' hpw' ↦
      hsA_bind (hsA_prodFG hz hone ν (colFac z one ws)
        (fun i X ↦ 1 + (X * (ws.map (ev2 M)).getD i 0 + X))
        (fun i x' ↦ hsA_of_hs (hs_colFac hz hone ws i x')) y) fun cv hcv ↦
      hsA_bind (hsA_of_hs (hs_g2Mul pw' cv acc)) fun acc' hacc' ↦
      hsA_mono (hsA_colsGW hz hone lam y hν xs wss (m + 1) pw' acc' hw.2 (by
        rw [ev2_mul hpw', ev2_of_zero hz, add_zero, hp1])) fun r hr ↦ ?_
    rw [hr, ev2_mul hacc', ev2_mul hpw', ev2_of_zero hz, add_zero, hp1, hcv,
      ← colL_eqW ν nw _ hν _ (by rw [hw.1, ofBits_kToNat])]
    simp only [List.map_cons, colsV]
    ring

/-- **The glue step reading the shared `Ŵ` cells** (`glueG` with `colsGW`). -/
def glueGW (wGp : List RndC → List C2 → Cell → BM C2) (rcP : List RndC) (oc : TailOutC)
    (wss : List (List C2)) (rc : List RndC) (τ : List C2) (gate : Cell) : BM C2 :=
  let y := rc.map (·.α) ++ τ
  wGp rcP y gate >>= fun pv ↦
  g2Zero oc.lam >>= fun z ↦ g2Const 1 z >>= fun one ↦
  prodFG z one (eqFac z one oc.z) oc.z.length y >>= fun ev ↦
  g2Mul oc.lam ev pv >>= fun acc ↦
  colsGW z one oc.lam y oc.z.length wss oc.lam acc

/-- **CC-8g with the shared cells proved.** -/
theorem glueHarW : WGlueWStmt glueGW := by
  intro κ' ℓ' ko t h ℓ nw hκ hnw w Pre wGp hwok hwp rcP rs oc o wss hlenP c M hpre rc rs' hr' hl'
    τ hτ gate hgate
  obtain ⟨hP, hrP, hoc, hws⟩ := hpre
  obtain ⟨_, hzs, _, hps, hlam, _⟩ := hoc
  have hν : oc.z.length = ko + 1 := by simpa using congrArg List.length hzs
  have hY : (rc.map (·.α) ++ τ).map (ev2 M) = rs'.map (·.α) ++ τ.map (ev2 M) := by
    rw [List.map_append, rndsRep_alpha hr']
  unfold glueGW
  have hyl : (rc.map (·.α) ++ τ).length = w.1 := by
    have hτ' : τ.length = κ' := hτ
    rw [List.length_append, List.length_map, List.Forall₂.length_eq hr', hl', hτ', hwok.1]
    omega
  refine hsA_bind (hwp c M hP rcP rs hrP hlenP _ hyl gate hgate) fun pv hpv ↦ ?_
  refine hsA_bind (hsA_of_hs (hs_g2Zero oc.lam)) fun z hz ↦ ?_
  refine hsA_bind (hsA_of_hs (hs_g2Const 1 z)) fun one hone ↦ ?_
  have hone' : ev2 M one = 1 := by
    show FE2.ringEquivE2 (one.val M) = 1
    rw [hone, map_one]
  refine hsA_bind (hsA_prodFG hz hone' oc.z.length (eqFac z one oc.z)
    (fun i X ↦ 1 + ((oc.z.map (ev2 M)).getD i 0 + X)) (fun i x ↦
      hsA_of_hs (hs_eqFac hz hone' oc.z i x)) _) fun ev hev ↦ ?_
  refine hsA_bind (hsA_of_hs (hs_g2Mul oc.lam ev pv)) fun acc hacc ↦ ?_
  refine hsA_mono (hsA_colsGW hz hone' oc.lam _ (by omega) oc.ps wss 0 oc.lam acc hws (by simp))
    fun r hr ↦ ?_
  have hma : Whir.MA ((rs'.map (·.α)).length + κ')
      (Whir.wGlueE κ' ℓ' ko t h (Whir.wFolds Whir.WtE ℓ rs w) o).2 := by
    rw [List.length_map, hl']
    exact (Whir.hglue_E hκ w hwok rs o).2
  rw [wFolds_snd ℓ' rs' _ hl', foldsT_MA _ _ κ' hma, hr, ev2_mul hacc, hev, hpv, ← hY]
  have hps' : oc.ps.map (fun x ↦ kToNat (kv M x)) = List.ofFn fun k ↦ (o.ps k : ℕ) := hps
  rw [hps', colsV_ofFn, hν, ← eqL_eq o.z _ hzs, hlam]
  show _ = _ + o.lam * _ + _
  simp only [Nat.zero_add]
  ring

/-! ## The claim chain -/

/-- `Σ_k λ^(m+k+2)·v_k`. -/
noncomputable def psV (lam : E2) : List E2 → ℕ → E2
  | [], _ => 0
  | v :: vs, m => lam ^ (m + 2) * v + psV lam vs (m + 1)

theorem psV_ofFn (lam : E2) : ∀ (t : ℕ) (f : Fin t → E2) (m : ℕ),
    psV lam (List.ofFn f) m = ∑ k : Fin t, lam ^ (m + (k : ℕ) + 2) * f k
  | 0, _, _ => by simp [psV]
  | t + 1, f, m => by
    rw [List.ofFn_succ, psV, psV_ofFn lam t, Fin.sum_univ_succ]
    have e : ∀ k : Fin t, m + 1 + (k : ℕ) + 2 = m + ((k.succ : Fin (t + 1)) : ℕ) + 2 :=
      fun k ↦ by simp only [Fin.val_succ]; omega
    simp only [e, Fin.val_zero, Nat.add_zero]

/-- **The answers' powers of `λ`**, one instance per answer: `pw' = pw·λ`, `acc' = pw'·v + acc`. -/
def psumG (z lam : C2) : List C2 → C2 → C2 → BM C2
  | [], _, acc => pure acc
  | v :: vs, pw, acc => g2Mul pw lam z >>= fun pw' ↦ g2Mul pw' v acc >>= fun acc' ↦
      psumG z lam vs pw' acc'

theorem hs_psumG {z : C2} (hz : z.val M = 0) (lam : C2) : ∀ (vs : List C2) (m : ℕ) (pw acc : C2),
    ev2 M pw = ev2 M lam ^ (m + 1) →
    Hs c M (psumG z lam vs pw acc) fun r ↦ ev2 M r = ev2 M acc + psV (ev2 M lam) (vs.map (ev2 M)) m
  | [], _, _, _, _ => hs_pure (by simp [psV])
  | v :: vs, m, pw, acc, hpw => by
    have hp1 : ev2 M pw * ev2 M lam = ev2 M lam ^ (m + 2) := by rw [hpw]; ring
    refine hs_bind (hs_g2Mul pw lam z) fun pw' hpw' ↦ hs_bind (hs_g2Mul pw' v acc) fun acc' hacc' ↦
      hs_mono (hs_psumG hz lam vs (m + 1) pw' acc' (by
        rw [ev2_mul hpw', ev2_of_zero hz, add_zero, hp1])) fun r hr ↦ ?_
    rw [hr, ev2_mul hacc', ev2_mul hpw', ev2_of_zero hz, add_zero, hp1]
    simp only [List.map_cons, psV]
    ring

/-- **The next level's claim**: the claim folded by the rounds, `+ λ·y`, `+ Σ_k λ^(k+2)·c_k`. -/
def claimGlueG (σc : C2) (rc : List RndC) (oc : TailOutC) : BM C2 :=
  foldsCG σc rc >>= fun σf ↦ g2Zero σc >>= fun z ↦ g2Mul oc.lam oc.y σf >>= fun acc ↦
    psumG z oc.lam oc.c oc.lam acc

/-- **CC-8c proved.** -/
theorem claimGlueHar : ClaimGlueStmt claimGlueG := by
  intro c M σc rc rs oc ko t n o hr hoc
  obtain ⟨_, _, hy, _, hlam, hcs⟩ := hoc
  refine hsA_of_hs (hs_bind (hs_foldsCG rc σc) fun σf hσf ↦ hs_bind (hs_g2Zero σc) fun z hz ↦
    hs_bind (hs_g2Mul oc.lam oc.y σf) fun acc hacc ↦
      hs_mono (hs_psumG hz oc.lam oc.c 0 oc.lam acc (by simp)) fun s hs ↦ ?_)
  rw [hs, ev2_mul hacc, hσf rs hr, hcs, psV_ofFn, hy, hlam, Whir.gluedC]
  simp only [Nat.zero_add]
  ring

end Lvm6.QC
