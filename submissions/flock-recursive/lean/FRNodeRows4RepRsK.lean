-- New for `flock-recursive` (R-OPS §5.2, stage R3: `rsWeight`'s replay at the previous-node slot).
import FRNodeRows4RepRs
import FRNodeRows4RepN

/-!
# `rsWeight`'s kind-muxed replay (prototype 0)

* **`rsT ν ts`**: the node kind `ν`'s sub-template at the operand types
  `ts = [af 7, f, f, ak m] ++ ns.map ak` (`r″`, `κ`, `β`, `ρ`, then the claims), `Tpl.rsG` over the
  inputs' forms; two empty outputs at any other types (which `rsIn` rejects).
* **`kRS`**: the `KOp` (C1's mechanism, `FRNodeRows4RepK`): covers an `rsWeight` op whose `act` holds
  at every index; operands `[r, κ, β, ρ] ++ pts ι`.
* **`kRS_ok`**: `KOk (implP impl₀ base 0 ι) ι kRS` at every index: the sub-template of `nodeAt ι`
  computes `rsWeightF4 (nodeAt ι)` (`Tpl.ok_rsG`, `RsR.rsWeightF4_ref`).
* **`rtRs`** (`rtRs_okW`): the replay template, its locals from `cbRS = repB + 2^16` (after
  `linkWAll`'s 42,601).
-/

namespace FR
namespace N4s
open RecursionFast Rev4 Circ Tpl

/-! ## Operand shapes and input forms -/

theorem akS_eq : ∀ {r : List Ty} {ns : List ℕ}, akS r = some ns → r = ns.map .ak
  | [], ns, h => by simp only [akS, Option.some.injEq] at h; subst h; rfl
  | .ak n :: r, ns, h => by
    simp only [akS, Option.map_eq_some_iff] at h
    obtain ⟨ns', h', rfl⟩ := h
    rw [akS_eq h']; rfl
  | .f :: _, _, h | .k :: _, _, h | .bit :: _, _, h | .d :: _, _, h | .af _ :: _, _, h => by simp [akS] at h

theorem rsShape_eq {ts : List Ty} {m : ℕ} {ns : List ℕ} (h : rsShape ts = some (m, ns)) :
    ts = .af 7 :: .f :: .f :: .ak m :: ns.map .ak := by
  unfold rsShape at h
  split at h
  · simp only [Option.map_eq_some_iff, Prod.mk.injEq] at h
    obtain ⟨ns', h', rfl, rfl⟩ := h
    rw [akS_eq h']
  · simp at h

theorem rsT_outs (ν : NodeKind) (ts : List Ty) : (rsT ν ts).outs.length = 2 := by
  unfold rsT; split <;> rfl

/-! ## Input values -/

variable {e : Env}

theorem getD_mid (pre m post : List F) {i : ℕ} (hi : i < m.length) :
    (pre ++ m ++ post).getD (pre.length + i) 0 = m.getD i 0 := by
  rw [List.append_assoc, List.getD_eq_getElem?_getD, List.getElem?_append_right (by omega),
    Nat.add_sub_cancel_left, List.getElem?_append_left hi, ← List.getD_eq_getElem?_getD]

theorem kIn_ev {xs pre post : List F} {x : List K} (h : InpIs e xs) (hx : xs = pre ++ x.flatMap encK ++ post) :
    (kIn pre.length x.length).map (evK e) = x := by
  refine List.ext_getElem (by simp [kIn]) fun l h1 h2 => ?_
  simp only [kIn, List.length_map, List.length_range] at h1
  have hl : 2 * l + 1 < (x.flatMap encK).length := by rw [length_flatMap_encK]; omega
  have e0 := encK_getD x l
  simp only [kIn, List.getElem_map, List.getElem_range, evK, ev_I]
  rw [h, h, hx, Nat.add_assoc, getD_mid _ _ _ (by omega), getD_mid _ _ _ hl, e0.1, e0.2,
    List.getD_eq_getElem _ _ h2]

theorem cIn_ev {xs : List F} (h : InpIs e xs) : ∀ (pss : List (List K)) (pre post : List F),
    xs = pre ++ (pss.map (·.flatMap encK)).flatten ++ post →
    (cIn pre.length (pss.map List.length)).map (List.map (evK e)) = pss
  | [], _, _, _ => rfl
  | x :: pss, pre, post, hx => by
    simp only [List.map_cons, cIn, List.cons.injEq]
    refine ⟨kIn_ev h (pre := pre) (post := (pss.map (·.flatMap encK)).flatten ++ post) (by
      rw [hx]; simp), ?_⟩
    have := cIn_ev h pss (pre ++ x.flatMap encK) post (by rw [hx]; simp)
    rwa [List.length_append, length_flatMap_encK] at this

theorem fIn_ev {xs pre post : List F} {x : List F} (h : InpIs e xs) (hx : xs = pre ++ x ++ post) :
    ((List.range x.length).map fun l => I (pre.length + l)).map (LinT.ev e) = x := by
  refine List.ext_getElem (by simp) fun l h1 h2 => ?_
  simp only [List.length_map, List.length_range] at h1
  simp only [List.getElem_map, List.getElem_range, ev_I]
  rw [h, hx, getD_mid _ _ _ h1, List.getD_eq_getElem _ _ h1]

/-! ## The `KOp` -/

theorem implP0_rsWeight {impl₀ : OpImpl} {base : Rev4.NodeKind → OpImpl} (ι : Kind) :
    (implP impl₀ base 0 ι).rsWeight = Impl.rsWeightF4 (nodeAt ι) := by
  simp only [implP, ite_true, OpImpl.fixK, NI4F.implN4F, NI4T.implN4T, NI4.implN4]
  rfl

theorem val_af {v : Val} {n : ℕ} (h : tyOf v = some (.af n)) : ∃ x : Array F, v = .af x ∧ x.size = n := by
  cases v <;> simp [tyOf] at h; exact ⟨_, rfl, h⟩

theorem val_ak {v : Val} {n : ℕ} (h : tyOf v = some (.ak n)) : ∃ x : Array K, v = .ak x ∧ x.size = n := by
  cases v <;> simp [tyOf] at h; exact ⟨_, rfl, h⟩

theorem val_f {v : Val} (h : tyOf v = some .f) : ∃ x : F, v = .f x := by
  cases v <;> simp [tyOf] at h; exact ⟨_, rfl⟩

/-- The claims' registers are `AK`s of the given sizes. -/
theorem claims_ak {regs : Array Val} : ∀ {as : List ℕ} {ns : List ℕ},
    as.map (fun a => tyOf (rd regs a)) = (ns.map Ty.ak).map some →
    as.flatMap (fun a => encV (rd regs a)) = ((as.map fun a => (rd regs a).toAK.toList).map (·.flatMap encK)).flatten ∧
      (as.map fun a => (rd regs a).toAK.toList).map List.length = ns
  | [], [], _ => ⟨rfl, rfl⟩
  | a :: as, n :: ns, h => by
    simp only [List.map_cons, List.cons.injEq] at h
    obtain ⟨x, hx, hs⟩ := val_ak h.1
    obtain ⟨ih1, ih2⟩ := claims_ak h.2
    refine ⟨?_, ?_⟩
    · rw [List.flatMap_cons, ih1, List.map_cons, List.map_cons, List.flatten_cons, hx]; rfl
    · rw [List.map_cons, List.map_cons, ih2, hx]; simp [Val.toAK, hs]
  | [], _ :: _, h => by simp at h
  | _ :: _, [], h => by simp at h

/-- **`rsWeight`'s replay obligation holds at every index.** -/
theorem kRS_ok {impl₀ : OpImpl} {base : Rev4.NodeKind → OpImpl} (ι : Kind) :
    KOk (implP impl₀ base 0 ι) ι kRS := by
  intro op hc
  cases op
  all_goals first | exact absurd hc Bool.false_ne_true | skip
  rename_i r ps κ' β act ρ
  have hact : act ι = true := by
    simp only [kRS, isRS, Bool.and_eq_true] at hc
    cases ι <;> simp [hc]
  refine ⟨fun _ _ _ h => Res.noConfusion h, fun ν ts => rsT_outs ν ts,
    fun inp regs vs ok ts hev hin hty => ?_⟩
  simp only [evalOp, Res.vals.injEq, hact, ite_true] at hev
  obtain ⟨rfl, -⟩ := hev
  refine ⟨rfl, fun e h1 hi hE => ?_⟩
  obtain ⟨⟨m, ns⟩, hsh⟩ := Option.isSome_iff_exists.1 hin
  have hts := rsShape_eq hsh
  simp only [kRS, rsArgs, hts, List.map_cons, List.map_append, List.cons_append, List.cons.injEq,
    List.map_map] at hty
  obtain ⟨hr, hκ, hβ, hρ, hps⟩ := hty
  obtain ⟨ra, hra, hrs⟩ := val_af hr
  obtain ⟨κv, hκv⟩ := val_f hκ
  obtain ⟨βv, hβv⟩ := val_f hβ
  obtain ⟨ρa, hρa, hρs⟩ := val_ak hρ
  obtain ⟨hpe, hpl⟩ := claims_ak (regs := regs) (as := ps ι) (ns := ns)
    (by simpa [List.map_map] using hps)
  have hx : (kRS.args (.rsWeight r ps κ' β act ρ) ι).flatMap (fun a => encV (rd regs a)) =
      ra.toList ++ [κv, βv] ++ ρa.toList.flatMap encK ++
        (((ps ι).map fun a => (rd regs a).toAK.toList).map (·.flatMap encK)).flatten := by
    show encV (rd regs r) ++ (encV (rd regs κ') ++ (encV (rd regs β) ++ (encV (rd regs ρ) ++
      (ps ι).flatMap fun a => encV (rd regs a)))) = _
    rw [hra, hκv, hβv, hρa, hpe]
    simp [encV]
  rw [hx] at hi
  simp only [kRS, rsT, hsh] at hE ⊢
  set cl := (((ps ι).map fun a => (rd regs a).toAK.toList).map (·.flatMap encK)).flatten with hcl
  have hO := ok_rsG (e := e) h1 (nodeAt ι)
    (r := ra.toList) (ps := (ps ι).map fun a => (rd regs a).toAK.toList) (κ := κv) (β := βv)
    (ρ := ρa.toList)
    (by
      have := fIn_ev (pre := []) (post := [κv, βv] ++ ρa.toList.flatMap encK ++ cl) hi (x := ra.toList)
        (by simp only [List.nil_append, List.append_assoc])
      simpa only [List.length_nil, zero_add, Array.length_toList, hrs] using this)
    (by
      have := cIn_ev hi _ (ra.toList ++ [κv, βv] ++ ρa.toList.flatMap encK) [] (by rw [List.append_nil])
      simp only [hpl, List.length_append, List.length_cons, List.length_nil, Array.length_toList, hrs,
        length_flatMap_encK, hρs] at this
      rwa [show 7 + (0 + 1 + 1) + 2 * m = 9 + 2 * m by ring] at this)
    (by
      rw [ev_I, hi, List.append_assoc (ra.toList ++ [κv, βv]),
        show 7 = ra.toList.length + 0 by simp [hrs], getD_mid _ _ _ (by simp)]; rfl)
    (by
      rw [ev_I, hi, List.append_assoc (ra.toList ++ [κv, βv]),
        show 8 = ra.toList.length + 1 by simp [hrs], getD_mid _ _ _ (by simp)]; rfl)
    (by
      have := kIn_ev hi (pre := ra.toList ++ [κv, βv]) (x := ρa.toList) (post := cl) rfl
      simpa only [List.length_append, List.length_cons, List.length_nil, Array.length_toList, hrs, hρs]
        using this)
    0 hE
  rw [implP0_rsWeight, show (rd regs r).toAF = ra by rw [hra]; rfl, hκv, hβv, hρa,
    show (Val.f κv).toF = κv from rfl, show (Val.f βv).toF = βv from rfl,
    show (Val.ak ρa).toAK = ρa from rfl, RsR.rsWeightF4_ref _ _ _ _ _ _ hrs, List.map_map]
  simp only [encV, encK, List.flatMap_cons, List.flatMap_nil, List.append_nil, Function.comp_def]
  rw [← hO]
  rfl

/-! ## The replay templates -/

theorem rtRs_okW {impl₀ : OpImpl} {base : Rev4.NodeKind → OpImpl} (ι : Kind) :
    RTOkW (implP impl₀ base 0 ι) (Xof 0) rtRs ι repB :=
  rtK_okW repB cbRS (kRS_ok ι)

/-- **The replay templates per prototype** (`rtC1` with `rsWeight` at prototype 0). -/
def rtR3 (π : ℕ) : RT := if π = 0 then rtN0R else if π = 1 then rtLinkSegW repB else RT.none

/-- **Every template of `rtR3` is sound** (`rtC1_ok`'s hypotheses). -/
theorem rtR3_ok {impl₀ : OpImpl} {base : Rev4.NodeKind → OpImpl} (hZ : LinkZero impl₀) (hB : STBase base)
    {π : ℕ} (hπ : π ≤ 1) (ι : Kind) : RTOkW (implP impl₀ base π ι) (Xof π) (rtR3 π) ι repB := by
  by_cases h : π = 0
  · subst h
    simp only [rtR3, ite_true, rtN0R]
    exact RT.orElse_okW (by simpa [rtC1] using rtC1_ok hZ hB (le_refl _ |>.trans (Nat.zero_le 1)) ι) (rtRs_okW ι)
  · obtain rfl : π = 1 := by omega
    simp only [rtR3, one_ne_zero, ite_false, ite_true]
    exact rtLinkSegW_ok base hZ repB ι

end N4s
end FR
