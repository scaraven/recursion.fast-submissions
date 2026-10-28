-- New for `flock-recursive` (BLUEPRINT §10 changes 17, revision 3.12 item 3; stage S-E4, track
-- L-circ). The node section (`Plan`, `planOf`, `nodeIRows`, `evalMT`, `evalMKT`) moved here from
-- `FRVIRTplEval` (S-E3); `evalMT` is now the flat evaluation. S-E11: the first half is
-- `FRVIRTplGrp`; the run class and the fast key preparation are `FRVIRTplRun`.
import FRVIRTplRun

namespace FR
namespace TEval
open Circ Tpl

/-- A prepared piece: grouped sparse rows, or an instance with its prepared own inputs. -/
inductive PPc where
  | sp (g : GRows)
  | ins (k xh ch : ℕ) (own : List OwnP)

/-- A row with some entry (the alignment's padding rows have none). -/
def nonEmpty (p : ℕ × Row) : Bool := !(p.2.a.isEmpty && p.2.b.isEmpty && p.2.c.isEmpty)

/-- A piece, prepared (`pats`: the run patterns per key, `FRVIRTplRun`). -/
def prepPiece (pats : Array (Array Pat)) : Piece → PPc
  | .sp rs => .sp (grows 2048 4096 (rs.filter nonEmpty))
  | .ins k xh ch own =>
    .ins k xh ch (prepOwn (pats.getD k #[]) (List.range (pats.getD k #[]).size) 0 own)

/-- **The tables of an evaluation point** (computed once, shared by the matrices and slots): `eq(τ,
·)` over `n` coordinates and `eq(σ, ·)` over 23, split at `2^11` and `2^12`, the per-key low tables,
and `E(one)`. -/
structure Tb where
  tlo : Array F
  thi : Array F
  slo : Array F
  shi : Array F
  nt : Array Bool
  ns : Array Bool
  ttab : Array (Array F)
  stab : Array (Array F)
  e1 : F
  /-- The keys' low tables `eq(τ_{<A}, ·)`, `eq(σ_{<B}, ·)` (S-E11), with their bits. -/
  lt : Array Bool
  lu : Array Bool
  pt : Array (Array F)
  pu : Array (Array F)

/-- The tables (`nt`, `ns`: the row and cell bits some key or run has; `lt`, `lu`: the low tables'
bits). -/
def tbOf (n : ℕ) (t u : ℕ → F) (one : Lin) (nt ns lt lu : Array Bool) : Tb :=
  let slo := loTab 12 u; let shi := loTab 11 fun l => u (12 + l)
  ⟨loTab 11 t, loTab (n - 11) fun l => t (11 + l), slo, shi, nt, ns, hiTabs t 11 nt, hiTabs u 12 ns,
    glVal slo shi (grp 4096 one), lt, lu, preTabs t lt, preTabs u lu⟩

/-- The bits `< m` that some key has as `A` (resp. `B`). -/
def needA (keys : Array Key) (m : ℕ) : Array Bool := (Array.range m).map fun A => keys.any (·.A == A)
def needB (keys : Array Key) (m : ℕ) : Array Bool := (Array.range m).map fun B => keys.any (·.B == B)

/-- **The evaluation context** of a slot and a matrix (`n`: the row coordinates). -/
structure ECtx where
  n : ℕ
  tb : Tb
  t : ℕ → F
  u : ℕ → F
  keys : Array Key
  kp : Array KP
  dkp : KP
  /-- Each key's shared value in the slot. -/
  sv : Array F
  /-- Each key's number of shared inputs in the slot. -/
  nsh : Array ℕ
  /-- Each key's run patterns and their inner sums. -/
  ps : Array (Array Pat)
  inr : Array (Array F)

/-- The high factor of a run, `eq(σ_{≥B}, ch)`. -/
@[inline] def hfS (tb : Tb) (u : ℕ → F) (B x : ℕ) : F := hfac tb.stab tb.ns tb.shi 12 23 u B x

/-- **A prepared piece's value** for matrix `s` (the specification of `ppv3`). -/
def ppv (s : Mat) (c : ECtx) : PPc → F
  | .sp g => growsVal s c.tb.tlo c.tb.thi c.tb.slo c.tb.shi g
  | .ins k xh ch own =>
    hfac c.tb.ttab c.tb.nt c.tb.thi 11 c.n c.t (c.keys.getD k dkey).A xh *
      (hfac c.tb.stab c.tb.ns c.tb.shi 12 23 c.u (c.keys.getD k dkey).B ch * (c.kp.getD k c.dkp).loc +
        (c.kp.getD k c.dkp).one * c.tb.e1 + c.sv.getD k 0 +
        ownSumP (c.kp.getD k c.dkp).u c.tb.slo c.tb.shi (c.inr.getD k #[]) (hfS c.tb c.u)
          (c.ps.getD k #[]) (c.nsh.getD k 0) own)

/-- **A slot's context** (`gsh`: its shared forms, grouped; `pats`: the run patterns). -/
def ectx (s : Mat) (n : ℕ) (tb : Tb) (t u : ℕ → F) (keys : Array Key) (kp : Array KP)
    (gsh : Array (List GForm)) (pats : Array (Array Pat)) : ECtx :=
  let dkp := kprep s t u dkey
  ⟨n, tb, t, u, keys, kp, dkp,
    (Array.range gsh.size).map (fun k => ownSum (kp.getD k dkp).u tb.slo tb.shi 0 (gsh.getD k [])),
    gsh.map List.length, pats,
    (Array.range pats.size).map fun k =>
      inrOf (kp.getD k dkp).u (tabOr tb.pu tb.lu u) ((gsh.map List.length).getD k 0) (pats.getD k #[])⟩

/-- A slot's value: the sum of its pieces'. -/
def slotV (s : Mat) (c : ECtx) (pps : List PPc) : F := sumL (ppv s c) pps

/-! ## Correctness of the pieces' values -/

/-- **Empty rows add nothing.** -/
theorem rowsValI_filter (s : Mat) (gt gs : ℕ → F) (rs : List (ℕ × Row)) :
    rowsValI (RingHom.id F) s gt gs (rs.filter nonEmpty) = rowsValI (RingHom.id F) s gt gs rs := by
  simp only [rowsValI, sumL_eq]
  induction rs with
  | nil => rfl
  | cons p rs ih =>
    rw [List.filter_cons]
    split_ifs with h
    · simp [ih]
    · have h' : p.2.a.isEmpty = true ∧ p.2.b.isEmpty = true ∧ p.2.c.isEmpty = true := by
        simpa [nonEmpty, and_assoc] using h
      have hm : s.r p.2 = [] := by
        cases s <;> simp only [Mat.r] <;> simp only [List.isEmpty_iff] at h' <;> simp [h']
      rw [List.map_cons, List.sum_cons, ← ih, hm]
      simp [linEI, sumL_eq]

theorem key_ok {n : ℕ} {keys : Array Key} (hk : keys.all (Key.ok n) = true) (k : ℕ) :
    (keys.getD k dkey).ok n = true := by
  rw [Array.getD_eq_getD_getElem?]
  rcases h : keys[k]? with _ | K
  · simp [Key.ok, dkey]
  · obtain ⟨hk', hK⟩ := Array.getElem?_eq_some_iff.1 h
    exact hK ▸ (Array.all_eq_true.1 hk) k hk'

theorem locOk_mem {B : ℕ} {l : LinT} (h : locOk B l = true) {k : ℕ} {c : F}
    (hm : (Wire.loc k, c) ∈ l) : k < 2 ^ B := by
  have := List.all_eq_true.1 h _ hm
  simpa using this

theorem Key.ok_spec {n : ℕ} {K : Key} (h : K.ok n = true) :
    K.A ≤ n ∧ K.B ≤ 23 ∧ K.rows.length ≤ 2 ^ K.A ∧
      ∀ s : Mat, ∀ r ∈ K.rows, ∀ k c, (Wire.loc k, c) ∈ s.t r → k < 2 ^ K.B := by
  simp only [Key.ok, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at h
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
  refine ⟨h1, h2, h3, fun s r hr k c hm => ?_⟩
  obtain ⟨⟨ha, hb⟩, hc⟩ := h4 r hr
  cases s
  · exact locOk_mem ha hm
  · exact locOk_mem hb hm
  · exact locOk_mem hc hm

/-- **The own inputs with runs** at an evaluation's tables are the own inputs' value. -/
theorem ownSumP_tb (n : ℕ) (t u : ℕ → F) (one : Lin) (nt ns lt lu : Array Bool) (U : Array F)
    (ps : Array Pat) (J : ℕ) (own : List Lin) :
    ownSumP U (tbOf n t u one nt ns lt lu).slo (tbOf n t u one nt ns lt lu).shi
        (inrOf U (tabOr (tbOf n t u one nt ns lt lu).pu (tbOf n t u one nt ns lt lu).lu u) J ps)
        (hfS (tbOf n t u one nt ns lt lu) u) ps J (prepOwn ps (List.range ps.size) 0 own) =
      ownSum U (loTab 12 u) (loTab 11 fun l => u (12 + l)) J (own.map (grp 4096)) := by
  have h := ownSumP_eq U (loTab 12 u) (loTab 11 fun l => u (12 + l))
    (inrOf U (tabOr (preTabs u lu) lu u) J ps) (hfS (tbOf n t u one nt ns lt lu) u) ps
    (List.range ps.size) u J (linE_glVal u)
    (fun B ch _ => by simp only [hfS, tbOf]; exact hfac_eq u (S := 12) (n := 23) (by norm_num) ns B ch)
    (fun i hi => by rw [inrOf_getD hi, tabOr_eq]) own.length own rfl 0
  simp only [tbOf, Nat.add_zero] at h ⊢
  exact h

/-- **A piece's value is its rows' sparse value** (`tplR_mle` for an instance). -/
theorem ppv_eq (s : Mat) {n : ℕ} (hn : 11 ≤ n) (t u : ℕ → F) (one : Lin) (nt ns lt lu : Array Bool)
    (keys : Array Key) (sh : Array (List Lin)) (pats : Array (Array Pat))
    (hk : keys.all (Key.ok n) = true) (p : Piece) :
    ppv s (ectx s n (tbOf n t u one nt ns lt lu) t u keys (keys.map (kprep s t u))
        (sh.map (·.map (grp 4096))) pats) (prepPiece pats p) =
      rowsVal (RingHom.id F) s n 23 t u (p.rows keys sh one) := by
  have hE : ∀ l, glVal (loTab 12 u) (loTab 11 fun l => u (12 + l)) (grp 4096 l) =
      linE (RingHom.id F) 23 u l := linE_glVal u
  cases p with
  | sp rs =>
    simp only [prepPiece, ppv, ectx, tbOf, Piece.rows]
    have h1 : splitAt (loTab 11 t) (loTab (n - 11) fun l => t (11 + l)) 2048 = gN n t :=
      splitE_eq (m := n) (s := 11) hn t
    have h2 : splitAt (loTab 12 u) (loTab 11 fun l => u (12 + l)) 4096 = gN 23 u :=
      splitE_eq (m := 23) (s := 12) (by norm_num) u
    rw [growsVal_grows, h1, h2, rowsValI_filter, rowsValI_eq]
  | ins k xh ch own =>
    obtain ⟨hA, hB, hT, hL⟩ := Key.ok_spec (key_ok hk k)
    set K := keys.getD k dkey with hK
    simp only [prepPiece, ppv, ectx, Piece.rows, range_getD_inr]
    rw [ownSumP_tb]
    simp only [tbOf]
    rw [← hK, tplR_mle (RingHom.id F) s t u K.rows one _ xh ch hA hB hT (hL s)
      (getD0 (loTab K.A t)) (getD0 (loTab K.B u))
      (fun j hj => loTab_getD _ _ (lt_of_lt_of_le hj hT)) (fun j hj => loTab_getD _ _ hj)]
    have hP : (keys.map (kprep s t u)).getD k (kprep s t u dkey) = kprep s t u K := getD_map' ..
    rw [hP, hfac_eq t (S := 11) (n := n) hn, hfac_eq u (S := 12) (n := 23) (by norm_num)]
    have hsh : (sh.map (·.map (grp 4096))).getD k [] = (sh.getD k []).map (grp 4096) :=
      getD_map' sh (·.map (grp 4096)) k []
    have hn' : ((sh.map (·.map (grp 4096))).map List.length).getD k 0 = (sh.getD k []).length := by
      rw [show (0 : ℕ) = List.length ([] : List GForm) from rfl, getD_map', hsh, List.length_map]
    have hsv : ((Array.range (sh.map (·.map (grp 4096))).size).map fun k' =>
        ownSum ((keys.map (kprep s t u)).getD k' (kprep s t u dkey)).u (loTab 12 u)
          (loTab 11 fun l => u (12 + l)) 0 ((sh.map (·.map (grp 4096))).getD k' [])).getD k 0 =
        ((List.range (sh.getD k []).length).map fun i =>
          (kprep s t u K).u.getD i 0 * linE (RingHom.id F) 23 u ((sh.getD k []).getD i [])).sum := by
      rw [Array.getD_eq_getD_getElem?, Array.getElem?_map, Array.getElem?_range]
      split_ifs with hks
      · simp only [Option.map_some, Option.getD_some]
        rw [hP, hsh, ownSum_eq _ _ _ _ hE]; simp
      · have : sh.getD k [] = [] := by
          rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_none (by simpa using hks)]; rfl
        simp [this]
    rw [hn', hsv, ownSum_eq _ _ _ _ hE, hE]
    unfold instClosed
    simp only [kprep, kprepT]
    rw [denseIT_sum _ (fun i => linE (RingHom.id F) 23 u ((sh.getD k [] ++ own).getD i []))
      ((sh.getD k []).length + own.length) (fun i hi => by
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by simpa using hi)]; rfl),
      sum_split _ _ rfl]
    ring

/-- **A slot's value is its pieces' rows' sparse value.** -/
theorem slotV_eq (s : Mat) {n : ℕ} (hn : 11 ≤ n) (t u : ℕ → F) (one : Lin) (nt ns lt lu : Array Bool)
    (keys : Array Key) (sh : Array (List Lin)) (pats : Array (Array Pat))
    (hk : keys.all (Key.ok n) = true) (pcs : List Piece) :
    slotV s (ectx s n (tbOf n t u one nt ns lt lu) t u keys (keys.map (kprep s t u))
        (sh.map (·.map (grp 4096))) pats) (pcs.map (prepPiece pats)) =
      rowsVal (RingHom.id F) s n 23 t u (pcs.flatMap (Piece.rows keys sh one)) := by
  rw [slotV, sumL_eq, rowsVal_flatMap, List.map_map]
  exact congrArg List.sum (List.map_congr_left fun p _ => ppv_eq s hn t u one nt ns lt lu keys sh pats hk p)

/-! ## The three matrices in one pass

`ppv3` computes a piece's `A`, `B` and `C` values together: the high `eq` factors, the own and
shared inputs' `E` values and the sparse rows' row factors are computed once for the three. -/

/-- The three matrices' values of grouped rows. -/
def growsVal3 (tlo thi slo shi : Array F) (G : GRows) : F3 :=
  sum3 (fun h =>
    let x := sum3 (fun r => let w := tlo.getD r.lo 0
      (rowMul slo shi w r.a, rowMul slo shi w r.b, rowMul slo shi w r.c)) h.2
    let y := thi.getD h.1 0
    (y * x.1, y * x.2.1, y * x.2.2)) G

theorem growsVal3_eq (tlo thi slo shi : Array F) (G : GRows) :
    growsVal3 tlo thi slo shi G = (growsVal .a tlo thi slo shi G, growsVal .b tlo thi slo shi G,
      growsVal .c tlo thi slo shi G) := by
  simp only [growsVal3, sum3_eq, growsVal, rInner, GRow.m]

/-- The own inputs of the three matrices: `E(g_j)` once. -/
def ownSum3 (Ua Ub Uc : Array F) (slo shi : Array F) : ℕ → List GForm → F3
  | _, [] => (0, 0, 0)
  | j, g :: gs =>
    let e := glVal slo shi g
    add3 (Ua.getD j 0 * e, Ub.getD j 0 * e, Uc.getD j 0 * e) (ownSum3 Ua Ub Uc slo shi (j + 1) gs)

theorem ownSum3_eq (Ua Ub Uc slo shi : Array F) : ∀ (j : ℕ) (g : List GForm),
    ownSum3 Ua Ub Uc slo shi j g = (ownSum Ua slo shi j g, ownSum Ub slo shi j g, ownSum Uc slo shi j g)
  | _, [] => rfl
  | j, g :: gs => by rw [ownSum3, ownSum3_eq Ua Ub Uc slo shi (j + 1) gs]; rfl

/-- The three preparations of a key. -/
abbrev KP3 := KP × KP × KP

/-- **The three preparations** (`kprepF`), the key's two tables from the evaluation's `tb`. -/
def kprep3 (tb : Tb) (t u : ℕ → F) (K : Key) : KP3 :=
  let eτ := getD0 (tabOr tb.pt tb.lt t K.A); let eσ := getD0 (tabOr tb.pu tb.lu u K.B)
  kprep3F eτ eσ K

theorem kprep3_eq (n : ℕ) (t u : ℕ → F) (one : Lin) (nt ns lt lu : Array Bool) (K : Key) :
    kprep3 (tbOf n t u one nt ns lt lu) t u K = (kprep .a t u K, kprep .b t u K, kprep .c t u K) := by
  simp only [kprep3, tbOf, tabOr_eq, kprep3F_eq, kprepF_eq, kprep]

/-- **A slot's context for the three matrices.** -/
structure ECtx3 where
  n : ℕ
  tb : Tb
  t : ℕ → F
  u : ℕ → F
  keys : Array Key
  kp : Array KP3
  dkp : KP3
  sv : Array F3
  nsh : Array ℕ
  ps : Array (Array Pat)
  inr : Array (Array F3)

/-- The patterns' inner sums of a slot: they depend on the slot's shared forms only through their
numbers `nl` (S-T1: so slots with equal numbers share them, `nodeV3`). -/
def inr3 (tb : Tb) (u : ℕ → F) (kp : Array KP3) (dkp : KP3) (nl : Array ℕ)
    (pats : Array (Array Pat)) : Array (Array F3) :=
  (Array.range pats.size).map fun k => let P := kp.getD k dkp
    inrOf3 P.1.u P.2.1.u P.2.2.u (tabOr tb.pu tb.lu u) (nl.getD k 0) (pats.getD k #[])

/-- A slot's context with its patterns' inner sums given. -/
def ectx3W (n : ℕ) (tb : Tb) (t u : ℕ → F) (keys : Array Key) (kp : Array KP3)
    (gsh : Array (List GForm)) (pats : Array (Array Pat)) (inr : Array (Array F3)) : ECtx3 :=
  let dkp := kprep3 tb t u dkey
  ⟨n, tb, t, u, keys, kp, dkp,
    (Array.range gsh.size).map (fun k => let P := kp.getD k dkp
      ownSum3 P.1.u P.2.1.u P.2.2.u tb.slo tb.shi 0 (gsh.getD k [])),
    gsh.map List.length, pats, inr⟩

def ectx3 (n : ℕ) (tb : Tb) (t u : ℕ → F) (keys : Array Key) (kp : Array KP3)
    (gsh : Array (List GForm)) (pats : Array (Array Pat)) : ECtx3 :=
  ectx3W n tb t u keys kp gsh pats (inr3 tb u kp (kprep3 tb t u dkey) (gsh.map List.length) pats)

/-- **A prepared piece's three values.** -/
def ppv3 (c : ECtx3) : PPc → F3
  | .sp g => growsVal3 c.tb.tlo c.tb.thi c.tb.slo c.tb.shi g
  | .ins k xh ch own =>
    let K := c.keys.getD k dkey; let P := c.kp.getD k c.dkp
    let h1 := hfac c.tb.ttab c.tb.nt c.tb.thi 11 c.n c.t K.A xh
    let h2 := hfac c.tb.stab c.tb.ns c.tb.shi 12 23 c.u K.B ch
    let sv := c.sv.getD k (0, 0, 0)
    let o := ownSumP3 P.1.u P.2.1.u P.2.2.u c.tb.slo c.tb.shi (c.inr.getD k #[]) (hfS c.tb c.u)
      (c.ps.getD k #[]) (c.nsh.getD k 0) own
    (h1 * (h2 * P.1.loc + P.1.one * c.tb.e1 + sv.1 + o.1),
     h1 * (h2 * P.2.1.loc + P.2.1.one * c.tb.e1 + sv.2.1 + o.2.1),
     h1 * (h2 * P.2.2.loc + P.2.2.one * c.tb.e1 + sv.2.2 + o.2.2))

def slotV3 (c : ECtx3) (pps : List PPc) : F3 := sum3 (ppv3 c) pps

theorem kp3_getD (n : ℕ) (t u : ℕ → F) (one : Lin) (nt ns lt lu : Array Bool) (keys : Array Key)
    (k : ℕ) :
    (keys.map (kprep3 (tbOf n t u one nt ns lt lu) t u)).getD k (kprep3 (tbOf n t u one nt ns lt lu) t u dkey) =
      ((keys.map (kprep .a t u)).getD k (kprep .a t u dkey),
       (keys.map (kprep .b t u)).getD k (kprep .b t u dkey),
       (keys.map (kprep .c t u)).getD k (kprep .c t u dkey)) := by
  rw [getD_map' keys (kprep3 _ t u), getD_map', getD_map', getD_map', kprep3_eq]

theorem getD_range3 (f g h : ℕ → F) (n k : ℕ) :
    ((Array.range n).map fun k => (f k, g k, h k)).getD k (0, 0, 0) =
      (((Array.range n).map f).getD k 0, ((Array.range n).map g).getD k 0,
        ((Array.range n).map h).getD k 0) := by
  simp only [Array.getD_eq_getD_getElem?, Array.getElem?_map, Array.getElem?_range]
  split_ifs <;> rfl

/-- **The one-pass value is the three values.** -/
theorem slotV3_eq (n n' : ℕ) (t u : ℕ → F) (one : Lin) (nt ns lt lu : Array Bool) (keys : Array Key)
    (g : Array (List GForm)) (pats : Array (Array Pat)) (pps : List PPc) :
    slotV3 (ectx3 n (tbOf n' t u one nt ns lt lu) t u keys
        (keys.map (kprep3 (tbOf n' t u one nt ns lt lu) t u)) g pats) pps =
      (slotV .a (ectx .a n (tbOf n' t u one nt ns lt lu) t u keys (keys.map (kprep .a t u)) g pats) pps,
       slotV .b (ectx .b n (tbOf n' t u one nt ns lt lu) t u keys (keys.map (kprep .b t u)) g pats) pps,
       slotV .c (ectx .c n (tbOf n' t u one nt ns lt lu) t u keys (keys.map (kprep .c t u)) g pats) pps) := by
  simp only [slotV3, slotV, sum3_eq]
  refine Prod.ext ?_ (Prod.ext ?_ ?_) <;> simp only <;>
    refine congrArg (sumL · pps) (funext fun p => ?_) <;>
    cases p <;> simp only [ppv3, ppv, ectx3, ectx3W, inr3, ectx, growsVal3_eq, kp3_getD, ownSum3_eq, getD_range3,
      ownSumP3_eq, range_getD_inr, range_getD_inr3, inrOf3_map1, inrOf3_map2, inrOf3_map3]

/-! ## The node -/

/-- Slot `σ`'s selector forms. -/
def slotP (σ : ℕ) : Params := muxP Layout.oneCell (Layout.selCells σ)

/-- Slot `σ`'s layout (the two-pass compile's first pass). -/
def slotLay (fin : Finals) (σ : ℕ) : TLay := layOf (slotP σ) (Layout.slotBase σ) (gen fin .mux).ops

/-- **Slot `σ`'s compiled program with the templates** (`compileT (gen fin .mux)`). -/
def slotCST (fin : Finals) (σ : ℕ) : CS :=
  compileT (slotLay fin σ) (slotP σ) (Layout.slotBase σ) (gen fin .mux).ops

/-- M's `one` form. -/
abbrev oneL : Lin := Lin.cell Layout.oneCell

/-- **The node's plan** (computed once per node): both slots' layouts and compiled programs, the
keys, each slot's shared forms and pieces — whose rows are the slot's indexed rows (`ok`) — and
their prepared forms. -/
structure Plan where
  lay : ℕ → TLay
  cs : ℕ → CS
  keys : Array Key
  sh0 : Array (List Lin)
  sh1 : Array (List Lin)
  pc0 : List Piece
  pc1 : List Piece
  ok : keys.all (Key.ok 21) = true ∧
    pc0.flatMap (Piece.rows keys sh0 oneL) = slotIRows (lay 0) oneL 0 (cs 0) ∧
    pc1.flatMap (Piece.rows keys sh1 oneL) = slotIRows (lay 1) oneL Layout.slotM (cs 1)
  g0 : Array (List GForm)
  g1 : Array (List GForm)
  p0 : List PPc
  p1 : List PPc
  hg0 : g0 = sh0.map (·.map (grp 4096))
  hg1 : g1 = sh1.map (·.map (grp 4096))
  /-- The run patterns per key (any table: `prepOwn` checks every run) and their chunk bits. -/
  pats : Array (Array Pat)
  pbs : List ℕ
  hp0 : p0 = pc0.map (prepPiece pats)
  hp1 : p1 = pc1.map (prepPiece pats)

/-- The chunk bits of the patterns. -/
def patBits (pats : Array (Array Pat)) : List ℕ :=
  pats.foldl (fun l ps => ps.foldl (fun l p => if l.contains p.B then l else p.B :: l) l) []

/-- A plan from its parts. -/
def mkPlanOf (l0 l1 : TLay) (c0 c1 : CS) (keys : Array Key) (sh0 sh1 : Array (List Lin))
    (pc0 pc1 : List Piece) (pats : Array (Array Pat)) (ok : keys.all (Key.ok 21) = true ∧
      pc0.flatMap (Piece.rows keys sh0 oneL) = slotIRows l0 oneL 0 c0 ∧
      pc1.flatMap (Piece.rows keys sh1 oneL) = slotIRows l1 oneL Layout.slotM c1) : Plan where
  lay σ := if σ = 0 then l0 else l1
  cs σ := if σ = 0 then c0 else c1
  keys := keys
  sh0 := sh0
  sh1 := sh1
  pc0 := pc0
  pc1 := pc1
  ok := by simpa using ok
  g0 := sh0.map (·.map (grp 4096))
  g1 := sh1.map (·.map (grp 4096))
  pats := pats
  pbs := patBits pats
  p0 := pc0.map (prepPiece pats)
  p1 := pc1.map (prepPiece pats)
  hg0 := rfl
  hg1 := rfl
  hp0 := rfl
  hp1 := rfl

/-- **The plan of two laid-out, compiled slots** from the search's data: kept if the keys are well
formed and the pieces' rows are the slots' rows (checked here, once), else one sparse piece per
slot. -/
def mkPlan (l0 l1 : TLay) (c0 c1 : CS)
    (d : Array Key × Array (List Lin) × Array (List Lin) × List Piece × List Piece) : Plan :=
  if h : (d.1.all (Key.ok 21) && eqL (d.2.2.2.1.flatMap (Piece.rows d.1 d.2.1 oneL))
      (slotIRows l0 oneL 0 c0) &&
      eqL (d.2.2.2.2.flatMap (Piece.rows d.1 d.2.2.1 oneL)) (slotIRows l1 oneL Layout.slotM c1)) = true
  then
    mkPlanOf l0 l1 c0 c1 d.1 d.2.1 d.2.2.1 d.2.2.2.1 d.2.2.2.2
      (mkPats d.1.size (d.2.2.2.1 ++ d.2.2.2.2)) (by
      simp only [Bool.and_eq_true] at h
      exact ⟨h.1.1, eqL_eq h.1.2, eqL_eq h.2⟩)
  else
    mkPlanOf l0 l1 c0 c1 #[] #[] #[] [.sp (slotIRows l0 oneL 0 c0)]
      [.sp (slotIRows l1 oneL Layout.slotM c1)] #[] (by simp [Piece.rows])

/-- **The node's plan** (once per node). -/
def planOf (fin : Finals) : Plan :=
  let ops := (gen fin .mux).ops
  let l0 := slotLay fin 0; let l1 := slotLay fin 1
  let c0 := compileT l0 (slotP 0) (Layout.slotBase 0) ops
  let c1 := compileT l1 (slotP 1) (Layout.slotBase 1) ops
  mkPlan l0 l1 c0 c1 (groupPPs
    (slotPPs (tplExt l0.ctx) (slotP 0) (Layout.slotBase 0) ops l0 oneL 0 c0)
    (slotPPs (tplExt l1.ctx) (slotP 1) (Layout.slotBase 1) ops l1 oneL Layout.slotM c1))

/-- **The node's indexed M rows**: slot `σ`'s at offset `σ · 2^20`. -/
def nodeIRows (pl : Plan) : List (ℕ × Row) :=
  slotIRows (pl.lay 0) oneL 0 (pl.cs 0) ++ slotIRows (pl.lay 1) oneL Layout.slotM (pl.cs 1)

/-- The node's value of matrix `s`, given the tables (the specification of `nodeV3`). -/
def nodeV (pl : Plan) (s : Mat) (t u : ℕ → F) (tb : Tb) : F :=
  let kp := pl.keys.map (kprep s t u)
  slotV s (ectx s 21 tb t u pl.keys kp pl.g0 pl.pats) pl.p0 +
    slotV s (ectx s 21 tb t u pl.keys kp pl.g1 pl.pats) pl.p1

theorem nodeV_eq (pl : Plan) (s : Mat) (t u : ℕ → F) (nt ns lt lu : Array Bool) :
    nodeV pl s t u (tbOf 21 t u oneL nt ns lt lu) = rowsVal (RingHom.id F) s 21 23 t u (nodeIRows pl) := by
  simp only [nodeV, nodeIRows]
  rw [pl.hg0, pl.hg1, pl.hp0, pl.hp1, slotV_eq _ (by norm_num) _ _ _ _ _ _ _ _ _ _ pl.ok.1,
    slotV_eq _ (by norm_num) _ _ _ _ _ _ _ _ _ _ pl.ok.1, pl.ok.2.1, pl.ok.2.2, rowsVal_append]

/-- The node's three matrices in one pass per slot. -/
def nodeV3 (pl : Plan) (t u : ℕ → F) (tb : Tb) : F3 :=
  let kp := pl.keys.map (kprep3 tb t u)
  let dkp := kprep3 tb t u dkey
  let n0 := pl.g0.map List.length; let n1 := pl.g1.map List.length
  let i0 := inr3 tb u kp dkp n0 pl.pats
  add3 (slotV3 (ectx3W 21 tb t u pl.keys kp pl.g0 pl.pats i0) pl.p0)
    (slotV3 (ectx3W 21 tb t u pl.keys kp pl.g1 pl.pats
      (if n1 = n0 then i0 else inr3 tb u kp dkp n1 pl.pats)) pl.p1)

/-- `nodeV3` is the two slots' `slotV3` (the inner sums shared when the slots' numbers agree). -/
theorem nodeV3_slots (pl : Plan) (t u : ℕ → F) (tb : Tb) : nodeV3 pl t u tb =
    add3 (slotV3 (ectx3 21 tb t u pl.keys (pl.keys.map (kprep3 tb t u)) pl.g0 pl.pats) pl.p0)
      (slotV3 (ectx3 21 tb t u pl.keys (pl.keys.map (kprep3 tb t u)) pl.g1 pl.pats) pl.p1) := by
  simp only [nodeV3, ectx3]
  split_ifs with h
  · rw [h]
  · rfl

theorem nodeV3_eq (pl : Plan) (t u : ℕ → F) (nt ns lt lu : Array Bool) :
    nodeV3 pl t u (tbOf 21 t u oneL nt ns lt lu) =
      (nodeV pl .a t u (tbOf 21 t u oneL nt ns lt lu), nodeV pl .b t u (tbOf 21 t u oneL nt ns lt lu),
        nodeV pl .c t u (tbOf 21 t u oneL nt ns lt lu)) := by
  simp only [nodeV3_slots, nodeV, slotV3_eq, add3]

/-- The tables' bit sets for keys `keys` and run chunk bits `pbs`. -/
def tbOfK (n : ℕ) (t u : ℕ → F) (keys : Array Key) (pbs : List ℕ) : Tb :=
  tbOf n t u oneL (needAll keys (·.A) 12) (needAll keys (·.B) 13 pbs) (needAll keys (·.A) (n + 1))
    (needAll keys (·.B) 24 pbs)

/-- **`evalM`** (revision 3.12; S-E5; S-E11: runs, the fast key preparation): the node's three M
matrices at `(τ, σ)`, the pieces of both slots in closed form or sparse, the three matrices in one
pass; the tables are computed once. -/
def evalMT (pl : Plan) (τ σ : Array F) : F × F × F :=
  let t := fun l => τ.getD l 0; let u := fun l => σ.getD l 0
  nodeV3 pl t u (tbOfK 21 t u pl.keys pl.pbs)

/-- **`evalM`'s specification**: the MLEs of the node's M matrices (`FRVIREval.matMLE`). -/
noncomputable def evalMS (pl : Plan) (τ σ : Array F) : F × F × F :=
  (Eval.matMLE (entriesI .a (nodeIRows pl)) (Eval.ptOf 21 τ) (Eval.ptOf 23 σ),
   Eval.matMLE (entriesI .b (nodeIRows pl)) (Eval.ptOf 21 τ) (Eval.ptOf 23 σ),
   Eval.matMLE (entriesI .c (nodeIRows pl)) (Eval.ptOf 21 τ) (Eval.ptOf 23 σ))

/-- **`evalM_eq`** (A.11: the instances' `tplR_mle` and the sparse pieces' `sparse_eq`). -/
theorem evalMT_eq (pl : Plan) (τ σ : Array F) : evalMT pl τ σ = evalMS pl τ σ := by
  simp only [evalMT, tbOfK, evalMS, nodeV3_eq, nodeV_eq, rowsVal_F, Eval.sparse_eq]

/-! ## `evalL`: L's rows (revision 3.13: at the full 23-coordinate point) -/

/-- **L's plan**: L's rows (indexed by position, 15 row coordinates) in aligned blocks of `2^6`. -/
structure LPlan where
  rows : List Row
  keys : Array Key
  sh : Array (List Lin)
  pc : List Piece
  ok : keys.all (Key.ok 15) = true ∧
    pc.flatMap (Piece.rows keys sh oneL) = rows.zipIdx.map fun p => (p.2, p.1)
  g : Array (List GForm)
  p : List PPc
  hg : g = sh.map (·.map (grp 4096))
  hp : p = pc.map (prepPiece #[])

def mkLPlanOf (rows : List Row) (keys : Array Key) (sh : Array (List Lin)) (pc : List Piece)
    (ok : keys.all (Key.ok 15) = true ∧
      pc.flatMap (Piece.rows keys sh oneL) = rows.zipIdx.map fun p => (p.2, p.1)) : LPlan :=
  ⟨rows, keys, sh, pc, ok, sh.map (·.map (grp 4096)), pc.map (prepPiece #[]), rfl, rfl⟩

/-- **L's plan** from its rows (checked as the node's). -/
def planL (rows : List Row) : LPlan :=
  let d := groupPPs (listPPs 6 rows) #[]
  let tgt := rows.zipIdx.map fun p => (p.2, p.1)
  if h : (d.1.all (Key.ok 15) && eqL (d.2.2.2.1.flatMap (Piece.rows d.1 d.2.1 oneL)) tgt) = true then
    mkLPlanOf rows d.1 d.2.1 d.2.2.2.1 (by
      simp only [Bool.and_eq_true] at h; exact ⟨h.1, eqL_eq h.2⟩)
  else mkLPlanOf rows #[] #[] [.sp tgt] (by simp [Piece.rows, tgt])

/-- L's plan keeps its rows. -/
theorem planL_rows (rows : List Row) : (planL rows).rows = rows := by
  simp only [planL]; split <;> rfl

/-- **`evalL`, templated**: L's three matrices at `(τ, σ)` (15 and 23 coordinates). -/
def evalLT (pl : LPlan) (τ σ : Array F) : F × F × F :=
  let t := fun l => τ.getD l 0; let u := fun l => σ.getD l 0
  let tb := tbOfK 15 t u pl.keys []
  slotV3 (ectx3 15 tb t u pl.keys (pl.keys.map (kprep3 tb t u)) pl.g #[]) pl.p

theorem entriesOf_eq (sel : Mat) (rows : List Row) :
    Eval.entriesOf sel.r rows = entriesI sel (rows.zipIdx.map fun p => (p.2, p.1)) := by
  simp only [Eval.entriesOf, entriesI, List.flatMap_map]

/-- **`evalL_eq`**: the templated `evalL` is the MLE of L's rows (`FRVIREval.evalRowsSpec`). -/
theorem evalLT_eq (pl : LPlan) (τ σ : Array F) : evalLT pl τ σ = Eval.evalRowsSpec 15 23 pl.rows τ σ := by
  simp only [evalLT, tbOfK, slotV3_eq, Eval.evalRowsSpec]
  rw [pl.hg, pl.hp]
  simp only [slotV_eq _ (by norm_num : 11 ≤ 15) _ _ _ _ _ _ _ _ _ _ pl.ok.1, pl.ok.2, rowsVal_F,
    Eval.sparse_eq]
  simp only [← entriesOf_eq]
  rfl

end TEval
end FR
