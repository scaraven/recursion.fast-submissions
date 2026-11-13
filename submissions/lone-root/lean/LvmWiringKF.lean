-- New for lvm2 (CT-FAST): fast versions of the compiler's slow phases, each proved equal to the original, and
-- `compileTF = compileT`. The originals (which L-A's/LA2's proofs mirror) are unchanged; the runtime cache
-- (`LvmQTypedInst.cacheOfTerms`) runs `compileTF` through the equality.
import LvmWiringKC
import LvmQTypedSWire

/-!
# The fast compiler `compileTF`

* `runMergeF`: the bucket push by `HashMap.modify` (in place) instead of `insert (getD …).push` (a copy per push:
  quadratic in a bucket; `runMergeF_eq`);
* `keysLtF`, `keysLtKF`: the key orders without building arrays (`keysLtF_eq`, `keysLtKF_eq`); `mergeAtomsF`;
* `bestLevelF`: a level's count of distinct nontrivial keys by a hash set, the runs built for the chosen level only
  (`bestLevelF_eq`); `genGF`, `atomCodeGF`, `initCodeGF`;
* `CS.rangeKeysG`/`CS.addAtomH`: an atom's key groups computed once per call site (`addAtomH_eq`); `CS.mkPassF`;
* **`compileTF_eq : compileTF = compileT`**.
-/

set_option autoImplicit false

namespace Lvm.Typed.K

open Lvm.Loop

/-! ## `limbOf` without the list -/

/-- `(List.range n).all f` is `Nat.all n` (no list built). -/
theorem range_all_eq (n : ℕ) (f : ℕ → Bool) : (List.range n).all f = Nat.all n (fun i _ ↦ f i) := by
  induction n with
  | zero => simp
  | succ n ih => rw [List.range_succ, List.all_append, ih, Nat.all_succ]; simp

def limbOfF (t0 t1 t2 : CTerm) : Option ℕ :=
  let y0 := t0.cls.atF 0
  let y1 := t1.cls.atF 0
  if !(t0.wv.isEmpty && t1.wv.isEmpty && t2.wv.isEmpty && t1.src == t0.src && t2.src == t0.src && t1.idx == t0.idx + 1 && t2.idx == t0.idx + 2 &&
      t1.o == t0.o && t2.o == t0.o && t1.x0 == t0.x0 && t2.x0 == t0.x0 && t1.l == t0.l && t2.l == t0.l) then none
  else if y1 < y0 || !isPow2 (y1 - y0) then none else
  let d := y1 - y0
  let e := log2 d
  if e + 1 < yVars && t1.w == t0.w * FE.y && t2.w == t0.w * FE.y * FE.y &&
      t1.cls == OpClass.addY d t0.cls && t2.cls == OpClass.addY (2 * d) t0.cls &&
      Nat.all (2 ^ t0.l) (fun jf _ ↦ (t0.cls.atF jf >>> e) % 4 == 0 &&
        t1.cls.atF jf == t0.cls.atF jf + d && t2.cls.atF jf == t0.cls.atF jf + 2 * d) then some e else none

theorem limbOfF_eq : limbOfF = limbOf := by
  funext t0 t1 t2
  unfold limbOfF limbOf
  simp only [range_all_eq, opClass_atF]

def mergeLimbsF (ts : Array CTerm) : Array (CTerm × Option ℕ) := Id.run do
  let mut out : Array (CTerm × Option ℕ) := Array.mkEmpty ts.size
  let mut i := 0
  while i < ts.size do
    let t0 := ts.getD i default
    match (if i + 2 < ts.size then limbOfF t0 (ts.getD (i + 1) default) (ts.getD (i + 2) default) else none) with
    | some e =>
      out := out.push (t0, some e)
      i := i + 3
    | none =>
      out := out.push (t0, none)
      i := i + 1
  return out

theorem mergeLimbsF_eq : mergeLimbsF = mergeLimbs := by
  funext ts
  unfold mergeLimbsF mergeLimbs
  rw [limbOfF_eq]
  rfl

/-! ## `runMerge` -/

def runMergeF (ps : Array (CTerm × Option ℕ)) : Array (CTerm × Option ℕ) := Id.run do
  let mut grp : Std.HashMap (ℕ × FE × ℕ × List ℕ × Option ℕ) (Array (ℕ × ℕ × ℕ)) := {}
  let mut out : Array (CTerm × Option ℕ) := #[]
  for i in [0:ps.size] do
    let (t, lim) := ps.getD i default
    match t.cls with
    | .aff a =>
      if t.wv.isEmpty && termWFB t && a.coef.length == t.l then
        let key := (t.o, t.w, t.l, a.coef, lim)
        grp := if grp.contains key then grp.modify key (·.push (t.x0, a.y0, i)) else grp.insert key #[(t.x0, a.y0, i)]
      else out := out.push (t, lim)
    | _ => out := out.push (t, lim)
  for (_, g) in grp.toList do
    let g := g.qsort fun a b ↦ a.1 < b.1
    let mut i := 0
    while i < g.size do
      let (x0, y0, ix) := g.getD i (0, 0, 0)
      let (t, lim) := ps.getD ix default
      let a : Aff := match t.cls with | .aff a => a | _ => default
      let d := (g.getD (i + 1) (0, 0, 0)).2.1 - y0
      let ok (k : ℕ) : Bool :=
        x0 % 2 ^ (t.l + k) == 0 && i + 2 ^ k ≤ g.size && x0 + 2 ^ (t.l + k) ≤ 2 ^ xVars &&
          (List.range (2 ^ k)).all fun m ↦
            let (x', y', _) := g.getD (i + m) (0, 0, 0)
            x' == x0 + m * 2 ^ t.l && y' ≥ y0 && y' == y0 + m * d
      -- only when the merged map stays a bit injection (else the automaton would cost more than the atoms)
      let k1 (k : ℕ) : Bool := injOk y0 (a.coef ++ (List.range k).map (d * 2 ^ ·))
      let k := ((List.range 13).reverse.find? fun k ↦ ok k && k1 k).getD 0
      if k == 0 then out := out.push (t, lim)
      else
        out := out.push ({ t with l := t.l + k, cls := .aff ⟨y0, a.coef ++ (List.range k).map (d * 2 ^ ·)⟩ }, lim)
      i := i + 2 ^ k
  return out

theorem hm_assoc_replace_getD {α β : Type} [BEq α] (a : α) (f : β → β) (d : β)
    (l : Std.DHashMap.Internal.AssocList α (fun _ => β)) (h : l.contains a = true) :
    l.replace a (f (l.getD a d)) = Std.DHashMap.Internal.AssocList.Const.modify a f l := by
  induction l with
  | nil => simp [Std.DHashMap.Internal.AssocList.contains] at h
  | cons k v l ih =>
    cases hk : k == a
    · simp only [Std.DHashMap.Internal.AssocList.contains, hk, Bool.false_or] at h
      simp only [Std.DHashMap.Internal.AssocList.replace, Std.DHashMap.Internal.AssocList.getD,
        Std.DHashMap.Internal.AssocList.Const.modify, hk, Bool.cond_false, ih h]
      rfl
    · simp only [Std.DHashMap.Internal.AssocList.replace, Std.DHashMap.Internal.AssocList.getD,
        Std.DHashMap.Internal.AssocList.Const.modify, hk, Bool.cond_true]
      rfl

theorem hm_modify_or_insert {α β : Type} [BEq α] [Hashable α] [LawfulBEq α]
    (m : Std.HashMap α β) (k : α) (f : β → β) (d : β) :
    (if m.contains k then m.modify k f else m.insert k (f d)) = m.insert k (f (m.getD k d)) := by
  split
  · rename_i h
    rcases m with ⟨⟨⟨size, buckets⟩, wf⟩⟩
    simp only [Std.HashMap.contains, Std.HashMap.modify, Std.HashMap.insert, Std.HashMap.getD,
      Std.DHashMap.contains, Std.DHashMap.Const.modify, Std.DHashMap.insert, Std.DHashMap.Const.getD,
      Std.DHashMap.Internal.Raw₀.contains, Std.DHashMap.Internal.Raw₀.Const.modify,
      Std.DHashMap.Internal.Raw₀.insert, Std.DHashMap.Internal.Raw₀.Const.getD] at h ⊢
    simp only [hm_assoc_replace_getD _ _ _ _ h]
    split <;> rfl
  · rename_i h
    rw [Std.HashMap.getD_eq_fallback_of_contains_eq_false (Bool.eq_false_iff.mpr h)]

theorem hm_push_step {α γ : Type} [BEq α] [Hashable α] [LawfulBEq α]
    (m : Std.HashMap α (Array γ)) (k : α) (x : γ) :
    (if m.contains k then m.modify k (·.push x) else m.insert k #[x]) = m.insert k ((m.getD k #[]).push x) :=
  hm_modify_or_insert m k (·.push x) #[]

theorem runMergeF_eq : runMergeF = runMerge := by
  funext ps
  unfold runMergeF runMerge
  simp only [hm_push_step]
  rfl

/-! ## The key orders and `mergeAtoms` -/

/-- `keysLt` without the monadic loop. -/
def keysLtF (a b : Array (ℕ × ℕ)) : Bool := go 0
where
  /-- From position `i` on. -/
  go (i : ℕ) : Bool :=
    if h : i < a.size ∧ i < b.size then
      let x := a[i]
      let y := b[i]
      if x.1 < y.1 then true else if x.1 > y.1 then false else if x.2 < y.2 then true else if x.2 > y.2 then false
      else go (i + 1)
    else a.size < b.size
  termination_by a.size - i

/-- Key `j` of `keysLtK kl`'s permuted array of `k` (`n` its size): the keys but level `kl`, then level `kl`. -/
@[inline] def pkey (kl : ℕ) (k : Array (ℕ × ℕ)) (n j : ℕ) : ℕ × ℕ :=
  if j + 1 = n then k.getD kl (0, 0) else if j < kl then k.getD j (0, 0) else k.getD (j + 1) (0, 0)

/-- `keysLtK`'s comparison from position `i` on, on the permuted arrays' sizes `na`, `nb`. -/
def keysLtKGo (kl : ℕ) (a b : Array (ℕ × ℕ)) (na nb : ℕ) (i : ℕ) : Bool :=
  if _h : i < na ∧ i < nb then
    let x := pkey kl a na i
    let y := pkey kl b nb i
    if x.1 < y.1 then true else if x.1 > y.1 then false else if x.2 < y.2 then true else if x.2 > y.2 then false
    else keysLtKGo kl a b na nb (i + 1)
  else na < nb
  termination_by na - i

/-- `keysLtK` without building the permuted arrays. -/
def keysLtKF (kl : ℕ) (a b : Array (ℕ × ℕ)) : Bool :=
  keysLtKGo kl a b (if kl < a.size then a.size else a.size + 1) (if kl < b.size then b.size else b.size + 1) 0

theorem kl_go_iff (a b : Array (ℕ × ℕ)) (k : ℕ) : ∀ i, i + k = min a.size b.size →
    (keysLtF.go a b i = true ↔
      List.Lex (Prod.Lex (· < ·) (· < ·)) (a.toList.drop i) (b.toList.drop i)) := by
  induction k with
  | zero =>
    intro s hs
    have ha : (a.toList.drop s).length = a.size - s := by simp
    have hb : (b.toList.drop s).length = b.size - s := by simp
    rw [keysLtF.go, dite_eq_right_of_eq_false (eq_false (by omega))]
    cases hA : a.toList.drop s <;> cases hB : b.toList.drop s <;> simp [hA, hB] at ha hb ⊢ <;> omega
  | succ k ih =>
    intro s hs
    have hsa : s < a.size := by omega
    have hsb : s < b.size := by omega
    rw [keysLtF.go, dite_eq_left_of_eq_true (eq_true ⟨hsa, hsb⟩),
      List.drop_eq_getElem_cons (l := a.toList) (i := s) (by simpa using hsa),
      List.drop_eq_getElem_cons (l := b.toList) (i := s) (by simpa using hsb),
      List.cons_lex_cons_iff, ← ih (s + 1) (by omega)]
    simp only [Array.getElem_toList, Prod.lex_def]
    by_cases h1 : a[s].1 < b[s].1
    · simp [h1]
    by_cases h2 : a[s].1 > b[s].1
    · have hne : a[s] ≠ b[s] := fun e ↦ by rw [e] at h2; omega
      simp [h1, h2, hne]; omega
    by_cases h3 : a[s].2 < b[s].2
    · simp [h1, h2, h3]; omega
    by_cases h4 : a[s].2 > b[s].2
    · have hne : a[s] ≠ b[s] := fun e ↦ by rw [e] at h4; omega
      simp [h1, h2, h3, h4, hne]
    have e : a[s] = b[s] := Prod.ext (by omega) (by omega)
    simp [e]

theorem keysLtF_eq : keysLtF = keysLt := by
  funext a b
  rw [Bool.eq_iff_iff, qs_keysLt_iff]
  simpa [keysLtF] using kl_go_iff a b (min a.size b.size) 0 (by omega)

/-- The permuted array of `keysLtK`. -/
theorem kl_perm_size (kl : ℕ) (k : Array (ℕ × ℕ)) :
    ((k.extract 0 kl ++ k.extract (kl + 1) k.size).push (k.getD kl (0, 0))).size =
      if kl < k.size then k.size else k.size + 1 := by
  simp only [Array.size_push, Array.size_append, Array.size_extract]
  split <;> omega

theorem kl_pkey (kl : ℕ) (k : Array (ℕ × ℕ)) (j : ℕ)
    (hj : j < ((k.extract 0 kl ++ k.extract (kl + 1) k.size).push (k.getD kl (0, 0))).size) :
    pkey kl k (if kl < k.size then k.size else k.size + 1) j =
      ((k.extract 0 kl ++ k.extract (kl + 1) k.size).push (k.getD kl (0, 0)))[j] := by
  have hA : (k.extract 0 kl ++ k.extract (kl + 1) k.size).size = min kl k.size + (k.size - (kl + 1)) := by
    simp only [Array.size_append, Array.size_extract]; omega
  have hj' : j < (k.extract 0 kl ++ k.extract (kl + 1) k.size).size + 1 := by
    simpa only [Array.size_push] using hj
  unfold pkey
  rw [Array.getElem_push]
  have key : ∀ (hlt : j < (k.extract 0 kl ++ k.extract (kl + 1) k.size).size),
      (if j < kl then k.getD j (0, 0) else k.getD (j + 1) (0, 0)) =
        (k.extract 0 kl ++ k.extract (kl + 1) k.size)[j] := by
    intro hlt
    by_cases h2 : j < kl
    · rw [ite_eq_left h2, Array.getElem_append_left (by simp only [Array.size_extract]; omega),
        Array.getElem_extract, Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem (by omega)]
      simp
    · rw [ite_eq_right h2, Array.getElem_append_right (by simp only [Array.size_extract]; omega),
        Array.getElem_extract, Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem (by omega)]
      simp only [Option.getD_some, Array.size_extract]
      congr 1; omega
  by_cases hk : kl < k.size
  · simp only [hk, ite_true]
    by_cases h1 : j + 1 = k.size
    · rw [ite_eq_left h1, dite_eq_right_of_eq_false (eq_false (by omega))]
    · rw [ite_eq_right h1, dite_eq_left_of_eq_true (eq_true (by omega))]; exact key (by omega)
  · simp only [hk, ite_false]
    by_cases h1 : j + 1 = k.size + 1
    · rw [ite_eq_left h1, dite_eq_right_of_eq_false (eq_false (by omega))]
    · rw [ite_eq_right h1, dite_eq_left_of_eq_true (eq_true (by omega))]; exact key (by omega)

theorem kl_go_eq (kl : ℕ) (a b pa pb : Array (ℕ × ℕ)) (na nb : ℕ) (hna : pa.size = na) (hnb : pb.size = nb)
    (hpa : ∀ j (h : j < pa.size), pkey kl a na j = pa[j])
    (hpb : ∀ j (h : j < pb.size), pkey kl b nb j = pb[j]) (k : ℕ) :
    ∀ i, i + k = min na nb → keysLtKGo kl a b na nb i = keysLtF.go pa pb i := by
  induction k with
  | zero =>
    intro i hi
    rw [keysLtKGo, keysLtF.go, dite_eq_right_of_eq_false (eq_false (by omega)), dite_eq_right_of_eq_false (eq_false (by omega)), hna, hnb]
  | succ k ih =>
    intro i hi
    rw [keysLtKGo, keysLtF.go, dite_eq_left_of_eq_true (eq_true (by omega)), dite_eq_left_of_eq_true (eq_true (by omega)), ih (i + 1) (by omega),
      hpa i (by omega), hpb i (by omega)]

theorem keysLtKF_eq (kl : ℕ) : keysLtKF kl = keysLtK kl := by
  funext a b
  unfold keysLtKF keysLtK
  simp only
  rw [← keysLtF_eq, keysLtF]
  exact kl_go_eq kl a b _ _ _ _ (kl_perm_size kl a) (kl_perm_size kl b) (kl_pkey kl a) (kl_pkey kl b) _ 0
    (Nat.zero_add _)

def mergeAtomsF (kl : ℕ) (as : Array Atom) : Array Atom := Id.run do
  let srt := as.qsort fun a b ↦ keysLtKF kl a.keys b.keys
  let mut m1 : Array Atom := #[]
  for a in srt do
    match m1.back? with
    | some b =>
      if b.keys == a.keys then m1 := m1.modify (m1.size - 1) fun b ↦ { b with w := b.w + a.w }
      else m1 := m1.push a
    | none => m1 := m1.push a
  let m1f := m1.filter fun a ↦ !(a.w == 0)
  let without (k : Array (ℕ × ℕ)) : Array (ℕ × ℕ) := k.extract 0 kl ++ k.extract (kl + 1) k.size
  let mut m2 : Array Atom := #[]
  for a in m1f do
    match m2.back? with
    | some b =>
      let mb := (b.keys.getD kl (0, 0)).2
      let ma := (a.keys.getD kl (0, 0)).2
      if without b.keys == without a.keys && b.w == a.w && mb &&& ma == 0 then
        m2 := m2.modify (m2.size - 1) fun b ↦ { b with keys := b.keys.set! kl (1, mb ||| ma) }
      else m2 := m2.push a
    | none => m2 := m2.push a
  return m2.qsort fun a b ↦ keysLtF a.keys b.keys

theorem mergeAtomsF_eq : mergeAtomsF = mergeAtoms := by
  funext kl as
  unfold mergeAtomsF mergeAtoms
  rw [keysLtKF_eq, keysLtF_eq]
  rfl

open private Array.qpartition.loop from Init.Data.Array.QSort.Basic
open private Array.qsort.sort from Init.Data.Array.QSort.Basic


theorem qn_map_swap {α β : Type} {n : ℕ} (f : α → β) (v : Vector α n) (i k : ℕ) (hi : i < n) (hk : k < n) :
    (v.swap i k hi hk).map f = (v.map f).swap i k hi hk := by
  ext j hj
  simp only [Vector.getElem_map, Vector.getElem_swap]
  split_ifs <;> rfl

theorem qn_loop_map {α β : Type} {n : ℕ} (f : α → β) (lt : α → α → Bool) (lt' : β → β → Bool)
    (h : ∀ a b, lt' (f a) (f b) = lt a b) (lo hi : ℕ) (hhi : hi < n) (pivot : α)
    (as : Vector α n) (i k : ℕ) (ilo : lo ≤ i) (ik : i ≤ k) (w : k ≤ hi) :
    Array.qpartition.loop lt' lo hi hhi (f pivot) (as.map f) i k ilo ik w =
      ((Array.qpartition.loop lt lo hi hhi pivot as i k ilo ik w).1,
        (Array.qpartition.loop lt lo hi hhi pivot as i k ilo ik w).2.map f) := by
  rw [Array.qpartition.loop.eq_def, Array.qpartition.loop.eq_def lt]
  by_cases hk : k < hi
  · rw [dite_eq_left hk, dite_eq_left hk, Vector.getElem_map, h]
    by_cases hl : lt as[k] pivot = true
    · rw [ite_eq_left hl, ite_eq_left hl, ← qn_map_swap]
      exact qn_loop_map f lt lt' h lo hi hhi pivot _ (i + 1) (k + 1) _ _ _
    · rw [ite_eq_right hl, ite_eq_right hl]
      exact qn_loop_map f lt lt' h lo hi hhi pivot as i (k + 1) _ _ _
  · rw [dite_eq_right hk, dite_eq_right hk, ← qn_map_swap]
termination_by hi - k

theorem qn_qpartition_map {α β : Type} {n : ℕ} (f : α → β) (lt : α → α → Bool) (lt' : β → β → Bool)
    (h : ∀ a b, lt' (f a) (f b) = lt a b) (as : Vector α n) (lo hi : ℕ)
    (w : lo ≤ hi) (hlo : lo < n) (hhi : hi < n) :
    Array.qpartition (as.map f) lt' lo hi w hlo hhi =
      ((Array.qpartition as lt lo hi w hlo hhi).1, (Array.qpartition as lt lo hi w hlo hhi).2.map f) := by
  unfold Array.qpartition
  dsimp only
  have e : ∀ (c : Prop) [Decidable c] (i k : ℕ) (hi' : i < n) (hk : k < n) (v : Vector α n),
      (if c then (v.map f).swap i k hi' hk else v.map f) = (if c then v.swap i k hi' hk else v).map f := by
    intro c _ i k hi' hk v
    split_ifs
    · rw [qn_map_swap]
    · rfl
  simp only [Vector.getElem_map, h, e]
  rw [qn_loop_map f lt lt' h]

theorem qn_sort_map {α β : Type} (f : α → β) (lt : α → α → Bool) (lt' : β → β → Bool)
    (h : ∀ a b, lt' (f a) (f b) = lt a b) {n : ℕ} (as : Vector α n) (lo hi : ℕ) (w : lo ≤ hi)
    (hlo : lo < n) (hhi : hi < n) :
    Array.qsort.sort lt' (as.map f) lo hi w hlo hhi = (Array.qsort.sort lt as lo hi w hlo hhi).map f := by
  rw [Array.qsort.sort.eq_def, Array.qsort.sort.eq_def lt]
  by_cases h₁ : lo < hi
  · rw [dite_eq_left h₁, dite_eq_left h₁]
    rw [qn_qpartition_map f lt lt' h]
    generalize Array.qpartition as lt lo hi _ _ _ = r
    obtain ⟨⟨mid, hmid⟩, b⟩ := r
    dsimp only
    by_cases h₂ : mid ≥ hi
    · rw [dite_eq_left h₂, dite_eq_left h₂]
    · rw [dite_eq_right h₂, dite_eq_right h₂, qn_sort_map f lt lt' h b lo mid,
        qn_sort_map f lt lt' h _ (mid + 1) hi]
  · rw [dite_eq_right h₁, dite_eq_right h₁]
termination_by hi - lo

theorem qn_sort_map_toArray {α β : Type} (f : α → β) (lt : α → α → Bool) (lt' : β → β → Bool)
    (h : ∀ a b, lt' (f a) (f b) = lt a b) {n n' : ℕ} (v : Vector α n) (u : Vector β n')
    (lo hi lo' hi' : ℕ) (w : lo ≤ hi) (hlo : lo < n) (hhi : hi < n) (w' : lo' ≤ hi') (hlo' : lo' < n')
    (hhi' : hi' < n') (el : lo' = lo) (eh : hi' = hi) (eu : u.toArray = v.toArray.map f) :
    (Array.qsort.sort lt' u lo' hi' w' hlo' hhi').toArray =
      (Array.qsort.sort lt v lo hi w hlo hhi).toArray.map f := by
  have hn : n' = n := by rw [← u.size_toArray, eu, Array.size_map, v.size_toArray]
  subst hn el eh
  have : u = v.map f := Vector.toArray_inj.mp (by rw [eu, Vector.toArray_map])
  subst this
  rw [qn_sort_map f lt lt' h, Vector.toArray_map]

theorem qn_qsort_map {α β : Type} (xs : Array α) (f : α → β) (lt : α → α → Bool) (lt' : β → β → Bool)
    (h : ∀ a b, lt' (f a) (f b) = lt a b) : (xs.map f).qsort lt' = (xs.qsort lt).map f := by
  unfold Array.qsort
  by_cases h0 : xs.size = 0
  · have h0' : (xs.map f).size = 0 := by rw [Array.size_map, h0]
    rw [dite_eq_left h0, dite_eq_left h0']
  · have h0' : ¬ (xs.map f).size = 0 := by rw [Array.size_map]; exact h0
    rw [dite_eq_right h0, dite_eq_right h0']
    exact qn_sort_map_toArray f lt lt' h _ _ _ _ _ _ _ _ _ _ _ _ (by rw [Array.size_map])
      (by rw [Array.size_map]) rfl

theorem qn_qsort_map_mem {α β : Type} (xs : Array α) (f : α → β) (lt : α → α → Bool)
    (lt' : β → β → Bool) (h : ∀ a ∈ xs, ∀ b ∈ xs, lt' (f a) (f b) = lt a b) :
    (xs.map f).qsort lt' = (xs.qsort lt).map f := by
  have e1 : xs.map f = xs.attach.map (fun a ↦ f a.1) := (Array.attach_map_val xs f).symm
  have e2 : xs.qsort lt = (xs.attach.map Subtype.val).qsort lt := by rw [Array.attach_map_subtype_val]
  rw [e1, qn_qsort_map xs.attach (fun a ↦ f a.1) (fun a b ↦ lt a.1 b.1) lt' (fun a b ↦ h _ a.2 _ b.2), e2,
    qn_qsort_map xs.attach Subtype.val (fun a b ↦ lt a.1 b.1) lt (fun _ _ ↦ rfl), Array.map_map]
  rfl

theorem qn_mixed (x y i j N : ℕ) (hi : i < N) (hj : j < N) :
    x * N + i < y * N + j ↔ x < y ∨ (x = y ∧ i < j) := by
  rcases lt_trichotomy x y with hxy | rfl | hxy
  · have : (x + 1) * N ≤ y * N := Nat.mul_le_mul_right _ hxy
    constructor
    · intro; exact Or.inl hxy
    · intro; rw [Nat.succ_mul] at this; omega
  · omega
  · have : (y + 1) * N ≤ x * N := Nat.mul_le_mul_right _ hxy
    rw [Nat.succ_mul] at this
    constructor
    · intro; omega
    · rintro (h | ⟨h, _⟩) <;> omega

theorem qn_foldl_max (g : ℕ → ℕ) (l : List ℕ) (m : ℕ) :
    m ≤ l.foldl (fun m i ↦ max m (g i)) m ∧ ∀ i ∈ l, g i ≤ l.foldl (fun m i ↦ max m (g i)) m := by
  induction l generalizing m with
  | nil => simp
  | cons a t ih =>
    obtain ⟨h1, h2⟩ := ih (max m (g a))
    simp only [List.foldl_cons, List.mem_cons, forall_eq_or_imp]
    exact ⟨le_trans (le_max_left _ _) h1, le_trans (le_max_right _ _) h1, h2⟩

theorem qn_mixed_eq (x y i j N : ℕ) (hi : i < N) (hj : j < N) :
    x * N + i = y * N + j ↔ x = y ∧ i = j := by
  constructor
  · intro h
    have h1 := (qn_mixed x y i j N hi hj).not.mp (by omega)
    have h2 := (qn_mixed y x j i N hj hi).not.mp (by omega)
    rcases lt_trichotomy x y with hxy | rfl | hxy
    · exact absurd (Or.inl hxy) h1
    · omega
    · exact absurd (Or.inl hxy) h2
  · rintro ⟨rfl, rfl⟩; rfl

theorem qn_pack_lt (a b : ℕ × ℕ) (i j B N : ℕ) (ha2 : a.2 < B) (hb2 : b.2 < B) (hi : i < N) (hj : j < N) :
    decide ((a.1 * B + a.2) * N + i < (b.1 * B + b.2) * N + j) = (keyLt a b || (a == b && i < j)) := by
  rw [Bool.eq_iff_iff, decide_eq_true_iff, qn_mixed _ _ _ _ _ hi hj, qn_mixed _ _ _ _ _ ha2 hb2,
    qn_mixed_eq _ _ _ _ _ ha2 hb2]
  obtain ⟨a1, a2⟩ := a
  obtain ⟨b1, b2⟩ := b
  simp only [keyLt, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, Prod.mk.injEq]

/-! ### Packed sorts (one `Nat` comparison per step when all key arrays have one size) -/

/-- A key array in `keysLtK kl`'s order as one number: digits `p.1·B1 + p.2` in base `B2`, most significant first. -/
def packK (kl B1 B2 : ℕ) (k : Array (ℕ × ℕ)) : ℕ :=
  let n := if kl < k.size then k.size else k.size + 1
  (List.range n).foldl (fun acc j ↦ let p := pkey kl k n j; acc * B2 + (p.1 * B1 + p.2)) 0

/-- A key array in `keysLt`'s order as one number. -/
def packL (B1 B2 : ℕ) (k : Array (ℕ × ℕ)) : ℕ :=
  k.foldl (fun acc p ↦ acc * B2 + (p.1 * B1 + p.2)) 0

/-- The digit bounds of a set of atoms: `B1` above every second component, `B2` above every digit. -/
def keyBounds (as : Array Atom) : ℕ × ℕ :=
  let B1 := as.foldl (fun m a ↦ a.keys.foldl (fun m p ↦ max m p.2) m) 0 + 1
  (B1, (as.foldl (fun m a ↦ a.keys.foldl (fun m p ↦ max m p.1) m) 0 + 1) * B1)

/-- `qsort` by `keysLtK kl` on the keys, packed when all key arrays have the first one's size. -/
def sortKF (kl : ℕ) (as : Array Atom) : Array Atom :=
  let kb := keyBounds as
  if as.all (·.keys.size == (as.getD 0 default).keys.size) then
    ((as.map fun a ↦ (packK kl kb.1 kb.2 a.keys, a)).qsort (fun x y ↦ x.1 < y.1)).map (·.2)
  else as.qsort fun a b ↦ keysLtKF kl a.keys b.keys

/-- `qsort` by `keysLt` on the keys, packed when all key arrays have the first one's size. -/
def sortLF (as : Array Atom) : Array Atom :=
  let kb := keyBounds as
  if as.all (·.keys.size == (as.getD 0 default).keys.size) then
    ((as.map fun a ↦ (packL kb.1 kb.2 a.keys, a)).qsort (fun x y ↦ x.1 < y.1)).map (·.2)
  else as.qsort fun a b ↦ keysLtF a.keys b.keys

/-- Base-`B2` numbers of digit sequences `p.1·B1 + p.2` (same length, `p.2 < B1`, digits `< B2`) compare as the
sequences compare in `List.Lex (Prod.Lex (· < ·) (· < ·))`. -/
theorem qn2_foldl_lt (B1 B2 : ℕ) (l1 l2 : List (ℕ × ℕ)) (hlen : l1.length = l2.length)
    (h1 : ∀ p ∈ l1, p.2 < B1 ∧ p.1 * B1 + p.2 < B2) (h2 : ∀ p ∈ l2, p.2 < B1 ∧ p.1 * B1 + p.2 < B2)
    (acc1 acc2 : ℕ) :
    l1.foldl (fun acc p ↦ acc * B2 + (p.1 * B1 + p.2)) acc1 <
        l2.foldl (fun acc p ↦ acc * B2 + (p.1 * B1 + p.2)) acc2 ↔
      acc1 < acc2 ∨ (acc1 = acc2 ∧ List.Lex (Prod.Lex (· < ·) (· < ·)) l1 l2) := by
  induction l1 generalizing l2 acc1 acc2 with
  | nil =>
    cases l2 with
    | nil => simp
    | cons _ _ => simp at hlen
  | cons p t ih =>
    cases l2 with
    | nil => simp at hlen
    | cons q u =>
      simp only [List.length_cons, Nat.add_right_cancel_iff] at hlen
      simp only [List.mem_cons, forall_eq_or_imp] at h1 h2
      rw [List.foldl_cons, List.foldl_cons, ih u hlen h1.2 h2.2, qn_mixed _ _ _ _ _ h1.1.2 h2.1.2,
        qn_mixed_eq _ _ _ _ _ h1.1.2 h2.1.2, List.cons_lex_cons_iff,
        qn_mixed _ _ _ _ _ h1.1.1 h2.1.1, qn_mixed_eq _ _ _ _ _ h1.1.1 h2.1.1, Prod.lex_def, Prod.ext_iff]
      constructor
      · rintro ((h | ⟨rfl, h⟩) | ⟨⟨rfl, h⟩, h'⟩)
        · exact Or.inl h
        · exact Or.inr ⟨rfl, Or.inl h⟩
        · exact Or.inr ⟨rfl, Or.inr ⟨h, h'⟩⟩
      · rintro (h | ⟨rfl, h | ⟨h, h'⟩⟩)
        · exact Or.inl (Or.inl h)
        · exact Or.inl (Or.inr ⟨rfl, h⟩)
        · exact Or.inr ⟨⟨rfl, h⟩, h'⟩

theorem qn2_foldl_max {γ : Type} (g : γ → ℕ) (l : List γ) (m : ℕ) :
    m ≤ l.foldl (fun m p ↦ max m (g p)) m ∧ ∀ p ∈ l, g p ≤ l.foldl (fun m p ↦ max m (g p)) m := by
  induction l generalizing m with
  | nil => simp
  | cons a t ih =>
    obtain ⟨h1, h2⟩ := ih (max m (g a))
    simp only [List.foldl_cons, List.mem_cons, forall_eq_or_imp]
    exact ⟨le_trans (le_max_left _ _) h1, le_trans (le_max_right _ _) h1, h2⟩

theorem qn2_foldl2_max (g : ℕ × ℕ → ℕ) (l : List Atom) (m : ℕ) :
    m ≤ l.foldl (fun m a ↦ a.keys.foldl (fun m p ↦ max m (g p)) m) m ∧
      ∀ a ∈ l, ∀ p ∈ a.keys, g p ≤ l.foldl (fun m a ↦ a.keys.foldl (fun m p ↦ max m (g p)) m) m := by
  induction l generalizing m with
  | nil => simp
  | cons a t ih =>
    have hin := qn2_foldl_max g a.keys.toList m
    rw [Array.foldl_toList] at hin
    obtain ⟨h1, h2⟩ := ih (a.keys.foldl (fun m p ↦ max m (g p)) m)
    simp only [List.foldl_cons, List.mem_cons, forall_eq_or_imp]
    exact ⟨le_trans hin.1 h1, fun p hp ↦ le_trans (hin.2 p (Array.mem_toList_iff.mpr hp)) h1, h2⟩

/-- Every key of every atom satisfies `keyBounds`. -/
theorem qn2_keyBounds (as : Array Atom) (a : Atom) (ha : a ∈ as) (p : ℕ × ℕ) (hp : p ∈ a.keys) :
    p.2 < (keyBounds as).1 ∧ p.1 * (keyBounds as).1 + p.2 < (keyBounds as).2 := by
  have h1 := (qn2_foldl2_max (fun p ↦ p.2) as.toList 0).2 a (Array.mem_toList_iff.mpr ha) p hp
  have h2 := (qn2_foldl2_max (fun p ↦ p.1) as.toList 0).2 a (Array.mem_toList_iff.mpr ha) p hp
  simp only [Array.foldl_toList] at h1 h2
  unfold keyBounds
  dsimp only
  generalize as.foldl (fun m a ↦ a.keys.foldl (fun m p ↦ max m p.2) m) 0 = M1 at h1 ⊢
  generalize as.foldl (fun m a ↦ a.keys.foldl (fun m p ↦ max m p.1) m) 0 = M2 at h2 ⊢
  refine ⟨by omega, ?_⟩
  have : (p.1 + 1) * (M1 + 1) ≤ (M2 + 1) * (M1 + 1) := Nat.mul_le_mul_right _ (by omega)
  rw [Nat.succ_mul] at this
  omega

theorem qn2_keyBounds_zero (as : Array Atom) :
    (0, 0).2 < (keyBounds as).1 ∧ (0, 0).1 * (keyBounds as).1 + (0, 0).2 < (keyBounds as).2 := by
  unfold keyBounds
  dsimp only
  refine ⟨by omega, ?_⟩
  simp only [Nat.zero_mul, Nat.add_zero]
  exact Nat.mul_pos (by omega) (by omega)

theorem qn2_getD_bound (as : Array Atom) (a : Atom) (ha : a ∈ as) (i : ℕ) :
    (a.keys.getD i (0, 0)).2 < (keyBounds as).1 ∧
      (a.keys.getD i (0, 0)).1 * (keyBounds as).1 + (a.keys.getD i (0, 0)).2 < (keyBounds as).2 := by
  rw [Array.getD_eq_getD_getElem?]
  by_cases hi : i < a.keys.size
  · rw [Array.getElem?_eq_getElem hi, Option.getD_some]
    exact qn2_keyBounds as a ha _ (Array.getElem_mem hi)
  · rw [Array.getElem?_eq_none (by omega), Option.getD_none]
    exact qn2_keyBounds_zero as

theorem qn2_all_size (as : Array Atom) (h : as.all (·.keys.size == (as.getD 0 default).keys.size) = true) :
    ∀ a ∈ as, a.keys.size = (as.getD 0 default).keys.size := by
  intro a ha
  have := Array.all_eq_true_iff_forall_mem.mp h a ha
  simpa using this

theorem qn2_packL_lt (as : Array Atom) (a b : Atom) (ha : a ∈ as) (hb : b ∈ as)
    (hs : a.keys.size = b.keys.size) :
    decide (packL (keyBounds as).1 (keyBounds as).2 a.keys < packL (keyBounds as).1 (keyBounds as).2 b.keys) =
      keysLt a.keys b.keys := by
  rw [Bool.eq_iff_iff, decide_eq_true_iff, qs_keysLt_iff]
  unfold packL
  rw [← Array.foldl_toList, ← Array.foldl_toList,
    qn2_foldl_lt _ _ _ _ (by simpa using hs) (fun p hp ↦ qn2_keyBounds as a ha p (Array.mem_toList_iff.mp hp))
      (fun p hp ↦ qn2_keyBounds as b hb p (Array.mem_toList_iff.mp hp))]
  simp

/-- `packK` is `packL`'s fold over `keysLtK`'s permuted array. -/
theorem qn2_packK_eq (kl B1 B2 : ℕ) (k : Array (ℕ × ℕ)) :
    packK kl B1 B2 k = ((k.extract 0 kl ++ k.extract (kl + 1) k.size).push (k.getD kl (0, 0))).toList.foldl
      (fun acc p ↦ acc * B2 + (p.1 * B1 + p.2)) 0 := by
  unfold packK
  dsimp only
  have e : (List.range (if kl < k.size then k.size else k.size + 1)).map
      (pkey kl k (if kl < k.size then k.size else k.size + 1)) =
      ((k.extract 0 kl ++ k.extract (kl + 1) k.size).push (k.getD kl (0, 0))).toList := by
    apply List.ext_getElem
    · rw [List.length_map, List.length_range, Array.length_toList, kl_perm_size]
    · intro j h1 h2
      rw [List.getElem_map, List.getElem_range, Array.getElem_toList]
      exact kl_pkey kl k j (by simpa using h2)
  rw [← e, List.foldl_map]

theorem qn2_pkey_bound (as : Array Atom) (a : Atom) (ha : a ∈ as) (kl n j : ℕ) :
    (pkey kl a.keys n j).2 < (keyBounds as).1 ∧
      (pkey kl a.keys n j).1 * (keyBounds as).1 + (pkey kl a.keys n j).2 < (keyBounds as).2 := by
  unfold pkey
  split_ifs <;> exact qn2_getD_bound as a ha _

theorem qn2_packK_lt (kl : ℕ) (as : Array Atom) (a b : Atom) (ha : a ∈ as) (hb : b ∈ as)
    (hs : a.keys.size = b.keys.size) :
    decide (packK kl (keyBounds as).1 (keyBounds as).2 a.keys <
        packK kl (keyBounds as).1 (keyBounds as).2 b.keys) = keysLtK kl a.keys b.keys := by
  rw [Bool.eq_iff_iff, decide_eq_true_iff]
  unfold keysLtK
  dsimp only
  rw [qs_keysLt_iff, qn2_packK_eq, qn2_packK_eq, qn2_foldl_lt]
  · simp
  · rw [Array.length_toList, Array.length_toList, kl_perm_size, kl_perm_size, hs]
  all_goals
    intro p hp
    obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hp
    rw [Array.getElem_toList, ← kl_pkey _ _ _ (by simpa using hj)]
    first
    | exact qn2_pkey_bound as a ha _ _ _
    | exact qn2_pkey_bound as b hb _ _ _

theorem sortKF_eq (kl : ℕ) (as : Array Atom) : sortKF kl as = as.qsort fun a b ↦ keysLtK kl a.keys b.keys := by
  unfold sortKF
  dsimp only
  split_ifs with h
  · rw [qn_qsort_map_mem as _ (fun a b ↦ keysLtK kl a.keys b.keys) _ ?_, Array.map_map]
    · exact Array.map_id'' (fun _ ↦ rfl) _
    · intro a ha b hb
      have hs := qn2_all_size as h
      exact qn2_packK_lt kl as a b ha hb ((hs a ha).trans (hs b hb).symm)
  · rw [keysLtKF_eq]

theorem sortLF_eq (as : Array Atom) : sortLF as = as.qsort fun a b ↦ keysLt a.keys b.keys := by
  unfold sortLF
  dsimp only
  split_ifs with h
  · rw [qn_qsort_map_mem as _ (fun a b ↦ keysLt a.keys b.keys) _ ?_, Array.map_map]
    · exact Array.map_id'' (fun _ ↦ rfl) _
    · intro a ha b hb
      have hs := qn2_all_size as h
      exact qn2_packL_lt as a b ha hb ((hs a ha).trans (hs b hb).symm)
  · rw [keysLtF_eq]

def mergeAtomsF2 (kl : ℕ) (as : Array Atom) : Array Atom := Id.run do
  let srt := sortKF kl as
  let mut m1 : Array Atom := #[]
  for a in srt do
    match m1.back? with
    | some b =>
      if b.keys == a.keys then m1 := m1.modify (m1.size - 1) fun b ↦ { b with w := b.w + a.w }
      else m1 := m1.push a
    | none => m1 := m1.push a
  let m1f := m1.filter fun a ↦ !(a.w == 0)
  let without (k : Array (ℕ × ℕ)) : Array (ℕ × ℕ) := k.extract 0 kl ++ k.extract (kl + 1) k.size
  let mut m2 : Array Atom := #[]
  for a in m1f do
    match m2.back? with
    | some b =>
      let mb := (b.keys.getD kl (0, 0)).2
      let ma := (a.keys.getD kl (0, 0)).2
      if without b.keys == without a.keys && b.w == a.w && mb &&& ma == 0 then
        m2 := m2.modify (m2.size - 1) fun b ↦ { b with keys := b.keys.set! kl (1, mb ||| ma) }
      else m2 := m2.push a
    | none => m2 := m2.push a
  return sortLF m2

theorem mergeAtomsF2_eq : mergeAtomsF2 = mergeAtoms := by
  funext kl as
  unfold mergeAtomsF2 mergeAtoms
  rw [sortKF_eq]
  simp only [sortLF_eq]
  rfl


/-! ## The greedy code -/

/-- The number of distinct nontrivial level-`L` keys among `ix`. -/
def distinctNT (as : Array Atom) (L : ℕ) (ix : Array ℕ) : ℕ :=
  (ix.foldl (fun (h : Std.HashSet (ℕ × ℕ)) i ↦ let k := keyAt as L i; if k.1 != 0 then h.insert k else h) {}).size

/-- `sortAt` on packed keys `(k.1·B + k.2)·N + i` (`B`, `N` above every key component and index): one `Nat`
comparison per step. -/
def sortAtF (as : Array Atom) (L : ℕ) (ix : Array ℕ) : Array ℕ :=
  let B := ix.foldl (fun m i ↦ max m (max (keyAt as L i).1 (keyAt as L i).2)) 0 + 1
  let N := ix.foldl (fun m i ↦ max m i) 0 + 1
  ((ix.map fun i ↦ ((((keyAt as L i).1 * B + (keyAt as L i).2) * N + i), i)).qsort
    (fun x y ↦ x.1 < y.1)).map (·.2)


theorem sortAtF_eq : sortAtF = sortAt := by
  funext as L ix
  unfold sortAtF sortAt
  dsimp only
  rw [qn_qsort_map_mem ix _ (fun i j ↦ keyLt (keyAt as L i) (keyAt as L j) ||
    (keyAt as L i == keyAt as L j && decide (i < j))) _ ?_, Array.map_map]
  · exact Array.map_id'' (fun _ ↦ rfl) _
  · intro a ha b hb
    have hB := (qn_foldl_max (fun i ↦ max (keyAt as L i).1 (keyAt as L i).2) ix.toList 0).2
    have hN := (qn_foldl_max (fun i ↦ i) ix.toList 0).2
    simp only [Array.foldl_toList] at hB hN
    have hBa := hB a (Array.mem_toList_iff.mpr ha)
    have hBb := hB b (Array.mem_toList_iff.mpr hb)
    have hNa := hN a (Array.mem_toList_iff.mpr ha)
    have hNb := hN b (Array.mem_toList_iff.mpr hb)
    exact qn_pack_lt _ _ _ _ _ _ (by omega) (by omega) (by omega) (by omega)

/-- `bestLevel`, counting each level's distinct nontrivial keys by a hash set and building the chosen level's runs
only. -/
def bestLevelF (as : Array Atom) (ix : Array ℕ) (levels : List ℕ) : ℕ × Array ((ℕ × ℕ) × Array ℕ) :=
  let L := (levels.foldl (fun (acc : ℕ × ℕ) L ↦
    let c := distinctNT as L ix
    if acc.2 ≤ c then acc else (L, c)) (0, ix.size + 1)).1
  (L, if levels.isEmpty then #[] else runsAt as L (sortAtF as L ix))

/-- Runs' keys inherit any pairwise relation of the input's keys. -/
theorem gg_runs_pairwise (as : Array Atom) (L : ℕ) (xs : Array ℕ) (R : ℕ × ℕ → ℕ × ℕ → Prop)
    (hs : xs.toList.Pairwise fun a b ↦ R (keyAt as L a) (keyAt as L b)) :
    ((runsAt as L xs).toList.map (·.1)).Pairwise R := by
  obtain ⟨h1, h2, -⟩ := greedy_runsAt_spec as L xs
  rw [← h1, List.pairwise_flatten, List.pairwise_map] at hs
  rw [List.pairwise_map]
  refine hs.2.imp_of_mem fun {r r'} hr hr' h ↦ ?_
  obtain ⟨i, hi⟩ := List.exists_mem_of_ne_nil _ (h2 r hr).1
  obtain ⟨j, hj⟩ := List.exists_mem_of_ne_nil _ (h2 r' hr').1
  have := h i hi j hj
  rwa [(h2 r hr).2 i hi, (h2 r' hr').2 j hj] at this

/-- A key list sorted (non-strictly) with consecutive entries distinct has no duplicates. -/
theorem gg_nodup (l : List (ℕ × ℕ)) (h1 : l.Pairwise fun a b ↦ keyLt b a = false) (h3 : greedy_adj l) :
    l.Nodup := by
  induction l with
  | nil => exact List.nodup_nil
  | cons x l ih =>
    rw [List.pairwise_cons] at h1
    refine List.nodup_cons.2 ⟨?_, ih h1.2 (by cases l with | nil => trivial | cons y l => exact h3.2)⟩
    cases l with
    | nil => simp
    | cons y l =>
      intro hx
      rcases List.mem_cons.1 hx with e | hx
      · exact h3.1 e
      · have a1 := (List.pairwise_cons.1 h1.2).1 x hx
        have a2 := h1.1 y List.mem_cons_self
        apply h3.1
        simp only [keyLt, Bool.or_eq_false_iff, Bool.and_eq_false_iff, decide_eq_false_iff_not,
          beq_eq_false_iff_ne, ne_eq] at a1 a2
        ext <;> omega

theorem gg_runs_keys_nodup (as : Array Atom) (L : ℕ) (ix : Array ℕ) :
    ((runsAt as L (sortAt as L ix)).toList.map (·.1)).Nodup :=
  gg_nodup _ (gg_runs_pairwise as L _ _ (greedy_sortAt_sorted as L ix))
    (greedy_runsAt_spec as L (sortAt as L ix)).2.2

theorem gg_runs_keys_mem (as : Array Atom) (L : ℕ) (xs : Array ℕ) (k : ℕ × ℕ) :
    k ∈ (runsAt as L xs).toList.map (·.1) ↔ ∃ i ∈ xs.toList, keyAt as L i = k := by
  obtain ⟨h1, h2, -⟩ := greedy_runsAt_spec as L xs
  constructor
  · intro hk
    obtain ⟨r, hr, rfl⟩ := List.mem_map.1 hk
    obtain ⟨i, hi⟩ := List.exists_mem_of_ne_nil _ (h2 r hr).1
    refine ⟨i, ?_, (h2 r hr).2 i hi⟩
    rw [← h1]
    exact List.mem_flatten.2 ⟨_, List.mem_map.2 ⟨r, hr, rfl⟩, hi⟩
  · rintro ⟨i, hi, rfl⟩
    rw [← h1] at hi
    obtain ⟨l, hl, hil⟩ := List.mem_flatten.1 hi
    obtain ⟨r, hr, rfl⟩ := List.mem_map.1 hl
    rw [(h2 r hr).2 i hil]
    exact List.mem_map.2 ⟨r, hr, rfl⟩

theorem gg_hs_mem (as : Array Atom) (L : ℕ) (l : List ℕ) (h : Std.HashSet (ℕ × ℕ)) (k : ℕ × ℕ) :
    k ∈ l.foldl (fun (h : Std.HashSet (ℕ × ℕ)) i ↦ let k := keyAt as L i; if k.1 != 0 then h.insert k else h) h ↔
      k ∈ h ∨ (k.1 ≠ 0 ∧ ∃ i ∈ l, keyAt as L i = k) := by
  induction l generalizing h with
  | nil => simp
  | cons j l ih =>
    rw [List.foldl_cons, ih]
    dsimp only
    split_ifs with hc
    · rw [Std.HashSet.mem_insert]
      simp only [bne_iff_ne, ne_eq, beq_iff_eq, List.mem_cons] at hc ⊢
      constructor
      · rintro ((rfl | h1) | ⟨h1, i, h2, h3⟩)
        · exact Or.inr ⟨hc, j, Or.inl rfl, rfl⟩
        · exact Or.inl h1
        · exact Or.inr ⟨h1, i, Or.inr h2, h3⟩
      · rintro (h1 | ⟨h1, i, (rfl | h2), h3⟩)
        · exact Or.inl (Or.inr h1)
        · exact Or.inl (Or.inl h3)
        · exact Or.inr ⟨h1, i, h2, h3⟩
    · simp only [bne_iff_ne, ne_eq, not_not, List.mem_cons] at hc ⊢
      constructor
      · rintro (h1 | ⟨h1, i, h2, h3⟩)
        · exact Or.inl h1
        · exact Or.inr ⟨h1, i, Or.inr h2, h3⟩
      · rintro (h1 | ⟨h1, i, (rfl | h2), h3⟩)
        · exact Or.inl h1
        · exact absurd (h3 ▸ hc) h1
        · exact Or.inr ⟨h1, i, h2, h3⟩

/-- **The number of nontrivial runs is the number of distinct nontrivial keys.** -/
theorem gg_count (as : Array Atom) (L : ℕ) (ix : Array ℕ) :
    ((runsAt as L (sortAt as L ix)).filter fun r ↦ r.1.1 != 0).size = distinctNT as L ix := by
  unfold distinctNT
  rw [← Std.HashSet.length_toList, ← Array.foldl_toList, ← Array.length_toList, Array.toList_filter]
  have hnd : (((runsAt as L (sortAt as L ix)).toList.map (·.1)).filter fun k ↦ k.1 != 0).Nodup :=
    (gg_runs_keys_nodup as L ix).filter _
  have hnd2 := (Std.HashSet.distinct_toList (m := ix.toList.foldl
    (fun (h : Std.HashSet (ℕ × ℕ)) i ↦ let k := keyAt as L i; if k.1 != 0 then h.insert k else h) {}))
  have hnd2' : (ix.toList.foldl
      (fun (h : Std.HashSet (ℕ × ℕ)) i ↦ let k := keyAt as L i; if k.1 != 0 then h.insert k else h) {}).toList.Nodup :=
    hnd2.imp fun {a b} h e ↦ by simp [e] at h
  have hp := (List.perm_ext_iff_of_nodup hnd hnd2').2 fun k ↦ by
    rw [List.mem_filter, gg_runs_keys_mem, Std.HashSet.mem_toList, gg_hs_mem]
    simp only [Std.HashSet.not_mem_empty, false_or, bne_iff_ne, ne_eq]
    constructor
    · rintro ⟨⟨i, hi, rfl⟩, h⟩
      exact ⟨h, i, (greedy_sortAt_perm as L ix).mem_iff.1 hi, rfl⟩
    · rintro ⟨h, i, hi, rfl⟩
      exact ⟨⟨i, (greedy_sortAt_perm as L ix).mem_iff.2 hi, rfl⟩, h⟩
  rw [← hp.length_eq, List.filter_map, List.length_map]
  rfl

theorem gg_fold (as : Array Atom) (ix : Array ℕ) (d : ℕ → ℕ) (l : List ℕ) :
    ∀ acc : ℕ × Array ((ℕ × ℕ) × Array ℕ) × ℕ, acc.2.1 = runsAt as acc.1 (sortAt as acc.1 ix) →
      (l.foldl (fun (acc : ℕ × Array ((ℕ × ℕ) × Array ℕ) × ℕ) L ↦
        if acc.2.2 ≤ d L then acc else (L, runsAt as L (sortAt as L ix), d L)) acc) =
      ((l.foldl (fun (acc : ℕ × ℕ) L ↦ if acc.2 ≤ d L then acc else (L, d L)) (acc.1, acc.2.2)).1,
        runsAt as (l.foldl (fun (acc : ℕ × ℕ) L ↦ if acc.2 ≤ d L then acc else (L, d L)) (acc.1, acc.2.2)).1
          (sortAt as (l.foldl (fun (acc : ℕ × ℕ) L ↦ if acc.2 ≤ d L then acc else (L, d L))
            (acc.1, acc.2.2)).1 ix),
        (l.foldl (fun (acc : ℕ × ℕ) L ↦ if acc.2 ≤ d L then acc else (L, d L)) (acc.1, acc.2.2)).2) := by
  induction l with
  | nil =>
    rintro ⟨a, b, c⟩ h
    simp only at h
    simp [h]
  | cons L l ih =>
    rintro ⟨a, b, c⟩ h
    rw [List.foldl_cons, List.foldl_cons]
    split_ifs with hc
    · exact ih _ h
    · exact ih _ rfl

theorem bestLevelF_eq : bestLevelF = bestLevel := by
  funext as ix levels
  unfold bestLevelF bestLevel
  simp only [sortAtF_eq, gg_count]
  cases levels with
  | nil => rfl
  | cons L0 t =>
    have hc : ¬ ix.size + 1 ≤ distinctNT as L0 ix := by
      have := greedy_runsAt_size as L0 (sortAt as L0 ix)
      have := Array.size_filter_le (p := fun r : (ℕ × ℕ) × Array ℕ ↦ r.1.1 != 0)
        (xs := runsAt as L0 (sortAt as L0 ix))
      rw [greedy_sortAt_size, gg_count] at *
      omega
    rw [List.foldl_cons, List.foldl_cons, ite_eq_right_of_eq_false _ _ (eq_false hc), ite_eq_right_of_eq_false _ _ (eq_false hc), gg_fold as ix _ t _ rfl]
    rfl

def genGF (as : Array Atom) : ℕ → Array ℕ → List ℕ → Code → Code
  | 0, _, _, c => c
  | fuel + 1, ix, levels, c0 =>
    match levels with
    | [] =>
      -- no level left (atoms without keys): one leaf of the trivial key with the weights summed
      let w := ix.foldl (fun acc i ↦ acc + (as.getD i default).w) 0
      if w == 0 then c0 else if w == 1 then c0.emit 2 0 0 0 else { c0.emit 2 0 0 c0.ws.size with ws := c0.ws.push w }
    | [L] => Id.run do
      let mut c := c0
      for (k, g) in runsAt as L (sortAtF as L ix) do
        let w := g.foldl (fun acc i ↦ acc + (as.getD i default).w) 0
        if !(w == 0) then
          if w == 1 then c := c.emit 2 k.1 k.2 0
          else c := { c.emit 2 k.1 k.2 c.ws.size with ws := c.ws.push w }
      return c
    | _ => Id.run do
      let (L, rs) := bestLevelF as ix levels
      let rest := levels.erase L
      let mut c := c0
      for (k, g) in rs do
        if k.1 == 0 then
          c := genGF as fuel g rest c
        else
          c := genGF as fuel g rest (c.emit 0 0 0 0)
          c := c.emit 1 k.1 k.2 0
      return c

def atomCodeGF (as : Array Atom) (D : ℕ) : Code :=
  genGF as (D + 1) (Array.range as.size) (List.range D) ⟨#[], #[], #[], #[], #[1]⟩

def initCodeGF (as : Array Atom) (D : ℕ) : Code := Id.run do
  let mut c : Code := ⟨#[], #[], #[], #[], #[1]⟩
  for (k, g) in runsAt as 0 (sortAtF as 0 (Array.range as.size)) do
    c := genGF as (D + 1) g ((List.range D).erase 0) (c.emit 0 0 0 0)
    c := c.emit 3 0 k.2 0
  return c

theorem genGF_eq : genGF = genG := by
  funext as fuel
  induction fuel with
  | zero => funext ix levels c; rfl
  | succ n ih =>
    funext ix levels c
    unfold genGF genG
    rw [ih, bestLevelF_eq, sortAtF_eq]
    rfl

theorem atomCodeGF_eq : atomCodeGF = atomCodeG := by
  funext as D
  unfold atomCodeGF atomCodeG
  rw [genGF_eq]

theorem initCodeGF_eq : initCodeGF = initCodeG := by
  funext as D
  unfold initCodeGF initCodeG
  rw [genGF_eq, sortAtF_eq]

/-! ## An atom's keys on precomputed groups -/

/-- The key groups of a mask (`rangeKeys`'s `groups`), each with its run start (`runOf`). -/
def groupsOf (N cut : ℕ) (mask : ℕ → Bool) : List (List ℕ × Option ℕ) :=
  let free := (List.range N).filter (!mask ·)
  ([free.filter (· < cut), free.filter (· ≥ cut)].filter (!·.isEmpty)).map fun bs ↦ (bs, runOf bs)

/-- `rangeKeys` on precomputed groups (a run is read by a shift). -/
def CS.rangeKeysG (s : CS) (isX : Bool) (groups : List (List ℕ × Option ℕ)) (v : ℕ) : CS × List (ℕ × ℕ) :=
  groups.foldl (fun (acc : CS × List (ℕ × ℕ)) g ↦
    let (s', t) := acc.1.tab (if isX then .eqx g.1 else .eqy g.1)
    (s', acc.2 ++ [(t, pextR g.2 (2 ^ g.1.length - 1) v g.1)])) (s, [])

/-- `addAtom` on precomputed groups (`fs` with the limb factor, `gx`/`gy` the `x`/`y` groups). -/
def CS.addAtomH (s : CS) (fs : List KF) (gx gy : List (List ℕ × Option ℕ)) (o x y : ℕ) (w : FE) : CS :=
  let (s, kid) := if fs.isEmpty then (s, 0) else s.ker fs
  let (s, xk) := s.rangeKeysG true gx x
  let (s, yk) := s.rangeKeysG false gy y
  let kk : ℕ × ℕ := if fs.isEmpty then (0, 0) else (2, kid)
  { s with atoms := s.atoms.push ⟨(([kk, (1, 1 <<< o)] : List (ℕ × ℕ)) ++ CS.interleave xk.reverse yk.reverse).toArray, w⟩ }

theorem rangeKeysG_eq (s : CS) (isX : Bool) (N cut : ℕ) (mask : ℕ → Bool) (v : ℕ) :
    s.rangeKeysG isX (groupsOf N cut mask) v = s.rangeKeys isX N cut mask v := by
  unfold CS.rangeKeysG groupsOf CS.rangeKeys
  simp only [List.foldl_map, la2_pextR]

theorem addAtomH_eq (s : CS) (fs : List KF) (o xm x : ℕ) (ym : List ℕ) (y : ℕ) (w : FE) (lim : Option ℕ) :
    s.addAtomH (ct_limFs fs lim) (groupsOf xVars xCut (fun b ↦ decide (b < xm)))
      (groupsOf yVars yCut (fun b ↦ (ct_limYm ym lim).contains b)) o x y w = s.addAtom fs o xm x ym y w lim := by
  cases lim <;> simp only [CS.addAtomH, CS.addAtom, rangeKeysG_eq, ct_limFs, ct_limYm] <;> rfl

/-! ## `mkPass` and the compiler -/

def CS.mkPassF (s : CS) (xs : List ℕ) (R : ℕ) (lim : Option ℕ) (raw : Array (ℕ × ℕ × ℕ × FE)) :
    CS × Option Pass :=
  let n := xs.length
  let sts := (raw.map (·.1)).qsort (· < ·)
  let dst := sts.foldl (fun (a : Array ℕ) c ↦ if a.back? == some c then a else a.push c) #[]
  let (ca, nf) := simAuto R n dst
  -- the points' exact cost: their atoms alone, merged and sorted, as code
  let gx := groupsOf xVars xCut (fun b ↦ decide (b < 0))
  let gy := groupsOf yVars yCut (fun b ↦ (ct_limYm [] lim).contains b)
  let fs := ct_limFs [] lim
  let pts (s : CS) : CS := raw.foldl (fun s (st, o, x, w) ↦
      (List.range (2 ^ n)).foldl (fun s j ↦
        let xx := x + ((List.range n).map fun k ↦ if j.testBit k then 2 ^ xs.getD k 0 else 0).sum
        s.addAtomH fs gx gy o xx (st + R * j) w) s) s
  let sp := pts { s with atoms := #[] }
  let pcost := if raw.size * 2 ^ n > 200000 then raw.size * 2 ^ n else
    let D := sp.atoms.foldl (fun d a ↦ max d a.keys.size) 0
    codeCost (atomCodeGF (mergeAtomsF2 1 (padTo D sp.atoms)) D)
  if ca + 2 * nf + raw.size > pcost then (pts s, none)
  else
  let masked (b : ℕ) : Bool := b < n || (match lim with | some e => b == e || b == e + 1 | none => false)
  let free := (List.range yVars).filter (!masked ·)
  let groups := [free.filter (· < yCut), free.filter (· ≥ yCut)].filter (!·.isEmpty)
  let (s, fin) := groups.foldl (fun (acc : CS × Array (ℕ × List ℕ)) bs ↦
    let (s', t) := acc.1.tab (.eqy bs)
    (s', acc.2.push (t, bs.map (· - n)))) (s, #[])
  let (s, mem) := raw.foldl (fun (acc : CS × Array Atom) (st, o, x, w) ↦
    let (s', xk) := acc.1.rangeKeys true xVars xCut (fun b ↦ xs.contains b) x
    (s', acc.2.push ⟨(#[(0, st), (1, 1 <<< o)] ++ xk.reverse.toArray), w⟩)) (s, #[])
  let D := mem.foldl (fun d a ↦ max d a.keys.size) 0
  let ms := mergeAtomsF2 1 (padTo D mem)
  (s, some ⟨xs.toArray, R, ms, D, fin, lim, initCodeGF ms D, none⟩)

theorem mkPassF_eq (s : CS) (xs : List ℕ) (R : ℕ) (lim : Option ℕ) (raw : Array (ℕ × ℕ × ℕ × FE)) :
    s.mkPassF xs R lim raw = s.mkPass xs R lim raw := by
  unfold CS.mkPassF CS.mkPass
  simp only [addAtomH_eq, mergeAtomsF2_eq, atomCodeGF_eq, initCodeGF_eq]
  rfl

def compileTF (ts : Array CTerm) : Comp :=
  let (rest, geos) := mergeGeo ts
  let s := geos.foldl CS.addGeo ({} : CS)
  let s := (runMergeF (mergeLimbsF rest)).foldl (fun s (t, lim) ↦ s.addTerm t lim) s
  let (s, ps) := s.pm.toList.foldl (fun (acc : CS × Array Pass) ((xs, R, lim), mem) ↦
    let (s', p) := acc.1.mkPassF xs R lim mem
    (s', match p with | some p => acc.2.push p | none => acc.2)) (s, #[])
  let D := s.atoms.foldl (fun d a ↦ max d a.keys.size) 0
  let as := mergeAtomsF2 1 (padTo D s.atoms)
  let tabs := ((s.tabs.set! 2 (.ker s.kers)).set! 3 (.prod s.xm)).set! 4 (.prod s.ym)
  let code := atomCodeGF as D
  { tabs, atoms := as, depth := D, passes := ps.map (fun p ↦ { p with fcode := fuse tabs p.code }), code,
    fcode := fuse tabs code }

/-- **The fast compiler is the compiler.** -/
theorem compileTF_eq : compileTF = compileT := by
  funext ts
  unfold compileTF compileT
  simp only [runMergeF_eq, mergeLimbsF_eq, mkPassF_eq, mergeAtomsF2_eq, atomCodeGF_eq]
  rfl

end Lvm.Typed.K
