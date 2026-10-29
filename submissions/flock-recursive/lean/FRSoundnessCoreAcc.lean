-- New for `flock-recursive` (BLUEPRINT §10 changes 27 (B) step 3; stage RET-2): the declarations of
-- the 3.x soundness modules that the revision 4.1 certificate reads, moved here verbatim (same
-- names, statements and proofs) from `FRSoundnessAccEq` (10), `FRSoundnessAccFin` (6),
-- `FRSoundnessAccPos` (4), `FRSoundnessAccVal` (3), `FRSoundnessAccSem` (8), `FRSoundnessAccSeg`
-- (6), `FRSoundnessAccLog` (17), `FRSoundnessAccQry` (2), `FRSoundnessAccLvl` (3),
-- `FRSoundnessAccPf` (2), `FRSoundnessAccW` (4), `FRSoundnessAccRun` (7), `FRSoundnessFrRun` (9),
-- `FRSoundnessFrRnd` (3), `FRSoundnessFrRndV` (3), `FRSoundnessFrLc` (1), `FRSoundnessExtStmt` (1),
-- `FRSoundnessExtLeaf` (6). Content: the 3.x accept-run semantics the R4 port reads (`AccSem`,
-- `AccRun`, `FrRun`, …) and `ExtLeaf`'s leaf pieces. The 3.x modules import this one.
import FRSoundnessCoreTail
import FRVIRChain
import FRVerifierImplOps

/-! ## From `FRSoundnessAccEq` (10 declarations) -/

section

namespace FR.Snd

open RecursionFast Finset

theorem getD_append_lt {R : Type} {a b : Array R} {q : ℕ} {d : R} (h : q < a.size) :
    (a ++ b).getD q d = a.getD q d := by
  simp [Array.getD_eq_getD_getElem?, Array.getElem?_append_left h]

theorem getD_append_ge {R : Type} {a b : Array R} {j : ℕ} {d : R} :
    (a ++ b).getD (a.size + j) d = b.getD j d := by
  simp [Array.getD_eq_getD_getElem?, Array.getElem?_append_right]

theorem getD_map_lt {R : Type} {a : Array R} {q : ℕ} {d : R} (f : R → R) (h : q < a.size) :
    (a.map f).getD q d = f (a.getD q d) := by
  simp [Array.getD_eq_getD_getElem?, h]

variable {R : Type} [CommRing R]

/-- `eqTab`'s fold from a table of `m` coordinates `g 0 … g (m − 1)`. -/
theorem eqTab_foldl : ∀ (l : List R) (t : Array R) (m : ℕ) (g : ℕ → R),
    t.size = 2 ^ m → (∀ q < 2 ^ m, t.getD q 0 = eqBits g m q) →
    (∀ k (hk : k < l.length), g (m + k) = l[k]) →
    (l.foldl (fun t x => t.map (· * (1 - x)) ++ t.map (· * x)) t).size = 2 ^ (m + l.length) ∧
      ∀ q < 2 ^ (m + l.length),
        (l.foldl (fun t x => t.map (· * (1 - x)) ++ t.map (· * x)) t).getD q 0 =
          eqBits g (m + l.length) q
  | [], t, m, g, hs, ht, _ => by
    simp only [List.foldl_nil, List.length_nil, Nat.add_zero]; exact ⟨hs, ht⟩
  | x :: l, t, m, g, hs, ht, hg => by
    have hx : g m = x := by have := hg 0 (by simp); rw [Nat.add_zero] at this; exact this
    have hs' : (t.map (· * (1 - x)) ++ t.map (· * x)).size = 2 ^ (m + 1) := by
      simp [hs, pow_succ, mul_two]
    have ht' : ∀ q < 2 ^ (m + 1), (t.map (· * (1 - x)) ++ t.map (· * x)).getD q 0 =
        eqBits g (m + 1) q := by
      intro q hq
      by_cases hlo : q < 2 ^ m
      · rw [getD_append_lt (by simp [hs, hlo]), getD_map_lt _ (by simp [hs, hlo]), ht q hlo,
          eqBits, eqBits, bitSel_succ_lo _ _ hlo, hx]
      · obtain ⟨j, rfl⟩ : ∃ j, q = 2 ^ m + j := ⟨q - 2 ^ m, by omega⟩
        have hj : j < 2 ^ m := by rw [pow_succ] at hq; omega
        rw [show 2 ^ m + j = (t.map (· * (1 - x))).size + j by simp [hs], getD_append_ge,
          getD_map_lt _ (by simp [hs, hj]), ht j hj, show (t.map (· * (1 - x))).size = 2 ^ m by
            simp [hs], eqBits, eqBits, bitSel_succ_hi _ _ hj, hx]
    have := eqTab_foldl l _ (m + 1) g hs' ht' fun k hk => by
      have := hg (k + 1) (by simp; omega)
      rw [show m + (k + 1) = m + 1 + k by omega] at this; exact this
    rw [List.foldl_cons]
    simpa [Nat.add_assoc, Nat.add_comm 1] using this

theorem eqTab_size' (r : Array R) : (eqTab r).size = 2 ^ r.size := by
  have := (eqTab_foldl r.toList #[1] 0 (fun v => r.getD v 0) rfl
    (fun q hq => by simp at hq; subst hq; simp [eqBits, bitSel]) fun k hk => by
      simp at hk; simp [Array.getD_eq_getD_getElem?, hk]).1
  rw [eqTab, ← Array.foldl_toList]; simpa using this

/-- **`eqTab r` at `q` is `eq(r, bits q)`**, bit `v` of `q` against coordinate `v`. -/
theorem eqTab_getD (r : Array R) {q : ℕ} (hq : q < 2 ^ r.size) :
    (eqTab r).getD q 0 = eqBits (fun v => r.getD v 0) r.size q := by
  have := (eqTab_foldl r.toList #[1] 0 (fun v => r.getD v 0) rfl
    (fun q hq => by simp at hq; subst hq; simp [eqBits, bitSel]) fun k hk => by
      simp at hk; simp [Array.getD_eq_getD_getElem?, hk]).2 q (by simpa using hq)
  rw [eqTab, ← Array.foldl_toList]; simpa using this

theorem foldl_add_eq {M : Type} [AddCommMonoid M] : ∀ (l : List M) (a : M),
    l.foldl (· + ·) a = a + l.sum
  | [], a => by simp
  | x :: l, a => by rw [List.foldl_cons, foldl_add_eq l, List.sum_cons, add_assoc]

/-- **`dotKF` at an `eqTab` weight**: `Σ_{r < 2^ℓ} eq(s, bits r)·col[r]` (the column has at least
`2^ℓ` elements). -/
theorem dotKF_eq_sum (s : Array K) (col : ByteArray) (hc : 2 ^ s.size ≤ col.size / 16) :
    dotKF (eqTab s) col = ∑ r ∈ range (2 ^ s.size),
      eqBits (fun v => s.getD v 0) s.size r * algebraMap F K (readF col (16 * r)) := by
  rw [← dotKFF_eq, dotKFF, dotKFGo_eq, foldl_add_eq, zero_add, eqTab_size',
    min_eq_right hc, ← List.range_eq_range', ← List.sum_toFinset _ (List.nodup_range),
    List.toFinset_range]
  · refine sum_congr rfl fun r hr => ?_
    have hr' := mem_range.1 hr
    have hlt : r < (eqTab s).size := by rw [eqTab_size']; exact hr'
    have hg : (eqTab s)[r] = (eqTab s).getD r 0 := by
      rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hlt, Option.getD_some]
    rw [getElem!_pos _ r hlt, hg, eqTab_getD s hr', K.smulF_eq_mul, ← K.algebraMap_eq_ofF, fAt_eq,
      readF, mul_comm]

/-- The unit vector `e_v` of `K^7`: coordinate `u` is `[u = v]`. -/
theorem unitK_getD (v u : ℕ) (hu : u < 7) : (unitK v).getD u 0 = if u = v then 1 else 0 := by
  simp [unitK, Array.getD_eq_getD_getElem?, hu]

/-- **`tensorW p e_v` is `Ŵ_v(D[p])`** (`v < 7`). -/
theorem tensorWS_unit (p : ℕ) {v : ℕ} (hv : v < 7) :
    Impl.tensorWS p (unitK v) = algebraMap F K (wAtD v p) := by
  rw [Impl.tensorWS, tensorTwin, show (unitK v).size = 7 by simp [unitK],
    prod_eq_single_of_mem v (mem_range.2 hv)]
  · rw [unitK_getD v v hv, if_pos rfl]; simp [wAtD]
  · intro u hu huv
    rw [unitK_getD v u (mem_range.1 hu), if_neg huv]; simp

end FR.Snd

end

/-! ## From `FRSoundnessAccFin` (6 declarations) -/

section

namespace FR.Snd

open RecursionFast FR.Merkle Finset

variable {W₀ : Log → Log → ℕ → K} {c₀ : Log → Log → K}

/-- `g(0) + g(1)` of round `l`'s message of the K rounds starting at `b`. -/
def rSum (b : ℕ) (es : Log) (l : ℕ) : K :=
  peval (g2At b 32 readK es l) 0 + peval (g2At b 32 readK es l) 1

/-- `g_l(r_l)`: round `l`'s message at its challenge. -/
def rVal (b : ℕ) (es : Log) (l : ℕ) : K := peval (g2At b 32 readK es l) (rch2 b chK es l)

theorem chk2_succ (b : ℕ) (c0 : Log → Log → K) (L es : Log) (l : ℕ) :
    Chk2 b 32 readK chK c0 L es (l + 1) ↔ rSum b es (l + 1) = rVal b es l := Iff.rfl

theorem chk2_zero (b : ℕ) (c0 : Log → Log → K) (L es : Log) :
    Chk2 b 32 readK chK c0 L es 0 ↔ rSum b es 0 = c0 L es := Iff.rfl

theorem extract40_absorbQ (st : Digest) (m : ByteArray) :
    (absorbQ st m).extract 40 (absorbQ st m).size = m := by
  have h : ((absorbQ st m).extract 40 (absorbQ st m).size).data.toList = m.data.toList := by
    rw [toList_extract, absorbQ_data, absorbQ_size]
    simp [tagAbs]
  have h2 := Array.ext' h
  calc (absorbQ st m).extract 40 (absorbQ st m).size
      = ⟨((absorbQ st m).extract 40 (absorbQ st m).size).data⟩ := rfl
    _ = ⟨m.data⟩ := by rw [h2]
    _ = m := rfl

theorem bytesAt_extract_of_le (π : Proof) {o len off : ℕ} (h : off + 32 ≤ len) :
    bytesAt (π.extract o (o + len)) off 32 = bytesAt π (o + off) 32 := by
  ext k hk
  rw [getElem_bytesAt _ _ _ _ hk, getElem_bytesAt _ _ _ _ hk, toList_extract,
    Nat.add_sub_cancel_left, List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
    List.getElem?_take_of_lt (by omega), List.getElem?_drop, Nat.add_assoc]

end FR.Snd

end

/-! ## From `FRSoundnessAccPos` (4 declarations) -/

section

namespace FR.Snd

open RecursionFast Finset

theorem charTwo_peval01 (a b c : K) : peval #[a, b, c] 0 + peval #[a, b, c] 1 = b + c := by
  rw [peval_three, peval_three]
  have h : a + a = 0 := CharTwo.add_self_eq_zero a
  ring_nf
  linear_combination h

/-- `rSum` is `c₁ + c₂` of round `l`'s message. -/
theorem rSum_eq (b : ℕ) (es : Log) (l : ℕ) :
    rSum b es l = readK (msgAt es (b + 2 * l)) 32 + readK (msgAt es (b + 2 * l)) 64 := by
  rw [rSum, g2At, charTwo_peval01]

theorem eqv_k (a b : K) : (Val.k a).eqv (Val.k b) = true ↔ a = b := by simp [Val.eqv]

/-- The answers of the squeezes of `n` rounds on a trace (entry `2l + 1`). -/
def sqAns (tr : Trace) (l : ℕ) : Digest := (tr.getD (2 * l + 1) default).2

end FR.Snd

end

/-! ## From `FRSoundnessAccVal` (3 declarations) -/

section

namespace FR.Snd

open RecursionFast

theorem sqAns_succ (q₁ q₂ : ByteArray) (a₁ a₂ : Digest) (tr : Trace) (l : ℕ) :
    sqAns ((q₁, a₁) :: (q₂, a₂) :: tr) (l + 1) = sqAns tr l := by
  simp only [sqAns, show 2 * (l + 1) + 1 = 2 * l + 1 + 1 + 1 by ring, List.getD_cons_succ]

/-- **`roundsT_vals`**: `n` K rounds leave 13 registers each; register `3` of round `l` is its
challenge `chK a₂`, register `12` (a real round) its `g(r)`. -/
theorem roundsT_vals (inp : Input) (f o real : ℕ) :
    ∀ (n j : ℕ) (d : Digest) (cv : Val) (tr : Trace) (x : List Val × Bool × Trace),
      roundsT inp f o 2 true real n j d cv tr = some x →
      x.1.length = 13 * n ∧ ∀ l < n, x.1.getD (13 * l + 3) default = .k (chK (sqAns tr l)) ∧
        (j + l < real → x.1.getD (13 * l + 12) default =
          .k (gK inp f (o + (j + l) * 96) (sqAns tr l)))
  | 0, _, _, _, _, x, h => by
    simp only [roundsT, Option.some.injEq] at h; subst h
    exact ⟨rfl, fun l hl => absurd hl (by omega)⟩
  | n + 1, j, d, cv, (q₁, a₁) :: (q₂, a₂) :: tr, x, h => by
    simp only [roundsT, ite_true] at h
    split_ifs at h with hq
    obtain ⟨x', hx', rfl⟩ := Option.map_eq_some_iff.mp h
    obtain ⟨ih1, ih2⟩ := roundsT_vals inp f o real n (j + 1) a₂ _ tr x' hx'
    have hl13 : (roundKVals inp f (o + j * roundBytes true) (decide (j < real)) a₁ a₂ cv).length =
      13 := rfl
    refine ⟨by rw [List.length_append, hl13, ih1]; ring, fun l hl => ?_⟩
    rcases l with _ | l
    · refine ⟨rfl, fun hj => ?_⟩
      simp [roundKVals, sqAns, roundBytes, show j < real by omega]
    · obtain ⟨i1, i2⟩ := ih2 l (by omega)
      rw [show 13 * (l + 1) + 3 = 13 + (13 * l + 3) by ring,
        show 13 * (l + 1) + 12 = 13 + (13 * l + 12) by ring,
        List.getD_append_right _ _ _ _ (by omega), List.getD_append_right _ _ _ _ (by omega), hl13,
        Nat.add_sub_cancel_left, Nat.add_sub_cancel_left, sqAns_succ]
      refine ⟨i1, fun hj => ?_⟩
      rw [i2 (by omega), show j + 1 + l = j + (l + 1) by omega]
  | _ + 1, _, _, _, [], _, h => by simp [roundsT] at h
  | _ + 1, _, _, _, [_], _, h => by simp [roundsT] at h

variable {impl : OpImpl} {κ : Kind} {inp : Input}

/-- On an all-Fiat–Shamir phase, the trace's entries are the chain's from `phStart`. -/
theorem seg_entries {es trk seg rest : Trace} {s : ℕ} {its more : List Item}
    (hdrop : es.drop s = fsOf trk (its ++ more)) (htrk : trk = seg ++ rest)
    (hl : seg.length = its.length) (hfs : ∀ it ∈ its, it.isFS = true) (hne : 0 < its.length) :
    s + its.length ≤ es.length ∧ ∀ m < its.length, trk.getD m default = es.getD (s + m) default := by
  rw [htrk, fsOf_append hl, fsOf_all hfs hl] at hdrop
  have hlen := congrArg List.length hdrop
  simp only [List.length_drop, List.length_append] at hlen
  refine ⟨by omega, fun m hm => ?_⟩
  have := congrArg (fun l => l.getD m default) hdrop
  simp only [List.getD_eq_getElem?_getD, List.getElem?_drop] at this
  rw [htrk, List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
    List.getElem?_append_left (by omega), this, List.getElem?_append_left (by omega)]

end FR.Snd

end

/-! ## From `FRSoundnessAccSem` (8 declarations) -/

section

namespace FR.Snd

open RecursionFast

variable (impl : OpImpl) (κ : Kind) (inp : Input)

/-- `Finals.ops`'s fold over fields, as a recursion: each field's ops at the next free register,
its exports pushed. -/
def runFields (outs : Array (List Reg)) (zh : List Reg) :
    List FinField → ℕ → Array (List Reg) → List Op
  | [], _, _ => []
  | f :: fs, b, ex => (f ⟨outs, zh, ex⟩ b).1 ++
      runFields outs zh fs (b + opsOut (f ⟨outs, zh, ex⟩ b).1) (ex.push (f ⟨outs, zh, ex⟩ b).2)

/-- **The exports the fold has pushed before field `k`** of `fs` (base `b`, exports `ex`): what
`runFields` passes field `k` as `ex`. -/
def exAt (outs : Array (List Reg)) (zh : List Reg) :
    List FinField → ℕ → Array (List Reg) → ℕ → Array (List Reg)
  | [], _, ex, _ => ex
  | _ :: _, _, ex, 0 => ex
  | f :: fs, b, ex, k + 1 =>
    exAt outs zh fs (b + opsOut (f ⟨outs, zh, ex⟩ b).1) (ex.push (f ⟨outs, zh, ex⟩ b).2) k

theorem foldl_step (outs : Array (List Reg)) (zh : List Reg) :
    ∀ (fs : List FinField) (A : List Op) (b : ℕ) (ex : Array (List Reg)),
      (fs.foldl (fun (acc : List Op × ℕ × Array (List Reg)) (f : FinField) =>
        (acc.1 ++ (f ⟨outs, zh, acc.2.2⟩ acc.2.1).1, acc.2.1 + opsOut (f ⟨outs, zh, acc.2.2⟩ acc.2.1).1,
          acc.2.2.push (f ⟨outs, zh, acc.2.2⟩ acc.2.1).2)) (A, b, ex)).1 =
        A ++ runFields outs zh fs b ex
  | [], A, _, _ => by simp [runFields]
  | f :: fs, A, b, ex => by
    rw [List.foldl_cons, foldl_step outs zh fs, runFields, List.append_assoc]

/-- `Finals.ops` is `finRS`'s ops, then the rest's, with `finRS`'s exports as `zhat`. -/
theorem finals_ops_eq (fin : Finals) (outs : Array (List Reg)) (b : ℕ) :
    fin.ops outs b = runFields outs [] [fin.finRS] b #[] ++
      runFields outs (fin.finRS ⟨outs, [], #[]⟩ b).2 fin.rest
        (b + opsOut (fin.finRS ⟨outs, [], #[]⟩ b).1) #[(fin.finRS ⟨outs, [], #[]⟩ b).2] := by
  rw [Finals.ops]
  dsimp only
  rw [foldl_step, List.nil_append, runFields, runFields, List.append_nil]

/-- Ops that ask nothing run purely. -/
theorem pureRun_noAsk (R : Array Val) :
    ∀ (o : List Op) (L₀ : List Val), o.filterMap Op.item? = [] →
      ∃ L f, pureRun impl κ inp o R L₀ = some (L, f)
  | [], L₀, _ => ⟨L₀, true, rfl⟩
  | op :: o, L₀, h => by
    have hop : op.item? = none := by
      by_contra hne
      obtain ⟨it, hit⟩ := Option.ne_none_iff_exists'.mp hne
      simp [hit] at h
    have ho : o.filterMap Op.item? = [] := by simpa [List.filterMap_cons, hop] using h
    simp only [pureRun]
    split
    · next vs ok _ =>
      obtain ⟨L, f, hL⟩ := pureRun_noAsk R o (L₀ ++ vs) ho
      exact ⟨L, ok && f, by rw [hL]; rfl⟩
    · next q hq => exact absurd (item?_of_ask impl κ inp hq) (by simp [hop])

/-- A run whose flag is down stays down. -/
theorem exec_ok_false : ∀ (ops : List Op) (R : Array Val) (tr : Trace) (s : St) (tr' : Trace),
    exec impl κ inp ops ⟨R, false⟩ tr = some (s, tr') → s.ok = false
  | [], R, tr, s, tr', h => by simp [exec] at h; rw [← h.1]
  | op :: ops, R, tr, s, tr', h => by
    simp only [exec] at h
    split at h
    · exact exec_ok_false ops _ tr s tr' (by simpa using h)
    · split at h
      · cases h
      · split at h
        · exact exec_ok_false ops _ _ s tr' h
        · cases h

/-- **One field**: on an accepted run, a field that asks nothing has flag `true`, the flag before
it was `true`, and the run continues from the extended registers. -/
theorem field_flag {o ops : List Op} {R : Array Val} {ok : Bool} {tr : Trace} {s : St}
    {tr' : Trace} (hna : o.filterMap Op.item? = [])
    (h : exec impl κ inp (o ++ ops) ⟨R, ok⟩ tr = some (s, tr')) (hs : s.ok = true) :
    ∃ L, pureRun impl κ inp o R [] = some (L, true) ∧ ok = true ∧
      exec impl κ inp ops ⟨R ++ L.toArray, true⟩ tr = some (s, tr') := by
  obtain ⟨L, f, hL⟩ := pureRun_noAsk impl κ inp R o [] hna
  rw [exec_field impl κ inp o ops R L f ok tr hL] at h
  cases hok : ok && f
  · rw [hok] at h; rw [exec_ok_false impl κ inp ops _ tr s tr' h] at hs; cases hs
  · rw [hok] at h
    simp only [Bool.and_eq_true] at hok
    exact ⟨L, by rw [hL, hok.2], hok.1, h⟩

/-- **Every field of `runFields`** has flag `true`, each from a register file extending `R` whose
size is the field's base. -/
theorem fields_ok (outs : Array (List Reg)) (zh : List Reg) :
    ∀ (fs : List FinField) (R : Array Val) (ex : Array (List Reg)) (ok : Bool) (tail : List Op)
      (tr : Trace) (s : St) (tr' : Trace),
      (∀ f ∈ fs, ∀ fi b, (f fi b).1.filterMap Op.item? = []) →
      exec impl κ inp (runFields outs zh fs R.size ex ++ tail) ⟨R, ok⟩ tr = some (s, tr') →
      s.ok = true →
      ok = true ∧ ∀ k (hk : k < fs.length), ∃ Rk : Array Val, ∃ L, ExtA R Rk ∧
        pureRun impl κ inp ((fs[k]'hk) ⟨outs, zh, exAt outs zh fs R.size ex k⟩ Rk.size).1 Rk [] =
          some (L, true)
  | [], R, ex, ok, tail, tr, s, tr', _, h, hs => by
    refine ⟨?_, fun k hk => absurd hk (by simp)⟩
    cases ok
    · rw [runFields, List.nil_append] at h
      rw [exec_ok_false impl κ inp tail R tr s tr' h] at hs; cases hs
    · rfl
  | f :: fs, R, ex, ok, tail, tr, s, tr', hna, h, hs => by
    rw [runFields, List.append_assoc] at h
    obtain ⟨L, hL, hok, h'⟩ := field_flag impl κ inp
      (hna f (List.mem_cons_self ..) _ _) h hs
    have hsz : (R ++ L.toArray).size = R.size + opsOut (f ⟨outs, zh, ex⟩ R.size).1 := by
      have hl := pureRun_len impl κ inp R _ [] L true hL
      simp [hl]
    rw [← hsz] at h'
    obtain ⟨-, hrest⟩ := fields_ok outs zh fs (R ++ L.toArray) _ true tail tr s tr'
      (fun g hg => hna g (List.mem_cons_of_mem _ hg)) h' hs
    refine ⟨hok, fun k hk => ?_⟩
    rcases k with _ | k
    · exact ⟨R, L, ⟨le_rfl, fun _ _ => rfl⟩, hL⟩
    · obtain ⟨Rk, Lk, hE, hk'⟩ := hrest k (by simpa using hk)
      rw [hsz] at hk'
      exact ⟨Rk, Lk, (ExtA.app R L).trans hE, hk'⟩

end FR.Snd

end

/-! ## From `FRSoundnessAccSeg` (6 declarations) -/

section

namespace FR.Snd

open RecursionFast

variable (impl : OpImpl) (κ : Kind) (inp : Input)

/-- The length of `fsOf` on a segment of the items' length: the number of Fiat–Shamir items. -/
theorem fsOf_length {seg : Trace} {its : List Item} (h : seg.length = its.length) :
    (fsOf seg its).length = (its.filter Item.isFS).length := by
  induction seg generalizing its with
  | nil => cases its <;> simp_all [fsOf]
  | cons e seg ih =>
    cases its with
    | nil => simp at h
    | cons it its =>
      simp only [List.length_cons, Nat.add_right_cancel_iff] at h
      have := ih h
      simp only [fsOf, List.zip_cons_cons, List.filter_cons] at this ⊢
      split <;> simp_all

theorem piopPhases_length : piopPhases.length = 26 := rfl

theorem levelPhases_length (i : ℕ) : (levelPhases i).length = 5 := rfl

theorem flatMap_level_length (n : ℕ) : ((List.range n).flatMap levelPhases).length = 5 * n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [List.range_succ, List.flatMap_append, List.length_append, ih]; simp [levelPhases_length]; ring

/-- The table's first row named `P1` is row 26 (the names of rows `0 … 25` are A.4's PIOP
names). -/
theorem phaseIx_P1 : phaseIx "P1" = 26 := by
  rw [phaseIx, phases, List.append_assoc, List.findIdx_append, List.findIdx_eq_length.2 (by decide)]
  simp [piopPhases_length, List.range_succ_eq_map, levelPhases, nLevels]; rfl

/-- The table's first row named `Pf` is row 51. -/
theorem phaseIx_Pf : phaseIx "Pf" = 51 := by
  have h : ∀ p ∈ piopPhases ++ (List.range nLevels).flatMap levelPhases,
      decide (p.name = "Pf") = false := by
    intro p hp
    simp only [List.mem_append, List.mem_flatMap, List.mem_range] at hp
    rcases hp with hp | ⟨i, -, hp⟩
    · revert p; decide
    · simp only [levelPhases, List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl | rfl | rfl | rfl <;> rfl
  rw [phaseIx, phases, List.findIdx_append, List.findIdx_eq_length.2 h]
  simp only [List.length_append, piopPhases_length, flatMap_level_length, nLevels]; rfl

end FR.Snd

end

/-! ## From `FRSoundnessAccLog` (17 declarations) -/

section

namespace FR.Snd

open RecursionFast FR.Merkle Finset

theorem headD_lt {l : List ℕ} {n : ℕ} (h : ∀ x ∈ l, x < n) (hn : 0 < n) : l.headD 0 < n := by
  cases l with
  | nil => exact hn
  | cons a l => exact h a (List.mem_cons_self ..)

theorem getLastD_lt {l : List ℕ} {n : ℕ} (h : ∀ x ∈ l, x < n) (hn : 0 < n) : l.getLastD 0 < n := by
  rcases List.eq_nil_or_concat l with rfl | ⟨L, b, rfl⟩
  · exact hn
  · rw [List.concat_eq_append, List.getLastD_concat]; exact h b (by simp)

theorem pureRun_det {impl : OpImpl} {κ : Kind} {inp : Input} {o : List Op} {r : Array Val}
    {L L' : List Val} {f : Bool} (h1 : pureRun impl κ inp o r [] = some (L, true))
    (h2 : pureRun impl κ inp o r [] = some (L', f)) : f = true := by
  rw [h1] at h2; cases h2; rfl

variable {impl : OpImpl} {κ : Kind} {inp : Input} {tr : Trace} {y : List Val × List Bool × Trace}

section Refs

variable {fi : FinIn} {N : ℕ}

theorem sub_lt {l l' : List ℕ} (h : ∀ x ∈ l, x < N) (hs : ∀ x ∈ l', x ∈ l) : ∀ x ∈ l', x < N :=
  fun x hx => h x (hs x hx)

theorem getD_lt (hN : 0 < N) {l : List ℕ} (h : ∀ x ∈ l, x < N) (n : ℕ) : l.getD n 0 < N := by
  rw [List.getD_eq_getElem?_getD]
  rcases hl : l[n]? with _ | z
  · exact hN
  · exact h z (List.mem_of_getElem? hl)

variable (hN : 0 < N) (hO : ∀ n, ∀ x ∈ fi.outs.getD n [], x < N)

include hN hO

theorem outsOf_lt (s : String) : ∀ x ∈ outsOf fi s, x < N := hO _

theorem chals_lt (s : String) (k : ℕ) : ∀ x ∈ chals fi s k, x < N :=
  sub_lt (outsOf_lt hN hO s) fun _ hx => List.mem_of_mem_drop (List.mem_of_mem_take hx)

theorem coordsR_lt (s : String) : ∀ x ∈ coordsR fi s, x < N :=
  sub_lt (outsOf_lt hN hO s) fun _ hx => List.mem_of_mem_drop hx

theorem lvOuts_lt (i k : ℕ) : ∀ x ∈ lvOuts fi i k, x < N := hO _

theorem sRegs_lt (i : ℕ) : ∀ x ∈ sRegs fi i, x < N :=
  sub_lt (lvOuts_lt hN hO i 0) fun _ hx => List.mem_of_mem_drop (List.mem_of_mem_take hx)

theorem kcOf_lt (i : ℕ) : ∀ x ∈ kcOf fi i, x < N :=
  sub_lt (lvOuts_lt hN hO i 4) fun _ hx => List.mem_of_mem_drop (List.mem_of_mem_take hx)

theorem ysOf_lt (i : ℕ) : ∀ x ∈ ysOf fi i, x < N := lvOuts_lt hN hO i 3

omit hN hO in
theorem srcs_f {l : List ℕ} (h : ∀ x ∈ l, x < N) : ∀ p ∈ l.map PtSrc.f, ∀ x ∈ p.regs, x < N := by
  intro p hp x hx
  obtain ⟨z, hz, rfl⟩ := List.mem_map.1 hp
  simp only [PtSrc.regs, List.mem_singleton] at hx; subst hx; exact h _ hz

omit hN hO in
theorem srcs_k {l : List ℕ} (h : ∀ x ∈ l, x < N) : ∀ p ∈ l.map PtSrc.k, ∀ x ∈ p.regs, x < N := by
  intro p hp x hx
  obtain ⟨z, hz, rfl⟩ := List.mem_map.1 hp
  simp only [PtSrc.regs, List.mem_singleton] at hx; subst hx; exact h _ hz

omit hN hO in
theorem srcs_c {α : Type} (l : List α) (g : α → K) :
    ∀ p ∈ l.map (fun a => PtSrc.c (g a)), ∀ x ∈ p.regs, x < N := by
  intro p hp x hx
  obtain ⟨z, -, rfl⟩ := List.mem_map.1 hp
  simp [PtSrc.regs] at hx

omit hN hO in
theorem srcs_app {a b : List PtSrc} (ha : ∀ p ∈ a, ∀ x ∈ p.regs, x < N)
    (hb : ∀ p ∈ b, ∀ x ∈ p.regs, x < N) : ∀ p ∈ a ++ b, ∀ x ∈ p.regs, x < N := by
  intro p hp
  rcases List.mem_append.1 hp with h | h
  exacts [ha p h, hb p h]

end Refs

theorem accVal_kc {g : ℕ → F} (Ys : List K) (A : K) (ht : Ys.length < 2 ^ 9) :
    accVal (eqTab ((List.range 9).map g).toArray) Ys 0 A =
      A + ∑ q ∈ range Ys.length, K.smulF (eqBits g 9 q) (Ys.getD q 0) := by
  rw [accVal_eq, ← List.sum_toFinset _ List.nodup_range, List.toFinset_range]
  refine congrArg (A + ·) (sum_congr rfl fun q hq => ?_)
  have hq' := mem_range.1 hq
  rw [Nat.zero_add, eqTab_getD _ (by simp; omega)]
  simp only [List.size_toArray, List.length_map, List.length_range]
  rw [eqBits_congr (r' := g) (fun v hv => by simp [Array.getD_eq_getD_getElem?, hv])]

end FR.Snd

end

/-! ## From `FRSoundnessAccQry` (2 declarations) -/

section

namespace FR.Snd

open RecursionFast FR.Merkle

/-- On a log that repeats no query, an entry is the first one for its query. -/
theorem find_of_mem {L : Log} (hL : (L.map Prod.fst).Nodup) {e : ByteArray × Digest}
    (he : e ∈ L) : L.find? (fun x => decide (x.1 = e.1)) = some e := by
  obtain ⟨e', he'⟩ := Option.isSome_iff_exists.mp
    (List.find?_isSome.mpr ⟨e, he, by simp⟩ : (L.find? fun x => decide (x.1 = e.1)).isSome)
  have hm := List.mem_of_find?_eq_some he'
  have hq : e'.1 = e.1 := by simpa using List.find?_some he'
  rw [he', List.inj_on_of_nodup_map hL hm he hq]

theorem runLog_query_mem {α : Type} {L : Log} (hL : (L.map Prod.fst).Nodup) {q : ByteArray}
    {a : Digest} (he : (q, a) ∈ L) (k : Digest → OProg α) :
    (OProg.query q k).runLog L = (k a).runLog L := by
  simp only [OProg.runLog]
  rw [show (fun e : ByteArray × Digest => decide (e.1 = q)) = fun x => decide (x.1 = (q, a).1)
    from rfl, find_of_mem hL he, Option.bind_some]

variable (κ : Kind) (inp : Input)

end FR.Snd

end

/-! ## From `FRSoundnessAccLvl` (3 declarations) -/

section

namespace FR.Snd

open RecursionFast FR.Merkle

variable {impl : OpImpl} {κ : Kind} {inp : Input}

theorem size_le_of_ext {M X : List Val} {R : Array Val} (hext : ExtA (#[] ++ (M ++ X).toArray) R) :
    M.length + X.length ≤ R.size := by
  have := hext.1; simpa using this

theorem replicate_sq_fs (k : ℕ) : ∀ it ∈ List.replicate k Item.squeeze, it.isFS = true := by
  intro it hit; rw [List.eq_of_mem_replicate hit]; rfl

theorem allZero_mem {a : ByteArray} (h : a.data.all (· == 0) = true) : ∀ b ∈ a.data.toList, b = 0 := by
  intro b hb
  obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hb
  simp only [Array.all_eq_true] at h
  have := h k (by simpa using hk)
  simpa using this

end FR.Snd

end

/-! ## From `FRSoundnessAccPf` (2 declarations) -/

section

namespace FR.Snd

open RecursionFast FR.Merkle Finset

theorem hEll_pos {i : ℕ} (hi : i < 5) : 0 < hEll i := by
  unfold hEll; interval_cases i <;> decide

variable {impl : OpImpl} {κ : Kind} {inp : Input} {tr : Trace} {y : List Val × List Bool × Trace}

theorem take_rs (b K : ℕ) (z : ℕ) :
    (((List.range K).map (fun j => b + 13 * j + 6) ++ [z]).take K) =
      (List.range K).map (fun j => b + 13 * j + 6) :=
  List.take_left' (by simp)

end FR.Snd

end

/-! ## From `FRSoundnessAccW` (4 declarations) -/

section

namespace FR.Snd

open RecursionFast FR.Merkle Finset

theorem map_range_append {α : Type} (a b : ℕ) (f g : ℕ → α) :
    (List.range a).map f ++ (List.range b).map g =
      (List.range (a + b)).map (fun v => if v < a then f v else g (v - a)) := by
  refine List.ext_getElem (by simp) fun v h1 h2 => ?_
  simp only [List.length_append, List.length_map, List.length_range] at h1
  by_cases hv : v < a
  · rw [List.getElem_append_left (by simpa using hv)]; simp [hv]
  · rw [List.getElem_append_right (by simpa using hv)]; simp [hv]

/-- The tail's length sum from level `k`. -/
def tLen (m k : ℕ) : ℕ := ((List.range' k (5 - k)).map fun j => hEll j - 1).sum + (m - 25)

variable {impl : OpImpl} {κ : Kind} {inp : Input} {tr : Trace} {y : List Val × List Bool × Trace}

theorem drop_one_map_range (g : ℕ → ℕ) (n : ℕ) :
    ((List.range n).map g).drop 1 = (List.range (n - 1)).map fun t => g (t + 1) := by
  rcases n with _ | n
  · rfl
  · rw [List.range_succ_eq_map, List.map_cons, List.map_map]; rfl

theorem lvsV_snoc (impl : OpImpl) (fi : FinIn) (rv : ℕ → Val) (tl : ℕ → Array K) (x : ℕ) :
    ∀ (l : List ℕ) (W : K), lvsV impl fi rv tl (l ++ [x]) W = lvStepV impl fi rv tl x (lvsV impl fi rv tl l W)
  | [], _ => rfl
  | k :: l, W => by simp only [List.cons_append, lvsV]; exact lvsV_snoc impl fi rv tl x l _

end FR.Snd

end

/-! ## From `FRSoundnessAccRun` (7 declarations) -/

section

namespace FR.Snd

open RecursionFast FR.Merkle

/-- **`runLog_trace`**: a verdict on the log is a verdict on a trace of the log's entries. -/
theorem runLog_trace {α : Type} {L : Log} :
    ∀ (p : OProg α) {b : α}, p.runLog L = some b → ∃ tr : Trace, p.runSeq tr = some b ∧ ∀ e ∈ tr, e ∈ L
  | .ret a, b, h => ⟨[], h, by simp⟩
  | .query q k, b, h => by
    obtain ⟨e, he, rfl, hk⟩ := runLog_query h
    obtain ⟨tr, h1, h2⟩ := runLog_trace (k e.2) hk
    refine ⟨e :: tr, ?_, ?_⟩
    · rw [show e = (e.1, e.2) from rfl, OProg.runSeq_query]; exact h1
    · intro x hx
      rcases List.mem_cons.mp hx with rfl | hx
      · exact he
      · exact h2 x hx

/-- **Entries linked to the previous answer, from an entry with no state, are the forest path of
the last one** (on a log without bad events, every entry in the log). -/
theorem path_of_links {L : Log} (hb : ¬ Bad L) {es : Log} (hin : ∀ e ∈ es, e ∈ L)
    (h0 : ∀ h : 0 < es.length, stateIn (es[0]'h).1 = none)
    (hs : ∀ n (h : n + 1 < es.length), stateIn (es[n + 1]'h).1 = some (es[n]'(by omega)).2) :
    ∀ n (h : n < es.length), ∃ j, ∃ hj : j < L.length, L[j] = es[n] ∧
      entriesOf L (pathOf L j) = es.take (n + 1) := by
  intro n
  induction n with
  | zero =>
    intro h
    obtain ⟨j, hj, hje⟩ := List.getElem_of_mem (hin _ (List.getElem_mem h))
    refine ⟨j, hj, hje, ?_⟩
    have hp : predIdx L j = none := by
      simp only [predIdx, List.getElem?_eq_getElem hj, Option.bind_some, hje, h0 h,
        Option.bind_none]
    rw [pathOf, back, hp]
    dsimp only
    simp only [entriesOf, List.map_cons, List.map_nil, getElem!_pos L j hj, hje]
    rw [List.take_add_one, List.take_zero, List.nil_append, List.getElem?_eq_getElem h]; rfl
  | succ n ih =>
    intro h
    obtain ⟨i, hi, hie, hpi⟩ := ih (by omega)
    obtain ⟨j, hj, hje⟩ := List.getElem_of_mem (hin _ (List.getElem_mem h))
    have hp : predIdx L j = some i := by
      simp only [predIdx, List.getElem?_eq_getElem hj, Option.bind_some, hje, hs n h, ← hie,
        ansIdx_self hb hi]
    have hij : i < j := predIdx_lt hb hp
    refine ⟨j, hj, hje, ?_⟩
    rw [pathOf, back, hp]
    dsimp only
    rw [ite_pos' hij, back_fuel L j i hij, ← pathOf]
    simp only [entriesOf, List.map_append, List.map_cons, List.map_nil] at hpi ⊢
    rw [hpi, getElem!_pos L j hj, hje]
    conv_rhs => rw [List.take_add_one, List.getElem?_eq_getElem h]
    rfl

theorem mem_fsOf {seg : Trace} {its : List Item} {e : ByteArray × Digest} (h : e ∈ fsOf seg its) :
    e ∈ seg := by
  simp only [fsOf, List.mem_map, List.mem_filter] at h
  obtain ⟨⟨e', it⟩, ⟨hm, -⟩, rfl⟩ := h
  exact (List.of_mem_zip hm).1

theorem size_extract_of_le {π : Proof} {o len : ℕ} (h : o + len ≤ π.size) :
    (π.extract o (o + len)).size = len := by
  rw [ByteArray.size_extract]; omega

theorem fsCheck_absorbQ (st : Digest) (msg : ByteArray) :
    fsCheck (.absorb msg.size) (absorbQ st msg) = true := by
  have hc : (absorbQ st msg).data.toList.take 8 = tagAbs := by rw [absorbQ_data]; simp [tagAbs]
  simp [fsCheck, hc, absorbQ_size]

theorem fsCheck_squeezeQ (st : Digest) : fsCheck .squeeze (squeezeQ st) = true := by
  have hc : (squeezeQ st).data.toList.take 8 = tagSqz := by rw [squeezeQ_data]; simp [tagSqz]
  simp [fsCheck, hc, squeezeQ_size]

theorem fsCheck_seedQ (vk c : Digest) (hdr : ByteArray) (hh : hdr.size = 48) :
    fsCheck .seed (seedQ vk c hdr) = true := by
  have h := (matches_seed vk c hdr hh zeroD).1
  simpa using h

end FR.Snd

end

/-! ## From `FRSoundnessFrRun` (9 declarations) -/

section

namespace FR.Snd

open RecursionFast Finset FR.Impl

section Chain

variable (impl : OpImpl) (κ : Kind) (inp : Input)

/-- **Every field of `runFields`, with the register files chained**: field `k` runs from
`Rs k` to flag `true`, and `Rs (k + 1)` is `Rs k` with its output appended. -/
theorem fields_chain (outs : Array (List Reg)) (zh : List Reg) :
    ∀ (fs : List FinField) (R : Array Val) (ex : Array (List Reg)) (ok : Bool) (tail : List Op)
      (tr : Trace) (s : St) (tr' : Trace),
      (∀ f ∈ fs, ∀ fi b, (f fi b).1.filterMap Op.item? = []) →
      exec impl κ inp (runFields outs zh fs R.size ex ++ tail) ⟨R, ok⟩ tr = some (s, tr') →
      s.ok = true →
      ∃ Rs : ℕ → Array Val, Rs 0 = R ∧ ∀ k (hk : k < fs.length), ∃ L,
        pureRun impl κ inp ((fs[k]'hk) ⟨outs, zh, exAt outs zh fs R.size ex k⟩ (Rs k).size).1
          (Rs k) [] = some (L, true) ∧ Rs (k + 1) = Rs k ++ L.toArray
  | [], R, _, _, _, _, _, _, _, _, _ => ⟨fun _ => R, rfl, fun k hk => absurd hk (by simp)⟩
  | f :: fs, R, ex, ok, tail, tr, s, tr', hna, h, hs => by
    rw [runFields, List.append_assoc] at h
    obtain ⟨L, hL, -, h'⟩ := field_flag impl κ inp (hna f (List.mem_cons_self ..) _ _) h hs
    have hsz : (R ++ L.toArray).size = R.size + opsOut (f ⟨outs, zh, ex⟩ R.size).1 := by
      have hl := pureRun_len impl κ inp R _ [] L true hL
      simp [hl]
    rw [← hsz] at h'
    obtain ⟨Rs, h0, hrest⟩ := fields_chain outs zh fs (R ++ L.toArray) _ true tail tr s tr'
      (fun g hg => hna g (List.mem_cons_of_mem _ hg)) h' hs
    refine ⟨fun k => Nat.casesOn k R fun k => Rs k, rfl, fun k hk => ?_⟩
    rcases k with _ | k
    · refine ⟨L, hL, ?_⟩
      change Rs 0 = R ++ L.toArray
      exact h0
    · obtain ⟨Lk, hLk, hnext⟩ := hrest k (by simpa using hk)
      rw [hsz] at hLk
      exact ⟨Lk, hLk, hnext⟩

/-- The chained files extend one another. -/
theorem chain_ext {Rs : ℕ → Array Val} {N : ℕ} (h : ∀ k < N, ExtA (Rs k) (Rs (k + 1))) :
    ∀ {j k : ℕ}, j ≤ k → k ≤ N → ExtA (Rs j) (Rs k)
  | j, k, hjk, hkN => by
    induction k with
    | zero => rw [Nat.le_zero.1 hjk]; exact ⟨le_rfl, fun _ _ => rfl⟩
    | succ k ih =>
      rcases Nat.lt_or_ge j (k + 1) with hj | hj
      · exact (ih (by omega) (by omega)).trans (h k (by omega))
      · rw [show j = k + 1 by omega]; exact ⟨le_rfl, fun _ _ => rfl⟩

end Chain

theorem phaseIx_piop {name : String} (h : piopPhases.findIdx (·.name = name) < 26) :
    phaseIx name = piopPhases.findIdx (·.name = name) := by
  rw [phaseIx, phases, List.append_assoc, List.findIdx_append, if_pos (by rwa [piopPhases_length])]

theorem phaseIx_vals : phaseIx "Z1" = 3 ∧ phaseIx "Z2" = 4 ∧ phaseIx "Z3" = 5 ∧
    phaseIx "L1" = 7 ∧ phaseIx "L2" = 8 ∧ phaseIx "L3β" = 10 ∧ phaseIx "S1" = 11 ∧
    phaseIx "S2" = 12 ∧ phaseIx "Lr1" = 13 ∧ phaseIx "Lr2" = 14 ∧ phaseIx "Lr3" = 16 ∧
    phaseIx "E1" = 17 ∧ phaseIx "E2" = 18 ∧ phaseIx "E3" = 20 ∧ phaseIx "E4" = 21 ∧
    phaseIx "RS1" = 24 ∧ phaseIx "B'" = 25 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    rw [phaseIx_piop (by decide)] <;> decide

theorem opsOut_append (a b : List Op) : opsOut (a ++ b) = opsOut a + opsOut b := by
  simp [opsOut]

theorem opsOut_elemsOps (j : ℕ) (wop : ℕ → Op) (hw : ∀ i, (wop i).outs = 1) (R : Reg) :
    ∀ n i aA aT b, opsOut (elemsOps j wop R n i aA aT b) = n * elemW
  | 0, _, _, _, _ => rfl
  | n + 1, i, aA, aT, b => by
    rw [elemsOps, opsOut_append, opsOut_elemsOps j wop hw R n]
    simp only [elemOps, opsOut, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
    rw [hw]
    simp only [Op.outs, elemW]
    ring

theorem opsOut_claimOps (j : ℕ) (wop : ℕ → Op) (R b : ℕ) (hw : ∀ i, (wop i).outs = 1) :
    opsOut (claimOps j wop R b) = 1 + 128 * elemW := by
  rw [claimOps, show ∀ o os, opsOut (o :: os) = Op.outs o + opsOut os from fun _ _ => by
    simp [opsOut], opsOut_elemsOps j wop hw R]
  rfl

section Start

variable {impl : OpImpl} {κ : Kind} {inp : Input} {tr : Trace} {y : List Val × List Bool × Trace}

theorem K.smulF_one (c : F) : K.smulF c 1 = algebraMap F K c := by
  rw [K.algebraMap_eq_ofF]
  show (⟨c * 1, c * 0⟩ : K) = ⟨c, 0⟩
  rw [mul_one, mul_zero]

theorem val_eqv_k {a : K} {v : Val} (h : (Val.k a).eqv v = true) : v = .k a := by
  cases v <;> simp_all [Val.eqv]

end Start

end FR.Snd

end

/-! ## From `FRSoundnessFrRnd` (3 declarations) -/

section

namespace FR.Snd

open RecursionFast Finset FR.Impl

theorem roundF_spec (inp : Input) (f o deg : ℕ) (re : Bool) (a₁ a₂ : Digest) (c : Val) :
    (if deg = 3 then round3V inp f o re a₁ a₂ c else round2Vals inp f o re a₁ a₂ c).length =
        roundW deg ∧
      (if deg = 3 then round3V inp f o re a₁ a₂ c else round2Vals inp f o re a₁ a₂ c).getD 3
        default = .f (chF a₂ 0) := by
  by_cases h : deg = 3 <;> simp [h, round3V, round2Vals, roundW]

/-- **`roundsT_chalF`**: `n` F rounds leave `roundW deg` registers each; register `3` of round
`l` is its challenge `chF a₂ 0`. -/
theorem roundsT_chalF (inp : Input) (f o deg real : ℕ) :
    ∀ (n j : ℕ) (d : Digest) (cv : Val) (tr : Trace) (x : List Val × Bool × Trace),
      roundsT inp f o deg false real n j d cv tr = some x →
      x.1.length = roundW deg * n ∧
        ∀ l < n, x.1.getD (roundW deg * l + 3) default = .f (chF (sqAns tr l) 0)
  | 0, _, _, _, _, x, h => by
    simp only [roundsT, Option.some.injEq] at h; subst h
    exact ⟨rfl, fun l hl => absurd hl (by omega)⟩
  | n + 1, j, d, cv, (q₁, a₁) :: (q₂, a₂) :: tr, x, h => by
    simp only [roundsT, Bool.false_eq_true, ite_false] at h
    obtain ⟨hl, h3⟩ := roundF_spec inp f (o + j * roundBytes false) deg (decide (j < real)) a₁ a₂ cv
    have hw : 4 ≤ roundW deg := by unfold roundW; split <;> omega
    split_ifs at h hl h3 with hq hd
    all_goals
      obtain ⟨x', hx', rfl⟩ := Option.map_eq_some_iff.mp h
      obtain ⟨ih1, ih2⟩ := roundsT_chalF inp f o deg real n (j + 1) a₂ _ tr x' hx'
      refine ⟨by rw [List.length_append, hl, ih1]; ring, fun l hl' => ?_⟩
      rcases l with _ | l
      · rw [Nat.mul_zero, Nat.zero_add, List.getD_append _ _ _ _ (by omega), h3]; rfl
      · rw [show roundW deg * (l + 1) + 3 = roundW deg + (roundW deg * l + 3) by ring,
          List.getD_append_right _ _ _ _ (by omega), hl, Nat.add_sub_cancel_left,
          ih2 l (by omega), sqAns_succ]
  | _ + 1, _, _, _, [], _, h => by simp [roundsT] at h
  | _ + 1, _, _, _, [_], _, h => by simp [roundsT] at h

variable {impl : OpImpl} {κ : Kind} {inp : Input}

theorem initValsF_length (init : Init) (f o : ℕ) :
    (initVals inp init f o false).length = init.width := by
  cases init <;> rfl

end FR.Snd

end

/-! ## From `FRSoundnessFrRndV` (3 declarations) -/

section

namespace FR.Snd

open RecursionFast Finset FR.Impl

theorem charTwo_peval01F (a b c : F) : peval #[a, b, c] 0 + peval #[a, b, c] 1 = b + c := by
  rw [peval_three, peval_three]
  have h : a + a = 0 := CharTwo.add_self_eq_zero a
  ring_nf
  linear_combination h

theorem bytesAt_extract_of_le16 (π : Proof) {o len off : ℕ} (h : off + 16 ≤ len) :
    bytesAt (π.extract o (o + len)) off 16 = bytesAt π (o + off) 16 := by
  ext k hk
  rw [getElem_bytesAt _ _ _ _ hk, getElem_bytesAt _ _ _ _ hk, toList_extract,
    Nat.add_sub_cancel_left, List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
    List.getElem?_take_of_lt (by omega), List.getElem?_drop, Nat.add_assoc]

theorem eqv_f (a b : F) : (Val.f a).eqv (Val.f b) = true ↔ a = b := by simp [Val.eqv]

variable {impl : OpImpl} {κ : Kind} {inp : Input}

end FR.Snd

end

/-! ## From `FRSoundnessFrLc` (1 declaration) -/

section

namespace FR.Snd

open RecursionFast Finset FR.Impl

theorem phaseIx_L3 : phaseIx "L3" = 9 := by rw [phaseIx_piop (by decide)]; decide

end FR.Snd

end

/-! ## From `FRSoundnessExtStmt` (1 declaration) -/

section

namespace FR.Snd

open RecursionFast Finset

set_option linter.constructorNameAsVariable false

variable {impl : OpImpl} {κ : Kind} {inp : Input} {tr : Trace} {y : List Val × List Bool × Trace}

theorem bytesAt_extract_le (π : ByteArray) {o len off n : ℕ} (h : off + n ≤ len) :
    bytesAt (π.extract o (o + len)) off n = bytesAt π (o + off) n := by
  ext k hk
  rw [getElem_bytesAt _ _ _ _ hk, getElem_bytesAt _ _ _ _ hk, toList_extract,
    Nat.add_sub_cancel_left, List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
    List.getElem?_take_of_lt (by omega), List.getElem?_drop, Nat.add_assoc]

variable {vk c : Digest} {π : Proof} {es : Log}

end FR.Snd

end

/-! ## From `FRSoundnessExtLeaf` (6 declarations) -/

section

namespace FR.Snd

open RecursionFast Finset ProductCircuit Blake2sCircuit

set_option linter.constructorNameAsVariable false

theorem testBit_ofListLE : ∀ (l : List UInt8) (j : ℕ),
    (CompPoly.Bytes.ofListLE l).testBit j = ((l.getD (j / 8) 0).toNat).testBit (j % 8)
  | [], j => by simp [CompPoly.Bytes.ofListLE]
  | b :: l, j => by
    rw [CompPoly.Bytes.ofListLE_cons, Nat.add_comm, show (256 : ℕ) = 2 ^ 8 from rfl,
      Nat.testBit_two_pow_mul_add _ (by simpa using b.toNat_lt)]
    split_ifs with h
    · rw [Nat.div_eq_of_lt h, Nat.mod_eq_of_lt h]; rfl
    · rw [testBit_ofListLE l (j - 8)]
      obtain ⟨t, rfl⟩ : ∃ t, j = t + 8 := ⟨j - 8, by omega⟩
      rw [Nat.add_sub_cancel, show (t + 8) / 8 = t / 8 + 1 by omega, Nat.add_mod_right]
      rfl

theorem getLsbD_ofBytes (v : Vector UInt8 8) (j : ℕ) :
    (B64.ofBytes v).val.toBitVec.getLsbD j = ((v.toList.getD (j / 8) 0).toNat).testBit (j % 8) := by
  rw [BitVec.getLsbD, ← UInt64.toNat, B64.ofBytes_toNat, CompPoly.Bytes.ofVecLE, testBit_ofListLE]

/-- **Bit `j` of a decoded F element is bit `j mod 8` of byte `j / 8`.** -/
theorem bitF_ofBytes (v : Vector UInt8 16) (j : Fin 128) :
    FR.bitF (F.ofBytes v) j = ((v.toList.getD (j.val / 8) 0).toNat).testBit (j.val % 8) := by
  have hj := j.isLt
  unfold FR.bitF F.ofBytes
  split_ifs with h
  · rw [getLsbD_ofBytes]
    congr 2
    simp only [Vector.toList_ofFn, List.getD_eq_getElem?_getD, List.getElem?_ofFn,
      show j.val / 8 < 8 by omega, dite_true, Option.getD_some, Vector.getElem_toList,
      List.getElem?_eq_getElem (show j.val / 8 < v.toList.length by simp; omega)]
  · rw [getLsbD_ofBytes]
    rw [show (j.val - 64) % 8 = j.val % 8 by omega]
    congr 2
    simp only [Vector.toList_ofFn, List.getD_eq_getElem?_getD, List.getElem?_ofFn,
      show (j.val - 64) / 8 < 8 by omega, dite_true, Option.getD_some,
      List.getElem?_eq_getElem (show j.val / 8 < v.toList.length by simp; omega)]
    simp only [Vector.getElem_toList]
    congr 1; omega

theorem bytesAt_toList_getD (q : ByteArray) (o n k : ℕ) (hk : k < n) :
    (bytesAt q o n).toList.getD k 0 = q.data.toList.getD (o + k) 0 := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by simpa using hk), Option.getD_some,
    Vector.getElem_toList, getElem_bytesAt _ _ _ _ hk]

theorem digestBit_bytesAt (q : ByteArray) (o : ℕ) {σ : ℕ} (hσ : σ < 256) :
    Block.digestBit (bytesAt q o 32) σ = ((q.data.toList.getD (o + σ / 8) 0).toNat).testBit (σ % 8) := by
  simp only [Block.digestBit, hσ, dite_true]
  rw [getElem_bytesAt _ _ _ _ (by omega)]
  rfl

/-- **The boundary bits are the digest's bits**: `digBit` of the two 16-byte halves at `o` and
`o + 16` is `digestBit` of the 32 bytes at `o`. -/
theorem digBit_readF (q : ByteArray) (o : ℕ) {σ : ℕ} (hσ : σ < 256) :
    Impl.digBit (readF q o) (readF q (o + 16)) σ = Block.digestBit (bytesAt q o 32) σ := by
  rw [digestBit_bytesAt q o hσ, Impl.digBit]
  split_ifs with h
  · rw [readF, bitF_ofBytes, bytesAt_toList_getD _ _ _ _ (by omega)]
  · rw [readF, bitF_ofBytes, bytesAt_toList_getD _ _ _ _ (by simp only; omega)]
    simp only
    rw [show (σ - 128) % 128 % 8 = σ % 8 by omega,
      show o + 16 + (σ - 128) % 128 / 8 = o + σ / 8 by omega]

variable {impl : OpImpl} {vk c : Digest} {π : Proof} {tr : Trace}
  {y : List Val × List Bool × Trace}

end FR.Snd

end
