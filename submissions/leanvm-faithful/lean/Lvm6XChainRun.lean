-- lvm6 X3 (extractor): `chain6_spec`, the accepting replay's challenges are the scan's chain (FORMAT6 v2.5.2,
-- seed `a₀ ‖ HDR`). New: an induction over V1's walk (`Lvm6VSpec.PS`), item by item, against `msgsAux`.
import Lvm6XChainSpec

/-!
# The replay follows the chain

The replay `trun` of V1's program walks the schedule from the seed's answer. The invariant `RS` at chain
position `p`, π offset `o`, buffer of `b` bytes: the body is `π.drop o`, the buffer `π[o − b, o)`, the state is
`fmAns … p`, and the history's challenges are the chain's answers at positions `2 … p`. A draw then asks
`fsQ6 (p + 1)` exactly when the next message is `(o − b, b)`, which is what `msgsAux` lists.

* **`walkOK`**: the static facts the induction uses (caps committed in order with V1's cap widths, every opening
  with an empty buffer, as many positions as openings, the occupied words of `occL`); **`walkOK_P18`**.
* **`trun_*`**: one step of the replay; **`openAll_rest`**: an accepted opening consumes
  `|ps| · (lb + 32 · (ht − lv))` bytes.
* **`draw_step`**, **`lanes_step`**, **`draws_step`**, **`posRest_step`**, **`item_step`**, **`walk_run`**.
* **`chain6_spec_of`** (`walkOK` → `Chain6Spec`), **`chain6_spec : Chain6Spec P18`**.
-/

set_option autoImplicit false

namespace Lvm6.X

open RecursionFast Lvm Lvm.X Lvm.FS
open LeanVM.Protocol.Compile (Ev VerifierProgram)

/-! ## The static facts -/

/-- **The walk's static facts**, the items from `nc` committed caps, `pl` positions held, a buffer of `b` bytes:
`cap i` is the `nc`-th cap and its width is V1's (`capOfL`), `open i` has an empty buffer, `t` positions and
V1's occupied words (`occL`). -/
def walkOK (L : List V.Lev) : List V.Item → ℕ → ℕ → ℕ → Bool
  | [], _, _, _ => true
  | .E k :: r, nc, pl, b => walkOK L r nc pl (b + 16 * k)
  | .K k :: r, nc, pl, b => walkOK L r nc pl (b + 8 * k)
  | .cap i :: r, nc, pl, b =>
    i == nc && V.capOfL L (L.getD i default).ht (L.getD i default).wd == (L.getD i default).lv &&
      walkOK L r (nc + 1) pl (b + 32 * 2 ^ (L.getD i default).lv)
  | .G _ :: r, nc, pl, _ => walkOK L r nc pl 0
  | .D 0 :: r, nc, pl, b => walkOK L r nc pl b
  | .D (_ + 1) :: r, nc, pl, _ => walkOK L r nc pl 0
  | .B :: r, nc, pl, _ => walkOK L r nc pl 0
  | .pos i _ :: r, nc, _, _ => walkOK L r nc (L.getD i default).cnts.sum 0
  | .open i :: r, nc, pl, b =>
    b == 0 && pl == (L.getD i default).t &&
      V.occL L (L.getD i default).ht (L.getD i default).wd == (L.getD i default).oc && walkOK L r nc pl b

theorem walkOK_P18 : walkOK P18.levs (sched6 P18) 0 0 0 = true := by decide +kernel

/-! ## One step of the replay -/

section Trun

variable (S : Scheme) (L : Log)

theorem trun_ret {b : Bool} {st : Digest} {buf : List UInt8} {caps : List CapI} {body : List UInt8}
    {h H : List Ev} (hT : S.trun L (.ret b) st buf caps body h = some (true, H)) : H = h := by
  simp only [Scheme.trun, Option.some.injEq, Prod.mk.injEq] at hT
  exact hT.2.symm

theorem trun_fail {st : Digest} {buf : List UInt8} {caps : List CapI} {body : List UInt8} {h H : List Ev}
    (hT : S.trun L .fail st buf caps body h = some (true, H)) : False := by
  simp [Scheme.trun] at hT

theorem trun_read {k : _} {st : Digest} {buf : List UInt8}
    {caps : List CapI} {body : List UInt8} {h H : List Ev}
    (hT : S.trun L (.read k) st buf caps body h = some (true, H)) :
    S.trun L (k (S.decE (body.take (S.rw (nReads h))))) st (buf ++ body.take (S.rw (nReads h))) caps
      (body.drop (S.rw (nReads h))) (h ++ [.read (S.decE (body.take (S.rw (nReads h))))]) = some (true, H) := by
  rw [Scheme.trun] at hT
  split_ifs at hT with h1
  · simp at hT
  · exact hT

theorem trun_sample {k : _} {st : Digest} {buf : List UInt8}
    {caps : List CapI} {body : List UInt8} {h H : List Ev}
    (hT : S.trun L (.sample k) st buf caps body h = some (true, H)) :
    ∃ e, L.find? (fun e => e.1 = toQ (st.toList ++ buf)) = some e ∧
      S.trun L (k (S.chal e.2)) e.2 [] caps body (h ++ [.sample (S.chal e.2)]) = some (true, H) := by
  rw [Scheme.trun] at hT
  split_ifs at hT with h1
  · cases hf : L.find? (fun e => e.1 = toQ (st.toList ++ buf)) with
    | none => rw [hf] at hT; simp at hT
    | some e => rw [hf, Option.bind_some] at hT; exact ⟨e, rfl, hT⟩
  · simp at hT

theorem trun_commit {ht w : ℕ} {k : VerifierProgram Bool} {st : Digest} {buf : List UInt8}
    {caps : List CapI} {body : List UInt8} {h H : List Ev}
    (hT : S.trun L (.commit ht w k) st buf caps body h = some (true, H)) :
    S.trun L k st (buf ++ body.take (S.capBytes ht w)) (caps ++ [S.capI ht w body])
      (body.drop (S.capBytes ht w)) (h ++ [.commit ht w (S.wordOf L (S.capI ht w body))]) = some (true, H) := by
  rw [Scheme.trun] at hT
  split_ifs at hT with h1
  · simp at hT
  · exact hT

theorem trun_query {i : ℕ} {ps : List ℕ} {k : _}
    {st : Digest} {buf : List UInt8} {caps : List CapI} {body : List UInt8} {h H : List Ev}
    (hT : S.trun L (.query i ps k) st buf caps body h = some (true, H)) :
    ∃ ci rows rest, caps[i]? = some ci ∧ (S.openAll ci ps body).runLog L = some (some (rows, rest)) ∧
      S.trun L (k rows) st buf caps rest (h ++ [.query rows]) = some (true, H) := by
  rw [Scheme.trun] at hT
  cases hc : caps[i]? with
  | none => rw [hc] at hT; simp at hT
  | some ci =>
    rw [hc] at hT
    cases ho : (S.openAll ci ps body).runLog L with
    | none => simp only [ho, Option.bind_none, reduceCtorEq] at hT
    | some r =>
      rcases r with _ | ⟨rows, rest⟩
      · simp only [ho, Option.bind_some, Option.some.injEq, Prod.mk.injEq, Bool.false_eq_true,
          false_and] at hT
      · simp only [ho, Option.bind_some] at hT
        exact ⟨ci, rows, rest, rfl, ho, hT⟩

/-- A climb consumes `32` bytes a level. -/
theorem climb_rest : ∀ (n : ℕ) (d : Digest) (q : ℕ) (body : List UInt8) (top : Digest) (rest : List UInt8),
    (Scheme.climb n d q body).runLog L = some (some (top, rest)) → rest = body.drop (32 * n) := by
  intro n
  induction n with
  | zero =>
    intro d q body top rest h
    simp only [Scheme.climb, OProg.runLog, Option.some.injEq, Prod.mk.injEq] at h
    simp [← h.2]
  | succ n ih =>
    intro d q body top rest h
    rw [Scheme.climb] at h
    by_cases hl : body.length < 32
    · rw [if_pos hl] at h; simp [OProg.runLog] at h
    · rw [if_neg hl, OProg.runLog] at h
      cases hf : L.find? (fun e => decide (e.1 = toQ (if q % 2 = 0 then d.toList ++ body.take 32
          else body.take 32 ++ d.toList))) with
      | none => rw [hf] at h; simp at h
      | some e =>
        rw [hf, Option.bind_some] at h
        rw [ih _ _ _ _ _ h, List.drop_drop]
        congr 1
        ring

/-- An accepted opening of one position consumes the leaf and the path. -/
theorem openOne_rest (ci : CapI) (p : ℕ) (body rest : List UInt8) (row : List LeanVM.Parameters.K)
    (h : (S.openOne ci p body).runLog L = some (some (row, rest))) :
    rest = body.drop (S.lb ci + 32 * (ci.ht - ci.lv)) := by
  rw [Scheme.openOne] at h
  by_cases hl : body.length < S.lb ci
  · rw [if_pos hl] at h; simp [OProg.runLog] at h
  · rw [if_neg hl, OProg.runLog] at h
    cases hf : L.find? (fun e => decide (e.1 = toQ (body.take (S.lb ci)))) with
    | none => rw [hf] at h; simp at h
    | some e =>
      rw [hf, Option.bind_some, OProgFacts.runLog_bind] at h
      cases hcl : (Scheme.climb (ci.ht - ci.lv) e.2 (p % 2 ^ ci.ht) (body.drop (S.lb ci))).runLog L with
      | none => rw [hcl] at h; simp at h
      | some r =>
        rw [hcl, Option.bind_some] at h
        rcases r with _ | ⟨top, rest'⟩
        · simp [OProg.runLog] at h
        · simp only [OProg.runLog] at h
          have hr := climb_rest L _ _ _ _ _ _ hcl
          by_cases hcap : ci.cap[p % 2 ^ ci.ht / 2 ^ (ci.ht - ci.lv)]? = some top
          · rw [if_pos hcap] at h
            simp only [Option.some.injEq, Prod.mk.injEq] at h
            rw [← h.2, hr, List.drop_drop]
          · rw [if_neg hcap] at h
            simp at h

/-- **An accepted opening consumes `|ps| · (lb + 32 · (ht − lv))` bytes.** -/
theorem openAll_rest (ci : CapI) : ∀ (ps : List ℕ) (body rest : List UInt8) (rows : List (List LeanVM.Parameters.K)),
    (S.openAll ci ps body).runLog L = some (some (rows, rest)) →
    rest = body.drop (ps.length * (S.lb ci + 32 * (ci.ht - ci.lv))) := by
  intro ps
  induction ps with
  | nil =>
    intro body rest rows h
    simp only [Scheme.openAll, OProg.runLog, Option.some.injEq, Prod.mk.injEq] at h
    simp [← h.2]
  | cons p ps ih =>
    intro body rest rows h
    simp only [Scheme.openAll] at h
    rw [OProgFacts.runLog_bind] at h
    cases h1 : (S.openOne ci p body).runLog L with
    | none => simp [h1] at h
    | some r =>
      rw [h1, Option.bind_some] at h
      rcases r with _ | ⟨row, rest₁⟩
      · simp [OProg.runLog] at h
      · simp only at h
        rw [OProgFacts.runLog_bind] at h
        cases h2 : (S.openAll ci ps rest₁).runLog L with
        | none => simp [h2] at h
        | some r' =>
          rw [h2, Option.bind_some] at h
          rcases r' with _ | ⟨rs, rest₂⟩
          · simp [OProg.runLog] at h
          · simp only [OProg.runLog, Option.some.injEq, Prod.mk.injEq] at h
            rw [← h.2, ih rest₁ rest₂ rs h2, openOne_rest S L ci p body rest₁ row h1, List.drop_drop,
              List.length_cons]
            congr 1
            ring

end Trun

/-! ## The specification's steps, unfolded -/

section PSeq

variable {L : List V.Lev} {ps : List ℕ} {acc : List V.Val} {K : V.Kt}

theorem ps_rd (w : ℕ) : V.PS.rd w ps acc K = .read fun x => K ps (.e x :: acc) := rfl

theorem ps_draw (chk : ℕ → Bool) (upd : List ℕ → ℕ → List ℕ) :
    V.PS.draw chk upd ps acc K = .sample fun c =>
      if chk (LeanVM.Protocol.Verifier.eToNat c) then K (upd ps (LeanVM.Protocol.Verifier.eToNat c)) (.c c :: acc)
      else .fail := rfl

theorem ps_rep_succ (f : V.St) (m : ℕ) :
    V.PS.rep f (m + 1) ps acc K = f ps acc (fun ps' acc' => V.PS.rep f m ps' acc' K) := rfl

theorem ps_posRest_cons (ht c : ℕ) (cs : List ℕ) :
    V.PS.posRest ht (c :: cs) ps acc K =
      V.PS.draw V.tt (V.addPs ht c) ps acc (fun ps' acc' => V.PS.posRest ht cs ps' acc' K) := rfl

theorem ps_walk_nil : V.PS.walk L [] ps acc K = K ps acc := rfl

theorem ps_walk_cons (it : V.Item) (r : List V.Item) :
    V.PS.walk L (it :: r) ps acc K = V.PS.item L it ps acc (fun ps' acc' => V.PS.walk L r ps' acc' K) := rfl

theorem ps_item_E (k : ℕ) : V.PS.item L (.E k) = V.PS.rep (V.PS.rd 16) k := rfl

theorem ps_item_K (k : ℕ) : V.PS.item L (.K k) = V.PS.rep (V.PS.rd 8) k := rfl

theorem ps_item_cap (i : ℕ) :
    V.PS.item L (.cap i) ps acc K =
      .commit (L.getD i default).ht (L.getD i default).wd (K ps (.cap (L.getD i default).ht (L.getD i default).wd :: acc)) :=
    rfl

theorem ps_item_G (g : ℕ) :
    V.PS.item L (.G g) ps acc K = V.PS.rd 8 ps acc (fun ps' acc' => V.PS.draw (V.pw g) V.keepPs ps' acc' K) := rfl

theorem ps_item_D (k : ℕ) : V.PS.item L (.D k) = V.PS.rep (V.PS.draw V.tt V.keepPs) k := rfl

theorem ps_item_B : V.PS.item L .B = V.PS.draw V.tt V.keepPs := rfl

theorem ps_item_pos (i g : ℕ) :
    V.PS.item L (.pos i g) ps acc K = V.PS.rd 8 [] acc (fun ps' acc' =>
      V.PS.draw (V.pw g) (V.addPs (L.getD i default).ht ((L.getD i default).cnts.headD 0)) ps' acc'
        (fun ps'' acc'' => V.PS.posRest (L.getD i default).ht (L.getD i default).cnts.tail ps'' acc'' K)) := rfl

theorem ps_item_open (i : ℕ) :
    V.PS.item L (.open i) ps acc K = .query i ps (fun rows => K ps (.rows i ps rows :: acc)) := rfl

end PSeq

/-! ## Read widths (V1 `ce6ea3e0`: `rd w`, `rw = rwOf sched`) -/

theorem nReads_read (h : List Ev) (x : _) : nReads (h ++ [.read x]) = nReads h + 1 := by
  simp [nReads, List.countP_append]

theorem nReads_sample (h : List Ev) (c : _) : nReads (h ++ [.sample c]) = nReads h := by
  simp [nReads, List.countP_append]

theorem nReads_commit (h : List Ev) (ht w : ℕ) (W : _) : nReads (h ++ [.commit ht w W]) = nReads h := by
  simp [nReads, List.countP_append]

theorem nReads_query (h : List Ev) (rows : _) : nReads (h ++ [.query rows]) = nReads h := by
  simp [nReads, List.countP_append]

/-- **The widths of the reads still to come** are `ws`: the scheme's width of read `nReads h + j` is `ws[j]`. -/
def RdW (S : Scheme) (h : List Ev) (ws : List ℕ) : Prop := ∀ j, S.rw (nReads h + j) = ws.getD j 8

theorem RdW.head {S : Scheme} {h : List Ev} {w : ℕ} {ws : List ℕ} (hW : RdW S h (w :: ws)) :
    S.rw (nReads h) = w := by simpa using hW 0

theorem RdW.read {S : Scheme} {h : List Ev} {w : ℕ} {ws : List ℕ} (hW : RdW S h (w :: ws)) (x : _) :
    RdW S (h ++ [.read x]) ws := fun j => by
  have e := hW (j + 1)
  rw [nReads_read, show nReads h + 1 + j = nReads h + (j + 1) by omega, e]; simp

theorem RdW.congr {S : Scheme} {h h' : List Ev} {ws : List ℕ} (hW : RdW S h ws) (he : nReads h' = nReads h) :
    RdW S h' ws := fun j => by rw [he]; exact hW j

theorem flatten_replicate_single (k a : ℕ) : (List.replicate k [a]).flatten = List.replicate k a := by
  induction k with
  | zero => rfl
  | succ k ih => rw [List.replicate_succ, List.flatten_cons, ih]; rfl

/-! ## The invariant -/

theorem samples_read (h : List Ev) (x : _) : samples (h ++ [.read x]) = samples h := by
  simp [samples]

theorem samples_commit (h : List Ev) (ht w : ℕ) (W : _) :
    samples (h ++ [.commit ht w W]) = samples h := by
  simp [samples]

theorem samples_query (h : List Ev) (rows : _) :
    samples (h ++ [.query rows]) = samples h := by
  simp [samples]

theorem samples_sample (h : List Ev) (c : _) :
    samples (h ++ [.sample c]) = samples h ++ [c] := by
  simp [samples]

section Inv

variable (sh : Shape) (π : Proof) (L : Log)

/-- **The replay's invariant** at chain position `p`, π offset `o`, a buffer of `b` bytes. -/
structure RS (p o b : ℕ) (st : Digest) (buf body : List UInt8) (h : List Ev) : Prop where
  body : body = π.data.toList.drop o
  buf : buf = (π.data.toList.drop (o - b)).take b
  bo : b ≤ o
  fm : fmAns (fsQ6 sh π) zeroDL L p = some st
  len : (samples h).length + 1 = p
  hist : ∀ j (hj : j < (samples h).length),
    ∃ a, fmAns (fsQ6 sh π) zeroDL L (j + 2) = some a ∧ (samples h)[j] = Lvm.FS.chalOf a

/-- The caps committed so far have their levels' shapes. -/
def CapsOK (Lv : List V.Lev) (caps : List CapI) : Prop :=
  ∀ k (hk : k < caps.length), caps[k].ht = (Lv.getD k default).ht ∧ caps[k].wd = (Lv.getD k default).wd ∧
    caps[k].lv = (Lv.getD k default).lv

variable {sh π L}

/-- Absorbing `n` body bytes. -/
theorem RS.absorb {p o b : ℕ} {st : Digest} {buf body : List UInt8} {h : List Ev}
    (hR : RS sh π L p o b st buf body h) (n : ℕ) (h' : List Ev) (hs : samples h' = samples h) :
    RS sh π L p (o + n) (b + n) st (buf ++ body.take n) (body.drop n) h' := by
  obtain ⟨e1, e2, e3, e4, e5, e6⟩ := hR
  refine ⟨by rw [e1, List.drop_drop], ?_, by omega, e4, by rw [hs]; exact e5, by rw [hs]; exact e6⟩
  rw [e2, e1, show o + n - (b + n) = o - b by omega, List.take_add, List.drop_drop,
    show o - b + b = o by omega]

theorem msgs_cons {p : ℕ} {m : ℕ × ℕ} {M : List (ℕ × ℕ)} (hm : (msgs6 sh).drop p = m :: M) :
    msg6 sh (p + 1) = m ∧ (msgs6 sh).drop (p + 1) = M := by
  constructor
  · have h0 := congrArg (fun l => l[0]?) hm
    simp only [List.getElem?_drop, Nat.add_zero, List.getElem?_cons_zero] at h0
    rw [msg6, show p + 1 - 1 = p by omega, List.getD_eq_getElem?_getD, h0] <;> rfl
  · rw [← List.drop_drop, hm] <;> rfl

theorem fsQ6_msg {p u n : ℕ} (hm : msg6 sh (p + 1) = (u, n)) (a : Digest) :
    fsQ6 sh π (p + 1) a = toQ (a.toList ++ (π.data.toList.drop u).take n) := by
  rw [fsQ6, if_neg (by omega), hm]
  apply ByteArray.ext
  simp only [ByteArray.data_append, ByteArray.data_extract, toQ, digestBytes]
  apply Array.ext'
  simp [Array.toList_append, Array.toList_extract, List.extract_eq_take_drop] <;> rfl

/-- The specified scheme at a shape. -/
abbrev S6 (sh : Shape) (vk : Digest) (dec : List UInt8 → List V.Val → Bool) : Scheme :=
  V.scheme6V (toV sh) vk dec

variable {vk : Digest} {dec : List UInt8 → List V.Val → Bool}

/-- **A draw** at a buffer `π[o − b, o)`: it asks `fsQ6 (p + 1)`, the chain's next query. -/
theorem draw_step {p o b : ℕ} {st : Digest} {buf body : List UInt8} {h H : List Ev} {caps : List CapI}
    {chk : ℕ → Bool} {upd : List ℕ → ℕ → List ℕ} {ps : List ℕ} {acc : List V.Val} {K : V.Kt}
    {M : List (ℕ × ℕ)} (hR : RS sh π L p o b st buf body h) (hm : (msgs6 sh).drop p = (o - b, b) :: M)
    (hT : (S6 sh vk dec).trun L (V.PS.draw chk upd ps acc K) st buf caps body h = some (true, H)) :
    ∃ st' h' acc' N, RS sh π L (p + 1) o 0 st' [] body h' ∧ nReads h' = nReads h ∧ (msgs6 sh).drop (p + 1) = M ∧
      (S6 sh vk dec).trun L (K (upd ps N) acc') st' [] caps body h' = some (true, H) := by
  obtain ⟨hm1, hm2⟩ := msgs_cons hm
  rw [ps_draw] at hT
  obtain ⟨e, hf, hT'⟩ := trun_sample _ _ hT
  have hfm : fmAns (fsQ6 sh π) zeroDL L (p + 1) = some e.2 := by
    simp only [fmAns, hR.fm, Option.bind_some]
    rw [fsQ6_msg hm1, ← hR.buf, hf] <;> rfl
  by_cases hc : chk (LeanVM.Protocol.Verifier.eToNat ((S6 sh vk dec).chal e.2)) = true
  · simp only [hc, ↓reduceIte] at hT'
    refine ⟨e.2, _, _, _, ⟨hR.body, by simp, Nat.zero_le _, hfm, ?_, ?_⟩, nReads_sample _ _, hm2, hT'⟩
    · rw [samples_sample, List.length_append, List.length_singleton, hR.len]
    · intro j hj
      rw [samples_sample, List.length_append, List.length_singleton] at hj
      by_cases hjl : j < (samples h).length
      · obtain ⟨a, ha1, ha2⟩ := hR.hist j hjl
        refine ⟨a, ha1, ?_⟩
        simp only [samples_sample, List.getElem_append_left hjl, ha2]
      · have hj' : j = (samples h).length := by omega
        subst hj'
        refine ⟨e.2, by rw [show (samples h).length + 2 = p + 1 by have := hR.len; omega]; exact hfm, ?_⟩
        simp [samples_sample]
        rfl
  · simp only [hc, ↓reduceIte] at hT'
    exact (trun_fail _ _ hT').elim

/-- **`m` reads of `w` bytes**: `w·m` bytes absorbed. -/
theorem rds_step {p : ℕ} {caps : List CapI} {ps : List ℕ} {K : V.Kt} {H : List Ev} (w : ℕ) {ws : List ℕ} :
    ∀ (m : ℕ) {o b : ℕ} {st : Digest} {buf body : List UInt8} {h : List Ev} {acc : List V.Val},
    RS sh π L p o b st buf body h → RdW (S6 sh vk dec) h (List.replicate m w ++ ws) →
    (S6 sh vk dec).trun L (V.PS.rep (V.PS.rd w) m ps acc K) st buf caps body h = some (true, H) →
    ∃ acc' buf' body' h', RS sh π L p (o + w * m) (b + w * m) st buf' body' h' ∧ RdW (S6 sh vk dec) h' ws ∧
      (S6 sh vk dec).trun L (K ps acc') st buf' caps body' h' = some (true, H)
  | 0, o, b, st, buf, body, h, acc, hR, hW, hT => ⟨acc, buf, body, h, hR, hW, hT⟩
  | m + 1, o, b, st, buf, body, h, acc, hR, hW, hT => by
    rw [ps_rep_succ, ps_rd] at hT
    have hT' := trun_read _ _ hT
    rw [List.replicate_succ, List.cons_append] at hW
    rw [hW.head] at hT'
    have hR' := hR.absorb w (h ++ [Ev.read ((S6 sh vk dec).decE (body.take w))]) (samples_read _ _)
    obtain ⟨acc', buf', body', h', hR'', hW'', hT''⟩ := rds_step w m hR' (hW.read _) hT'
    refine ⟨acc', buf', body', h', ?_, hW'', hT''⟩
    rw [show o + w * (m + 1) = o + w + w * m by ring, show b + w * (m + 1) = b + w + w * m by ring]
    exact hR''

/-- **`k` draws** on an empty buffer. -/
theorem draws_step {o : ℕ} {body : List UInt8} {caps : List CapI} {ps : List ℕ} {K : V.Kt} {H : List Ev}
    {M : List (ℕ × ℕ)} :
    ∀ (k : ℕ) {p : ℕ} {st : Digest} {h : List Ev} {acc : List V.Val},
    RS sh π L p o 0 st [] body h → (msgs6 sh).drop p = List.replicate k (o, 0) ++ M →
    (S6 sh vk dec).trun L (V.PS.rep (V.PS.draw V.tt V.keepPs) k ps acc K) st [] caps body h = some (true, H) →
    ∃ st' h' acc', RS sh π L (p + k) o 0 st' [] body h' ∧ nReads h' = nReads h ∧ (msgs6 sh).drop (p + k) = M ∧
      (S6 sh vk dec).trun L (K ps acc') st' [] caps body h' = some (true, H)
  | 0, p, st, h, acc, hR, hm, hT => ⟨st, h, acc, hR, rfl, hm, hT⟩
  | k + 1, p, st, h, acc, hR, hm, hT => by
    rw [ps_rep_succ] at hT
    obtain ⟨st', h', acc', N, hR', hn', hm', hT'⟩ :=
      draw_step (M := List.replicate k (o, 0) ++ M) hR (by rw [hm, Nat.sub_zero] <;> rfl) hT
    obtain ⟨st'', h'', acc'', hR'', hn'', hm'', hT''⟩ := draws_step k hR' hm' hT'
    refine ⟨st'', h'', acc'', ?_, hn''.trans hn', ?_, hT''⟩
    · rw [show p + (k + 1) = p + 1 + k by ring]; exact hR''
    · rw [show p + (k + 1) = p + 1 + k by ring]; exact hm''

theorem length_posList (ht cnt N : ℕ) : (V.posList ht cnt N).length = cnt := by
  simp [V.posList]

/-- **A level's further draws**: one per count, each adding its positions. -/
theorem posRest_step {o : ℕ} {body : List UInt8} {caps : List CapI} {K : V.Kt} {H : List Ev}
    {M : List (ℕ × ℕ)} (ht : ℕ) :
    ∀ (cs : List ℕ) {p : ℕ} {st : Digest} {h : List Ev} {ps : List ℕ} {acc : List V.Val},
    RS sh π L p o 0 st [] body h → (msgs6 sh).drop p = List.replicate cs.length (o, 0) ++ M →
    (S6 sh vk dec).trun L (V.PS.posRest ht cs ps acc K) st [] caps body h = some (true, H) →
    ∃ st' h' ps' acc', RS sh π L (p + cs.length) o 0 st' [] body h' ∧ nReads h' = nReads h ∧
      (msgs6 sh).drop (p + cs.length) = M ∧
      ps'.length = ps.length + cs.sum ∧ (S6 sh vk dec).trun L (K ps' acc') st' [] caps body h' = some (true, H)
  | [], p, st, h, ps, acc, hR, hm, hT => ⟨st, h, ps, acc, hR, rfl, hm, by simp, hT⟩
  | c :: cs, p, st, h, ps, acc, hR, hm, hT => by
    rw [ps_posRest_cons] at hT
    obtain ⟨st', h', acc', N, hR', hn', hm', hT'⟩ :=
      draw_step (M := List.replicate cs.length (o, 0) ++ M) hR (by rw [hm, Nat.sub_zero] <;> rfl) hT
    obtain ⟨st'', h'', ps'', acc'', hR'', hn'', hm'', hl'', hT''⟩ := posRest_step ht cs hR' hm' hT'
    refine ⟨st'', h'', ps'', acc'', ?_, hn''.trans hn', ?_, ?_, hT''⟩
    · rw [List.length_cons, show p + (cs.length + 1) = p + 1 + cs.length by ring]; exact hR''
    · rw [List.length_cons, show p + (cs.length + 1) = p + 1 + cs.length by ring]; exact hm''
    · simp only [hl'', V.addPs, List.length_append, length_posList, List.sum_cons] <;> omega

theorem headD_add_sum_tail (l : List ℕ) : l.headD 0 + l.tail.sum = l.sum := by
  cases l <;> simp

theorem length_cnts (l : V.Lev) : l.cnts.length = l.draws := by
  simp [V.Lev.cnts]

/-- **One item** of the schedule. -/
theorem item_step (it : V.Item) (r : List V.Item) {p o b : ℕ} {st : Digest} {buf body : List UInt8}
    {h H : List Ev} {caps : List CapI} {ps : List ℕ} {acc : List V.Val} {K : V.Kt}
    (hR : RS sh π L p o b st buf body h) (hC : CapsOK sh.levs caps)
    (hok : walkOK sh.levs (it :: r) caps.length ps.length b = true)
    (hm : (msgs6 sh).drop p = msgsAux sh.levs (it :: r) o b) (hW : RdW (S6 sh vk dec) h (V.widths (it :: r)))
    (hT : (S6 sh vk dec).trun L (V.PS.item sh.levs it ps acc K) st buf caps body h = some (true, H)) :
    ∃ p' o' b' st' buf' body' h' caps' ps' acc', RS sh π L p' o' b' st' buf' body' h' ∧
      RdW (S6 sh vk dec) h' (V.widths r) ∧
      CapsOK sh.levs caps' ∧ walkOK sh.levs r caps'.length ps'.length b' = true ∧
      (msgs6 sh).drop p' = msgsAux sh.levs r o' b' ∧
      (S6 sh vk dec).trun L (K ps' acc') st' buf' caps' body' h' = some (true, H) := by
  cases it with
  | E k =>
    rw [ps_item_E] at hT
    rw [V.widths, V.widthsI, flatten_replicate_single] at hW
    obtain ⟨acc', buf', body', h', hR', hW', hT'⟩ := rds_step 16 k hR hW hT
    exact ⟨p, _, _, st, buf', body', h', caps, ps, acc', hR', hW', hC, hok, hm, hT'⟩
  | K k =>
    rw [ps_item_K] at hT
    rw [V.widths, V.widthsI, flatten_replicate_single] at hW
    obtain ⟨acc', buf', body', h', hR', hW', hT'⟩ := rds_step 8 k hR hW hT
    exact ⟨p, _, _, st, buf', body', h', caps, ps, acc', hR', hW', hC, hok, hm, hT'⟩
  | cap i =>
    simp only [walkOK, Bool.and_eq_true, beq_iff_eq] at hok
    obtain ⟨⟨hi, hlv⟩, hok⟩ := hok
    rw [ps_item_cap] at hT
    have hT' := trun_commit _ _ hT
    have hcb : (S6 sh vk dec).capBytes (sh.levs.getD i default).ht (sh.levs.getD i default).wd =
        32 * 2 ^ (sh.levs.getD i default).lv := by
      show 32 * 2 ^ V.capOfL sh.levs _ _ = _
      rw [hlv]
    rw [hcb] at hT'
    have hR' := hR.absorb (32 * 2 ^ (sh.levs.getD i default).lv)
      (h ++ [Ev.commit (sh.levs.getD i default).ht (sh.levs.getD i default).wd
        ((S6 sh vk dec).wordOf L ((S6 sh vk dec).capI (sh.levs.getD i default).ht (sh.levs.getD i default).wd body))])
      (samples_commit _ _ _ _)
    refine ⟨p, _, _, st, _, _, _, _, ps, _, hR', hW.congr (nReads_commit _ _ _ _), fun k hk => ?_,
      by rw [List.length_append, List.length_singleton]; exact hok, hm, hT'⟩
    rw [List.length_append, List.length_singleton] at hk
    rcases Nat.lt_succ_iff_lt_or_eq.mp hk with hk | hk
    · rw [List.getElem_append_left hk]; exact hC k hk
    · subst hk
      simp only [List.getElem_concat_length]
      rw [← hi]
      exact ⟨rfl, rfl, hlv⟩
  | G g =>
    rw [ps_item_G, ps_rd] at hT
    have hT' := trun_read _ _ hT
    have hW8 : RdW (S6 sh vk dec) h (8 :: V.widths r) := hW
    rw [hW8.head] at hT'
    have hR' := hR.absorb 8 (h ++ [Ev.read ((S6 sh vk dec).decE (body.take 8))]) (samples_read _ _)
    obtain ⟨st', h', acc', N, hR'', hn'', hm'', hT''⟩ :=
      draw_step (M := msgsAux sh.levs r (o + 8) 0) hR'
        (by rw [hm, show o + 8 - (b + 8) = o - b by omega] <;> rfl) hT'
    exact ⟨_, _, _, st', _, _, h', caps, ps, acc', hR'', (hW8.read _).congr hn'', hC, hok, hm'', hT''⟩
  | D k =>
    cases k with
    | zero => exact ⟨p, o, b, st, buf, body, h, caps, ps, acc, hR, hW, hC, hok, hm, hT⟩
    | succ k =>
      rw [ps_item_D, ps_rep_succ] at hT
      obtain ⟨st', h', acc', N, hR', hn', hm', hT'⟩ :=
        draw_step (M := List.replicate k (o, 0) ++ msgsAux sh.levs r o 0) hR (by rw [hm] <;> rfl) hT
      obtain ⟨st'', h'', acc'', hR'', hn'', hm'', hT''⟩ := draws_step k hR' hm' hT'
      exact ⟨_, _, _, st'', _, _, h'', caps, ps, acc'', hR'', hW.congr (hn''.trans hn'), hC, hok, hm'', hT''⟩
  | B =>
    rw [ps_item_B] at hT
    obtain ⟨st', h', acc', N, hR', hn', hm', hT'⟩ :=
      draw_step (M := msgsAux sh.levs r o 0) hR (by rw [hm] <;> rfl) hT
    exact ⟨_, _, _, st', _, _, h', caps, ps, acc', hR', hW.congr hn', hC, hok, hm', hT'⟩
  | pos i g =>
    rw [ps_item_pos, ps_rd] at hT
    have hT' := trun_read _ _ hT
    have hW8 : RdW (S6 sh vk dec) h (8 :: V.widths r) := hW
    rw [hW8.head] at hT'
    have hR' := hR.absorb 8 (h ++ [Ev.read ((S6 sh vk dec).decE (body.take 8))]) (samples_read _ _)
    obtain ⟨st', h', acc', N, hR'', hn'', hm'', hT''⟩ :=
      draw_step (M := List.replicate ((sh.levs.getD i default).draws - 1) (o + 8, 0) ++
        msgsAux sh.levs r (o + 8) 0) hR' (by rw [hm, show o + 8 - (b + 8) = o - b by omega] <;> rfl) hT'
    have hcl : (sh.levs.getD i default).cnts.tail.length = (sh.levs.getD i default).draws - 1 := by
      rw [List.length_tail, length_cnts]
    rw [← hcl] at hm''
    obtain ⟨st₃, h₃, ps₃, acc₃, hR₃, hn₃, hm₃, hl₃, hT₃⟩ :=
      posRest_step (sh.levs.getD i default).ht (sh.levs.getD i default).cnts.tail hR'' hm'' hT''
    refine ⟨_, _, _, st₃, _, _, h₃, caps, ps₃, acc₃, hR₃, (hW8.read _).congr (hn₃.trans hn''), hC, ?_, hm₃, hT₃⟩
    have hl : ps₃.length = (sh.levs.getD i default).cnts.sum := by
      simp only [hl₃, V.addPs, List.length_append, length_posList, List.length_nil, Nat.zero_add,
        headD_add_sum_tail]
    rw [hl]
    exact hok
  | «open» i =>
    simp only [walkOK, Bool.and_eq_true, beq_iff_eq] at hok
    obtain ⟨⟨⟨hb, hpl⟩, hoc⟩, hok⟩ := hok
    subst hb
    rw [ps_item_open] at hT
    obtain ⟨ci, rows, rest, hci, ho, hT'⟩ := trun_query _ _ hT
    have hrest := openAll_rest _ _ ci ps body rest rows ho
    obtain ⟨hi, hci'⟩ := List.getElem?_eq_some_iff.mp hci
    obtain ⟨c1, c2, c3⟩ := hC i hi
    rw [hci'] at c1 c2 c3
    have hlb : (S6 sh vk dec).lb ci + 32 * (ci.ht - ci.lv) =
        (sh.levs.getD i default).lb + 32 * (sh.levs.getD i default).path := by
      show 8 * min (V.occL sh.levs ci.ht ci.wd) ci.wd + 32 * (ci.ht - ci.lv) = _
      rw [c1, c2, c3, hoc]; rfl
    rw [hlb, hpl] at hrest
    have hbuf : buf = [] := by rw [hR.buf]; simp
    refine ⟨p, o + (sh.levs.getD i default).t * ((sh.levs.getD i default).lb + 32 * (sh.levs.getD i default).path),
      0, st, buf, rest, _, caps, ps, _, ⟨?_, ?_, Nat.zero_le _, hR.fm, ?_, ?_⟩, hW.congr (nReads_query _ _), hC, hok,
      hm, hT'⟩
    · rw [hrest, hR.body, List.drop_drop]
    · rw [hbuf]; simp
    · rw [samples_query]; exact hR.len
    · rw [samples_query]; exact hR.hist

/-- **The walk**: along an accepting replay, the history's challenges are the chain's. -/
theorem walk_run (x : List UInt8) :
    ∀ (s : List V.Item) {p o b : ℕ} {st : Digest} {buf body : List UInt8} {h H : List Ev} {caps : List CapI}
      {ps : List ℕ} {acc : List V.Val},
    RS sh π L p o b st buf body h → CapsOK sh.levs caps → walkOK sh.levs s caps.length ps.length b = true →
    (msgs6 sh).drop p = msgsAux sh.levs s o b → RdW (S6 sh vk dec) h (V.widths s) →
    (S6 sh vk dec).trun L (V.PS.walk sh.levs s ps acc fun _ acc => .ret (dec x acc)) st buf caps body h =
      some (true, H) →
    ∀ j (hj : j < (samples H).length),
      ∃ a, fmAns (fsQ6 sh π) zeroDL L (j + 2) = some a ∧ (samples H)[j] = Lvm.FS.chalOf a
  | [], p, o, b, st, buf, body, h, H, caps, ps, acc, hR, _, _, _, _, hT => by
    rw [ps_walk_nil] at hT
    have hH := trun_ret _ _ hT
    subst hH
    exact hR.hist
  | it :: r, p, o, b, st, buf, body, h, H, caps, ps, acc, hR, hC, hok, hm, hW, hT => by
    rw [ps_walk_cons] at hT
    obtain ⟨p', o', b', st', buf', body', h', caps', ps', acc', hR', hW', hC', hok', hm', hT'⟩ :=
      item_step it r hR hC hok hm hW hT
    exact walk_run x r hR' hC' hok' hm' hW' hT'

end Inv

/-- **`chain6_spec` at a shape** whose walk has the static facts. -/
theorem chain6_spec_of (sh : Shape) (hw : walkOK sh.levs (sched6 sh) 0 0 0 = true) : Chain6Spec sh := by
  intro vk dec π L x body a₁ H hh h1 hT j hj _
  have hh' : V.hdr6 (toV sh) π = some (x, body) := hh
  have hb : body = π.data.toList.drop (hdrLen sh) := by
    rw [V.hdr6] at hh'
    by_cases hz : V.hdrLen (toV sh) ≤ π.size
    · rw [if_pos hz] at hh'
      simp only [Option.some.injEq, Prod.mk.injEq] at hh'
      exact hh'.2.symm
    · rw [if_neg hz] at hh'
      exact absurd hh' (by simp)
  have hR : RS sh π L 1 (hdrLen sh) 0 a₁ [] body [] :=
    ⟨hb, by simp, Nat.zero_le _, h1, rfl, fun j hj => absurd hj (by simp [samples])⟩
  exact walk_run (vk := vk) (dec := dec) x (sched6 sh) (caps := []) (ps := []) (acc := []) hR
    (fun k hk => absurd hk (by simp)) hw rfl (fun j => by simp [nReads]; rfl) hT j hj

/-- **`chain6_spec`**: at `P18`, the challenges of an accepting replay are the scan's chain. -/
theorem chain6_spec : Chain6Spec P18 := chain6_spec_of P18 walkOK_P18

end Lvm6.X
