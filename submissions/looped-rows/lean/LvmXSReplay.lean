-- New for lvm2 E2F (E2F-L, 2026-11-13): the O5c replay with per-read widths. `LvmCertSExq2Run`'s `simK2`/`trun_simK2`/
-- `simK2_chain` with the read index carried (`n`): the `n`-th read takes `rw n` bytes (`Scheme.rw`), so the replay
-- needs no `Uniform` scheme and its offsets are functions of the widths `rw` (decided per stage).
import LvmCertSExq2

/-!
# The replay with read widths

* `simK2W S L B ks n off pend st`: `simK2` with the read index `n` (a read takes `S.rw n` bytes);
  `capsK2W`, `offK2W rw`, `pendK2W rw`, `fsPreK2W rw` (the offsets as functions of the widths `rw`);
* **`trun_simK2W`**: `trun` from a history with `n` reads, along a history of the kinds `ks`, is `simK2W`'s history
  (`trun_simK2` without `Uniform`);
* **`simK2W_chain`**: `simK2W`'s samples are the first-match chain's answers (`simK2_chain`).
-/

set_option autoImplicit false

namespace Lvm.ASM

open RecursionFast Lvm.FS
open LeanVM.Parameters
open LeanVM.Protocol.Compile hiding Proof Bytes

section Sim

variable (S : Scheme) (L : Log) (B : List UInt8)

/-- **The replay on kinds with read widths** (`simK2`: the `n`-th read takes `S.rw n` bytes). -/
def simK2W : List K2 → ℕ → ℕ → ℕ → Digest → Option (List Ev × Digest)
  | [], _, _, _, st => some ([], st)
  | .read :: ks, n, off, pend, st =>
    (simK2W ks (n + 1) (off + S.rw n) pend st).map fun r => (.read (S.decE (sl B off (S.rw n))) :: r.1, r.2)
  | .sample :: ks, n, off, pend, st =>
    (L.find? fun e => e.1 = toQ (st.toList ++ sl B pend (off - pend))).bind fun e =>
      (simK2W ks n off off e.2).map fun r => (.sample (S.chal e.2) :: r.1, r.2)
  | .commit ht w nb :: ks, n, off, pend, st =>
    (simK2W ks n (off + nb) pend st).map fun r =>
      (.commit ht w (S.wordOf L (S.capI ht w (B.drop off))) :: r.1, r.2)

/-- The commitments' records the replay appends. -/
def capsK2W (rw : ℕ → ℕ) : List K2 → ℕ → ℕ → List CapI → List CapI
  | [], _, _, caps => caps
  | .read :: ks, n, off, caps => capsK2W rw ks (n + 1) (off + rw n) caps
  | .sample :: ks, n, off, caps => capsK2W rw ks n off caps
  | .commit ht w nb :: ks, n, off, caps => capsK2W rw ks n (off + nb) (caps ++ [S.capI ht w (B.drop off)])

end Sim

/-- The body offset after the kinds. -/
def offK2W (rw : ℕ → ℕ) : List K2 → ℕ → ℕ → ℕ
  | [], _, off => off
  | .read :: ks, n, off => offK2W rw ks (n + 1) (off + rw n)
  | .sample :: ks, n, off => offK2W rw ks n off
  | .commit _ _ nb :: ks, n, off => offK2W rw ks n (off + nb)

/-- The first pending byte after the kinds. -/
def pendK2W (rw : ℕ → ℕ) : List K2 → ℕ → ℕ → ℕ → ℕ
  | [], _, _, pend => pend
  | .read :: ks, n, off, pend => pendK2W rw ks (n + 1) (off + rw n) pend
  | .sample :: ks, n, off, _ => pendK2W rw ks n off off
  | .commit _ _ nb :: ks, n, off, pend => pendK2W rw ks n (off + nb) pend

/-- The slices the samples absorb. -/
def fsPreK2W (rw : ℕ → ℕ) : List K2 → ℕ → ℕ → ℕ → List (ℕ × ℕ)
  | [], _, _, _ => []
  | .read :: ks, n, off, pend => fsPreK2W rw ks (n + 1) (off + rw n) pend
  | .sample :: ks, n, off, pend => (pend, off - pend) :: fsPreK2W rw ks n off off
  | .commit _ _ nb :: ks, n, off, pend => fsPreK2W rw ks n (off + nb) pend

/-- The reads among the kinds. -/
def readsK2 : List K2 → ℕ
  | [] => 0
  | .read :: ks => readsK2 ks + 1
  | _ :: ks => readsK2 ks

/-! ## The replay is `simK2W` -/

/-- **The replay along reads, samples and commitments with read widths** (`trun_simK2` without `Uniform`): from a
history with `n` reads, `trun`'s history is `simK2W`'s, the program after it is `p.after pre`. -/
theorem trun_simK2W (S : Scheme) (L : Log) (B : List UInt8) : ∀ (ks : List K2)
    (p : VerifierProgram Bool) (n off pend : ℕ) (st : Digest) (caps : List CapI)
    (h pre post : List Ev) (b : Bool), nReads h = n →
    (∀ ht w nb, K2.commit ht w nb ∈ ks → S.capBytes ht w = nb) → pend ≤ off →
    List.Forall₂ KM pre ks →
    S.trun L p st (sl B pend (off - pend)) caps (B.drop off) h = some (b, h ++ pre ++ post) →
    ∃ st' p', simK2W S L B ks n off pend st = some (pre, st') ∧ p.after pre = some p' ∧
      pendK2W S.rw ks n off pend ≤ offK2W S.rw ks n off ∧
      S.trun L p' st' (sl B (pendK2W S.rw ks n off pend) (offK2W S.rw ks n off - pendK2W S.rw ks n off pend))
        (capsK2W S B S.rw ks n off caps) (B.drop (offK2W S.rw ks n off)) (h ++ pre) =
          some (b, h ++ pre ++ post) := by
  intro ks
  induction ks with
  | nil =>
    intro p n off pend st caps h pre post b _ _ hle hk e
    have : pre = [] := by cases hk; rfl
    subst this
    exact ⟨st, p, rfl, after_nil p, hle, by simpa [pendK2W, offK2W, capsK2W] using e⟩
  | cons k ks ih =>
    intro p n off pend st caps h pre post b hn hcb hle hk e
    obtain ⟨e₀, pre', rfl⟩ : ∃ e₀ pre', pre = e₀ :: pre' := by
      cases hk with
      | cons a b => exact ⟨_, _, rfl⟩
    obtain ⟨hk0, hks⟩ := forall₂_cons_inv hk
    have hcb' : ∀ ht w nb, K2.commit ht w nb ∈ ks → S.capBytes ht w = nb :=
      fun ht w nb hm => hcb ht w nb (List.mem_cons_of_mem _ hm)
    have hcon : ∀ b', some (b', h) ≠ some (b, h ++ (e₀ :: pre') ++ post) := fun b' he => by
      simp only [Option.some.injEq, Prod.mk.injEq] at he
      have := congrArg List.length he.2
      simp at this
    cases p with
    | ret a => exact absurd e (hcon _)
    | fail => exact absurd e (hcon _)
    | grind _ _ => exact absurd e (hcon _)
    | read k' =>
      simp only [Scheme.trun, hn] at e
      split_ifs at e with hlen
      · exact absurd e (hcon _)
      have hpre := trun_prefix S L _ _ _ _ _ _ _ _ e
      have he0 := head_of_prefix hpre
      subst he0
      cases k with
      | sample => exact absurd hk0 (by simp [KM])
      | commit _ _ _ => exact absurd hk0 (by simp [KM])
      | read =>
        rw [sl_append B hle, drop_drop'] at e
        obtain ⟨st', p', hs, ha, hle', ht⟩ := ih _ (n + 1) (off + S.rw n) pend st caps
          (h ++ [Ev.read (S.decE ((B.drop off).take (S.rw n)))]) pre' post b (by rw [nReads_read, hn])
          hcb' (by omega) hks (by rw [e]; simp)
        refine ⟨st', p', ?_, ?_, hle', by simpa [pendK2W, offK2W, capsK2W] using ht⟩
        · simp only [simK2W, hs, Option.map_some]
          rfl
        · simp only [VerifierProgram.after]
          exact ha
    | sample k' =>
      simp only [Scheme.trun] at e
      split_ifs at e with hq
      · cases hfd : L.find? (fun e => decide (e.1 = toQ (st.toList ++ sl B pend (off - pend)))) with
        | none => rw [hfd] at e; simp at e
        | some e' =>
          rw [hfd, Option.bind_some] at e
          have hpre := trun_prefix S L _ _ _ _ _ _ _ _ e
          have he0 := head_of_prefix hpre
          subst he0
          cases k with
          | read => exact absurd hk0 (by simp [KM])
          | commit _ _ _ => exact absurd hk0 (by simp [KM])
          | sample =>
            have e2 : S.trun L (k' (S.chal e'.2)) e'.2 (sl B off (off - off)) caps (B.drop off)
                (h ++ [Ev.sample (S.chal e'.2)]) =
                some (b, h ++ [Ev.sample (S.chal e'.2)] ++ pre' ++ post) := by
              simpa [sl] using e
            obtain ⟨st', p', hs, ha, hle', ht⟩ := ih _ n off off e'.2 caps _ pre' post b
              (by rw [nReads_sample, hn]) hcb' le_rfl hks e2
            refine ⟨st', p', ?_, ?_, hle', by simpa [pendK2W, offK2W, capsK2W] using ht⟩
            · simp only [simK2W, hfd, Option.bind_some, hs, Option.map_some]
            · simp only [VerifierProgram.after]
              exact ha
      · exact absurd e (hcon _)
    | commit ht w k' =>
      simp only [Scheme.trun] at e
      split_ifs at e
      · exact absurd e (hcon _)
      have hpre := trun_prefix S L _ _ _ _ _ _ _ _ e
      have he0 := head_of_prefix hpre
      subst he0
      cases k with
      | read => exact absurd hk0 (by simp [KM])
      | sample => exact absurd hk0 (by simp [KM])
      | commit ht' w' nb =>
        obtain ⟨rfl, rfl⟩ := hk0
        have hnb : S.capBytes ht w = nb := hcb ht w nb List.mem_cons_self
        rw [hnb, sl_append B hle, drop_drop'] at e
        obtain ⟨st', p', hs, ha, hle', ht'⟩ := ih k' n (off + nb) pend st
          (caps ++ [S.capI ht w (B.drop off)])
          (h ++ [Ev.commit ht w (S.wordOf L (S.capI ht w (B.drop off)))]) pre' post b
          (by rw [nReads_commit, hn]) hcb' (by omega) hks (by rw [e]; simp)
        refine ⟨st', p', ?_, ?_, hle', by simpa [pendK2W, offK2W, capsK2W] using ht'⟩
        · simp only [simK2W, hs, Option.map_some]
        · simp only [VerifierProgram.after, and_self, ite_true]
          exact ha
    | query i ps k' =>
      simp only [Scheme.trun] at e
      cases hc : caps[i]? with
      | none => rw [hc] at e; exact absurd e (hcon _)
      | some ci =>
        rw [hc] at e
        simp only at e
        cases ho : (S.openAll ci ps (B.drop off)).runLog L with
        | none => rw [ho] at e; simp at e
        | some o =>
          rw [ho, Option.bind_some] at e
          rcases o with _ | ⟨rows, rest⟩
          · exact absurd e (hcon _)
          · have hpre := trun_prefix S L _ _ _ _ _ _ _ _ e
            have he0 := head_of_prefix hpre
            subst he0
            cases k <;> simp [KM] at hk0

/-! ## `simK2W`'s samples are the first-match chain -/

/-- **The chain** (`simK2_chain` with read widths). -/
theorem simK2W_chain (S : Scheme) (L : Log) (B : List UInt8) (T : ℕ → Digest → ByteArray)
    (st₀ : Digest) : ∀ (ks : List K2) (n off pend : ℕ) (st : Digest) (j : ℕ) (pre : List Ev)
    (st' : Digest), simK2W S L B ks n off pend st = some (pre, st') →
    Lvm.X.fmAns T st₀ L j = some st →
    (∀ i (hi : i < (fsPreK2W S.rw ks n off pend).length) (s : Digest),
      T (j + 1 + i) s =
        toQ (s.toList ++ sl B ((fsPreK2W S.rw ks n off pend)[i]).1 ((fsPreK2W S.rw ks n off pend)[i]).2)) →
    (∀ i (hi : i < (pre.filterMap smpOf).length), ∃ a,
      Lvm.X.fmAns T st₀ L (j + 1 + i) = some a ∧ (pre.filterMap smpOf)[i] = S.chal a) ∧
    Lvm.X.fmAns T st₀ L (j + (pre.filterMap smpOf).length) = some st' := by
  intro ks
  induction ks with
  | nil =>
    intro n off pend st j pre st' hs hj _
    simp only [simK2W, Option.some.injEq, Prod.mk.injEq] at hs
    obtain ⟨rfl, rfl⟩ := hs
    exact ⟨fun i hi => by simp at hi, by simpa using hj⟩
  | cons k ks ih =>
    intro n off pend st j pre st' hs hj hT
    cases k with
    | read =>
      simp only [simK2W] at hs
      cases hr : simK2W S L B ks (n + 1) (off + S.rw n) pend st with
      | none => rw [hr] at hs; simp at hs
      | some r =>
        obtain ⟨pre₁, st₁⟩ := r
        rw [hr, Option.map_some, Option.some.injEq, Prod.mk.injEq] at hs
        obtain ⟨rfl, rfl⟩ := hs
        exact ih (n + 1) (off + S.rw n) pend st j pre₁ st₁ hr hj (fun i hi s => hT i hi s)
    | commit ht w nb =>
      simp only [simK2W] at hs
      cases hr : simK2W S L B ks n (off + nb) pend st with
      | none => rw [hr] at hs; simp at hs
      | some r =>
        obtain ⟨pre₁, st₁⟩ := r
        rw [hr, Option.map_some, Option.some.injEq, Prod.mk.injEq] at hs
        obtain ⟨rfl, rfl⟩ := hs
        exact ih n (off + nb) pend st j pre₁ st₁ hr hj (fun i hi s => hT i hi s)
    | sample =>
      simp only [simK2W] at hs
      cases hfd : L.find? (fun e => decide (e.1 = toQ (st.toList ++ sl B pend (off - pend)))) with
      | none => rw [hfd] at hs; simp at hs
      | some e =>
        rw [hfd, Option.bind_some] at hs
        cases hr : simK2W S L B ks n off off e.2 with
        | none => rw [hr] at hs; simp at hs
        | some r =>
          obtain ⟨pre₁, st₁⟩ := r
          rw [hr, Option.map_some, Option.some.injEq, Prod.mk.injEq] at hs
          obtain ⟨rfl, rfl⟩ := hs
          have hT0 := hT 0 (by simp [fsPreK2W]) st
          simp only [fsPreK2W, List.getElem_cons_zero, add_zero] at hT0
          have hj1 : Lvm.X.fmAns T st₀ L (j + 1) = some e.2 := by
            simp only [Lvm.X.fmAns, hj, Option.bind_some, hT0, hfd, Option.map_some]
          obtain ⟨h1, h2⟩ := ih n off off e.2 (j + 1) pre₁ st₁ hr hj1 (fun i hi s => by
            have := hT (i + 1) (by simp [fsPreK2W]; omega) s
            simp only [fsPreK2W, List.getElem_cons_succ] at this
            rw [show j + 1 + 1 + i = j + 1 + (i + 1) by omega]
            exact this)
          refine ⟨fun i hi => ?_, ?_⟩
          · rcases i with _ | i
            · exact ⟨e.2, by simpa using hj1, by simp [smpOf]⟩
            · simp only [List.filterMap_cons, smpOf, List.length_cons] at hi
              obtain ⟨a, ha, he⟩ := h1 i (by omega)
              refine ⟨a, by rw [show j + 1 + (i + 1) = j + 1 + 1 + i by omega]; exact ha, ?_⟩
              simpa [smpOf] using he
          · simp only [List.filterMap_cons, smpOf, List.length_cons]
            rw [show j + (List.length (List.filterMap smpOf pre₁) + 1) =
              j + 1 + (List.filterMap smpOf pre₁).length by omega]
            exact h2

/-! ## The reads' values -/

/-- **A run of reads** is the scalars of consecutive slices of the widths. -/
theorem simK2W_reads (S : Scheme) (L : Log) (B : List UInt8) : ∀ (m n off pend : ℕ) (st : Digest),
    simK2W S L B (List.replicate m .read) n off pend st =
      some ((List.range m).map (fun i => Ev.read (S.decE (sl B (offK2W S.rw (List.replicate i .read) n off)
        (S.rw (n + i))))), st)
  | 0, _, _, _, _ => rfl
  | m + 1, n, off, pend, st => by
    rw [List.replicate_succ, simK2W, simK2W_reads S L B m (n + 1) (off + S.rw n) pend st, Option.map_some,
      List.range_succ_eq_map, List.map_cons, List.map_map]
    simp only [List.replicate_zero, offK2W, Nat.add_zero]
    congr 2
    refine congrArg _ (List.map_congr_left fun i _ => ?_)
    simp only [Function.comp, List.replicate_succ, offK2W, Nat.add_right_comm n 1 i, Nat.succ_eq_add_one,
      Nat.add_assoc]

end Lvm.ASM
