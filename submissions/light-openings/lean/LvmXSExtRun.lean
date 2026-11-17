-- New for lvm2 E2F (E2F-L, 2026-11-13): the replay's static facts generic in the stage (`LvmMPXExtRun.openMain_P20`
-- and `LvmMPXLayout.layoutM_P20`'s facts with the stage's middle items, read widths and offsets), checked by one
-- Boolean evaluation per stage (`replayOkB`).
import LvmXSLayout
import LvmXSKinds
import LvmMPXExtEq
import LvmCertSExq2

-- ===== merged from `LvmXSReplay` (VQ module merge: `LvmXSReplay.lean` removed) =====
section
-- New for lvm2 E2F (E2F-L, 2026-11-13): the O5c replay with per-read widths. `LvmCertSExq2Run`'s `simK2`/`trun_simK2`/
-- `simK2_chain` with the read index carried (`n`): the `n`-th read takes `rw n` bytes (`Scheme.rw`), so the replay
-- needs no `Uniform` scheme and its offsets are functions of the widths `rw` (decided per stage).

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
          hcb' (by (clear * - pend off S n B h hle; omega)) hks (by rw [e]; simp)
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
          (by rw [nReads_commit, hn]) hcb' (by (clear * - pend off nb S B n h hle ht w hnb; omega)) hks (by rw [e]; simp)
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
            have := hT (i + 1) (by simp [fsPreK2W]; (clear * - hi; omega)) s
            simp only [fsPreK2W, List.getElem_cons_succ] at this
            rw [show j + 1 + 1 + i = j + 1 + (i + 1) by (clear * - j i S ks n off; omega)]
            exact this)
          refine ⟨fun i hi => ?_, ?_⟩
          · rcases i with _ | i
            · exact ⟨e.2, by simpa using hj1, by simp [smpOf]⟩
            · simp only [List.filterMap_cons, smpOf, List.length_cons] at hi
              obtain ⟨a, ha, he⟩ := h1 i (by (clear * - i pre₁ hi; omega))
              refine ⟨a, by rw [show j + 1 + (i + 1) = j + 1 + 1 + i by (clear * - j i pre₁; omega)]; exact ha, ?_⟩
              simpa [smpOf] using he
          · simp only [List.filterMap_cons, smpOf, List.length_cons]
            rw [show j + (List.length (List.filterMap smpOf pre₁) + 1) =
              j + 1 + (List.filterMap smpOf pre₁).length by (clear * - j pre₁; omega)]
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
end
-- ===== end of `LvmXSReplay` =====

/-!
# The replay's facts at a stage

The pinned middle phases' items (`midItemsS st`) are reads (of any width) and samples; `openMain` is `P20`'s
(`mainHeadA1 … mainHeadB2`). With the widths as a list (`offK2L ws`, `pendK2L ws`, `fsPreK2L ws`: a read takes the
next width, so a stage is checked by one linear evaluation), the replay's segments (`A1` = the middle phases, `ρ`,
the intro and level 0's fold rounds; `A2`; level 0's opening; `B1`; `A3`; level 1's opening; `B2`; the residual)
absorb the chain's messages `fsMsgsS st` and end at the stage's offsets (`capOffS`, `resOffS`): **`replayOkB st`**.
`offK2W_eq_L` (and the `pend`/`fsPre` twins) turn the list forms into `trun_simK2W`'s.
-/

set_option autoImplicit false

namespace Lvm.ASM

open RecursionFast Lvm Lvm.XS

/-! ## Kinds of `ItemF` -/

/-- The kinds of items (`itemK2` over `ItemF`: `readW m w` is `m` reads). -/
def itemK2F (p : Params) (sh : Ref → ℕ × ℕ) : List Item → List K2
  | [] => []
  | .readW m _ :: its => List.replicate m .read ++ itemK2F p sh its
  | .read m :: its => List.replicate m .read ++ itemK2F p sh its
  | .sample :: its => .sample :: itemK2F p sh its
  | .cap c r :: its => itemK2 p sh [.cap c r] ++ itemK2F p sh its
  | .positions r :: its => itemK2 p sh [.positions r] ++ itemK2F p sh its
  | .opening r :: its => itemK2 p sh [.opening r] ++ itemK2F p sh its

/-- Items of reads and samples only (`RSItems` over `ItemF`). -/
def RSItemsF : List Item → Bool
  | [] => true
  | .readW _ _ :: its => RSItemsF its
  | .read _ :: its => RSItemsF its
  | .sample :: its => RSItemsF its
  | _ :: _ => false

theorem itemK2F_rs (p : Params) (sh : Ref → ℕ × ℕ) : ∀ (its : List Item), RSItemsF its = true →
    itemK2F p sh its = (itemKindsS its).map toK2
  | [], _ => rfl
  | .readW m _ :: its, h => by
    rw [itemK2F, itemKindsS, itemK2F_rs p sh its h, List.map_append, List.map_replicate]; rfl
  | .read m :: its, h => by
    rw [itemK2F, itemKindsS, itemK2F_rs p sh its h, List.map_append, List.map_replicate]; rfl
  | .sample :: its, h => by
    rw [itemK2F, itemKindsS, itemK2F_rs p sh its h]; rfl
  | .cap _ _ :: _, h => by simp [RSItemsF] at h
  | .positions _ :: _, h => by simp [RSItemsF] at h
  | .opening _ :: _, h => by simp [RSItemsF] at h

theorem other_not_mem_F : ∀ (its : List Item), RSItemsF its = true → EvK.other ∉ itemKindsS its
  | [], _ => by simp [itemKindsS]
  | .readW m _ :: its, h => by
    simpa [itemKindsS] using other_not_mem_F its h
  | .read m :: its, h => by
    simpa [itemKindsS] using other_not_mem_F its h
  | .sample :: its, h => by
    simp only [itemKindsS, List.mem_cons, not_or]
    exact ⟨by decide, other_not_mem_F its h⟩
  | .cap _ _ :: _, h => by simp [RSItemsF] at h
  | .positions _ :: _, h => by simp [RSItemsF] at h
  | .opening _ :: _, h => by simp [RSItemsF] at h

/-! ## The offsets with a list of widths -/

/-- The body offset after the kinds, the widths a list (a read takes the next). -/
def offK2L : List ℕ → List K2 → ℕ → ℕ
  | _, [], off => off
  | ws, .read :: ks, off => offK2L ws.tail ks (off + ws.headD eBytes)
  | ws, .sample :: ks, off => offK2L ws ks off
  | ws, .commit _ _ nb :: ks, off => offK2L ws ks (off + nb)

/-- The first pending byte after the kinds, the widths a list. -/
def pendK2L : List ℕ → List K2 → ℕ → ℕ → ℕ
  | _, [], _, pend => pend
  | ws, .read :: ks, off, pend => pendK2L ws.tail ks (off + ws.headD eBytes) pend
  | ws, .sample :: ks, off, _ => pendK2L ws ks off off
  | ws, .commit _ _ nb :: ks, off, pend => pendK2L ws ks (off + nb) pend

/-- The slices the samples absorb, the widths a list. -/
def fsPreK2L : List ℕ → List K2 → ℕ → ℕ → List (ℕ × ℕ)
  | _, [], _, _ => []
  | ws, .read :: ks, off, pend => fsPreK2L ws.tail ks (off + ws.headD eBytes) pend
  | ws, .sample :: ks, off, pend => (pend, off - pend) :: fsPreK2L ws ks off off
  | ws, .commit _ _ nb :: ks, off, pend => fsPreK2L ws ks (off + nb) pend

theorem headD_eq_getD (ws : List ℕ) : ws.headD eBytes = ws.getD 0 eBytes := by cases ws <;> rfl

theorem getD_tail (ws : List ℕ) (i : ℕ) : ws.tail.getD i eBytes = ws.getD (i + 1) eBytes := by
  cases ws <;> simp

/-- The list forms are `trun_simK2W`'s when the widths from index `n` are the list's. -/
theorem offK2W_eq_L (rw : ℕ → ℕ) : ∀ (ks : List K2) (n : ℕ) (ws : List ℕ) (off pend : ℕ),
    (∀ i, rw (n + i) = ws.getD i eBytes) →
    offK2W rw ks n off = offK2L ws ks off ∧ pendK2W rw ks n off pend = pendK2L ws ks off pend ∧
      fsPreK2W rw ks n off pend = fsPreK2L ws ks off pend
  | [], _, _, _, _, _ => ⟨rfl, rfl, rfl⟩
  | .read :: ks, n, ws, off, pend, h => by
    have h0 : rw n = ws.headD eBytes := by rw [headD_eq_getD, ← h 0, Nat.add_zero]
    have h1 : ∀ i, rw (n + 1 + i) = ws.tail.getD i eBytes := fun i => by
      rw [getD_tail, ← h (i + 1), Nat.add_right_comm, Nat.add_assoc, Nat.add_comm i]
    obtain ⟨a, b, c⟩ := offK2W_eq_L rw ks (n + 1) ws.tail (off + rw n) pend h1
    simp only [offK2W, pendK2W, fsPreK2W, offK2L, pendK2L, fsPreK2L, ← h0]
    exact ⟨a, b, c⟩
  | .sample :: ks, n, ws, off, pend, h => by
    obtain ⟨a, b, c⟩ := offK2W_eq_L rw ks n ws off off h
    simp only [offK2W, pendK2W, fsPreK2W, offK2L, pendK2L, fsPreK2L]
    exact ⟨a, b, by rw [c]⟩
  | .commit _ _ nb :: ks, n, ws, off, pend, h => by
    obtain ⟨a, b, c⟩ := offK2W_eq_L rw ks n ws (off + nb) pend h
    simp only [offK2W, pendK2W, fsPreK2W, offK2L, pendK2L, fsPreK2L]
    exact ⟨a, b, c⟩

/-! ## A stage's segments -/

/-- The middle items' kinds. -/
def kMS (st : XStage) : List K2 := itemK2F st.p shMain (midItemsS st)

/-- Segment `A1`: the middle phases, `ρ`, the intro, level 0's fold rounds. -/
def kA1S (st : XStage) : List K2 := kMS st ++ itemK2 P20 shMain mainHeadA1

/-- The reads before segments `A2`, `B1`, `A3`, `B2` and the residual. -/
def nr1 (st : XStage) : ℕ := readsK2 (kA1S st)
def nr2 (st : XStage) : ℕ := nr1 st + readsK2 (itemK2 P20 shMain mainHeadA2)
def nr3 (st : XStage) : ℕ := nr2 st + readsK2 (itemK2 P20 shMain mainHeadB1)
def nr4 (st : XStage) : ℕ := nr3 st + readsK2 (itemK2 P20 shMain mainHeadA3)
def nr5 (st : XStage) : ℕ := nr4 st + readsK2 (itemK2 P20 shMain mainHeadB2)

/-- The root cap's end. -/
def o1S (st : XStage) : ℕ := st.hb + 8192

/-- Segment `A1`'s end. -/
def offA1 (st : XStage) : ℕ := offK2L (readWidthsS st) (kA1S st) (o1S st)
def pendA1 (st : XStage) : ℕ := pendK2L (readWidthsS st) (kA1S st) (o1S st) st.hb
/-- Segment `A2`'s end (level 0's opening's start). -/
def offA2 (st : XStage) : ℕ := offK2L ((readWidthsS st).drop (nr1 st)) (itemK2 P20 shMain mainHeadA2) (offA1 st)
def pendA2 (st : XStage) : ℕ :=
  pendK2L ((readWidthsS st).drop (nr1 st)) (itemK2 P20 shMain mainHeadA2) (offA1 st) (pendA1 st)
/-- Level 0's opening's end: `115` positions of `8·occ0 + 32·11` bytes. -/
def q0End (st : XStage) : ℕ := offA2 st + 115 * (8 * st.occ0 + 32 * 11)
/-- Segment `B1`'s end (level 2's cap's start). -/
def offB1 (st : XStage) : ℕ := offK2L ((readWidthsS st).drop (nr2 st)) (itemK2 P20 shMain mainHeadB1) (q0End st)
def pendB1 (st : XStage) : ℕ :=
  pendK2L ((readWidthsS st).drop (nr2 st)) (itemK2 P20 shMain mainHeadB1) (q0End st) (q0End st)
/-- Segment `A3`'s end (level 1's opening's start). -/
def offA3 (st : XStage) : ℕ := offK2L ((readWidthsS st).drop (nr3 st)) (itemK2 P20 shMain mainHeadA3) (offB1 st)
def pendA3 (st : XStage) : ℕ :=
  pendK2L ((readWidthsS st).drop (nr3 st)) (itemK2 P20 shMain mainHeadA3) (offB1 st) (pendB1 st)
/-- Level 1's opening's end: `77` positions of `8·48 + 32·9` bytes. -/
def q1End (st : XStage) : ℕ := offA3 st + 77 * (8 * 48 + 32 * 9)
/-- Segment `B2`'s end (the residual's start). -/
def offB2 (st : XStage) : ℕ := offK2L ((readWidthsS st).drop (nr4 st)) (itemK2 P20 shMain mainHeadB2) (q1End st)
def pendB2 (st : XStage) : ℕ :=
  pendK2L ((readWidthsS st).drop (nr4 st)) (itemK2 P20 shMain mainHeadB2) (q1End st) (q1End st)

/-- The middle phases' samples. -/
def nMidS (st : XStage) : ℕ := (itemKindsS (midItemsS st)).count .sample

/-- **The replay's static facts at a stage** (one evaluation per stage; right-nested). -/
def replayOkB (st : XStage) : Bool :=
  RSItemsF (midItemsS st) && (
  fsPreK2L (readWidthsS st) (kA1S st) (o1S st) st.hb == ((fsMsgsS st).drop 1).take (nMidS st + 7) && (
  offA1 st == capOffS st 1 && (
  fsPreK2L ((readWidthsS st).drop (nr1 st)) (itemK2 P20 shMain mainHeadA2) (offA1 st) (pendA1 st) ==
    ((fsMsgsS st).drop (nMidS st + 8)).take 35 && (
  offA2 st == pendA2 st && (
  fsPreK2L ((readWidthsS st).drop (nr2 st)) (itemK2 P20 shMain mainHeadB1) (q0End st) (q0End st) ==
    ((fsMsgsS st).drop (nMidS st + 43)).take 4 && (
  offB1 st == capOffS st 2 && (
  fsPreK2L ((readWidthsS st).drop (nr3 st)) (itemK2 P20 shMain mainHeadA3) (offB1 st) (pendB1 st) ==
    ((fsMsgsS st).drop (nMidS st + 47)).take 26 && (
  offA3 st == pendA3 st && (
  fsPreK2L ((readWidthsS st).drop (nr4 st)) (itemK2 P20 shMain mainHeadB2) (q1End st) (q1End st) ==
    ((fsMsgsS st).drop (nMidS st + 73)).take 4 && (
  offB2 st == resOffS st && (
  ((readWidthsS st).drop (nr5 st)).take (2 ^ 9) == List.replicate (2 ^ 9) eBytes && (
  foldPosS st 0 0 == nMidS st + 3 && (foldPosS st 1 0 == nMidS st + 44 && (foldPosS st 2 0 == nMidS st + 74 && (
  nChainS st == nMidS st + 78 && (
  st.hb % 8 == 0 && (capOffS st 1 % 8 == 0 && (capOffS st 2 % 8 == 0 && (resOffS st % 8 == 0 && (
  decide ((if st.p.leafOut then hdrFixS else hdrFix) ≤ st.hb) && (decide (8 ≤ st.hb) && (decide (st.occ0 ≤ 64) && (
  decide (o1S st ≤ st.pz) && (decide (capOffS st 1 + 32 * 2 ^ 7 ≤ st.pz) && (
  decide (capOffS st 2 + 32 * 2 ^ 7 ≤ st.pz) && decide (resOffS st + 24 * 2 ^ 9 ≤ st.pz))))))))))))))))))))))))))

/-- **The replay's facts at a stage.** -/
structure ReplayOK (st : XStage) : Prop where
  rs : RSItemsF (midItemsS st) = true
  fA1 : fsPreK2L (readWidthsS st) (kA1S st) (o1S st) st.hb = ((fsMsgsS st).drop 1).take (nMidS st + 7)
  oA1 : offA1 st = capOffS st 1
  fA2 : fsPreK2L ((readWidthsS st).drop (nr1 st)) (itemK2 P20 shMain mainHeadA2) (offA1 st) (pendA1 st) =
    ((fsMsgsS st).drop (nMidS st + 8)).take 35
  oA2 : offA2 st = pendA2 st
  fB1 : fsPreK2L ((readWidthsS st).drop (nr2 st)) (itemK2 P20 shMain mainHeadB1) (q0End st) (q0End st) =
    ((fsMsgsS st).drop (nMidS st + 43)).take 4
  oB1 : offB1 st = capOffS st 2
  fA3 : fsPreK2L ((readWidthsS st).drop (nr3 st)) (itemK2 P20 shMain mainHeadA3) (offB1 st) (pendB1 st) =
    ((fsMsgsS st).drop (nMidS st + 47)).take 26
  oA3 : offA3 st = pendA3 st
  fB2 : fsPreK2L ((readWidthsS st).drop (nr4 st)) (itemK2 P20 shMain mainHeadB2) (q1End st) (q1End st) =
    ((fsMsgsS st).drop (nMidS st + 73)).take 4
  oB2 : offB2 st = resOffS st
  r24 : ((readWidthsS st).drop (nr5 st)).take (2 ^ 9) = List.replicate (2 ^ 9) eBytes
  fp0 : foldPosS st 0 0 = nMidS st + 3
  fp1 : foldPosS st 1 0 = nMidS st + 44
  fp2 : foldPosS st 2 0 = nMidS st + 74
  nc : nChainS st = nMidS st + 78
  a0 : st.hb % 8 = 0
  a1 : capOffS st 1 % 8 = 0
  a2 : capOffS st 2 % 8 = 0
  ar : resOffS st % 8 = 0
  /-- The header's fixed part (without `σ_leaf` at `leafOut`, lvm2 σ_LEAF) fits the header. -/
  hl : (if st.p.leafOut then hdrFixS else hdrFix) ≤ st.hb
  h8 : 8 ≤ st.hb
  oc : st.occ0 ≤ 64
  s0 : o1S st ≤ st.pz
  s1 : capOffS st 1 + 32 * 2 ^ 7 ≤ st.pz
  s2 : capOffS st 2 + 32 * 2 ^ 7 ≤ st.pz
  sr : resOffS st + 24 * 2 ^ 9 ≤ st.pz

/-- The evaluation gives the facts. -/
theorem replayOK_of {st : XStage} (h : replayOkB st = true) : ReplayOK st := by
  simp only [replayOkB, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
  obtain ⟨rs, fA1, oA1, fA2, oA2, fB1, oB1, fA3, oA3, fB2, oB2, r24, fp0, fp1, fp2, nc, a0, a1, a2, ar, hl, h8, oc,
    s0, s1, s2, sr⟩ := h
  exact ⟨rs, fA1, oA1, fA2, oA2, fB1, oB1, fA3, oA3, fB2, oB2, r24, fp0, fp1, fp2, nc, a0, a1, a2, ar, hl, h8, oc,
    s0, s1, s2, sr⟩

/-! ## The run-length checker

`replayOkB` expands every run `readW m w` into `m` kinds and `m` widths (≈ 7 k entries at S2GF, ≈ 16 s of kernel
time). `replayOkR` walks the middle items once by runs (`endF`, `sampR`), and checks the segments after them with the
widths of `openMain`'s items only; `replayOK_ofR` turns it into `ReplayOK` for every stage. -/

/-- An item's read widths. -/
def wsI : Item → List ℕ
  | .readW m w => List.replicate m w
  | .read m => List.replicate m eBytes
  | _ => []

theorem readWidthsS_eq (st : XStage) : readWidthsS st = st.items.flatMap wsI := by
  unfold readWidthsS
  exact List.flatMap_congr fun it _ => by cases it <;> rfl

/-- `fsPre`'s body offset and first pending byte after the items. -/
def endF (p : Params) : List Item → ℕ → ℕ → ℕ × ℕ
  | [], off, pend => (off, pend)
  | .read m :: r, off, pend => endF p r (off + eBytes * m) pend
  | .readW m w :: r, off, pend => endF p r (off + w * m) pend
  | .cap c ref :: r, off, pend => endF p r (off + nodeBytes * 2 ^ p.capSendBits ref.lv c) pend
  | .sample :: r, off, _ => endF p r off off
  | .positions _ :: r, off, _ => endF p r off off
  | .opening ref :: r, off, _ =>
      endF p r (off + (p.level ref).t * ((p.level ref).row + nodeBytes * (p.level ref).path))
        (off + (p.level ref).t * ((p.level ref).row + nodeBytes * (p.level ref).path))

theorem fsPre_append (p : Params) : ∀ (a b : List Item) (off pend : ℕ),
    Lvm.X.fsPre p (a ++ b) off pend =
      Lvm.X.fsPre p a off pend ++ Lvm.X.fsPre p b (endF p a off pend).1 (endF p a off pend).2
  | [], _, _, _ => rfl
  | it :: a, b, off, pend => by
    cases it <;> simp only [List.cons_append, Lvm.X.fsPre, endF, fsPre_append p a b, List.append_assoc]

theorem endF_append (p : Params) : ∀ (a b : List Item) (off pend : ℕ),
    endF p (a ++ b) off pend = endF p b (endF p a off pend).1 (endF p a off pend).2
  | [], _, _, _ => rfl
  | it :: a, b, off, pend => by cases it <;> simp only [List.cons_append, endF, endF_append p a b]

/-- The samples among the items. -/
def sampR : List Item → ℕ
  | [] => 0
  | .sample :: r => sampR r + 1
  | .readW _ _ :: r | .read _ :: r | .cap _ _ :: r | .positions _ :: r | .opening _ :: r => sampR r

theorem fsPre_length_rs (p : Params) : ∀ (its : List Item) (off pend : ℕ), RSItemsF its = true →
    (Lvm.X.fsPre p its off pend).length = sampR its
  | [], _, _, _ => rfl
  | .readW _ _ :: its, _, _, h | .read _ :: its, _, _, h => by
    rw [Lvm.X.fsPre, sampR]; exact fsPre_length_rs p its _ _ h
  | .sample :: its, _, _, h => by
    rw [Lvm.X.fsPre, sampR, List.length_cons, fsPre_length_rs p its _ _ h]
  | .cap _ _ :: _, _, _, h | .positions _ :: _, _, _, h | .opening _ :: _, _, _, h => by simp [RSItemsF] at h

theorem count_sample_rs : ∀ (its : List Item), RSItemsF its = true → (itemKindsS its).count .sample = sampR its
  | [], _ => rfl
  | .readW _ _ :: its, h | .read _ :: its, h => by
    simp [itemKindsS, sampR, List.count_append, List.count_replicate, count_sample_rs its h]
  | .sample :: its, h => by
    simp [itemKindsS, sampR, List.count_cons, count_sample_rs its h]
  | .cap _ _ :: _, h | .positions _ :: _, h | .opening _ :: _, h => by simp [RSItemsF] at h

theorem readsK2_append : ∀ (a b : List K2), readsK2 (a ++ b) = readsK2 a + readsK2 b
  | [], b => (Nat.zero_add _).symm
  | .read :: a, b => by
    rw [List.cons_append, readsK2, readsK2, readsK2_append a b, Nat.add_right_comm]
  | .sample :: a, b => readsK2_append a b
  | .commit _ _ _ :: a, b => readsK2_append a b

theorem K2L_rep (w : ℕ) (ws : List ℕ) (ks : List K2) : ∀ (m off pend : ℕ),
    offK2L (List.replicate m w ++ ws) (List.replicate m .read ++ ks) off = offK2L ws ks (off + w * m) ∧
    pendK2L (List.replicate m w ++ ws) (List.replicate m .read ++ ks) off pend = pendK2L ws ks (off + w * m) pend ∧
    fsPreK2L (List.replicate m w ++ ws) (List.replicate m .read ++ ks) off pend =
      fsPreK2L ws ks (off + w * m) pend ∧
    readsK2 (List.replicate m .read ++ ks) = m + readsK2 ks
  | 0, off, pend => by simp only [List.replicate_zero, List.nil_append, Nat.mul_zero, Nat.add_zero, Nat.zero_add,
      and_self]
  | m + 1, off, pend => by
    obtain ⟨a, b, c, d⟩ := K2L_rep w ws ks m (off + w) pend
    have e : off + w * (m + 1) = off + w + w * m := by rw [Nat.mul_succ, Nat.add_comm (w * m), Nat.add_assoc]
    simp only [List.replicate_succ, List.cons_append, offK2L, pendK2L, fsPreK2L, readsK2, List.headD_cons,
      List.tail_cons, a, b, c, d, e, Nat.add_right_comm m 1, and_self]

/-- **The middle items by runs**: the list forms over `items ++ rest` are the run walk (`endF`, `fsPre`) followed by
the list forms over `rest`. -/
theorem K2L_items (p : Params) (sh : Ref → ℕ × ℕ) : ∀ (its : List Item) (ws : List ℕ) (ks : List K2) (off pend : ℕ),
    RSItemsF its = true →
    offK2L (its.flatMap wsI ++ ws) (itemK2F p sh its ++ ks) off = offK2L ws ks (endF p its off pend).1 ∧
    pendK2L (its.flatMap wsI ++ ws) (itemK2F p sh its ++ ks) off pend =
      pendK2L ws ks (endF p its off pend).1 (endF p its off pend).2 ∧
    fsPreK2L (its.flatMap wsI ++ ws) (itemK2F p sh its ++ ks) off pend =
      Lvm.X.fsPre p its off pend ++ fsPreK2L ws ks (endF p its off pend).1 (endF p its off pend).2 ∧
    readsK2 (itemK2F p sh its ++ ks) = (its.flatMap wsI).length + readsK2 ks
  | [], ws, ks, off, pend, _ => by
    simp only [List.flatMap_nil, List.nil_append, itemK2F, endF, Lvm.X.fsPre, List.length_nil, Nat.zero_add,
      and_self]
  | .readW m w :: its, ws, ks, off, pend, h => by
    obtain ⟨a, b, c, d⟩ := K2L_items p sh its ws ks (off + w * m) pend h
    obtain ⟨a', b', c', d'⟩ := K2L_rep w (its.flatMap wsI ++ ws) (itemK2F p sh its ++ ks) m off pend
    simp only [List.flatMap_cons, wsI, itemK2F, List.append_assoc, endF, Lvm.X.fsPre, a', b', c', d', a, b, c, d,
      List.length_append, List.length_replicate, Nat.add_assoc, and_self]
  | .read m :: its, ws, ks, off, pend, h => by
    obtain ⟨a, b, c, d⟩ := K2L_items p sh its ws ks (off + eBytes * m) pend h
    obtain ⟨a', b', c', d'⟩ := K2L_rep eBytes (its.flatMap wsI ++ ws) (itemK2F p sh its ++ ks) m off pend
    simp only [List.flatMap_cons, wsI, itemK2F, List.append_assoc, endF, Lvm.X.fsPre, a', b', c', d', a, b, c, d,
      List.length_append, List.length_replicate, Nat.add_assoc, and_self]
  | .sample :: its, ws, ks, off, pend, h => by
    obtain ⟨a, b, c, d⟩ := K2L_items p sh its ws ks off off h
    refine ⟨a, b, ?_, d⟩
    rw [List.flatMap_cons, show wsI .sample = [] from rfl, List.nil_append, itemK2F, List.cons_append, fsPreK2L,
      Lvm.X.fsPre, endF, List.cons_append]
    exact congrArg _ c
  | .cap _ _ :: _, _, _, _, _, h | .positions _ :: _, _, _, _, _, h | .opening _ :: _, _, _, _, _, h => by
    simp [RSItemsF] at h

/-- The chain offset of level `i`'s fold rounds after `foldPosS`'s `nPreS st + 3`. -/
def lvOffS (st : XStage) (i : ℕ) : ℕ :=
  if i = 0 then 0 else if i = 1 then lvlFsS st 0 else lvlFsS st 0 + lvlFsS st 1

/-- Level `i`'s cap offset (`i < 2`) or the residual's (`i = 2`), read off `R`, the chain's messages after the middle
phases' (`capOffS`, `resOffS`). -/
def capR (st : XStage) (R : List (ℕ × ℕ)) (i : ℕ) : ℕ :=
  (R.getD (2 + lvOffS st i + ((mainLS st i).fold - 1)) (0, 0)).1 + 2 * eBytes

/-- The segments after `A1` (`replayOkB`'s conjuncts from `oA1` on), with `ws0` the widths after `A1`, `oA`/`pA`
`A1`'s end, `nM` the middle phases' samples and `R` the chain's messages after theirs. -/
def replayOkG (st : XStage) (ws0 : List ℕ) (oA pA nM : ℕ) (R : List (ℕ × ℕ)) : Bool :=
  let w2 := ws0.drop (readsK2 (itemK2 P20 shMain mainHeadA2))
  let w3 := w2.drop (readsK2 (itemK2 P20 shMain mainHeadB1))
  let w4 := w3.drop (readsK2 (itemK2 P20 shMain mainHeadA3))
  let w5 := w4.drop (readsK2 (itemK2 P20 shMain mainHeadB2))
  let q0 := offK2L ws0 (itemK2 P20 shMain mainHeadA2) oA + 115 * (8 * st.occ0 + 32 * 11)
  let oB1 := offK2L w2 (itemK2 P20 shMain mainHeadB1) q0
  let pB1 := pendK2L w2 (itemK2 P20 shMain mainHeadB1) q0 q0
  let q1 := offK2L w3 (itemK2 P20 shMain mainHeadA3) oB1 + 77 * (8 * 48 + 32 * 9)
  oA == capR st R 0 && (
  fsPreK2L ws0 (itemK2 P20 shMain mainHeadA2) oA pA == (R.drop 7).take 35 && (
  offK2L ws0 (itemK2 P20 shMain mainHeadA2) oA == pendK2L ws0 (itemK2 P20 shMain mainHeadA2) oA pA && (
  fsPreK2L w2 (itemK2 P20 shMain mainHeadB1) q0 q0 == (R.drop 42).take 4 && (
  oB1 == capR st R 1 && (
  fsPreK2L w3 (itemK2 P20 shMain mainHeadA3) oB1 pB1 == (R.drop 46).take 26 && (
  offK2L w3 (itemK2 P20 shMain mainHeadA3) oB1 == pendK2L w3 (itemK2 P20 shMain mainHeadA3) oB1 pB1 && (
  fsPreK2L w4 (itemK2 P20 shMain mainHeadB2) q1 q1 == (R.drop 72).take 4 && (
  offK2L w4 (itemK2 P20 shMain mainHeadB2) q1 == capR st R 2 && (
  w5.take (2 ^ 9) == List.replicate (2 ^ 9) eBytes && (
  lvOffS st 0 == 0 && (lvOffS st 1 == 41 && (lvOffS st 2 == 71 && (
  lvOffS st 2 + ((mainLS st 2).fold - 1) == 74 && (
  st.hb % 8 == 0 && (capR st R 0 % 8 == 0 && (capR st R 1 % 8 == 0 && (capR st R 2 % 8 == 0 && (
  decide ((if st.p.leafOut then hdrFixS else hdrFix) ≤ st.hb) && (decide (8 ≤ st.hb) && (decide (st.occ0 ≤ 64) && (
  decide (o1S st ≤ st.pz) && (decide (capR st R 0 + 32 * 2 ^ 7 ≤ st.pz) && (
  decide (capR st R 1 + 32 * 2 ^ 7 ≤ st.pz) && decide (capR st R 2 + 24 * 2 ^ 9 ≤ st.pz))))))))))))))))))))))))

/-- **The run-length checker** at a split `st.items = pre ++ rest` (`pre`: the root cap and the middle phases): the
first item has no reads or messages and ends at `o1S`; the middle items `pre.drop 1` are reads and samples, walked
once by runs; `A1`'s slices; `replayOkG` at the walk's end, with the messages of `rest` from there. -/
def replayOkR (st : XStage) (pre rest : List Item) : Bool :=
  let e := endF st.p (pre.drop 1) (o1S st) st.hb
  let ws := rest.flatMap wsI
  let R := Lvm.X.fsPre st.p rest e.1 e.2
  let kA := itemK2 P20 shMain mainHeadA1
  !pre.isEmpty && (
  ((pre.take 1).flatMap wsI).isEmpty && (
  (Lvm.X.fsPre st.p (pre.take 1) st.hb st.hb).isEmpty && (
  endF st.p (pre.take 1) st.hb st.hb == (o1S st, st.hb) && (
  RSItemsF (pre.drop 1) && (
  fsPreK2L ws kA e.1 e.2 == R.take 7 &&
  replayOkG st (ws.drop (readsK2 kA)) (offK2L ws kA e.1) (pendK2L ws kA e.1 e.2) (sampR (pre.drop 1)) R)))))

theorem getD_msgs (x : ℕ × ℕ) (F R : List (ℕ × ℕ)) (k : ℕ) :
    (x :: (F ++ R)).getD (F.length + 1 + k) (0, 0) = R.getD k (0, 0) := by
  rw [List.getD_eq_getElem?_getD, show F.length + 1 + k = F.length + k + 1 by (clear * - F k; omega), List.getElem?_cons_succ,
    List.getElem?_append_right (Nat.le_add_right _ _), Nat.add_sub_cancel_left, ← List.getD_eq_getElem?_getD]

theorem drop_msgs (x : ℕ × ℕ) (F R : List (ℕ × ℕ)) (k : ℕ) :
    (x :: (F ++ R)).drop (F.length + 1 + k) = R.drop k := by
  rw [show F.length + 1 + k = F.length + k + 1 by (clear * - F k; omega), List.drop_succ_cons, List.drop_append,
    List.drop_eq_nil_of_le (Nat.le_add_right _ _), List.nil_append, Nat.add_sub_cancel_left]

/-- `replayOkG` at the stage's own `A1` values gives `ReplayOK`, the chain's messages being `F ++ R` after the seed
with `F` the middle phases' (`nMidS st = nPreS st = |F|`). -/
theorem replayOK_ofG {st : XStage} (F R : List (ℕ × ℕ)) (rs : RSItemsF (midItemsS st) = true)
    (fA1 : fsPreK2L (readWidthsS st) (kA1S st) (o1S st) st.hb = ((fsMsgsS st).drop 1).take (nMidS st + 7))
    (hmsg : fsMsgsS st = (8, st.hb - 8) :: (F ++ R)) (hnM : nMidS st = F.length) (hnP : nPreS st = F.length)
    (h : replayOkG st ((readWidthsS st).drop (nr1 st)) (offA1 st) (pendA1 st) F.length R = true) :
    ReplayOK st := by
  have hfp : ∀ i j, foldPosS st i j = F.length + 1 + (2 + lvOffS st i + j) := fun i j => by
    rw [show foldPosS st i j = nPreS st + 3 + lvOffS st i + j from rfl, hnP]; (clear * - F st i j; omega)
  have hc : ∀ i, (fsMsgsS st).getD (foldPosS st i ((mainLS st i).fold - 1)) (0, 0) =
      R.getD (2 + lvOffS st i + ((mainLS st i).fold - 1)) (0, 0) := fun i => by
    rw [hfp, hmsg, getD_msgs]
  have hc1 : capOffS st 1 = capR st R 0 := congrArg (·.1 + 2 * eBytes) (hc 0)
  have hc2 : capOffS st 2 = capR st R 1 := congrArg (·.1 + 2 * eBytes) (hc 1)
  have hcr : resOffS st = capR st R 2 := by
    rw [resOffS, nChainS, Nat.add_sub_cancel]; exact congrArg (·.1 + 2 * eBytes) (hc 2)
  have hd : ∀ k n, n = nMidS st + 1 + k → (fsMsgsS st).drop n = R.drop k := fun k n hn => by
    rw [hn, hmsg, hnM, drop_msgs]
  simp only [replayOkG, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, List.drop_drop] at h
  obtain ⟨oA1, fA2, oA2, fB1, oB1, fA3, oA3, fB2, oB2, r24, l0, l1, l2, l3, a0, a1, a2, ar, hl, h8, oc,
    s0, s1, s2, sr⟩ := h
  refine ⟨rs, fA1, by rw [hc1]; exact oA1, by rw [hd 7 _ (by (clear * - st F R; omega))]; exact fA2, oA2,
    by rw [hd 42 _ (by (clear * - st F R; omega))]; exact fB1, by rw [hc2]; exact oB1, by rw [hd 46 _ (by (clear * - st F R; omega))]; exact fA3, oA3,
    by rw [hd 72 _ (by (clear * - st F R; omega))]; exact fB2, by rw [hcr]; exact oB2, r24, ?_, ?_, ?_, ?_, a0, by rw [hc1]; exact a1,
    by rw [hc2]; exact a2, by rw [hcr]; exact ar, hl, h8, oc, s0, by rw [hc1]; exact s1, by rw [hc2]; exact s2,
    by rw [hcr]; exact sr⟩
  · have := hfp 0 0; (clear * - st F R hnM hnP l0 this; omega)
  · have := hfp 1 0; (clear * - st F R hnM hnP l1 this; omega)
  · have := hfp 2 0; (clear * - st F R hnM hnP l2 this; omega)
  · have := hfp 2 ((mainLS st 2).fold - 1); rw [nChainS]; (clear * - st F R hnM hnP l2 l3 this; omega)

/-- **The run-length checker gives the replay's facts** (every stage, at any split of its items with `pre` of
length `st.nOpen`). -/
theorem replayOK_ofR {st : XStage} {pre rest : List Item} (hs : st.items = pre ++ rest)
    (hn : st.nOpen = pre.length) (h : replayOkR st pre rest = true) : ReplayOK st := by
  simp only [replayOkR, Bool.and_eq_true, beq_iff_eq, List.isEmpty_iff] at h
  obtain ⟨-, hw1, hf1, he1, rs, fA, hG⟩ := h
  have hmid : midItemsS st = pre.drop 1 := by rw [midItemsS, hs, hn, List.take_append_length]
  have hrest : st.items.drop st.nOpen = rest := by rw [hs, hn, List.drop_left' rfl]
  have hpre : pre = pre.take 1 ++ pre.drop 1 := (List.take_append_drop 1 pre).symm
  rw [← hmid] at rs fA hG
  rw [← hmid] at hpre
  have hW : readWidthsS st = (midItemsS st).flatMap wsI ++ rest.flatMap wsI := by
    rw [readWidthsS_eq, hs, hpre, List.flatMap_append, List.flatMap_append, hw1, List.nil_append]
  obtain ⟨ho, hp, hf, hr⟩ := K2L_items st.p shMain (midItemsS st) (rest.flatMap wsI)
    (itemK2 P20 shMain mainHeadA1) (o1S st) st.hb rs
  have hoA : offA1 st = offK2L (rest.flatMap wsI) (itemK2 P20 shMain mainHeadA1)
      (endF st.p (midItemsS st) (o1S st) st.hb).1 := by
    rw [offA1, hW]; exact ho
  have hpA : pendA1 st = pendK2L (rest.flatMap wsI) (itemK2 P20 shMain mainHeadA1)
      (endF st.p (midItemsS st) (o1S st) st.hb).1 (endF st.p (midItemsS st) (o1S st) st.hb).2 := by
    rw [pendA1, hW]; exact hp
  have hnr : (readWidthsS st).drop (nr1 st) = (rest.flatMap wsI).drop (readsK2 (itemK2 P20 shMain mainHeadA1)) := by
    rw [show nr1 st = readsK2 (itemK2F st.p shMain (midItemsS st) ++ itemK2 P20 shMain mainHeadA1) from rfl, hr, hW,
      List.drop_append, List.drop_eq_nil_of_le (Nat.le_add_right _ _), List.nil_append, Nat.add_sub_cancel_left]
  have hpreF : Lvm.X.fsPre st.p pre st.hb st.hb = Lvm.X.fsPre st.p (midItemsS st) (o1S st) st.hb := by
    rw [hpre, fsPre_append, hf1, he1, List.nil_append]
  have hfs : Lvm.X.fsPre st.p st.items st.hb st.hb = Lvm.X.fsPre st.p (midItemsS st) (o1S st) st.hb ++
      Lvm.X.fsPre st.p rest (endF st.p (midItemsS st) (o1S st) st.hb).1
        (endF st.p (midItemsS st) (o1S st) st.hb).2 := by
    have hend : endF st.p pre st.hb st.hb = endF st.p (midItemsS st) (o1S st) st.hb := by
      rw [hpre, endF_append, he1]
    rw [hs, fsPre_append, hpreF, hend]
  have hlen : (Lvm.X.fsPre st.p (midItemsS st) (o1S st) st.hb).length = sampR (midItemsS st) :=
    fsPre_length_rs _ _ _ _ rs
  have hnM : nMidS st = (Lvm.X.fsPre st.p (midItemsS st) (o1S st) st.hb).length := by
    rw [hlen]; exact count_sample_rs _ rs
  have hmsg : fsMsgsS st = (8, st.hb - 8) :: (Lvm.X.fsPre st.p (midItemsS st) (o1S st) st.hb ++
      Lvm.X.fsPre st.p rest (endF st.p (midItemsS st) (o1S st) st.hb).1
        (endF st.p (midItemsS st) (o1S st) st.hb).2) := by
    rw [fsMsgsS, hfs]
  have hnP : nPreS st = (Lvm.X.fsPre st.p (midItemsS st) (o1S st) st.hb).length := by
    rw [nPreS, hs, hn, List.take_append_length, hpreF]
  have hle : (Lvm.X.fsPre st.p (midItemsS st) (o1S st) st.hb).length ≤ nMidS st + 7 := by
    rw [hnM]; exact Nat.le_add_right _ _
  have fA1 : fsPreK2L (readWidthsS st) (kA1S st) (o1S st) st.hb = ((fsMsgsS st).drop 1).take (nMidS st + 7) := by
    rw [hW]
    refine hf.trans ?_
    rw [hmsg, List.drop_one, List.tail_cons, fA, List.take_append, List.take_of_length_le hle, hnM,
      Nat.add_sub_cancel_left]
  refine replayOK_ofG _ _ rs fA1 hmsg hnM hnP ?_
  rw [hnr, hoA, hpA, hlen]
  exact hG

end Lvm.ASM
