-- New for `flock-recursive` (BLUEPRINT §5.4, §6.2; S-H2 Part 19 deviation 2; stage S-N1).
import FRSoundnessExtStmt
import FRXNodeRun

/-!
# `E_node`'s chain links from the run (S-H2 Part 19 §6, deviation 2)

`E_node` takes the links between the transcript `es` the extractor decodes and the log `L` and
proof `π` as hypotheses. On the **run's own chain** (`SkRun`: `es = fsOf tr items`, the queries
are `fsQ vk c π`'s) with `¬ Bad L` and Ligerito's output, each link holds:

| link | lemma |
|---|---|
| `fmAns (fsQ (vkOf π) c π) st₀ L p = some (ansAt es p)` | **`fmAns_of_run`** (no repeated query; `vkOf_of_run`) |
| `capDig es 0 e = capPi π e`, `capDig es i e = capPiL i π e` | **`cap0_of_run`**, **`capL_of_run`** (`capDig_eq`) |
| `finalAt es x = finPi π x` | **`final_of_run`** (`finalAt_fsQ`) |
| `¬ StateHit L` | `¬ Bad L` |
| `¬ farL`, `consSet = jointAgree` | `LigeritoOut.close`, `.agree` |

**`E_node_of_run`** assembles them: `E c π L = some (readWit (fF .N30 L es))`.
-/

namespace FR.Snd
open RecursionFast Finset

set_option linter.constructorNameAsVariable false

variable {impl : OpImpl} {vk c : Digest} {π : Proof} {tr : Trace}
  {y : List Val × List Bool × Trace}

/-- In a log without repeated queries, the first match of an entry's query is its answer. -/
theorem findSnd_of_mem {L : Log} (hL : (L.map Prod.fst).Nodup) {e : ByteArray × Digest}
    (he : e ∈ L) : (L.find? fun x => decide (x.1 = e.1)).map Prod.snd = some e.2 := by
  rw [find_of_mem hL he]; rfl

/-- **The forward chain of first matches is the run's chain** (`E_node`'s `hfm`). -/
theorem fmAns_of_run {L : Log} (h : SkRun impl .N30 ⟨vk, c, π⟩ tr y) (hb : ¬ Bad L)
    (hin : ∀ e ∈ tr, e ∈ L) (st₀ : Digest) :
    ∀ p < 468, X.fmAns (X.fsQ (X.vkOf π) c π) st₀ L p = some (ansAt (fsOf tr items) p) := by
  have hvk := vkOf_of_run h
  rw [hvk]
  have hnd : (L.map Prod.fst).Nodup := by
    by_contra hr; exact hb (Or.inr (Or.inr (Or.inr hr)))
  have hlen := h.len
  have hmem : ∀ p < 468, (fsOf tr items).getD p default ∈ L := fun p hp =>
    by
    rw [List.getD_eq_getElem _ _ (by omega)]
    exact hin _ (mem_fsOf (List.getElem_mem _))
  intro p
  induction p with
  | zero =>
    intro _
    have hq := h.hq 0 (by norm_num)
    have e0 : X.fsQ vk c π 0 st₀ = X.fsQ vk c π 0 ((fsOf tr items).getD (0 - 1) default).2 := by
      simp only [X.fsQ, X.fsMsgs_ctl.1, ite_true]
    rw [X.fmAns, e0, ← hq]
    exact findSnd_of_mem hnd (hmem 0 (by norm_num))
  | succ p ih =>
    intro hp
    rw [X.fmAns, ih (by omega), Option.bind_some]
    have hq := h.hq (p + 1) hp
    rw [Nat.add_sub_cancel] at hq
    rw [show ansAt (fsOf tr items) p = ((fsOf tr items).getD p default).2 from rfl, ← hq]
    exact findSnd_of_mem hnd (hmem (p + 1) hp)

/-- **Level 0's cap on the log is π's** (`E_node`'s `hcap0`). -/
theorem cap0_of_run (h : SkRun impl .N30 ⟨vk, c, π⟩ tr y) :
    ∀ e < 2 ^ 9, capDig (fsOf tr items) 0 e = X.capPi π e := by
  intro e he
  rw [capDig_eq h.hq (by norm_num) (by simpa [X.capLogL] using he), capOff_abs (by norm_num),
    X.capPi]
  rfl

/-- **Levels 1–4's caps on the log are π's** (`E_node`'s `hcap`). -/
theorem capL_of_run (h : SkRun impl .N30 ⟨vk, c, π⟩ tr y) :
    ∀ i, 1 ≤ i → i ≤ 4 → ∀ e < 2 ^ X.capLogL i, capDig (fsOf tr items) i e = X.capPiL i π e := by
  intro i _ hi e he
  rw [capDig_eq h.hq (by omega) he, capOff_abs (by omega), X.capPiL]

/-- **The final message on the log is π's** (`E_node`'s `hfin`). -/
theorem final_of_run (h : SkRun impl .N30 ⟨vk, c, π⟩ tr y) :
    ∀ x < 32, finalAt (fsOf tr items) x = X.finPi π x := by
  intro x hx
  rw [finalAt_fsQ h.hq (by omega), finV, X.finPi, chK, absOff_eq (by decide)]
  rfl

/-- `f⁽⁰⁾` of a node is its level-0 messages read row-major (`(lvl .N30 0).rows = 64`). -/
theorem fF_N30 (L es : Log) :
    fF .N30 L es = fun e => (msgOf .N30 L es 0 (e % 64) (e / 64)).f₀ := by
  have h : (lvl .N30 0).rows = 64 := by decide
  funext e; simp only [fF, fTab, h]

/-- **`E_node` on the run's chain**: with the run's links, `¬ Bad`, Ligerito's output and the
extractor's domain, the extractor returns `readWit` of the decoded `f⁽⁰⁾`. -/
theorem E_node_of_run {L : Log} {W₀ : Log → Log → ℕ → K} {c₀ : Log → Log → K}
    (h : SkRun impl .N30 ⟨vk, c, π⟩ tr y) (hb : ¬ Bad L) (hin : ∀ e ∈ tr, e ∈ L)
    (hk : FR.kindOf π = .snark .N30) (hD : InDom c π L)
    (hLig : LigeritoOut W₀ c₀ L (fsOf tr items)) {A : Digest → Digest → Signed → Bool} :
    X.E A c π L = some (FR.readWit (fF .N30 L (fsOf tr items))) := by
  have hkc : kindOf (fsOf tr items) = .N30 := kindOf_chain h.hq hk
  have hS : ¬ StateHit L := fun hs => hb (Or.inr (Or.inr (Or.inl hs)))
  have hE := X.E_node A c π L hD.1 hD.2 hk hS zeroD (es := fsOf tr items)
    (fun p hp => fmAns_of_run h hb hin zeroD p (by unfold X.nRep at hp; omega))
    (cap0_of_run h) (capL_of_run h) (final_of_run h)
    (fun i hi => hkc ▸ hLig.close i hi) (fun i hi => hkc ▸ hLig.agree i hi)
  rw [hE, fF_N30]

end FR.Snd
