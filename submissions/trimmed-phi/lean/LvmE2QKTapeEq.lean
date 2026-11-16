-- New for lvm2 E2F (E2F-QH4): the tape GKR at `E2` (phase CHtape): `V`'s `tapeGkrD (P + 5)` (`LvmDecideE2`) replayed by
-- `tapeGadgetE2` (`LvmE2QKGkr`); the loop of `E2` layers (`layers2_spec`), shared with the `KS` GKR. The `E2`
-- counterpart of `LvmQEqKeccakTape`; the field-agnostic loop/relocation/rank facts are `LvmQEqKeccakGkr`'s.
import LvmE2QKLayerEq
import LvmQEqKeccakTape
import LvmQAsmHarTop

/-!
# The tape GKR at `E2`

* **`V` side.** `chain2 v va io C₀ p L k`: `V`'s claim after `k` layers (layer `k` with the `ι` term `io k`, read at
  `p + k·L`, `layerSpec2`); `lay2At` its layer `k`; `chain2_add` (two runs are one).
* **`layers2_spec`**: a loop `[d]` of the relocated `E2` layer template (`layTpl2`) with `N ≤ 2^d` real layers
  (constants: round-constant bits, the first flag, the gate) carries `chain2 … N` in the copy rows of iteration
  `N − 1`; with the gate `1` its assertions hold iff every real layer's two checks do (the rest gated off).
  Its layout facts come from `layOk2 P` (decided per `P`).
* The first claim (`preTBT2_spec`, `rep_firstT2`), the copy block (`cp2_spec`), the loop's last copy rows
  (`lay_last_cell2`); **`tape_core2`**: the tape gadget's carried cells represent `chain2 … 24` from `V`'s first claim.
* **`tapeGkrD_run`** (`V`'s tape GKR on a view: `samplesG_run`, `keccakLayersD_run`, `chainOk2`); the
  proof-of-work flags by answer lane (`PowOkV`, `layer_pw`); **`tape_spec2`**: `V`'s `tapeGkrD (P + 5)` replayed by
  `tapeGadgetE2` (claim, end position, flag ⇔ flag before ∧ `PowOkV (tapeChals2 P qs)` ∧ the gadget's assertions);
  **`tape_phase2`**: the same as a `PhaseAt` fact.
-/

set_option autoImplicit false

namespace Lvm.Q1

open Lvm Lvm.Loop Lvm.Loop.Build Lvm.E2V DM

/-! ## `V`'s chain of layers on a view -/

/-- `V`'s claim after `k` layers from `C₀` (layer `k` with the `ι` term `io k`, at `p + k·L`). -/
def chain2 (v : Nat → FE2) (va : Nat → FE) (io : Nat → KClaim FE2 → FE2) (C₀ : KClaim FE2) (p L : Nat) :
    Nat → KClaim FE2
  | 0 => C₀
  | k + 1 => (layerSpec2 v va (io k) (chain2 v va io C₀ p L k) (p + k * L)).claim

/-- Layer `k` of the chain. -/
def lay2At (v : Nat → FE2) (va : Nat → FE) (io : Nat → KClaim FE2 → FE2) (C₀ : KClaim FE2) (p L k : Nat) :
    LayerOut2 :=
  layerSpec2 v va (io k) (chain2 v va io C₀ p L k) (p + k * L)

theorem chain2_succ (v : Nat → FE2) (va : Nat → FE) (io : Nat → KClaim FE2 → FE2) (C₀ : KClaim FE2) (p L k : Nat) :
    chain2 v va io C₀ p L (k + 1) = (lay2At v va io C₀ p L k).claim := rfl

/-- Two consecutive runs of the chain are one. -/
theorem chain2_add (v : Nat → FE2) (va : Nat → FE) (io : Nat → KClaim FE2 → FE2) (C₀ : KClaim FE2) (p L n : Nat) :
    ∀ k, chain2 v va io C₀ p L (n + k) =
      chain2 v va (fun j => io (n + j)) (chain2 v va io C₀ p L n) (p + n * L) L k
  | 0 => rfl
  | k + 1 => by
    show (layerSpec2 v va (io (n + k)) (chain2 v va io C₀ p L (n + k)) (p + (n + k) * L)).claim =
      (layerSpec2 v va (io (n + k)) (chain2 v va (fun j => io (n + j)) (chain2 v va io C₀ p L n) (p + n * L) L k)
        (p + n * L + k * L)).claim
    rw [chain2_add v va io C₀ p L n k, show p + (n + k) * L = p + n * L + k * L by ring]

theorem lay2At_add (v : Nat → FE2) (va : Nat → FE) (io : Nat → KClaim FE2 → FE2) (C₀ : KClaim FE2) (p L n k : Nat) :
    lay2At v va io C₀ p L (n + k) =
      lay2At v va (fun j => io (n + j)) (chain2 v va io C₀ p L n) (p + n * L) L k := by
  unfold lay2At
  rw [chain2_add, show p + (n + k) * L = p + n * L + k * L by ring]

/-! ## The relocated `E2` layer template -/

theorem evalF2_reloc (xv : Src → FE) (V : Nat → FE) (q cst : Nat) (i : Ins) :
    (relocI q cst i).evalF2 xv V = i.evalF2 (fun s => xv (relocS q cst s)) V := by
  unfold Ins.evalF2
  have e : (relocI q cst i).op = i.op := rfl
  rw [e]
  split
  · simp only [relocI, getD_map_default (relocS q cst) rfl, relocS_valF]
  · exact evalF_reloc xv V q cst i

theorem thold2_reloc {xv : Src → FE} {V : Nat → FE} {n q cst : Nat} {δ : List Ins}
    (h : THold2 xv V n (δ.map (relocI q cst))) : THold2 (fun s => xv (relocS q cst s)) V n δ := by
  intro k hk ha
  have ha' : ((δ.map (relocI q cst)).getD k default).arith2 := by
    rw [reloc_getD]
    rcases ha with ha | ⟨f, hh, he⟩
    · exact Or.inl ha
    · exact Or.inr ⟨f, hh, he⟩
  have := h k (by simpa using hk) ha'
  rw [this, reloc_getD, evalF2_reloc]

/-- The rows from `cb` on each write one `K` cell: their ranks are consecutive up to the end. -/
theorem lrank_suffixK {δ : List Ins} {cb C : Nat} (hl : δ.length = cb + C)
    (h : ∀ i ∈ δ.drop cb, Row.w .K ⟨i.op, i.ty, []⟩ = 1) {j : Nat} (hj : j ≤ C) :
    lrank .K (tplOf δ) (cb + j) + C = ltw .K (tplOf δ) + j := by
  have hδ : δ = δ.take cb ++ δ.drop cb := (List.take_append_drop cb δ).symm
  have hd : (δ.drop cb).length = C := by rw [List.length_drop]; (clear * - hl; omega)
  have ht : (δ.take cb).length = cb := by rw [List.length_take]; (clear * - hl; omega)
  rw [lrank_tplOf, ltw_tplOf, hδ, List.take_append, ht, show cb + j - cb = j by (clear * -; omega),
    List.take_of_length_le (by (clear * - ht; omega) : (δ.take cb).length ≤ cb + j), List.map_append, List.map_append,
    List.sum_append, List.sum_append, sum_ones h, sum_ones (fun i hi => h i (List.mem_of_mem_take hi)),
    List.length_take, hd]
  (clear * - hj; omega)

theorem rep2_congr {P : Nat} {cv cv' : Nat → FE2} {C : KClaim FE2} {f : Bool} (h : Rep2 P cv C f)
    (e : ∀ j < 57 + P, cv j = cv' j) : Rep2 P cv' C f := by
  have hB : repB2 P cv = repB2 P cv' := List.map_congr_left fun l hl => e _ (by simp at hl; (clear * - hl; omega))
  have hA : repA2 P cv = repA2 P cv' := List.map_congr_left fun l hl => e _ (by simp at hl; (clear * - hl; omega))
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [← e 0 (by (clear * -; omega))]; exact h.value
  · rw [← h.mu]; exact (List.map_congr_left fun i hi => e _ (by simp at hi; (clear * - hi; omega))).symm
  · rw [← e 17 (by (clear * -; omega))]; exact h.kappa
  · rw [← h.point]; exact (List.map_congr_left fun i hi => e _ (by simp at hi; (clear * - hi; omega))).symm
  · rw [h.weights, hB, hA]
  · intro i hi; rw [← e _ (by (clear * - hi; omega)), h.flips i hi, hB, hA]

theorem relocS_k2 (P q cst j : Nat) : relocS q cst ((lay02 P).k j) = .ext ⟨.K, cst + (0 + j), [16]⟩ := by
  simp [LCfg.k, lay02, relocS]

/-- The carried claim of the `E2` layer loop at iteration `k`: the `2C` `K` cells before the loop (`k = 0`), the
copy rows of iteration `k − 1`. -/
def layCv2 (M : Mem) (o : LoopOut) (C cb : Nat) : Nat → Nat → FE2
  | 0, j => ⟨M.k (o.p.k - 2 * C + 2 * j), M.k (o.p.k - 2 * C + 2 * j + 1)⟩
  | k + 1, j => (o.cell2 (cb + 2 * j) k).val M

theorem cell2_val (M : Mem) (o : LoopOut) (t jf : Nat) :
    (o.cell2 t jf).val M = ⟨((o.cell t jf).val M).c₀, ((o.cell (t + 1) jf).val M).c₀⟩ := rfl

/-- A carried input's value at iteration `jf` (proof help for `layers2_spec`: generic, so the kernel checks it without
the template). -/
private theorem valF_prev_iter (M : Mem) (o : LoopOut) (jf q cst k : Nat) (V : Nat → FE) :
    (Src.prev k).valF (fun s => iterXv M o jf (relocS q cst s)) V = (Opd.prev k).val M o jf := rfl

/-- **A loop of `E2` layers** (the loop `[d]` of the relocated template, `N ≤ 2^d` real layers, the rest gated
off): with layer `k`'s constants the bits of `rc0 k`, `rc1 k` (slots `0–13`), the first flag in slot `14` and the
gate `β` in slot `15` (`0` past `N`), and the claim `C₀` in the `2C` cells before the loop, the copy rows of
iteration `N − 1` represent `V`'s claim after `N` layers; with `β = 1` the assertions hold iff all of the
layers' checks do. -/
theorem layers2_spec {c : Ctx} {M : Mem} {pL : Ptr} {P q cst d : Nat} {sig : ByteArray} {T : Nat}
    (hP : layOk2 P = true) (h : SegsHold c M pL (loop [d] (layTpl2 P q cst) pL).2)
    (hS : Streamed M sig T) {N : Nat} (hT : q + N * (lay02 P).str2 + 2 ≤ T) (hq : 5 ≤ q)
    (hN1 : 1 ≤ N) (hN : N ≤ 2 ^ d)
    {io : Nat → KClaim FE2 → FE2} {rc0 rc1 : Nat → UInt64}
    (hrcm : ∀ k < N, rc0 k ∈ keccakRC ∧ rc1 k ∈ keccakRC)
    (hio : ∀ k < N, ∀ C : KClaim FE2, C.point.length = P + 1 →
      io k C = (1 + C.point.getD P 0) * iotaFG (rc0 k) C.weights + C.point.getD P 0 * iotaFG (rc1 k) C.weights)
    {first0 : Bool} {β : FE}
    (hcst : ∀ jf < N, (∀ i < 7, FE.ofK (M.k (cst + (16 * jf + i))) = rcBit (rc0 jf) i ∧
      FE.ofK (M.k (cst + (16 * jf + (7 + i)))) = rcBit (rc1 jf) i) ∧
      FE.ofK (M.k (cst + (16 * jf + 14))) = if (first0 && jf == 0) = true then 1 else 0)
    (hgate : ∀ jf < 2 ^ d, FE.ofK (M.k (cst + (16 * jf + 15))) = if jf < N then β else 0)
    {C0 : KClaim FE2} (hpk : 2 * (57 + P) ≤ pL.k)
    (h0 : Rep2 P (layCv2 M ⟨pL, [d], layTpl2 P q cst⟩ (57 + P) (cbOf2 P) 0) C0 first0) :
    Rep2 P (fun j => ((loop [d] (layTpl2 P q cst) pL).1.cell2 (cbOf2 P + 2 * j) (N - 1)).val M)
      (chain2 (fe2At sig) (feAt sig) io C0 (8 * q - 40) (8 * (lay02 P).str2) N) false ∧
    (β = 1 → (SegsAssert M pL (loop [d] (layTpl2 P q cst) pL).2 ↔
      ∀ k < N, (lay2At (fe2At sig) (feAt sig) io C0 (8 * q - 40) (8 * (lay02 P).str2) k).ok1 = true ∧
        (lay2At (fe2At sig) (feAt sig) io C0 (8 * q - 40) (8 * (lay02 P).str2) k).ok2 = true)) := by
  have hok := hP
  simp only [layOk2, Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at hok
  obtain ⟨⟨hlen, hgateAll⟩, hsuf⟩ := hok
  have hcb : (lay02 P).cb + 2 * (57 + (lay02 P).P) = (layerTB2 (lay02 P) 0).2.length := by
    show cbOf2 P + 2 * (57 + P) = (layIns2 P).length; rw [hlen]
  have hw : ∀ i ∈ (layIns2 P).drop (cbOf2 P), Row.w .K ⟨i.op, i.ty, []⟩ = 1 := by
    intro i hi
    have := hsuf i hi
    try simp only [Bool.and_eq_true, beq_iff_eq, bne_iff_ne, ne_eq] at this
    obtain ⟨h1, h2⟩ := this
    have hwr : Row.writes ⟨i.op, i.ty, []⟩ = some .K := by
      unfold Row.writes; cases hop : i.op <;> simp_all
    simp [Row.w, hwr]
  have hrank : ∀ j ≤ 2 * (57 + P), lrank .K (layTpl2 P q cst) (cbOf2 P + j) + 2 * (57 + P) =
      ltw .K (layTpl2 P q cst) + j := by
    intro j hj; rw [layTpl2, lrank_reloc, ltw_reloc]; exact lrank_suffixK hlen hw hj
  have hty : ∀ j < 2 * (57 + P), ((layTpl2 P q cst).getD (cbOf2 P + j) default).ty = .K := by
    intro j hj
    rw [layTpl2, tplOf_getD _ (by rw [List.length_map, hlen]; (clear * - hj; omega)), reloc_getD, relocI_toLRow_ty]
    have hm : (layIns2 P).getD (cbOf2 P + j) default ∈ (layIns2 P).drop (cbOf2 P) := by
      rw [show (layIns2 P).getD (cbOf2 P + j) default = ((layIns2 P).drop (cbOf2 P)).getD j default by
        simp [List.getD_eq_getElem?_getD]]
      rw [List.getD_eq_getElem _ _ (by simp; (clear * - hlen hj; omega))]; exact List.getElem_mem _
    have := hsuf _ hm
    try simp only [Bool.and_eq_true, beq_iff_eq] at this
    exact this.1
  have hO : (loop [d] (layTpl2 P q cst) pL).1 = ⟨pL, [d], layTpl2 P q cst⟩ := rfl
  have hdims : (⟨pL, [d], layTpl2 P q cst⟩ : LoopOut).dims = [d] := rfl
  rw [hO]
  have hH : ∀ jf < 2 ^ d, THold2 (fun s => iterXv M ⟨pL, [d], layTpl2 P q cst⟩ jf (relocS q cst s))
      (iterF M ⟨pL, [d], layTpl2 P q cst⟩ jf) 0 (layIns2 P) := by
    intro jf hjf
    have := thold2_of_loop (dims := [d]) (ins := (layIns2 P).map (relocI q cst)) (p := pL) h (jf := jf)
      (by simpa using hjf)
    exact thold2_reloc this
  have hk : ∀ jf < 2 ^ d, ∀ j < 16,
      (fun s => iterXv M ⟨pL, [d], layTpl2 P q cst⟩ jf (relocS q cst s)) ((lay02 P).k j) =
        FE.ofK (M.k (cst + (16 * jf + j))) := by
    intro jf hjf j _
    show iterXv M _ jf (relocS q cst ((lay02 P).k j)) = _
    rw [relocS_k2 P, iterXv_ext1 M _ hdims (by simpa using hjf)]
    show FE.ofK (M.k _) = _
    rw [show cst + (0 + j) + 16 * jf = cst + (16 * jf + j) by (clear * -; omega)]
  have hstr : (lay02 P).str2 ≠ 16 := by simp only [lay02, LCfg.str2]; (clear * -; omega)
  have hv : ∀ jf < N, ∀ m < (lay02 P).q + (lay02 P).str2,
      lv2 (fun s => iterXv M ⟨pL, [d], layTpl2 P q cst⟩ jf (relocS q cst s)) [(lay02 P).str2] m =
        fe2At sig (8 * m + 8 * (q + (lay02 P).str2 * jf)) := by
    intro jf hjf m hm
    have hm' : m < (lay02 P).str2 := by simpa [lay02] using hm
    have e : ∀ m', (fun s => iterXv M ⟨pL, [d], layTpl2 P q cst⟩ jf (relocS q cst s)) (.ext ⟨.K, m', [(lay02 P).str2]⟩) =
        FE.ofK (M.k (q + m' + (lay02 P).str2 * jf)) := by
      intro m'
      show iterXv M _ jf (relocS q cst (.ext ⟨.K, m', [(lay02 P).str2]⟩)) = _
      simp only [relocS, if_neg hstr]
      rw [iterXv_ext1 M _ hdims (by (clear * - hN hjf; omega))]
      rfl
    have hlt : q + m + (lay02 P).str2 * jf + 1 < T := by
      have : (lay02 P).str2 * jf + (lay02 P).str2 ≤ N * (lay02 P).str2 := by
        rw [Nat.mul_comm N]; exact (Nat.mul_succ _ _).symm ▸ Nat.mul_le_mul_left _ hjf
      (clear * - hT hm' this; omega)
    unfold lv2
    rw [e, e, show q + (m + 1) + (lay02 P).str2 * jf = q + m + (lay02 P).str2 * jf + 1 by (clear * -; omega),
      fe_ofK_c0, fe_ofK_c0, hS _ (by (clear * - hlt; omega)), hS _ hlt]
    show (⟨kAt sig (8 * (q + m + (lay02 P).str2 * jf)), kAt sig (8 * (q + m + (lay02 P).str2 * jf + 1))⟩ : FE2) =
      ⟨kAt sig (8 * m + 8 * (q + (lay02 P).str2 * jf)), kAt sig (8 * m + 8 * (q + (lay02 P).str2 * jf) + 8)⟩
    rw [show 8 * (q + m + (lay02 P).str2 * jf) = 8 * m + 8 * (q + (lay02 P).str2 * jf) by ring,
      show 8 * (q + m + (lay02 P).str2 * jf + 1) = 8 * m + 8 * (q + (lay02 P).str2 * jf) + 8 by ring]
  have hpv : ∀ jf < 2 ^ d, ∀ j < 57 + P,
      ((lay02 P).pv2 j).valF (fun s => iterXv M ⟨pL, [d], layTpl2 P q cst⟩ jf (relocS q cst s))
        (iterF M ⟨pL, [d], layTpl2 P q cst⟩ jf) =
      layCv2 M ⟨pL, [d], layTpl2 P q cst⟩ (57 + P) (cbOf2 P) jf j := by
    intro jf hjf j hj
    have hval : ∀ t, t < 2 * (57 + P) → (Src.prev (cbOf2 P + t)).valF
        (fun s => iterXv M ⟨pL, [d], layTpl2 P q cst⟩ jf (relocS q cst s)) (iterF M ⟨pL, [d], layTpl2 P q cst⟩ jf) =
        FE.ofK (M.k (pL.k + lrank .K (layTpl2 P q cst) (cbOf2 P + t) - ltw .K (layTpl2 P q cst) +
          ltw .K (layTpl2 P q cst) * jf)) := by
      intro t ht
      -- a `rw` with a generic lemma, not `show`: the kernel's defeq check of the `show` unfolded `Opd.val` first and
      -- ran the template at a symbolic `P` (18.4 M hb)
      rw [valF_prev_iter, Opd.val_prev M _ (by simpa using hjf), hty t ht]
      rfl
    have h1 := hval (2 * j) (by (clear * - hj; omega))
    have h2 := hval (2 * j + 1) (by (clear * - hj; omega))
    have hr1 := hrank (2 * j) (by (clear * - hj; omega))
    have hr2 := hrank (2 * j + 1) (by (clear * - hj; omega))
    show (⟨(Src.valF _ _ (.prev (cbOf2 P + 2 * j))).c₀, (Src.valF _ _ (.prev (cbOf2 P + 2 * j + 1))).c₀⟩ : FE2) = _
    rw [show cbOf2 P + 2 * j + 1 = cbOf2 P + (2 * j + 1) by (clear * -; omega), h1, h2, fe_ofK_c0, fe_ofK_c0]
    rcases jf with _ | jf
    · show _ = (⟨M.k (pL.k - 2 * (57 + P) + 2 * j), M.k (pL.k - 2 * (57 + P) + 2 * j + 1)⟩ : FE2)
      generalize lrank .K (layTpl2 P q cst) (cbOf2 P + 2 * j) = a at hr1 ⊢
      generalize lrank .K (layTpl2 P q cst) (cbOf2 P + (2 * j + 1)) = a' at hr2 ⊢
      generalize ltw .K (layTpl2 P q cst) = w at hr1 hr2 ⊢
      rw [show pL.k + a - w + w * 0 = pL.k - 2 * (57 + P) + 2 * j by (clear * - hpk hr1; omega),
        show pL.k + a' - w + w * 0 = pL.k - 2 * (57 + P) + 2 * j + 1 by (clear * - hpk hr2; omega)]
    · show _ = ((⟨pL, [d], layTpl2 P q cst⟩ : LoopOut).cell2 (cbOf2 P + 2 * j) jf).val M
      rw [cell2_val, LoopOut.cell_val, LoopOut.cell_val, show cbOf2 P + 2 * j + 1 = cbOf2 P + (2 * j + 1) by (clear * -; omega)]
      show _ = (⟨(M.rd ((layTpl2 P q cst).getD (cbOf2 P + 2 * j) default).ty _).c₀,
        (M.rd ((layTpl2 P q cst).getD (cbOf2 P + (2 * j + 1)) default).ty _).c₀⟩ : FE2)
      rw [hty _ (by (clear * - hj; omega)), hty _ (by (clear * - hj; omega))]
      show _ = (⟨(FE.ofK (M.k (pL.k + lrank .K (layTpl2 P q cst) (cbOf2 P + 2 * j) + ltw .K (layTpl2 P q cst) * jf))).c₀,
        (FE.ofK (M.k (pL.k + lrank .K (layTpl2 P q cst) (cbOf2 P + (2 * j + 1)) +
          ltw .K (layTpl2 P q cst) * jf))).c₀⟩ : FE2)
      rw [fe_ofK_c0, fe_ofK_c0]
      generalize lrank .K (layTpl2 P q cst) (cbOf2 P + 2 * j) = a at hr1 ⊢
      generalize lrank .K (layTpl2 P q cst) (cbOf2 P + (2 * j + 1)) = a' at hr2 ⊢
      generalize ltw .K (layTpl2 P q cst) = w at hr1 hr2 ⊢
      rw [show pL.k + a - w + w * (jf + 1) = pL.k + a + w * jf by rw [Nat.mul_succ]; (clear * - hpk hr1; omega),
        show pL.k + a' - w + w * (jf + 1) = pL.k + a' + w * jf by rw [Nat.mul_succ]; (clear * - hpk hr2; omega)]
  have hp : ∀ k < 2 ^ d, 8 * q - 40 + k * (8 * (lay02 P).str2) + 40 = 8 * (lay02 P).q + 8 * (q + (lay02 P).str2 * k) := by
    intro k _; simp only [lay02]; rw [Nat.mul_comm k]; ring_nf; (clear * - hq; omega)
  have hL : ∀ k < N, ∀ (C : KClaim FE2) (f : Bool),
      Rep2 P (layCv2 M ⟨pL, [d], layTpl2 P q cst⟩ (57 + P) (cbOf2 P) k) C f →
      f = (first0 && k == 0) → _ := fun k hkN C f hR hf =>
    layer2_spec (c := lay02 P) (hH k (by (clear * - hN hkN; omega))) hcb
      (rep2_congr hR (fun j hj => (hpv k (by (clear * - hN hkN; omega)) j hj).symm)) (hrcm k hkN).1 (hrcm k hkN).2
      (hio k hkN C (by rw [← hR.point, List.length_map, List.length_range]))
      (fun i hi => ⟨(hk k (by (clear * - hN hkN; omega)) i (by (clear * - hi; omega))).trans ((hcst k hkN).1 i hi).1,
        (hk k (by (clear * - hN hkN; omega)) (7 + i) (by (clear * - hi; omega))).trans ((hcst k hkN).1 i hi).2⟩)
      ((hk k (by (clear * - hN hkN; omega)) 14 (by (clear * -; omega))).trans ((hcst k hkN).2.trans (by rw [hf]))) (va := feAt sig) (fun o => rfl)
      (hv k (by (clear * - hkN; omega))) (hp k (by (clear * - hN hkN; omega)))
  have hrep : ∀ k ≤ N, Rep2 P (layCv2 M ⟨pL, [d], layTpl2 P q cst⟩ (57 + P) (cbOf2 P) k)
      (chain2 (fe2At sig) (feAt sig) io C0 (8 * q - 40) (8 * (lay02 P).str2) k) (first0 && k == 0) := by
    intro k
    induction k with
    | zero => intro _; rw [show (first0 && (0 == 0)) = first0 by simp]; exact h0
    | succ k ih =>
      intro hk'
      have := (hL k (by (clear * - hk'; omega)) _ _ (ih (by (clear * - hk'; omega))) rfl).1
      rw [show (first0 && (k + 1 == 0)) = false by simp]
      exact this
  have hd1 : 1 ≤ 2 ^ d := Nat.one_le_two_pow
  refine ⟨?_, fun hβ => ?_⟩
  · have := hrep N le_rfl
    rw [show (first0 && (N == 0)) = false by rw [Bool.and_eq_false_iff]; right; rw [beq_eq_false_iff_ne]; (clear * - hN1; omega)] at this
    obtain ⟨m, hm⟩ : ∃ m, N = m + 1 := ⟨N - 1, by (clear * - hN1; omega)⟩
    rw [hm] at this ⊢
    exact this
  have hgate0 : ∀ jf < 2 ^ d, N ≤ jf → TAssert (fun s => iterXv M ⟨pL, [d], layTpl2 P q cst⟩ jf (relocS q cst s))
      (iterF M ⟨pL, [d], layTpl2 P q cst⟩ jf) (layIns2 P) := by
    intro jf hjf hN' t ht ha
    have hm : (layIns2 P).getD t default ∈ layIns2 P := by
      rw [List.getD_eq_getElem _ _ ht]; exact List.getElem_mem ht
    have hg := hgateAll _ hm
    simp only [ha, bne_self_eq_false, Bool.false_or, beq_iff_eq] at hg
    rw [hg]
    show (fun s => iterXv M _ jf (relocS q cst s)) ((lay02 P).k 15) * _ = 0
    rw [hk jf hjf 15 (by (clear * -; omega)), hgate jf hjf, if_neg (by (clear * - hN'; omega)), zero_mul]
  change SegsAssert M pL (loop [d] (tplOf ((layIns2 P).map (relocI q cst))) pL).2 ↔ _
  rw [segsAssert_loop_iff]
  simp only [tassert_reloc]
  constructor
  · intro hA k hk'
    exact (hL k hk' _ _ (hrep k hk'.le) rfl).2.2.1 (hA k (by simpa using (show k < 2 ^ d by (clear * - hN hk'; omega))))
      (by rw [show iterXv M _ k (relocS q cst ((lay02 P).k 15)) = _ from hk k (by (clear * - hN hk'; omega)) 15 (by (clear * -; omega)),
        hgate k (by (clear * - hN hk'; omega)), if_pos hk', hβ])
  · intro hok jf hjf
    have hjf' : jf < 2 ^ d := by simpa using hjf
    by_cases hj : jf < N
    · exact (hL jf hj _ _ (hrep jf hj.le) rfl).2.2.2 (hok jf hj).1 (hok jf hj).2
    · exact hgate0 jf hjf' (by (clear * - hj; omega))

/-! ## `V`'s ground challenges and layers on a view -/

/-- `n` ground challenges from `p` (answer at `p + 48`, the next at `p + 80`). -/
def sampsG (va : Nat → FE) : Nat → Nat → List FE2
  | _, 0 => []
  | p, n + 1 => e2OfFE (va (p + 48)) :: sampsG va (p + 80) n

/-- Their proof-of-work checks. -/
def powsG (va : Nat → FE) (g : Nat) : Nat → Nat → Bool
  | _, 0 => true
  | p, n + 1 => powOKR g (va (p + 48)) && powsG va g (p + 80) n

theorem samplesG_succ (g n : Nat) :
    samplesG g (n + 1) = (sampleG g >>= fun x => samplesG g n >>= fun xs => pure (x :: xs)) := rfl

theorem samplesG_zero (g : Nat) : samplesG g 0 = pure [] := rfl

/-- **`V`'s ground challenges on a view**: values, position, flag. -/
theorem samplesG_run (sig : ByteArray) (g : Nat) : ∀ (n : Nat) (s : RS),
    samplesG g (n + 1) sig s = (sampsG (feAt sig) (s.ent + s.msg) (n + 1),
      ⟨s.ent + s.msg + 80 * (n + 1), 0, powsG (feAt sig) g (s.ent + s.msg) (n + 1) && s.ok⟩)
  | 0, ⟨e, m, o⟩ => by
    simp only [samplesG_succ, samplesG_zero, rdE_bind_run, sampleG_run, rdE_pure_run, sampsG, powsG, Bool.and_true]
  | n + 1, ⟨e, m, o⟩ => by
    rw [samplesG_succ]
    simp only [rdE_bind_run, sampleG_run]
    rw [samplesG_run sig g n]
    simp only [rdE_pure_run]
    rw [Prod.mk.injEq, RS.mk.injEq]
    refine ⟨rfl, by omega, rfl, ?_⟩
    show (powsG (feAt sig) g (e + m + 80 + 0) (n + 1) && (powOKR g (feAt sig (e + m + 48)) && o)) =
      ((powOKR g (feAt sig (e + m + 48)) && powsG (feAt sig) g (e + m + 80) (n + 1)) && o)
    rw [Nat.add_zero]
    cases powOKR g (feAt sig (e + m + 48)) <;> cases o <;> simp

theorem layerSpec2_pos (v : Nat → FE2) (va : Nat → FE) (io : KClaim FE2 → FE2) (C : KClaim FE2) (p : Nat) :
    (layerSpec2 v va io C p).pos = p + 2440 + 112 * C.point.length := by
  show packSpec2 v va gC3 C.point _ 1 (p + 904) |>.2.2.2.1 + LeanVM.Protocol.Verifier.keccakLocalBits * roundLen2 4 + 128 = _
  rw [packSpec2_pos, show LeanVM.Protocol.Verifier.keccakLocalBits = 11 from rfl]
  simp only [roundLen2]
  (clear * -; omega)

theorem layerSpec2_point_length (v : Nat → FE2) (va : Nat → FE) (io : KClaim FE2 → FE2) (C : KClaim FE2) (p : Nat) :
    (layerSpec2 v va io C p).claim.point.length = C.point.length :=
  packSpec2_length v va gC3 C.point _ 1 (p + 904)

/-- The checks of the first `n` layers of the chain (both checks and the proof-of-work flags). -/
def chainOk2 (v : Nat → FE2) (va : Nat → FE) (io : Nat → KClaim FE2 → FE2) (C₀ : KClaim FE2) (p L : Nat) : Nat → Bool
  | 0 => true
  | k + 1 => chainOk2 v va io C₀ p L k &&
    ((lay2At v va io C₀ p L k).ok1 && (lay2At v va io C₀ p L k).ok2 && (lay2At v va io C₀ p L k).pw)

theorem chain2_length (v : Nat → FE2) (va : Nat → FE) (io : Nat → KClaim FE2 → FE2) (C₀ : KClaim FE2) (p L : Nat) :
    ∀ k, (chain2 v va io C₀ p L k).point.length = C₀.point.length
  | 0 => rfl
  | k + 1 => by rw [chain2_succ, lay2At, layerSpec2_point_length, chain2_length v va io C₀ p L k]

theorem chainOk2_iff (v : Nat → FE2) (va : Nat → FE) (io : Nat → KClaim FE2 → FE2) (C₀ : KClaim FE2) (p L : Nat) :
    ∀ n, chainOk2 v va io C₀ p L n = true ↔ ∀ k < n, (lay2At v va io C₀ p L k).ok1 = true ∧
      (lay2At v va io C₀ p L k).ok2 = true ∧ (lay2At v va io C₀ p L k).pw = true
  | 0 => by simp [chainOk2]
  | n + 1 => by
    rw [chainOk2, Bool.and_eq_true, chainOk2_iff v va io C₀ p L n, Bool.and_eq_true, Bool.and_eq_true]
    constructor
    · rintro ⟨h1, ⟨h2, h3⟩, h4⟩ k hk
      rcases Nat.lt_or_ge k n with hk' | hk'
      · exact h1 k hk'
      · obtain rfl : k = n := by omega
        exact ⟨h2, h3, h4⟩
    · intro h
      exact ⟨fun k hk => h k (by omega), ⟨(h n (by omega)).1, (h n (by omega)).2.1⟩, (h n (by omega)).2.2⟩

theorem chainOk2_succ (v : Nat → FE2) (va : Nat → FE) (io : Nat → KClaim FE2 → FE2) (C₀ : KClaim FE2) (p L : Nat) :
    ∀ n, chainOk2 v va io C₀ p L (n + 1) =
      (((lay2At v va io C₀ p L 0).ok1 && (lay2At v va io C₀ p L 0).ok2 && (lay2At v va io C₀ p L 0).pw) &&
        chainOk2 v va (fun j => io (1 + j)) (chain2 v va io C₀ p L 1) (p + 1 * L) L n)
  | 0 => by
    show (true && _) = (_ && true)
    rw [Bool.true_and, Bool.and_true]
  | n + 1 => by
    rw [chainOk2, chainOk2_succ v va io C₀ p L n, chainOk2, show n + 1 = 1 + n by omega, lay2At_add]
    generalize chainOk2 _ _ _ _ _ _ n = X
    generalize ((lay2At v va io C₀ p L 0).ok1 && (lay2At v va io C₀ p L 0).ok2 && (lay2At v va io C₀ p L 0).pw) = a
    generalize ((lay2At _ _ _ _ _ _ n).ok1 && _ && _) = b
    cases a <;> cases b <;> cases X <;> rfl

theorem lay2At_zero (v : Nat → FE2) (va : Nat → FE) (io : Nat → KClaim FE2 → FE2) (C₀ : KClaim FE2) (p L : Nat) :
    lay2At v va io C₀ p L 0 = layerSpec2 v va (io 0) C₀ p := by
  rw [lay2At, Nat.zero_mul, Nat.add_zero]; rfl

theorem chain2_one (v : Nat → FE2) (va : Nat → FE) (io : Nat → KClaim FE2 → FE2) (C₀ : KClaim FE2) (p L : Nat) :
    chain2 v va io C₀ p L 1 = (layerSpec2 v va (io 0) C₀ p).claim := by
  rw [chain2_succ, lay2At_zero]

/-- **`V`'s layers on a view** (`n + 1` steps from `j0`, every claim's point of length `P + 1`). -/
theorem keccakLayersD_run (sig : ByteArray) (sh : LeanVM.Protocol.KeccakGkr.Shape) (ls P : Nat) :
    ∀ (n j0 : Nat) (C : KClaim FE2) (s : RS), C.point.length = P + 1 →
    keccakLayersD sh ls (List.range' j0 (n + 1)) C sig s =
      (chain2 (fe2At sig) (feAt sig) (fun k => iotaSF sh ls (j0 + k)) C (s.ent + s.msg) (2440 + 112 * (P + 1)) (n + 1),
        ⟨s.ent + s.msg + (n + 1) * (2440 + 112 * (P + 1)), 0,
          chainOk2 (fe2At sig) (feAt sig) (fun k => iotaSF sh ls (j0 + k)) C (s.ent + s.msg) (2440 + 112 * (P + 1))
            (n + 1) && s.ok⟩)
  | 0, j0, C, s, hC => by
    have hpt : C.point ≠ [] := by intro h; rw [h] at hC; simp at hC
    rw [List.range'_succ, List.range'_zero]
    show (verifyKeccakLayerD sh ls j0 C >>= fun C' => keccakLayersD sh ls [] C') sig s = _
    rw [rdE_bind_run, verifyKeccakLayerD_run sig sh ls j0 C hpt s]
    show (pure _ : DM _) sig _ = _
    rw [rdE_pure_run, Prod.mk.injEq, RS.mk.injEq, Nat.zero_add, chain2_one, Nat.add_zero, chainOk2,
      chainOk2, lay2At_zero, Nat.add_zero, Bool.true_and]
    exact ⟨rfl, by rw [layerSpec2_pos, hC]; ring, rfl, rfl⟩
  | n + 1, j0, C, s, hC => by
    have hpt : C.point ≠ [] := by intro h; rw [h] at hC; simp at hC
    rw [List.range'_succ]
    show (verifyKeccakLayerD sh ls j0 C >>= fun C' => keccakLayersD sh ls (List.range' (j0 + 1) (n + 1)) C') sig s = _
    rw [rdE_bind_run, verifyKeccakLayerD_run sig sh ls j0 C hpt s]
    dsimp only
    rw [keccakLayersD_run sig sh ls P n (j0 + 1) _ _ (by rw [layerSpec2_point_length, hC])]
    have hio : (fun k => iotaSF (F := FE2) sh ls (j0 + 1 + k)) = (fun j => iotaSF sh ls (j0 + (1 + j))) := by
      funext k; rw [show j0 + 1 + k = j0 + (1 + k) by omega]
    have hpos : (layerSpec2 (fe2At sig) (feAt sig) (iotaSF sh ls j0) C (s.ent + s.msg)).pos =
        s.ent + s.msg + 1 * (2440 + 112 * (P + 1)) := by rw [layerSpec2_pos, hC]; ring
    have e := chain2_add (fe2At sig) (feAt sig) (fun k => iotaSF sh ls (j0 + k)) C (s.ent + s.msg)
      (2440 + 112 * (P + 1)) 1 (n + 1)
    rw [show 1 + (n + 1) = n + 1 + 1 by omega] at e
    simp only [chain2_one, Nat.add_zero] at e
    rw [e, chainOk2_succ (fe2At sig) (feAt sig) (fun k => iotaSF sh ls (j0 + k)) C (s.ent + s.msg) _ (n + 1)]
    simp only [lay2At_zero, chain2_one, Nat.add_zero]
    rw [hio, hpos, Prod.mk.injEq, RS.mk.injEq]
    refine ⟨rfl, by ring, rfl, ?_⟩
    generalize chainOk2 _ _ _ _ _ _ (n + 1) = X
    generalize (layerSpec2 (fe2At sig) (feAt sig) (iotaSF sh ls j0) C (s.ent + s.msg)).ok1 = a
    generalize (layerSpec2 (fe2At sig) (feAt sig) (iotaSF sh ls j0) C (s.ent + s.msg)).ok2 = b
    generalize (layerSpec2 (fe2At sig) (feAt sig) (iotaSF sh ls j0) C (s.ent + s.msg)).pw = c
    cases a <;> cases b <;> cases c <;> cases X <;> cases s.ok <;> rfl

/-- **`V`'s tape GKR on a view** (`tapeGkrD (P + 5)`): the five lane challenges from `p = ent + msg`, then the 24
layers from `p + 400` on the first claim. -/
theorem tapeGkrD_run (sig : ByteArray) (P : Nat) (inst out : List FE2) (hinst : inst.length = P + 5) (s : RS) :
    tapeGkrD (P + 5) inst out sig s =
      (chain2 (fe2At sig) (feAt sig) (fun k => iotaSF LeanVM.Protocol.KeccakGkr.Shape.tape (P + 5) (0 + k))
          (firstClaimSF LeanVM.Protocol.KeccakGkr.Shape.tape inst [] (sampsG (feAt sig) (s.ent + s.msg) 5) out 0)
          (s.ent + s.msg + 400) (2440 + 112 * (P + 1)) 24,
        ⟨s.ent + s.msg + 400 + 24 * (2440 + 112 * (P + 1)), 0,
          chainOk2 (fe2At sig) (feAt sig) (fun k => iotaSF LeanVM.Protocol.KeccakGkr.Shape.tape (P + 5) (0 + k))
            (firstClaimSF LeanVM.Protocol.KeccakGkr.Shape.tape inst [] (sampsG (feAt sig) (s.ent + s.msg) 5) out 0)
            (s.ent + s.msg + 400) (2440 + 112 * (P + 1)) 24 && (powsG (feAt sig) gC1 (s.ent + s.msg) 5 && s.ok)⟩) := by
  show (samplesG gC1 (4 + 1) >>= fun lanesPt => keccakLayersD LeanVM.Protocol.KeccakGkr.Shape.tape (P + 5)
    (List.range' 0 (23 + 1)) (firstClaimSF LeanVM.Protocol.KeccakGkr.Shape.tape inst [] lanesPt out 0)) sig s = _
  rw [rdE_bind_run, samplesG_run]
  dsimp only
  rw [keccakLayersD_run sig _ (P + 5) P 23 0 _ _ (by
    show (inst.drop 4 ++ []).length = P + 1
    rw [List.append_nil, List.length_drop, hinst]; (clear * -; omega))]
  simp only [Nat.add_zero]

/-! ## The first claim at `E2` -/

/-- `x^z` as `V` writes it (`nF (2^z)`), `z < 64`. -/
theorem nF_two_pow {z : Nat} (hz : z < 64) : (nF (2 ^ z) : FE2) = gx ^ z := by
  have h1 : FK.ringEquivBF64.symm (LeanVM.Parameters.K.ofBits (2 ^ z)) = FK.x ^ z := by
    rw [RingEquiv.symm_apply_eq, FK.ringEquivBF64_apply, show z = ((⟨z, hz⟩ : Fin 64) : Nat) from rfl,
      FK.x_pow_word ⟨z, hz⟩, ← toUInt64_two_pow z hz]
    rfl
  show FE2.ofK (FK.ringEquivBF64.symm (LeanVM.Parameters.K.ofBits (2 ^ z))) = _
  rw [h1, fe2_ofK_pow]; rfl

/-- **`V`'s first-claim weights** are `lanes ⊗ x^z`. -/
theorem firstWeightsF_eq (lanesPt : List FE2) : firstWeightsF lanesPt = firstWG gx (eqKernelF lanesPt) := by
  unfold firstWeightsF firstWG
  refine List.map_congr_left fun j _ => ?_
  rw [nF_two_pow (Nat.mod_lt _ (by (clear * -; omega)))]

theorem firstWG_congr {g : FE2} {l l' : List FE2} (h : ∀ i < 25, l.getD i 0 = l'.getD i 0) :
    firstWG g l = firstWG g l' := by
  unfold firstWG
  refine List.map_congr_left fun j hj => ?_
  have := List.mem_range.mp hj
  rw [h _ (by simp only [keccakBits] at this; (clear * - this; omega))]

theorem sumF_eqKernelF (pt : List FE2) : sumF (eqKernelF pt) = 1 := by
  rw [sumF_eq_sum, list_sum_getDF, eqKernelF_length, ← sum_eqAtF pt]
  refine Finset.sum_congr rfl fun w hw => ?_
  rw [eqKernelF_getD, ite_eq_left (Finset.mem_range.mp hw)]

/-- An `E2` operand a straight block exports: both coordinates rows or fixed cells. -/
def Fx2 (s : S2) : Prop := Fx s.1 ∧ Fx s.2

theorem fx2_emit2 (f : E2Fn) (xs : List S2) (n : Nat) : Fx2 (emit2 f xs n).1 := ⟨Or.inl ⟨n, rfl⟩, Or.inl ⟨n + 1, rfl⟩⟩

theorem fx2_mapT2 {α : Type} {f : α → TB S2} (hf : ∀ a n, Fx2 (f a n).1) :
    ∀ (as : List α) (n : Nat), ∀ x ∈ (mapT2 f as n).1, Fx2 x
  | [], _, x, hx => by simp [mapT2, tb_pure] at hx
  | a :: as, n, x, hx => by
    simp only [mapT2, tb_bind, tb_pure, List.mem_cons] at hx
    rcases hx with rfl | hx
    · exact hf a n
    · exact fx2_mapT2 hf as _ x hx

theorem fx2_q2EqTab (z : S2) : ∀ (pt tab : List S2) (n : Nat), (∀ x ∈ tab, Fx2 x) →
    ∀ x ∈ (q2EqTab z tab pt n).1, Fx2 x
  | [], tab, n, h => by simpa [q2EqTab, tb_pure] using h
  | r :: rs, tab, n, h => by
    simp only [q2EqTab, tb_bind]
    refine fx2_q2EqTab z rs _ _ (fun x hx => ?_)
    simp only [q2EqStep, tb_bind, tb_pure, List.mem_append] at hx
    rcases hx with hx | hx
    · exact fx2_mapT2 (fun _ _ => fx2_emit2 _ _ _) _ _ x hx
    · exact fx2_mapT2 (fun _ _ => fx2_emit2 _ _ _) _ _ x hx

theorem fx2_q2Dot : ∀ (acc : S2) (cds : List (S2 × S2)) (n : Nat), Fx2 acc → Fx2 (q2Dot acc cds n).1
  | _, [], _, h => h
  | acc, cd :: rest, n, _ => by
    simp only [q2Dot, tb_bind]
    exact fx2_q2Dot _ rest _ (fx2_emit2 _ _ _)

theorem fx2_s2 (c : C2) : Fx2 c.s2 := ⟨Or.inr ⟨_, _, rfl⟩, Or.inr ⟨_, _, rfl⟩⟩

/-- The carried values of the tape's first claim. -/
def carVT2 (v0 : FE2) (mu instP lanes fl : List FE2) : List FE2 :=
  [v0] ++ mu ++ [1] ++ instP ++ lanes.take 25 ++ List.replicate 6 0 ++ fl

section carV
variable {v0 : FE2} {mu instP lanes fl : List FE2}

theorem carVT2_v0 : (carVT2 v0 mu instP lanes fl).getD 0 0 = v0 := rfl

theorem carVT2_mu (hmu : mu.length = 16) {i : Nat} (hi : i < 16) :
    (carVT2 v0 mu instP lanes fl).getD (1 + i) 0 = mu.getD i 0 := by
  unfold carVT2
  rw [List.getD_append _ _ _ _ (by simp only [List.length_append, List.length_singleton, hmu]; (clear * - hi; omega)),
    List.getD_append _ _ _ _ (by simp only [List.length_append, List.length_singleton, hmu]; (clear * - hi; omega)),
    List.getD_append _ _ _ _ (by simp only [List.length_append, List.length_singleton, hmu]; (clear * - hi; omega)),
    List.getD_append _ _ _ _ (by simp only [List.length_append, List.length_singleton, hmu]; (clear * - hi; omega)),
    List.getD_append _ _ _ _ (by simp only [List.length_append, List.length_singleton, hmu]; (clear * - hi; omega)),
    List.getD_append_right _ _ _ _ (by simp), List.length_singleton, Nat.add_sub_cancel_left]

theorem carVT2_kappa (hmu : mu.length = 16) : (carVT2 v0 mu instP lanes fl).getD 17 0 = 1 := by
  unfold carVT2
  rw [List.getD_append _ _ _ _ (by simp only [List.length_append, List.length_singleton, hmu]; (clear * -; omega)),
    List.getD_append _ _ _ _ (by simp only [List.length_append, List.length_singleton, hmu]; (clear * -; omega)),
    List.getD_append _ _ _ _ (by simp only [List.length_append, List.length_singleton, hmu]; (clear * -; omega)),
    List.getD_append _ _ _ _ (by simp only [List.length_append, List.length_singleton, hmu]; (clear * -; omega)),
    List.getD_append_right _ _ _ _ (by simp only [List.length_append, List.length_singleton, hmu]; (clear * -; omega))]
  simp [hmu]

theorem carVT2_pt (hmu : mu.length = 16) {P : Nat} (hiP : instP.length = P + 1) {i : Nat} (hi : i < P + 1) :
    (carVT2 v0 mu instP lanes fl).getD (18 + i) 0 = instP.getD i 0 := by
  unfold carVT2
  rw [List.getD_append _ _ _ _ (by simp only [List.length_append, List.length_singleton, hmu, hiP]; (clear * - hi; omega)),
    List.getD_append _ _ _ _ (by simp only [List.length_append, List.length_singleton, hmu, hiP]; (clear * - hi; omega)),
    List.getD_append _ _ _ _ (by simp only [List.length_append, List.length_singleton, hmu, hiP]; (clear * - hi; omega)),
    List.getD_append_right _ _ _ _ (by simp only [List.length_append, List.length_singleton, hmu]; (clear * -; omega))]
  simp only [List.length_append, List.length_singleton, hmu]
  rw [show 18 + i - (1 + 16 + 1) = i by (clear * -; omega)]

theorem carVT2_B (hmu : mu.length = 16) {P : Nat} (hiP : instP.length = P + 1) (hla : 25 ≤ lanes.length) {l : Nat}
    (hl : l < 25) : (carVT2 v0 mu instP lanes fl).getD (19 + P + l) 0 = lanes.getD l 0 := by
  unfold carVT2
  rw [List.getD_append _ _ _ _ (by simp only [List.length_append, List.length_singleton, hmu, hiP, List.length_take, List.length_replicate]; (clear * - hla hl; omega)),
    List.getD_append _ _ _ _ (by simp only [List.length_append, List.length_singleton, hmu, hiP, List.length_take]; (clear * - hla hl; omega)),
    List.getD_append_right _ _ _ _ (by simp only [List.length_append, List.length_singleton, hmu, hiP]; (clear * -; omega))]
  simp only [List.length_append, List.length_singleton, hmu, hiP]
  rw [show 19 + P + l - (1 + 16 + 1 + (P + 1)) = l by (clear * -; omega)]
  simp [List.getD_eq_getElem?_getD, List.getElem?_take, hl]

theorem carVT2_fl (hmu : mu.length = 16) {P : Nat} (hiP : instP.length = P + 1) (hla : 25 ≤ lanes.length) {i : Nat} :
    (carVT2 v0 mu instP lanes fl).getD (50 + P + i) 0 = fl.getD i 0 := by
  unfold carVT2
  rw [List.getD_append_right _ _ _ _ (by simp only [List.length_append, List.length_singleton, hmu, hiP, List.length_take, List.length_replicate]; (clear * -; omega))]
  simp only [List.length_append, List.length_singleton, hmu, hiP, List.length_take, List.length_replicate]
  rw [show 50 + P + i - (1 + 16 + 1 + (P + 1) + min 25 lanes.length + 6) = i by (clear * - hla; omega)]

theorem carVT2_length {P : Nat} (hmu : mu.length = 16) (hiP : instP.length = P + 1) (hla : 25 ≤ lanes.length)
    (hfl : fl.length = 7) : (carVT2 v0 mu instP lanes fl).length = 57 + P := by
  simp [carVT2, hmu, hiP, hfl]; (clear * - hla; omega)

end carV

/-- The tape's lane challenges, answer `k` at lane `qs + 10k`. -/
def lanePtT2 (u : Nat → FE2) (qs : Nat) : List FE2 := (List.range 5).map fun k => u (qs + 10 * k)

/-- **The tape's first claim** is represented by its carried values. -/
theorem rep_firstT2 (P : Nat) {instV lp out fl : List FE2} (hinst : instV.length = P + 5) (hlp : lp.length = 5)
    (hout : out.length = 25) (hfl : ∀ i < 7, fl.getD i 0 = (eqKernelF lp).getD 0 0 * gx ^ iotaPos i) :
    Rep2 P (fun j => (carVT2 (((List.range 25).map fun l => (eqKernelF lp).getD l 0 * out.getD l 0).sum)
        (eqKernelF (instV.take 4)) (instV.drop 4) (eqKernelF lp) fl).getD j 0)
      (firstClaimSF LeanVM.Protocol.KeccakGkr.Shape.tape instV [] lp out 0) true := by
  have hL : (eqKernelF lp).length = 32 := by rw [eqKernelF_length, hlp]; rfl
  have hmu : (eqKernelF (instV.take 4)).length = 16 := by
    rw [eqKernelF_length, List.length_take, hinst]; rfl
  have hiP1 : (instV.drop 4).length = P + 1 := by rw [List.length_drop, hinst]; (clear * -; omega)
  have hla : 25 ≤ (eqKernelF lp).length := by (clear * - hL; omega)
  have hB : ∀ l < 25, (repB2 P fun j => (carVT2 (((List.range 25).map fun l => (eqKernelF lp).getD l 0 *
      out.getD l 0).sum) (eqKernelF (instV.take 4)) (instV.drop 4) (eqKernelF lp) fl).getD j 0).getD l 0 =
      (eqKernelF lp).getD l 0 := by
    intro l hl
    simp only [repB2, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hl, Option.map_some,
      Option.getD_some]
    rw [← List.getD_eq_getElem?_getD, carVT2_B hmu hiP1 hla hl, List.getD_eq_getElem?_getD]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · show (carVT2 _ _ _ _ _).getD 0 0 = 0 + (eqKernelF ([] : List FE2)).getD (1 - 1) 0 *
      dotF ((eqKernelF lp).take 25) out
    rw [carVT2_v0, show (eqKernelF ([] : List FE2)).getD (1 - 1) 0 = 1 from rfl, zero_add, one_mul,
      dotF_eq _ _ (by rw [List.length_take, hL, hout]; rfl), List.length_take, hL,
      show min 25 32 = 25 from rfl, ← sumF_eq_sum, sumF_map_range]
    refine Finset.sum_congr rfl fun l hl => ?_
    have hl' := Finset.mem_range.mp hl
    simp [List.getD_eq_getElem?_getD, List.getElem?_take, hl']
  · show (List.range 16).map (fun i => (carVT2 _ _ _ _ _).getD (1 + i) 0) = eqKernelF (instV.take 4)
    apply List.ext_getElem (by simp [hmu])
    intro i h1 h2
    rw [List.getElem_map, List.getElem_range, carVT2_mu hmu (by simpa using h1), List.getD_eq_getElem _ _ h2]
  · show (carVT2 _ _ _ _ _).getD 17 0 = sumF (eqKernelF (instV.take 4))
    rw [carVT2_kappa hmu, sumF_eqKernelF]
  · show (List.range (P + 1)).map (fun i => (carVT2 _ _ _ _ _).getD (18 + i) 0) = instV.drop 4 ++ []
    rw [List.append_nil]
    apply List.ext_getElem (by simp [hiP1])
    intro i h1 h2
    rw [List.getElem_map, List.getElem_range, carVT2_pt hmu hiP1 (by simpa using h1), List.getD_eq_getElem _ _ h2]
  · rw [if_pos rfl]
    unfold firstClaimSF
    dsimp only
    rw [firstWeightsF_eq]
    exact firstWG_congr fun i hi => (hB i hi).symm
  · intro i hi
    rw [if_pos rfl, hB 0 (by decide), carVT2_fl hmu hiP1 hla, hfl i hi]

theorem tb_peel2 {α β : Type} {xv : Src → FE} {V : Nat → FE} {n : Nat} (m : TB α) (f : α → TB β)
    (h : THold2 xv V n ((m >>= f) n).2) :
    THold2 xv V n (m n).2 ∧ THold2 xv V (n + (m n).2.length) (f (m n).1 (n + (m n).2.length)).2 ∧
      ((m >>= f) n).1 = (f (m n).1 (n + (m n).2.length)).1 :=
  ⟨((thold2_bind m f).mp h).1, ((thold2_bind m f).mp h).2, rfl⟩

theorem fx2_q2Base (b : Src) (n : Nat) : Fx2 (q2Base b n).1.2.1 ∧ Fx2 (q2Base b n).1.2.2 :=
  ⟨⟨Or.inl ⟨n, rfl⟩, Or.inl ⟨n, rfl⟩⟩, ⟨Or.inl ⟨n + 1, rfl⟩, Or.inl ⟨n, rfl⟩⟩⟩

/-- **The tape's first-claim block** at `E2`: its lanes and the carried values (`carVT2`). -/
theorem preTBT2_spec {xv : Src → FE} {V : Nat → FE} {P qs : Nat} {inst out : Nat → S2} {b : Src}
    {u : Nat → FE2} (hu : ∀ m ≤ qs + 40, lv2 xv [] m = u m) (hinst : ∀ i, Fx2 (inst i)) {n : Nat}
    (h : THold2 xv V n (preTBT2 P qs inst out b n).2) :
    vals2 xv V (preTBT2 P qs inst out b n).1.lanes = eqKernelF (lanePtT2 u qs) ∧
    (preTBT2 P qs inst out b n).1.carried.length = 57 + P ∧ (∀ x ∈ (preTBT2 P qs inst out b n).1.carried, Fx2 x) ∧
    vals2 xv V (preTBT2 P qs inst out b n).1.carried =
      carVT2 (((List.range 25).map fun l =>
          (eqKernelF (lanePtT2 u qs)).getD l 0 * ((List.range 25).map fun l => (out l).valF xv V).getD l 0).sum)
        (eqKernelF ((List.range 4).map fun i => (inst i).valF xv V))
        ((List.range (P + 1)).map fun i => (inst (4 + i)).valF xv V) (eqKernelF (lanePtT2 u qs))
        ((List.range 7).map fun i => (eqKernelF (lanePtT2 u qs)).getD 0 0 * gx ^ iotaPos i) := by
  unfold preTBT2 at h ⊢
  -- zero, one
  obtain ⟨h1, h, e⟩ := tb_peel2 _ _ h; rw [e]; clear e
  obtain ⟨-, ez, eo⟩ := q2Base_spec h1
  obtain ⟨fz, fo⟩ := fx2_q2Base b n
  generalize (q2Base b n).1 = base at h ez eo fz fo ⊢
  generalize n + (q2Base b n).2.length = n1 at h ⊢
  -- the lanes
  obtain ⟨h2, h, e⟩ := tb_peel2 _ _ h; rw [e]; clear e
  have el := eqTab_one2 ez eo _ n1 h2
  have elp : vals2 xv V ((List.range 5).map fun k => lane2 (qs + 10 * k) []) = lanePtT2 u qs := by
    simp only [vals2, List.map_map, lanePtT2]
    refine List.map_congr_left fun k hk => ?_
    simp only [Function.comp_apply]
    rw [lane2_valF, hu _ (by have := List.mem_range.mp hk; (clear * - this; omega))]
  rw [elp] at el
  have fl := fx2_q2EqTab base.2.1 ((List.range 5).map fun k => lane2 (qs + 10 * k) []) [base.2.2] n1
    (by simpa using fo)
  generalize (q2EqTab base.2.1 [base.2.2] ((List.range 5).map fun k => lane2 (qs + 10 * k) []) n1).1 = lanes
    at h el fl ⊢
  generalize n1 + (q2EqTab base.2.1 [base.2.2] ((List.range 5).map fun k => lane2 (qs + 10 * k) []) n1).2.length = n2
    at h ⊢
  have hll : lanes.length = 32 := by
    have := congrArg List.length el; rw [vals2, List.length_map, eqKernelF_length] at this; simpa [lanePtT2] using this
  -- the value
  obtain ⟨h3, h, e⟩ := tb_peel2 _ _ h; rw [e]; clear e
  have ed := q2Dot_spec _ _ _ h3
  have fv := fx2_q2Dot base.2.1 ((List.range 25).map fun l => (lanes.getD l default, out l)) n2 fz
  generalize (q2Dot base.2.1 ((List.range 25).map fun l => (lanes.getD l default, out l)) n2).1 = v0 at h ed fv ⊢
  generalize n2 + (q2Dot base.2.1 ((List.range 25).map fun l => (lanes.getD l default, out l)) n2).2.length = n3
    at h ⊢
  -- `μ`
  obtain ⟨h4, h, e⟩ := tb_peel2 _ _ h; rw [e]; clear e
  have em := eqTab_one2 ez eo ((List.range 4).map inst) n3 h4
  have fm := fx2_q2EqTab base.2.1 ((List.range 4).map inst) [base.2.2] n3 (by simpa using fo)
  generalize (q2EqTab base.2.1 [base.2.2] ((List.range 4).map inst) n3).1 = mu at h em fm ⊢
  generalize n3 + (q2EqTab base.2.1 [base.2.2] ((List.range 4).map inst) n3).2.length = n4 at h ⊢
  -- the flips
  obtain ⟨h5, -, e⟩ := tb_peel2 _ _ h; rw [e]; clear e
  have ef : vals2 xv V (mapT2 (fun i => q2Scale (FK.x ^ iotaPos i) (lanes.getD 0 default)) (List.range 7) n4).1 =
      (List.range 7).map fun i => (eqKernelF (lanePtT2 u qs)).getD 0 0 * gx ^ iotaPos i :=
    forall₂_map_eq2 (mapT2_spec (P := fun i x => S2.valF xv V x = (eqKernelF (lanePtT2 u qs)).getD 0 0 * gx ^ iotaPos i)
      (fun i m hm => by rw [q2Scale_spec hm, getD_valF2 _ (by (clear * - hll; omega)), el, mul_comm, fe2_ofK_pow]; rfl) _ _ h5)
  have ffl : ∀ x ∈ (mapT2 (fun i => q2Scale (FK.x ^ iotaPos i) (lanes.getD 0 default)) (List.range 7) n4).1, Fx2 x :=
    fx2_mapT2 (fun _ _ => fx2_emit2 _ _ _) _ _
  have hfl : (mapT2 (fun i => q2Scale (FK.x ^ iotaPos i) (lanes.getD 0 default)) (List.range 7) n4).1.length = 7 := by
    rw [mapT2_length]; rfl
  generalize (mapT2 (fun i => q2Scale (FK.x ^ iotaPos i) (lanes.getD 0 default)) (List.range 7) n4).1 = fls
    at ef ffl hfl ⊢
  rw [tb_pure]
  have hmu : mu.length = 16 := by
    have := congrArg List.length em; rw [vals2, List.length_map, eqKernelF_length] at this; simpa using this
  refine ⟨el, ?_, ?_, ?_⟩
  · simp [hmu, hll, hfl]; (clear * -; omega)
  · intro x hx
    simp only [List.mem_append, List.mem_singleton, List.mem_map, List.mem_range] at hx
    rcases hx with ((((((rfl | hx) | rfl) | ⟨i, -, rfl⟩) | hx) | hx) | hx)
    · exact fv
    · exact fm x hx
    · exact fo
    · exact hinst _
    · exact fl x (List.mem_of_mem_take hx)
    · rw [List.eq_of_mem_replicate hx]; exact fz
    · exact ffl x hx
  · simp only [vals2, List.map_append, List.map_cons, List.map_nil, List.map_take, List.map_replicate] at em el ef ⊢
    rw [em, el, ef, ed, eo, ez, zero_add]
    simp only [carVT2, List.map_map, Function.comp_def]
    have hs : (List.map (fun x => S2.valF xv V (lanes.getD x default) * S2.valF xv V (out x)) (List.range 25)).sum =
        (List.map (fun l => (eqKernelF (lanePtT2 u qs)).getD l 0 *
          (List.map (fun l => S2.valF xv V (out l)) (List.range 25)).getD l 0) (List.range 25)).sum := by
      refine congrArg List.sum (List.map_congr_left fun l hl => ?_)
      have hl' := List.mem_range.mp hl
      rw [getD_valF2 _ (by (clear * - hll hl'; omega)), vals2, el]
      simp [List.getD_eq_getElem?_getD, hl']
    rw [hs]

theorem cpIns2_w (l : List S2) : ∀ i ∈ cpIns2 l, Row.w .K ⟨i.op, i.ty, []⟩ = 1 := by
  intro i hi
  simp only [cpIns2, List.mem_flatMap] at hi
  obtain ⟨a, -, hi⟩ := hi
  simp only [q2Copy, q2Lin, emit2, e2I, List.mem_cons, List.mem_nil_iff, or_false] at hi
  rcases hi with rfl | rfl <;> rfl

theorem cpIns2_ty (l : List S2) : ∀ i ∈ cpIns2 l, i.ty = .K := by
  intro i hi
  simp only [cpIns2, List.mem_flatMap] at hi
  obtain ⟨a, -, hi⟩ := hi
  simp only [q2Copy, q2Lin, emit2, e2I, List.mem_cons, List.mem_nil_iff, or_false] at hi
  rcases hi with rfl | rfl <;> rfl

theorem gkOut2_val (M : Mem) (o o' : LoopOut) (jf : Nat) (V : Nat → FE) {s : S2} (hs : Fx2 s) :
    (S2.gkOut o s).valF (iterXv M o' jf) V = s.valF (iterXv M o 0) (iterF M o 0) := by
  show (⟨((s.1.gkOut o).valF _ V).c₀, ((s.2.gkOut o).valF _ V).c₀⟩ : FE2) = ⟨(s.1.valF _ _).c₀, (s.2.valF _ _).c₀⟩
  rw [gkOut_val M o o' jf V hs.1, gkOut_val M o o' jf V hs.2]

/-- **The `E2` copy block**: copy `j` is in the `K` cells `p.k + 2j`, `p.k + 2j + 1` and holds carried value `j`. -/
theorem cp2_spec {c : Ctx} {M : Mem} {p : Ptr} {l : List S2} {o : LoopOut}
    (h : SegsHold c M p (loop [] (tplOf (cpIns2 (l.map (S2.gkOut o)))) p).2) (hl : ∀ x ∈ l, Fx2 x) {j : Nat}
    (hj : j < l.length) :
    (⟨M.k (p.k + 2 * j), M.k (p.k + 2 * j + 1)⟩ : FE2) = (vals2 (iterXv M o 0) (iterF M o 0) l).getD j 0 := by
  have hH := thold2_of_loop h (jf := 0) (by simp)
  have hC : CopyHold2 (iterXv M (loop [] (tplOf (cpIns2 (l.map (S2.gkOut o)))) p).1 0)
      (iterF M (loop [] (tplOf (cpIns2 (l.map (S2.gkOut o)))) p).1 0) 0 (l.map (S2.gkOut o)) := hH
  have e := cp2_get' hC j (by simpa using hj)
  have hlen : (cpIns2 (l.map (S2.gkOut o))).length = 2 * l.length := by rw [cpIns2_length, List.length_map]
  have hcell : ∀ t < 2 * l.length, iterF M (loop [] (tplOf (cpIns2 (l.map (S2.gkOut o)))) p).1 0 t =
      FE.ofK (M.k (p.k + t)) := by
    intro t ht
    rw [gk_loop_fst]
    show Cell.val M (LoopOut.cell ⟨p, [], tplOf (cpIns2 (l.map (S2.gkOut o)))⟩ t 0) = _
    have hty : ((tplOf (cpIns2 (l.map (S2.gkOut o)))).getD t default).ty = .K := by
      rw [tplOf_getD _ (by rw [hlen]; exact ht)]
      have hm : (cpIns2 (l.map (S2.gkOut o))).getD t default ∈ cpIns2 (l.map (S2.gkOut o)) := by
        rw [List.getD_eq_getElem _ _ (by rw [hlen]; exact ht)]; exact List.getElem_mem _
      exact cpIns2_ty _ _ hm
    simp only [LoopOut.cell, hty, Cell.val, Ptr.at,
      lrank_ones (δ := cpIns2 (l.map (S2.gkOut o))) (cpIns2_w _) (show t ≤ (cpIns2 (l.map (S2.gkOut o))).length by
        rw [hlen]; (clear * - ht; omega)), Nat.mul_zero, Nat.add_zero]
    rfl
  simp only [Nat.zero_add] at e
  rw [hcell _ (by (clear * - hj; omega)), hcell _ (by (clear * - hj; omega)), fe_ofK_c0, fe_ofK_c0] at e
  rw [show p.k + 2 * j + 1 = p.k + (2 * j + 1) by (clear * -; omega), e, ← getD_valF2 _ (by simpa using hj),
    ← getD_valF2 _ hj, List.getD_eq_getElem _ _ (by simpa using hj), List.getElem_map,
    List.getD_eq_getElem _ _ hj, gkOut2_val M o _ 0 _ (hl _ (List.getElem_mem hj))]

/-! ## The layer loop's last copy rows -/

/-- A row writing `K` names cell `p.k + rank + width·jf`. -/
theorem cell_of_tyK {o : LoopOut} {t : Nat} (jf : Nat) (h : (o.tpl.getD t default).ty = .K) :
    o.cell t jf = ⟨.K, o.p.k + lrank .K o.tpl t + ltw .K o.tpl * jf⟩ := by
  simp only [LoopOut.cell, h, Ptr.at]

theorem layOk2_facts {P : Nat} (hP : layOk2 P = true) :
    (layIns2 P).length = cbOf2 P + 2 * (57 + P) ∧ ∀ i ∈ (layIns2 P).drop (cbOf2 P), Row.w .K ⟨i.op, i.ty, []⟩ = 1 ∧
      i.ty = .K := by
  have hok := hP
  simp only [layOk2, Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at hok
  obtain ⟨⟨hlen, -⟩, hsuf⟩ := hok
  refine ⟨hlen, fun i hi => ?_⟩
  have := hsuf i hi
  try simp only [Bool.and_eq_true, beq_iff_eq, bne_iff_ne, ne_eq] at this
  obtain ⟨h1, h2⟩ := this
  have hwr : Row.writes ⟨i.op, i.ty, []⟩ = some .K := by
    unfold Row.writes; cases hop : i.op <;> simp_all
  exact ⟨by simp [Row.w, hwr], h1⟩

/-- A layer iteration writes at least its `2C` carried cells. -/
theorem lay_ltw2 {P : Nat} (hP : layOk2 P = true) {q cst : Nat} : 2 * (57 + P) ≤ ltw .K (layTpl2 P q cst) := by
  obtain ⟨hlen, hsuf⟩ := layOk2_facts hP
  have hr0 : lrank .K (layTpl2 P q cst) (cbOf2 P + 0) + 2 * (57 + P) = ltw .K (layTpl2 P q cst) + 0 := by
    rw [layTpl2, lrank_reloc, ltw_reloc]; exact lrank_suffixK hlen (fun i hi => (hsuf i hi).1) (by (clear * -; omega))
  (clear * - hr0; omega)

/-- The copy rows of a layer loop's last iteration are the `2C` `K` cells before the pointer after it. -/
theorem lay_last_cell2 {M : Mem} {P : Nat} (hP : layOk2 P = true) (pL : Ptr) (q cst d : Nat) {j : Nat}
    (hj : j < 57 + P) :
    ((⟨pL, [d], layTpl2 P q cst⟩ : LoopOut).cell2 (cbOf2 P + 2 * j) (2 ^ d - 1)).val M =
      ⟨M.k ((pL.adv (loop [d] (layTpl2 P q cst) pL).2).k - 2 * (57 + P) + 2 * j),
        M.k ((pL.adv (loop [d] (layTpl2 P q cst) pL).2).k - 2 * (57 + P) + 2 * j + 1)⟩ := by
  obtain ⟨hlen, hsuf⟩ := layOk2_facts hP
  have hr : ∀ t ≤ 2 * (57 + P), lrank .K (layTpl2 P q cst) (cbOf2 P + t) + 2 * (57 + P) = ltw .K (layTpl2 P q cst) + t := by
    intro t ht; rw [layTpl2, lrank_reloc, ltw_reloc]; exact lrank_suffixK hlen (fun i hi => (hsuf i hi).1) ht
  have hty : ∀ t < 2 * (57 + P), ((layTpl2 P q cst).getD (cbOf2 P + t) default).ty = .K := by
    intro t ht
    rw [layTpl2, tplOf_getD _ (by rw [List.length_map, hlen]; (clear * - ht; omega)), reloc_getD, relocI_toLRow_ty]
    have hm : (layIns2 P).getD (cbOf2 P + t) default ∈ (layIns2 P).drop (cbOf2 P) := by
      rw [show (layIns2 P).getD (cbOf2 P + t) default = ((layIns2 P).drop (cbOf2 P)).getD t default by
        simp [List.getD_eq_getElem?_getD]]
      rw [List.getD_eq_getElem _ _ (by simp; (clear * - hlen ht; omega))]; exact List.getElem_mem _
    exact (hsuf _ hm).2
  have hcell : ∀ t < 2 * (57 + P), ((⟨pL, [d], layTpl2 P q cst⟩ : LoopOut).cell (cbOf2 P + t) (2 ^ d - 1)).val M =
      FE.ofK (M.k (pL.k + lrank .K (layTpl2 P q cst) (cbOf2 P + t) + ltw .K (layTpl2 P q cst) * (2 ^ d - 1))) := by
    intro t ht
    rw [cell_of_tyK (2 ^ d - 1) (hty t ht)]
    rfl
  rw [cell2_val, hcell _ (by (clear * - hj; omega)), show cbOf2 P + 2 * j + 1 = cbOf2 P + (2 * j + 1) by (clear * -; omega), hcell _ (by (clear * - hj; omega)),
    fe_ofK_c0, fe_ofK_c0, gk_adv_loop]
  have h1 : 1 ≤ 2 ^ d := Nat.one_le_two_pow
  have e1 : ([d] : List Nat).sum = d := by simp
  simp only [e1]
  have hw0 := lay_ltw2 hP (q := q) (cst := cst)
  have hr1 := hr (2 * j) (by (clear * - hj; omega))
  have hr2 := hr (2 * j + 1) (by (clear * - hj; omega))
  generalize lrank .K (layTpl2 P q cst) (cbOf2 P + 2 * j) = a at hr1 ⊢
  generalize lrank .K (layTpl2 P q cst) (cbOf2 P + (2 * j + 1)) = a' at hr2 ⊢
  generalize ltw .K (layTpl2 P q cst) = w at hr1 hr2 hw0 ⊢
  obtain ⟨m, hm⟩ : ∃ m, 2 ^ d = m + 1 := ⟨2 ^ d - 1, by (clear * - h1; omega)⟩
  rw [hm, Nat.add_sub_cancel]
  rw [show pL.k + w * (m + 1) - 2 * (57 + P) + 2 * j = pL.k + a + w * m by rw [Nat.mul_succ]; (clear * - hr1 hw0; omega),
    show pL.k + a + w * m + 1 = pL.k + a' + w * m by (clear * - hr1 hr2; omega)]

/-! ## The tape gadget -/

theorem take_range_map2 (f : Nat → FE2) {n N : Nat} (h : n ≤ N) :
    ((List.range N).map f).take n = (List.range n).map f := by
  rw [← List.map_take, List.take_range, Nat.min_eq_left h]

theorem drop_range_map2 (f : Nat → FE2) (n N : Nat) :
    ((List.range N).map f).drop n = (List.range (N - n)).map fun i => f (n + i) := by
  apply List.ext_getElem
  · simp
  · intro i h1 h2
    simp only [List.getElem_drop, List.getElem_map, List.getElem_range]

/-- The tape's `ι` term at `E2`: one segment, the point's last coordinate unread. -/
theorem iotaSF_tape {P k : Nat} {C : KClaim FE2} (hC : C.point.length = P + 1) :
    iotaSF LeanVM.Protocol.KeccakGkr.Shape.tape (P + 5) k C =
      (1 + C.point.getD P 0) * iotaFG (keccakRC.getD (tapeDepth - k - 1) 0) C.weights +
        C.point.getD P 0 * iotaFG (keccakRC.getD (tapeDepth - k - 1) 0) C.weights := by
  have hd : C.point.drop (P + 5 - 4) = [] := by rw [show P + 5 - 4 = P + 1 by (clear * -; omega), ← hC, List.drop_length]
  have e : iotaSF LeanVM.Protocol.KeccakGkr.Shape.tape (P + 5) k C =
      iotaFG (keccakRC.getD (tapeDepth - k - 1) 0) C.weights := by
    unfold iotaSF
    rw [hd]
    show sumF [(eqKernelF ([] : List FE2)).getD 0 0 * _] = _
    rw [show (eqKernelF ([] : List FE2)).getD 0 0 = 1 from rfl, one_mul, sumF_eq_sum, List.sum_singleton]
    rfl
  rw [e, ← add_mul, add_assoc, fe2_add_self, add_zero, one_mul]

/-- The tape's constant `j` of layer `jf`, as `layers2_spec` reads it. -/
theorem tape_cst {M : Mem} {cst j0 : Nat} {β : FE}
    (hc : ∀ t < 16 * tapeDepth, FE.ofK (M.k (cst + t)) = if t % 16 = 15 then β else FE.ofK (cstKT (t / 16) (t % 16)))
    {jf : Nat} (hjf : j0 + jf < tapeDepth) :
    (∀ i < 7, FE.ofK (M.k (cst + (16 * (j0 + jf) + i))) = rcBit (keccakRC.getD (tapeDepth - (j0 + jf) - 1) 0) i ∧
      FE.ofK (M.k (cst + (16 * (j0 + jf) + (7 + i)))) = rcBit (keccakRC.getD (tapeDepth - (j0 + jf) - 1) 0) i) ∧
    FE.ofK (M.k (cst + (16 * (j0 + jf) + 14))) = (if (j0 + jf == 0) = true then 1 else 0) ∧
    FE.ofK (M.k (cst + (16 * (j0 + jf) + 15))) = β := by
  refine ⟨fun i hi => ⟨?_, ?_⟩, ?_, ?_⟩
  · rw [hc _ (by simp only [tapeDepth] at hjf ⊢; (clear * - hjf hi; omega)), if_neg (by (clear * - hi; omega)), show (16 * (j0 + jf) + i) / 16 = j0 + jf by (clear * - hi; omega),
      show (16 * (j0 + jf) + i) % 16 = i by (clear * - hi; omega), ← ofK_rcK]
    simp only [cstKT, if_neg (show ¬ tapeDepth ≤ j0 + jf by (clear * - hjf; omega)), if_pos hi]
  · rw [hc _ (by simp only [tapeDepth] at hjf ⊢; (clear * - hjf hi; omega)), if_neg (by (clear * - hi; omega)),
      show (16 * (j0 + jf) + (7 + i)) / 16 = j0 + jf by (clear * - hi; omega), show (16 * (j0 + jf) + (7 + i)) % 16 = 7 + i by (clear * - hi; omega),
      ← ofK_rcK]
    simp only [cstKT, if_neg (show ¬ tapeDepth ≤ j0 + jf by (clear * - hjf; omega)), if_neg (show ¬ 7 + i < 7 by (clear * -; omega)),
      if_pos (show 7 + i < 14 by (clear * - hi; omega)), show 7 + i - 7 = i by (clear * -; omega)]
  · rw [hc _ (by simp only [tapeDepth] at hjf ⊢; (clear * - hjf; omega)), if_neg (by (clear * -; omega)), show (16 * (j0 + jf) + 14) / 16 = j0 + jf by (clear * -; omega),
      show (16 * (j0 + jf) + 14) % 16 = 14 by (clear * -; omega)]
    simp only [cstKT, if_neg (show ¬ tapeDepth ≤ j0 + jf by (clear * - hjf; omega)), if_neg (show ¬ 14 < 7 by (clear * -; omega)),
      if_neg (show ¬ 14 < 14 by (clear * -; omega))]
    rcases Nat.eq_zero_or_pos (j0 + jf) with h0 | h0
    · rw [h0]; rfl
    · rw [if_neg (by (clear * - h0; omega)), if_neg (by rw [beq_iff_eq]; (clear * - h0; omega))]; rfl
  · rw [hc _ (by simp only [tapeDepth] at hjf ⊢; (clear * - hjf; omega)), if_pos (by (clear * -; omega))]

theorem noA_preTBT2 (P qs : Nat) (inst out : Nat → S2) (b : Src) : NoA (preTBT2 P qs inst out b) :=
  noA_bind (noA_q2Base _) fun _ => noA_bind (noA_q2EqTab _ _ _) fun _ => noA_bind (noA_q2Dot _ _) fun _ =>
    noA_bind (noA_q2EqTab _ _ _) fun _ => noA_bind (noA_mapT2 (fun _ => noA_q2Scale _ _) _) fun _ => noA_pure _

theorem noA_cpIns2 (l : List S2) (xv : Src → FE) (V : Nat → FE) : TAssert xv V (cpIns2 l) := by
  rw [← mapT2_q2Copy_snd l 0]
  exact noA_mapT2 (fun _ => noA_q2Copy _) l xv V 0

theorem s2_valF_s2 (M : Mem) (o : LoopOut) (jf : Nat) (V : Nat → FE) (c : C2) :
    c.s2.valF (iterXv M o jf) V = c.val M := by
  show (⟨(iterXv M o jf (.ext c.re.addr)).c₀, (iterXv M o jf (.ext c.im.addr)).c₀⟩ : FE2) = _
  rw [show c.re.addr = ⟨c.re.ty, c.re.n, []⟩ from rfl, show c.im.addr = ⟨c.im.ty, c.im.n, []⟩ from rfl,
    gk_iterXv_fix, gk_iterXv_fix]
  rfl

theorem lv2_fix {M : Mem} {sig : ByteArray} {T : Nat} (hS : Streamed M sig T) (o : LoopOut) (jf m : Nat)
    (hm : m + 1 < T) : lv2 (iterXv M o jf) [] m = fe2At sig (8 * m) := by
  unfold lv2
  rw [gk_iterXv_fix, gk_iterXv_fix]
  show (⟨(FE.ofK (M.k m)).c₀, (FE.ofK (M.k (m + 1))).c₀⟩ : FE2) = _
  rw [fe_ofK_c0, fe_ofK_c0, hS _ (by (clear * - hm; omega)), hS _ hm, show 8 * (m + 1) = 8 * m + 8 by ring]
  rfl

/-- **The tape gadget at `E2`** (`V`'s `tapeGkrD (P + 5) inst output`, read as `chain2` from the first claim): in any
memory where its rows hold and the input lanes are the stream, the carried cells of the last layer represent
`V`'s claim after the 24 layers; with the gate `1` its assertions hold iff every layer's two checks do. -/
theorem tape_core2 {c : Ctx} {M : Mem} {p : Ptr} {P qs : Nat} {inst out : Nat → C2} {b : Cell}
    {sig : ByteArray} {T : Nat} (hP : layOk2 P = true) (hq : 5 ≤ qs) (hS : Streamed M sig T)
    (hT : tapeEnd2 P qs + 2 ≤ T) (h : SegsHold c M p (tapeGadgetE2 P qs inst out b p).2) :
    Rep2 P (fun j => ((tapeGadgetE2 P qs inst out b p).1.cv j).val M)
      (chain2 (fe2At sig) (feAt sig) (fun k => iotaSF LeanVM.Protocol.KeccakGkr.Shape.tape (P + 5) (0 + k))
        (firstClaimSF LeanVM.Protocol.KeccakGkr.Shape.tape ((List.range (P + 5)).map fun i => (inst i).val M) []
          (lanePtT2 (fun m => fe2At sig (8 * m)) qs) ((List.range 25).map fun l => (out l).val M) 0)
        (8 * tapeQ2 qs - 40) (8 * (lay02 P).str2) 24) false ∧
    (b.val M = 1 → (SegsAssert M p (tapeGadgetE2 P qs inst out b p).2 ↔
      ∀ k < 24,
        (lay2At (fe2At sig) (feAt sig) (fun k => iotaSF LeanVM.Protocol.KeccakGkr.Shape.tape (P + 5) (0 + k))
          (firstClaimSF LeanVM.Protocol.KeccakGkr.Shape.tape ((List.range (P + 5)).map fun i => (inst i).val M) []
            (lanePtT2 (fun m => fe2At sig (8 * m)) qs) ((List.range 25).map fun l => (out l).val M) 0)
          (8 * tapeQ2 qs - 40) (8 * (lay02 P).str2) k).ok1 = true ∧
        (lay2At (fe2At sig) (feAt sig) (fun k => iotaSF LeanVM.Protocol.KeccakGkr.Shape.tape (P + 5) (0 + k))
          (firstClaimSF LeanVM.Protocol.KeccakGkr.Shape.tape ((List.range (P + 5)).map fun i => (inst i).val M) []
            (lanePtT2 (fun m => fe2At sig (8 * m)) qs) ((List.range 25).map fun l => (out l).val M) 0)
          (8 * tapeQ2 qs - 40) (8 * (lay02 P).str2) k).ok2 = true)) := by
  generalize hinstV : ((List.range (P + 5)).map fun i => (inst i).val M) = instV
  generalize houtV : ((List.range 25).map fun l => (out l).val M) = outV
  have hstr : (lay02 P).str2 = 305 + 14 * (P + 1) := rfl
  have hTe : tapeEnd2 P qs = qs + 49 + 24 * (lay02 P).str2 := rfl
  rw [tapeGadgetE2, VF.loopF_eq] at h ⊢
  simp only [hold_bind, assert_bind, gk_bind_fst_eq, gk_pure_apply_eq, gk_getPtr_eq, Ptr.adv_nil] at h ⊢
  obtain ⟨-, hK, hPre, hCp, hL1, hL2, -⟩ := h
  -- the constants
  have hc := fun t (ht : t < 16 * tapeDepth) => cstT_spec hK (t := t) ht
  have hc2 : ∀ t < 16 * tapeDepth - 256, FE.ofK (M.k (p.k + 16 * 16 + t)) =
      if (256 + t) % 16 = 15 then b.val M else FE.ofK (cstKT ((256 + t) / 16) ((256 + t) % 16)) := by
    intro t ht
    rw [show p.k + 16 * 16 + t = p.k + (256 + t) by (clear * -; omega), hc _ (by (clear * - ht; omega))]
  have hAK : SegsAssert M p (loop [] (tplOf (cstInsT (gkS b))) p).2 :=
    segsAssert_loop_iff.mpr fun _ _ => tassert_noA (gnoA_map _ _ fun t => by
      obtain ⟨k, k', hk⟩ := cstIT_op (gkS b) t; rw [hk]; exact Lvm.Loop.Op.noConfusion)
  generalize p.adv (loop [] (tplOf (cstInsT (gkS b))) p).2 = p1 at hPre hCp hL1 hL2 ⊢
  -- the first claim
  have hpre0 := thold2_of_loop hPre (jf := 0) (by simp)
  rw [gk_loop_fst] at hpre0
  obtain ⟨el, lc, fcar, ecar⟩ := preTBT2_spec (u := fun m => fe2At sig (8 * m))
    (fun m hm => lv2_fix hS _ 0 m (by simp only [tapeEnd2, tapeQ2] at hT; (clear * - hT hm; omega))) (fun i => fx2_s2 (inst i)) hpre0
  have hAPre := (segsAssert_loop_iff (M := M) (dims := []) (p := p1)).mpr fun _ _ =>
    noA_preTBT2 P qs (fun i => (inst i).s2) (fun l => (out l).s2) (gkS b) _ _ 0
  simp only [s2_valF_s2, hinstV, houtV] at ecar
  set preT := preTBT2 P qs (fun i => (inst i).s2) (fun l => (out l).s2) (gkS b) 0 with hpreT
  simp only [gk_loop_fst] at hCp hL1 hL2 ⊢
  generalize p1.adv (loop [] (tplOf preT.2) p1).2 = p2 at hCp hL1 hL2 ⊢
  -- the copies
  have hcopy : ∀ j < 57 + P, (⟨M.k (p2.k + 2 * j), M.k (p2.k + 2 * j + 1)⟩ : FE2) =
      (vals2 (iterXv M ⟨p1, [], tplOf preT.2⟩ 0) (iterF M ⟨p1, [], tplOf preT.2⟩ 0) preT.1.carried).getD j 0 :=
    fun j hj => cp2_spec hCp fcar (by rw [lc]; exact hj)
  set cpL := cpIns2 (preT.1.carried.map (S2.gkOut ⟨p1, [], tplOf preT.2⟩)) with hcpL
  have hp3 : (p2.adv (loop [] (tplOf cpL) p2).2).k = p2.k + 2 * (57 + P) := by
    rw [gk_adv_loop, ltw_ones (cpIns2_w _)]
    simp [cpL, cpIns2_length, lc]
  have hACp : SegsAssert M p2 (loop [] (tplOf cpL) p2).2 :=
    segsAssert_loop_iff.mpr fun _ _ => noA_cpIns2 _ _ _
  generalize p2.adv (loop [] (tplOf cpL) p2).2 = p3 at hp3 hL1 hL2 ⊢
  -- the first claim, carried
  have hinstL : instV.length = P + 5 := by rw [← hinstV]; simp
  have hlp : (lanePtT2 (fun m => fe2At sig (8 * m)) qs).length = 5 := by simp [lanePtT2]
  have houtL : outV.length = 25 := by rw [← houtV]; simp
  have hfl : ∀ i < 7, ((List.range 7).map fun i =>
      (eqKernelF (lanePtT2 (fun m => fe2At sig (8 * m)) qs)).getD 0 0 * gx ^ iotaPos i).getD i 0 =
      (eqKernelF (lanePtT2 (fun m => fe2At sig (8 * m)) qs)).getD 0 0 * gx ^ iotaPos i := by
    intro i hi; simp [List.getD_eq_getElem?_getD, hi]
  have hr := rep_firstT2 P hinstL hlp houtL hfl
  have htake : instV.take 4 = (List.range 4).map fun i => (inst i).val M := by
    rw [← hinstV, take_range_map2 _ (by (clear * -; omega))]
  have hdrop : instV.drop 4 = (List.range (P + 1)).map fun i => (inst (4 + i)).val M := by
    rw [← hinstV, drop_range_map2, show P + 5 - 4 = P + 1 by (clear * -; omega)]
  rw [htake, hdrop] at hr
  set C0 := firstClaimSF LeanVM.Protocol.KeccakGkr.Shape.tape instV [] (lanePtT2 (fun m => fe2At sig (8 * m)) qs) outV 0
    with hC0
  have h0 : Rep2 P (layCv2 M ⟨p3, [4], layTpl2 P (tapeQ2 qs) p.k⟩ (57 + P) (cbOf2 P) 0) C0 true :=
    rep2_congr hr fun j hj => by
      show _ = (⟨M.k (p3.k - 2 * (57 + P) + 2 * j), M.k (p3.k - 2 * (57 + P) + 2 * j + 1)⟩ : FE2)
      rw [hp3, show p2.k + 2 * (57 + P) - 2 * (57 + P) + 2 * j = p2.k + 2 * j by (clear * -; omega), hcopy j hj, ecar]
  have hCpt : C0.point.length = P + 1 := by
    show (instV.drop 4 ++ []).length = P + 1
    rw [List.append_nil, List.length_drop, hinstL]; (clear * -; omega)
  -- the first block of layers (0 … 15)
  have hio : ∀ j0 k, j0 + k < 24 → ∀ C : KClaim FE2, C.point.length = P + 1 →
      iotaSF LeanVM.Protocol.KeccakGkr.Shape.tape (P + 5) (0 + (j0 + k)) C =
        (1 + C.point.getD P 0) * iotaFG (keccakRC.getD (tapeDepth - (j0 + k) - 1) 0) C.weights +
          C.point.getD P 0 * iotaFG (keccakRC.getD (tapeDepth - (j0 + k) - 1) 0) C.weights := by
    intro j0 k _ C hC; rw [Nat.zero_add]; exact iotaSF_tape hC
  have hrcm : ∀ j0 k, j0 + k < 24 → keccakRC.getD (tapeDepth - (j0 + k) - 1) 0 ∈ keccakRC :=
    fun j0 k h => rc_mem (by simp only [tapeDepth]; (clear * -; omega))
  obtain ⟨hrep1, hA1⟩ := layers2_spec (d := 4) (N := 16) (first0 := true) (β := b.val M) (C0 := C0)
    (io := fun k => iotaSF LeanVM.Protocol.KeccakGkr.Shape.tape (P + 5) (0 + (0 + k)))
    (rc0 := fun k => keccakRC.getD (tapeDepth - (0 + k) - 1) 0) (rc1 := fun k => keccakRC.getD (tapeDepth - (0 + k) - 1) 0)
    hP hL1 hS (by simp only [tapeQ2, Nat.reducePow]; (clear * - hT hTe; omega)) (by simp only [tapeQ2]; (clear * -; omega))
    (by norm_num) (by norm_num) (fun k hk => ⟨hrcm 0 k (by (clear * - hk; omega)), hrcm 0 k (by (clear * - hk; omega))⟩)
    (fun k hk => hio 0 k (by (clear * - hk; omega)))
    (fun jf hjf => by
      have := tape_cst (j0 := 0) hc (jf := jf) (by simp only [tapeDepth]; (clear * - hjf; omega))
      simp only [Nat.zero_add, Bool.true_and] at this ⊢
      exact ⟨this.1, this.2.1⟩)
    (fun jf hjf => by
      have := tape_cst (j0 := 0) hc (jf := jf) (by simp only [tapeDepth]; (clear * - hjf; omega))
      simp only [Nat.zero_add] at this
      rw [this.2.2, if_pos (by simpa using hjf)])
    (by (clear * - hp3; omega)) h0
  simp only [gk_loop_fst] at hrep1
  have hp4 : ∀ j < 57 + P, _ := fun j (hj : j < 57 + P) =>
    lay_last_cell2 (M := M) hP p3 (tapeQ2 qs) p.k 4 hj
  generalize hp4e : p3.adv (loop [4] (layTpl2 P (tapeQ2 qs) p.k) p3).2 = p4 at hL2 hp4 ⊢
  -- the second block (16 … 23)
  have hL : 8 * tapeQ2 qs - 40 + 16 * (8 * (lay02 P).str2) = 8 * (tapeQ2 qs + 16 * (lay02 P).str2) - 40 := by
    simp only [tapeQ2]; (clear * -; omega)
  have h0' : Rep2 P (layCv2 M ⟨p4, [3], layTpl2 P (tapeQ2 qs + 16 * (lay02 P).str2) (p.k + 16 * 16)⟩ (57 + P)
      (cbOf2 P) 0) (chain2 (fe2At sig) (feAt sig) (fun k => iotaSF LeanVM.Protocol.KeccakGkr.Shape.tape (P + 5)
        (0 + (0 + k))) C0 (8 * tapeQ2 qs - 40) (8 * (lay02 P).str2) 16) false :=
    rep2_congr hrep1 fun j hj => hp4 j hj
  obtain ⟨hrep2, hA2⟩ := layers2_spec (d := 3) (N := 8) (first0 := false) (β := b.val M)
    (io := fun k => iotaSF LeanVM.Protocol.KeccakGkr.Shape.tape (P + 5) (0 + (16 + k)))
    (rc0 := fun k => keccakRC.getD (tapeDepth - (16 + k) - 1) 0) (rc1 := fun k => keccakRC.getD (tapeDepth - (16 + k) - 1) 0)
    hP hL2 hS (by simp only [tapeQ2, Nat.reducePow]; (clear * - hT hTe; omega)) (by simp only [tapeQ2]; (clear * -; omega))
    (by norm_num) (by norm_num) (fun k hk => ⟨hrcm 16 k (by (clear * - hk; omega)), hrcm 16 k (by (clear * - hk; omega))⟩)
    (fun k hk => hio 16 k (by (clear * - hk; omega)))
    (fun jf hjf => by
      have := tape_cst (j0 := 16) hc (jf := jf) (by simp only [tapeDepth]; (clear * - hjf; omega))
      refine ⟨fun i hi => ?_, ?_⟩
      · rw [show p.k + 16 * 16 + (16 * jf + i) = p.k + (16 * (16 + jf) + i) by (clear * -; omega),
          show p.k + 16 * 16 + (16 * jf + (7 + i)) = p.k + (16 * (16 + jf) + (7 + i)) by (clear * -; omega)]
        exact this.1 i hi
      · rw [show p.k + 16 * 16 + (16 * jf + 14) = p.k + (16 * (16 + jf) + 14) by (clear * -; omega), this.2.1,
          if_neg (by rw [beq_iff_eq]; (clear * -; omega)), Bool.false_and, if_neg (by simp)])
    (fun jf hjf => by
      have := tape_cst (j0 := 16) hc (jf := jf) (by simp only [tapeDepth] at hjf ⊢; (clear * - hjf; omega))
      rw [show p.k + 16 * 16 + (16 * jf + 15) = p.k + (16 * (16 + jf) + 15) by (clear * -; omega), this.2.2,
        if_pos (by simpa using hjf)])
    (by
      rw [← hp4e, gk_adv_loop]
      have := lay_ltw2 (q := tapeQ2 qs) (cst := p.k) hP
      have : ltw .K (layTpl2 P (tapeQ2 qs) p.k) ≤ ltw .K (layTpl2 P (tapeQ2 qs) p.k) * 2 ^ ([4] : List Nat).sum :=
        Nat.le_mul_of_pos_right _ Nat.one_le_two_pow
      dsimp only
      (clear * - hp3; omega))
    h0'
  simp only [gk_loop_fst] at hrep2
  have hio2 : (fun k => iotaSF LeanVM.Protocol.KeccakGkr.Shape.tape (P + 5) (0 + (16 + k))) =
      (fun j => (fun k => iotaSF (F := FE2) LeanVM.Protocol.KeccakGkr.Shape.tape (P + 5) (0 + (0 + k))) (16 + j)) := by
    funext k; simp only [Nat.zero_add]
  have hio1 : (fun k => iotaSF (F := FE2) LeanVM.Protocol.KeccakGkr.Shape.tape (P + 5) (0 + (0 + k))) =
      (fun k => iotaSF LeanVM.Protocol.KeccakGkr.Shape.tape (P + 5) (0 + k)) := by
    funext k; simp only [Nat.zero_add]
  rw [hio2, ← hL, ← chain2_add (fe2At sig) (feAt sig)
    (fun k => iotaSF LeanVM.Protocol.KeccakGkr.Shape.tape (P + 5) (0 + (0 + k))) C0 (8 * tapeQ2 qs - 40)
    (8 * (lay02 P).str2) 16 8] at hrep2
  rw [hio1] at hrep2 hA1
  refine ⟨?_, fun hb => ?_⟩
  · exact hrep2
  · rw [← hp4e] at hA2 ⊢
    constructor
    · rintro ⟨-, -, -, -, h1, h2, -⟩
      intro k hk
      rcases Nat.lt_or_ge k 16 with hk1 | hk1
      · exact (hA1 hb).mp h1 k hk1
      · obtain ⟨k', rfl⟩ : ∃ k', k = 16 + k' := ⟨k - 16, by (clear * - hk1; omega)⟩
        have := (hA2 hb).mp h2 k' (by (clear * - hk; omega))
        rw [hio2, ← hL, ← lay2At_add (fe2At sig) (feAt sig)
          (fun k => iotaSF LeanVM.Protocol.KeccakGkr.Shape.tape (P + 5) (0 + (0 + k))) C0 (8 * tapeQ2 qs - 40)
          (8 * (lay02 P).str2) 16 k', hio1] at this
        exact this
    · intro hall
      refine ⟨trivial, hAK, hAPre, hACp, (hA1 hb).mpr fun k hk => hall k (by (clear * - hk; omega)),
        (hA2 hb).mpr fun k hk => ?_, trivial⟩
      rw [hio2, ← hL, ← lay2At_add (fe2At sig) (feAt sig)
        (fun k => iotaSF LeanVM.Protocol.KeccakGkr.Shape.tape (P + 5) (0 + (0 + k))) C0 (8 * tapeQ2 qs - 40)
        (8 * (lay02 P).str2) 16 k, hio1]
      exact hall (16 + k) (by (clear * - hk; omega))

/-! ## The proof-of-work checks by answer lane -/

/-- **Every ground answer `(lane, g)` of `L` passes `V`'s check** on the `E` view `va` (byte `8·lane`). -/
def PowOkV (va : Nat → FE) (L : List (Nat × Nat)) : Prop := ∀ a ∈ L, powOKR a.2 (va (8 * a.1)) = true

theorem powOkV_append (va : Nat → FE) (A B : List (Nat × Nat)) :
    PowOkV va (A ++ B) ↔ PowOkV va A ∧ PowOkV va B := List.forall_mem_append

theorem powOkV_map (va : Nat → FE) (n : Nat) (f : Nat → Nat × Nat) :
    PowOkV va ((List.range n).map f) ↔ ∀ i < n, powOKR (f i).2 (va (8 * (f i).1)) = true := by
  unfold PowOkV
  simp only [List.forall_mem_map, List.mem_range]

theorem powOkV_single (va : Nat → FE) (a : Nat × Nat) : PowOkV va [a] ↔ powOKR a.2 (va (8 * a.1)) = true := by
  unfold PowOkV; simp

theorem powsG_iff (va : Nat → FE) (g : Nat) : ∀ (n p : Nat),
    powsG va g p n = true ↔ ∀ k < n, powOKR g (va (p + 48 + 80 * k)) = true
  | 0, p => by simp [powsG]
  | n + 1, p => by
    rw [powsG, Bool.and_eq_true, powsG_iff va g n (p + 80)]
    constructor
    · rintro ⟨h0, h⟩ k hk
      rcases k with _ | k
      · simpa using h0
      · rw [show p + 48 + 80 * (k + 1) = p + 80 + 48 + 80 * k by ring]; exact h k (by omega)
    · intro h
      refine ⟨by simpa using h 0 (by omega), fun k hk => ?_⟩
      rw [show p + 80 + 48 + 80 * k = p + 48 + 80 * (k + 1) by ring]; exact h (k + 1) (by omega)

theorem sampsG_eq (va : Nat → FE) : ∀ (n p : Nat), sampsG va p n = (List.range n).map fun k => e2OfFE (va (p + 48 + 80 * k))
  | 0, p => rfl
  | n + 1, p => by
    rw [sampsG, sampsG_eq va n (p + 80)]
    apply List.ext_getElem (by simp)
    intro i h1 h2
    rcases i with _ | i
    · simp
    · simp only [List.getElem_cons_succ, List.getElem_map, List.getElem_range]
      rw [show p + 80 + 48 + 80 * i = p + 48 + 80 * (i + 1) by ring]

theorem packSpec2_pw (v : Nat → FE2) (va : Nat → FE) (g : Nat) : ∀ (pt : List FE2) (value scale : FE2) (p : Nat),
    (packSpec2 v va g pt value scale p).2.2.2.2 = true ↔ ∀ i < pt.length, powOKR g (va (p + 80 + 112 * i)) = true
  | [], _, _, p => by simp [packSpec2]
  | r :: rs, value, scale, p => by
    simp only [packSpec2, Bool.and_eq_true, List.length_cons]
    rw [packSpec2_pw v va g rs]
    constructor
    · rintro ⟨h0, h⟩ k hk
      rcases k with _ | k
      · simpa using h0
      · rw [show p + 80 + 112 * (k + 1) = p + 112 + 80 + 112 * k by ring]; exact h k (by omega)
    · intro h
      refine ⟨by simpa using h 0 (by omega), fun k hk => ?_⟩
      rw [show p + 112 + 80 + 112 * k = p + 80 + 112 * (k + 1) by ring]; exact h (k + 1) (by omega)

theorem scSpec2_pw (v : Nat → FE2) (va : Nat → FE) (g count : Nat) : ∀ (R p : Nat) (claim : FE2),
    (scSpec2 v va g count p claim R).2.2 = true ↔
      ∀ i < R, powOKR g (va (ansAt2 (p + i * roundLen2 count) count)) = true
  | 0, p, claim => by simp [scSpec2]
  | R + 1, p, claim => by
    simp only [scSpec2, Bool.and_eq_true]
    rw [scSpec2_pw v va g count R]
    constructor
    · rintro ⟨h0, h⟩ k hk
      rcases k with _ | k
      · simpa using h0
      · rw [show p + (k + 1) * roundLen2 count = p + roundLen2 count + k * roundLen2 count by ring]
        exact h k (by omega)
    · intro h
      refine ⟨by simpa using h 0 (by omega), fun k hk => ?_⟩
      rw [show p + roundLen2 count + k * roundLen2 count = p + (k + 1) * roundLen2 count by ring]
      exact h (k + 1) (by omega)

/-- **A layer's proof-of-work flag** is the checks of its ground answers `layerChals2` (lanes from `q`,
`p + 40 = 8q`). -/
theorem layer_pw (v : Nat → FE2) (va : Nat → FE) (io : KClaim FE2 → FE2) {C : KClaim FE2} {P p q : Nat}
    (hC : C.point.length = P + 1) (hp : p + 40 = 8 * q) :
    (layerSpec2 v va io C p).pw = true ↔ PowOkV va (layerChals2 P q) := by
  show (powOKR gC46 (va (p + 872)) && (packSpec2 v va gC3 C.point _ 1 (p + 904)).2.2.2.2 &&
    (scSpec2 v va gC3 4 (packSpec2 v va gC3 C.point _ 1 (p + 904)).2.2.2.1
      (packSpec2 v va gC3 C.point _ 1 (p + 904)).1 LeanVM.Protocol.Verifier.keccakLocalBits).2.2 &&
    powOKR gC2 (va ((packSpec2 v va gC3 C.point _ 1 (p + 904)).2.2.2.1 +
      LeanVM.Protocol.Verifier.keccakLocalBits * roundLen2 4 + 96))) = true ↔ _
  rw [packSpec2_pos, hC, show LeanVM.Protocol.Verifier.keccakLocalBits = 11 from rfl]
  simp only [Bool.and_eq_true, packSpec2_pw, scSpec2_pw, hC]
  unfold layerChals2
  rw [powOkV_append, powOkV_append, powOkV_append, powOkV_single, powOkV_single, powOkV_map, powOkV_map]
  simp only [ansAt2, roundLen2]
  have e1 : 8 * (q + 104) = p + 872 := by (clear * - hp; omega)
  have e2 : ∀ i, 8 * (q + 113 + 14 * i + 5) = p + 904 + 80 + 112 * i := fun i => by (clear * - e1; omega)
  have e3 : ∀ i, 8 * (q + 113 + 14 * (P + 1) + 16 * i + 7) = p + 904 + 112 * (P + 1) + i * (80 + 16 * (4 - 1)) + 48 +
      16 * (4 - 1) := fun i => by (clear * - e1; omega)
  have e4 : 8 * (q + 289 + 14 * (P + 1) + 7) = p + 904 + 112 * (P + 1) + 11 * (80 + 16 * (4 - 1)) + 96 := by (clear * - e1; omega)
  simp only [e1, e2, e3, e4]

theorem powOkV_flatMap (va : Nat → FE) (n : Nat) (f : Nat → List (Nat × Nat)) :
    PowOkV va ((List.range n).flatMap f) ↔ ∀ i < n, PowOkV va (f i) := by
  unfold PowOkV
  simp only [List.forall_mem_flatMap, List.mem_range]

/-- **`V`'s tape GKR, replayed by the tape gadget** (`tapeGkrD (P + 5)` from the first lane challenge's entry,
`8 qs − 48`): the gadget's carried cells represent `V`'s input claim, `V`'s position after is the gadget's last lane
(`tapeEnd2`, the wiring's first message), and with the gate `1` `V`'s flag after holds iff the flag before does, every
ground answer of the tape passes its proof of work (`tapeChals2`), and every assertion of the gadget holds. -/
theorem tape_spec2 {c : Ctx} {M : Mem} {p : Ptr} {P qs : Nat} {inst out : Nat → C2} {b : Cell}
    {sig : ByteArray} {T : Nat} (hP : layOk2 P = true) (hq : 6 ≤ qs) (hS : Streamed M sig T)
    (hT : tapeEnd2 P qs + 2 ≤ T) (h : SegsHold c M p (tapeGadgetE2 P qs inst out b p).2) (s : RS)
    (hs : s.ent + s.msg = 8 * qs - 48) :
    Rep2 P (fun j => ((tapeGadgetE2 P qs inst out b p).1.cv j).val M)
      (tapeGkrD (P + 5) ((List.range (P + 5)).map fun i => (inst i).val M)
        ((List.range 25).map fun l => (out l).val M) sig s).1 false ∧
    (tapeGkrD (P + 5) ((List.range (P + 5)).map fun i => (inst i).val M)
        ((List.range 25).map fun l => (out l).val M) sig s).2.ent = 8 * tapeEnd2 P qs - 40 ∧
    (tapeGkrD (P + 5) ((List.range (P + 5)).map fun i => (inst i).val M)
        ((List.range 25).map fun l => (out l).val M) sig s).2.msg = 0 ∧
    (b.val M = 1 →
      ((tapeGkrD (P + 5) ((List.range (P + 5)).map fun i => (inst i).val M)
        ((List.range 25).map fun l => (out l).val M) sig s).2.ok = true ↔
        s.ok = true ∧ PowOkV (feAt sig) (tapeChals2 P qs) ∧ SegsAssert M p (tapeGadgetE2 P qs inst out b p).2)) := by
  obtain ⟨hrep, hA⟩ := tape_core2 hP (by (clear * - hq; omega)) hS hT h
  generalize hinstV : ((List.range (P + 5)).map fun i => (inst i).val M) = instV at hrep hA ⊢
  generalize houtV : ((List.range 25).map fun l => (out l).val M) = outV at hrep hA ⊢
  have hinstL : instV.length = P + 5 := by rw [← hinstV]; simp
  rw [tapeGkrD_run sig P instV outV hinstL s, hs]
  have hlanes : sampsG (feAt sig) (8 * qs - 48) 5 = lanePtT2 (fun m => fe2At sig (8 * m)) qs := by
    rw [sampsG_eq, lanePtT2]
    refine List.map_congr_left fun k _ => ?_
    rw [e2OfFE_feAt, show 8 * qs - 48 + 48 + 80 * k = 8 * (qs + 10 * k) by (clear * - hq; omega)]
  have hp0 : 8 * qs - 48 + 400 = 8 * tapeQ2 qs - 40 := by simp only [tapeQ2]; (clear * - hq; omega)
  have hL : 2440 + 112 * (P + 1) = 8 * (lay02 P).str2 := by simp only [lay02, LCfg.str2]; ring
  rw [hlanes, hp0, hL]
  refine ⟨hrep, ?_, rfl, fun hb => ?_⟩
  · simp only [tapeEnd2, tapeQ2, tapeDepth]; (clear * -; omega)
  · show (chainOk2 _ _ _ _ _ _ 24 && (powsG (feAt sig) gC1 (8 * qs - 48) 5 && s.ok)) = true ↔ _
    have hCpt : (firstClaimSF LeanVM.Protocol.KeccakGkr.Shape.tape instV [] (lanePtT2 (fun m => fe2At sig (8 * m)) qs)
        outV 0).point.length = P + 1 := by
      show (instV.drop 4 ++ []).length = P + 1
      rw [List.append_nil, List.length_drop, hinstL]; (clear * -; omega)
    rw [Bool.and_eq_true, Bool.and_eq_true, chainOk2_iff, powsG_iff, (hA hb)]
    unfold tapeChals2
    rw [powOkV_append, powOkV_map, powOkV_flatMap]
    have hpw : ∀ k < 24, (lay2At (fe2At sig) (feAt sig) (fun k => iotaSF LeanVM.Protocol.KeccakGkr.Shape.tape (P + 5) (0 + k))
        (firstClaimSF LeanVM.Protocol.KeccakGkr.Shape.tape instV [] (lanePtT2 (fun m => fe2At sig (8 * m)) qs) outV 0)
        (8 * tapeQ2 qs - 40) (8 * (lay02 P).str2) k).pw = true ↔
        PowOkV (feAt sig) (layerChals2 P (tapeQ2 qs + k * (lay02 P).str2)) := by
      intro k _
      unfold lay2At
      exact layer_pw _ _ _ (by rw [chain2_length, hCpt]) (by
        rw [show k * (8 * (lay02 P).str2) = 8 * (k * (lay02 P).str2) by ring]; simp only [tapeQ2]; (clear * -; omega))
    have hl : ∀ k < 5, powOKR gC1 (feAt sig (8 * qs - 48 + 48 + 80 * k)) = true ↔
        powOKR ((fun k => (qs + 10 * k, 1)) k).2 (feAt sig (8 * ((fun k => (qs + 10 * k, 1)) k).1)) = true := by
      intro k _
      rw [show 8 * qs - 48 + 48 + 80 * k = 8 * (qs + 10 * k) by (clear * - hq; omega)]
    constructor
    · rintro ⟨hlay, hlan, hok⟩
      exact ⟨hok, ⟨fun k hk => (hl k hk).mp (hlan k hk), fun k hk => (hpw k hk).mp (hlay k hk).2.2⟩,
        fun k hk => ⟨(hlay k hk).1, (hlay k hk).2.1⟩⟩
    · rintro ⟨hok, ⟨hlan, hlay⟩, hA'⟩
      exact ⟨fun k hk => ⟨(hA' k hk).1, (hA' k hk).2, (hpw k hk).mpr (hlay k hk)⟩,
        fun k hk => (hl k hk).mpr (hlan k hk), hok⟩

/-- **The tape GKR as a `PhaseAt` fact** (roll 11's HAR form): with the gadget's rows and assertions holding, the
gate `1` and every ground answer's proof of work passing, `V`'s `tapeGkrD (P + 5)` on the cells' values runs from
`8 qs − 48` to the wiring's first message, stays ok, and returns the claim the gadget's carried cells represent. -/
theorem tape_phase2 {c : Ctx} {M : Mem} {p : Ptr} {P qs : Nat} {inst out : Nat → C2} {b : Cell}
    {sig : ByteArray} {T : Nat} (hP : layOk2 P = true) (hq : 6 ≤ qs) (hS : Streamed M sig T)
    (hT : tapeEnd2 P qs + 2 ≤ T) (hh : SegsHold c M p (tapeGadgetE2 P qs inst out b p).2)
    (ha : SegsAssert M p (tapeGadgetE2 P qs inst out b p).2) (hb : b.val M = 1)
    (hpow : PowOkV (feAt sig) (tapeChals2 P qs)) :
    Lvm.Har.PhaseAt (tapeGkrD (P + 5) ((List.range (P + 5)).map fun i => (inst i).val M)
        ((List.range 25).map fun l => (out l).val M)) sig (8 * qs - 48) (8 * tapeEnd2 P qs - 40)
      (tapeGkrD (P + 5) ((List.range (P + 5)).map fun i => (inst i).val M)
        ((List.range 25).map fun l => (out l).val M) sig ⟨8 * qs - 48, 0, true⟩).1 ∧
    Rep2 P (fun j => ((tapeGadgetE2 P qs inst out b p).1.cv j).val M)
      (tapeGkrD (P + 5) ((List.range (P + 5)).map fun i => (inst i).val M)
        ((List.range 25).map fun l => (out l).val M) sig ⟨8 * qs - 48, 0, true⟩).1 false := by
  have hinstL : ((List.range (P + 5)).map fun i => (inst i).val M).length = P + 5 := by simp
  refine ⟨fun s hs hok => ⟨?_, ?_, ?_⟩, (tape_spec2 hP hq hS hT hh _ (by simp)).1⟩
  · rw [tapeGkrD_run sig P _ _ hinstL s, tapeGkrD_run sig P _ _ hinstL ⟨8 * qs - 48, 0, true⟩,
      show s.ent + s.msg = 8 * qs - 48 from hs]
    simp only [Nat.add_zero]
  · exact ((tape_spec2 hP hq hS hT hh s hs).2.2.2 hb).mpr ⟨hok, hpow, ha⟩
  · obtain ⟨-, h1, h2, -⟩ := tape_spec2 hP hq hS hT hh s hs
    show _ + _ = _
    rw [h1, h2]; rfl

end Lvm.Q1
