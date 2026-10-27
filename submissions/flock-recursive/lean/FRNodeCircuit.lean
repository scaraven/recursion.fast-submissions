-- New for `flock-recursive` (BLUEPRINT §4.3, §5.4, §7, stage S-E2).
import FRVIREval
import FRWots

/-!
# The node circuit: `PubCells`, the M side of `node_sound`

BLUEPRINT §4.3 ("What the circuit asserts of slot `σ`") and §5.4 (what `final` hands over).

The node's region M holds both slots' compiled programs (`FRVIREval.slotCS fin σ`, i.e.
`compileMux (gen fin .mux)` from `slotBase σ`), sharing M's `one` cell `f[Mbase] = 1`
(`PubCells`, a point claim, revision 3.6). `SlotHolds` bundles what `final` establishes about one
slot's M cells: the L selector cells are bits (Lr) satisfying the one-hot rows, every compiled row
holds (E2), and — at the kind the selector picks — the slot's run uses its trace up, its imports'
cells hold their values (trace cells, irregular entries, templates) and its foreign flags hold
(the H blocks' pins and point claims). **`node_m_sound`**: then both slots' **mux** programs
accept (`semIR (gen fin .mux) = some true`).

The H side (`blake2s_chain` for the digest chains, `wots_sound`, `hashStmt_sound` with the gated
rows) is proved in `FRBlockStream`/`FRWots`; assembling it with the M side over the packed
witness `z` (`ShHolds`, `LrHolds`, `EHolds`, `readSigned`) needs `FRVerifier`'s `accWith` (S-F) and
is left to the RESULT's open items.
-/

namespace FR
namespace Node
open RecursionFast Circ Eval

/-- **The node's public cells** fixed by point claims (§4.3): M's `one` cell. (`vk`, `cᵢ` are the
`input` imports of each slot, `SlotHolds.imp`.) -/
structure PubCells (w : Asg) : Prop where
  one : w Layout.oneCell = 1

/-- **What `final` establishes of slot `σ`'s M cells** (input `inp`, trace `tr`). -/
structure SlotHolds (impl : OpImpl) (fin : Finals) (σ : ℕ) (w : Asg) (inp : Input)
    (tr : Trace) : Prop where
  /-- Lr: the selector cells are bits. -/
  bits : ∀ κ, IsBitCell w (selCells σ κ)
  /-- The one-hot rows (`assertOneHot` on `kindSel`). -/
  oneHot : OneHotRows w Layout.oneCell (selCells σ)
  /-- E2: every compiled row holds. -/
  rows : ∀ r ∈ (slotCS fin σ).rows, r.Holds w
  /-- At the selected kind: `hdr`'s kind byte, the run, the imports and the foreign flags. -/
  run : ∀ κ, SelOk w (muxP Layout.oneCell (selCells σ)) κ →
    inp.π.data[0]? = some κ.byte ∧ ∃ s : St, exec impl κ inp (gen fin .mux).ops St.init tr =
      some (s, []) ∧
      (∀ i ∈ (slotCS fin σ).imp, RepS w ((slotCS fin σ).slot i) (rd s.regs i)) ∧
      (∀ p ∈ (slotCS fin σ).fors, flagOf impl κ inp (s.regs.extract 0 p.2) p.1 = true)

theorem gen_mux_eta (fin : Finals) : gen fin .mux = ⟨.mux, (gen fin .mux).ops⟩ := by
  unfold gen genWith; rfl

/-- **One slot** (§4.3 (1)–(8)): the slot's mux program accepts. -/
theorem slot_sound {impl : OpImpl} {fin : Finals} {σ : ℕ} {w : Asg} {inp : Input} {tr : Trace}
    (hp : PubCells w) (h : SlotHolds impl fin σ w inp tr) :
    semIR impl (gen fin .mux) inp tr = some true := by
  obtain ⟨hbits, hhot, hrows, hrun⟩ := h
  obtain ⟨κ, hκ⟩ := oneHot_of_rows hp.one hbits hhot
  obtain ⟨hbyte, s, he, hi, hf⟩ := hrun κ hκ
  unfold slotCS at hrows hi hf
  rw [gen_mux_eta]
  generalize (gen fin .mux).ops = ops at he hrows hi hf ⊢
  exact (compile_mux_sound (slotBase σ) hκ hbyte he hrows hi hf).1

/-- **`node_m_sound`** (the M side of `node_sound`, §4.3): with the public `one` cell and both
slots' facts, both children's mux programs accept. -/
theorem node_m_sound {impl : OpImpl} {fin : Finals} {w : Asg} {inp₁ inp₂ : Input}
    {tr₁ tr₂ : Trace} (hp : PubCells w) (h₁ : SlotHolds impl fin 0 w inp₁ tr₁)
    (h₂ : SlotHolds impl fin 1 w inp₂ tr₂) :
    semIR impl (gen fin .mux) inp₁ tr₁ = some true ∧
      semIR impl (gen fin .mux) inp₂ tr₂ = some true :=
  ⟨slot_sound hp h₁, slot_sound hp h₂⟩

/-- The slots' selector cells and M halves are disjoint (slot 1's cells start `2^14` elements,
resp. `2^20`, after slot 0's). -/
theorem slots_apart :
    selCells 0 .N30 < selCells 1 .L32 ∧ slotBase 0 + Layout.slotM = slotBase 1 := by
  simp only [selCells, slotBase, Layout.slotM]; omega

end Node
end FR
