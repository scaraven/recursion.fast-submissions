-- New for `flock-recursive` (BLUEPRINT §4.3, §5.4, §7, stage S-E2).
import FRNodeLayout
import FRWots
import FRVerifier

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
open RecursionFast Circ Layout

/-- H cell of slot `σ`'s seed payload element `e` (A.7: the payload starts at stream element 1;
stream element `e'` is slot `4 + e' mod 4` of block `chainBase_σ + ⌊e'/4⌋`). -/
def seedCell (σ e : ℕ) : ℕ := (σ * chainN + (1 + e) / 4) * 128 + 4 + (1 + e) % 4

/-- **The public cells in A.7's order** (revision 3.9): `pub_0 = f[Mbase]`; slot 1's `vk` and `c₁`
halves; slot 2's `vk` and `c₂` halves; the six padding cells `pad` (a parameter: A.7 names them,
the prover's layout fixes them). -/
def pubCells (pad : List ℕ) : List ℕ :=
  oneCell :: (List.range 2).flatMap (fun σ => (List.range 4).map (seedCell σ)) ++ pad

/-- A digest's two F halves. -/
def halves (d : Digest) : List F := [dlo d, dhi d]

/-- Their values: `1`, the digests' halves, six zeros. -/
def pubVals (vk c₁ c₂ : Digest) : List F :=
  1 :: (halves vk ++ halves c₁ ++ halves vk ++ halves c₂) ++ List.replicate 6 0

/-- **`PubCells`** (§4.3, A.7): the point claims on `f` hold. -/
def PubCells (w : Asg) (vk c₁ c₂ : Digest) (pad : List ℕ) : Prop :=
  (pubCells pad).map w = pubVals vk c₁ c₂

theorem PubCells.one {w : Asg} {vk c₁ c₂ : Digest} {pad : List ℕ} (h : PubCells w vk c₁ c₂ pad) :
    w oneCell = 1 := by
  simpa [PubCells, pubCells, pubVals] using congrArg List.head? h

/-- **What `final` establishes of slot `σ`'s M cells** (input `inp`, trace `tr`). -/
structure SlotHolds (impl : OpImpl) (fin : Finals) (σ : ℕ) (w : Asg) (inp : Input)
    (tr : Trace) : Prop where
  /-- Lr: the selector cells are bits. -/
  bits : ∀ κ, IsBitCell w (selCells σ κ)
  /-- The one-hot rows (`assertOneHot` on `kindSel`). -/
  oneHot : OneHotRows w oneCell (selCells σ)
  /-- E2: every compiled row holds. -/
  rows : ∀ r ∈ (slotCS fin σ).rows, r.Holds w
  /-- At the selected kind: `hdr`'s kind byte, the run, the imports and the foreign flags. -/
  run : ∀ κ, SelOk w (muxP oneCell (selCells σ)) κ →
    inp.π.data[0]? = some κ.byte ∧ ∃ s : St, exec impl κ inp (gen fin .mux).ops St.init tr =
      some (s, []) ∧
      (∀ i ∈ (slotCS fin σ).imp, RepS w ((slotCS fin σ).slot i) (rd s.regs i)) ∧
      (∀ p ∈ (slotCS fin σ).fors, flagOf impl κ inp (s.regs.extract 0 p.2) p.1 = true)

theorem gen_mux_eta (fin : Finals) : gen fin .mux = ⟨.mux, (gen fin .mux).ops⟩ := by
  unfold gen genWith; rfl

/-- The fixed-kind program is the mux program's op list (one list for all kinds). -/
theorem gen_fixed_eq (fin : Finals) (k : FR.Kind) :
    gen fin (.fixed k) = ⟨.fixed k, (gen fin .mux).ops⟩ := by
  unfold gen genWith; rfl

/-- **One slot** (§4.3 (1)–(8)): the slot's mux program accepts. -/
theorem slot_sound {impl : OpImpl} {fin : Finals} {σ : ℕ} {w : Asg} {inp : Input} {tr : Trace}
    (hp : w oneCell = 1) (h : SlotHolds impl fin σ w inp tr) :
    semIR impl (gen fin .mux) inp tr = some true := by
  obtain ⟨hbits, hhot, hrows, hrun⟩ := h
  obtain ⟨κ, hκ⟩ := oneHot_of_rows hp hbits hhot
  obtain ⟨hbyte, s, he, hi, hf⟩ := hrun κ hκ
  unfold slotCS at hrows hi hf
  rw [gen_mux_eta]
  generalize (gen fin .mux).ops = ops at he hrows hi hf ⊢
  exact (compile_mux_sound (slotBase σ) hκ hbyte he hrows hi hf).1

/-- **`node_m_sound`** (the M side of `node_sound`, §4.3): with the public `one` cell and both
slots' facts, both children's mux programs accept. -/
theorem node_m_sound {impl : OpImpl} {fin : Finals} {w : Asg} {inp₁ inp₂ : Input}
    {tr₁ tr₂ : Trace} (hp : w oneCell = 1) (h₁ : SlotHolds impl fin 0 w inp₁ tr₁)
    (h₂ : SlotHolds impl fin 1 w inp₂ tr₂) :
    semIR impl (gen fin .mux) inp₁ tr₁ = some true ∧
      semIR impl (gen fin .mux) inp₂ tr₂ = some true :=
  ⟨slot_sound hp h₁, slot_sound hp h₂⟩

theorem byte_of_ofByte {b : UInt8} {k : FR.Kind} (h : Kind.ofByte? b = some k) : b = k.byte := by
  unfold Kind.ofByte? at h
  split_ifs at h <;> cases h <;> simp_all [Kind.byte]

/-- Nine public cells, then the paddings. -/
theorem pubCells_length (pad : List ℕ) : (pubCells pad).length = 9 + pad.length := by
  simp [pubCells]; omega

/-- Non-vacuity of `PubCells`: the nine cells are distinct (so values can be assigned freely). -/
theorem pubCells_nodup : (pubCells []).Nodup := by decide

/-- A SNARK child's proof starts with its kind byte. -/
theorem byte_of_kindOf {π : Proof} {k : FR.Kind} (h : kindOf π = .snark k) :
    π.data[0]? = some k.byte := by
  unfold kindOf at h
  rcases e : π.data[0]? with _ | b <;> simp only [e, Option.bind_none, Option.bind_some] at h
  · cases h
  · rcases e' : Kind.ofByte? b with _ | k' <;> simp only [e'] at h
    · cases h
    · split_ifs at h; cases h; rw [byte_of_ofByte e']

/-- **`node_sound` for one SNARK child** (§4.3, §5.4): the child's size and query facts (format),
its signature (`wots_sound` over the chain digest), `PubCells` and the slot's `SlotHolds` give the
contract-facing acceptance `accV impl fin vk c p` (S-F's `V_snark`, `runSeq_runIR`,
`semIR_mux_eq`, `slot_sound`). -/
theorem child_sound {impl : OpImpl} {fin : Finals} {vk c : Digest} {p : Signed} {k : FR.Kind}
    {σ : ℕ} {w : Asg} (hk : kindOf p.π = .snark k) (hsize : p.π.size ≤ proofCap)
    (hq : p.tr.length ≤ qV) (hcap : ∀ e ∈ p.tr, e.1.size ≤ queryCap)
    (hsig : SigOk vk (traceDigest p.tr) p.σ = true) (hp : w oneCell = 1)
    (hM : SlotHolds impl fin σ w ⟨vk, c, p.π⟩ p.tr) : accV impl fin vk c p = true := by
  have hrun : (Vwith impl fin vk c p.π).runSeq p.tr = some true := by
    rw [V_snark impl fin vk c p.π hk, runSeq_runIR, gen_fixed_eq,
      ← semIR_mux_eq (inp := ⟨vk, c, p.π⟩) (byte_of_kindOf hk), ← gen_mux_eta]
    exact slot_sound hp hM
  simp only [accV, accWith, hsize, hq, SigOkF_eq, traceDigestF_eq, hsig, hrun, decide_true,
    Bool.and_true, Bool.true_and, decide_eq_true_eq]
  exact hcap

/-- **`node_sound`** (§4.3): both SNARK children accepted, under one `PubCells`. -/
theorem node_sound {impl : OpImpl} {fin : Finals} {vk c₁ c₂ : Digest} {p₁ p₂ : Signed}
    {k₁ k₂ : FR.Kind} {w : Asg} {pad : List ℕ} (hp : PubCells w vk c₁ c₂ pad)
    (hk₁ : kindOf p₁.π = .snark k₁) (hk₂ : kindOf p₂.π = .snark k₂)
    (hs₁ : p₁.π.size ≤ proofCap ∧ p₁.tr.length ≤ qV ∧ ∀ e ∈ p₁.tr, e.1.size ≤ queryCap)
    (hs₂ : p₂.π.size ≤ proofCap ∧ p₂.tr.length ≤ qV ∧ ∀ e ∈ p₂.tr, e.1.size ≤ queryCap)
    (hg₁ : SigOk vk (traceDigest p₁.tr) p₁.σ = true) (hg₂ : SigOk vk (traceDigest p₂.tr) p₂.σ = true)
    (h₁ : SlotHolds impl fin 0 w ⟨vk, c₁, p₁.π⟩ p₁.tr)
    (h₂ : SlotHolds impl fin 1 w ⟨vk, c₂, p₂.π⟩ p₂.tr) :
    accV impl fin vk c₁ p₁ = true ∧ accV impl fin vk c₂ p₂ = true :=
  ⟨child_sound hk₁ hs₁.1 hs₁.2.1 hs₁.2.2 hg₁ hp.one h₁,
    child_sound hk₂ hs₂.1 hs₂.2.1 hs₂.2.2 hg₂ hp.one h₂⟩

/-- The slots' selector cells and M halves are disjoint (slot 1's cells start `2^14` elements,
resp. `2^20`, after slot 0's). -/
theorem slots_apart :
    selCells 0 .N30 < selCells 1 .L32 ∧ slotBase 0 + slotM = slotBase 1 := by
  simp only [selCells, slotBase, slotM]; omega

end Node
end FR
