/-
# The v4 verifier `V vk c π`: the branches `L`, `C`, `N`, `B` (BLUEPRINT §1, §2; new in v4)

The verifier of the entry under the v4 contract. It takes the signer's public key `vk` (the
contract's `Submission.V`), decides the branch from `π` before any query, and is generic in the
leaf verifier `LV` (`SpartanSromVerifierTop`; `SpartanSromVerifier` instantiates it).

* **`L`** (tag word `0`, `|π| ≠ 48`): v3's `leafProg`, unchanged: the header, then `h = s` for
  `n = 0` or the SNARK verifier with oracle queries.
* **`C`** (tag word `0`, `|π| = 48`, the clear leaf `encode (.leaf s n)`): `n ≤ chainCap` and
  `c = leafStmt (chainEnd s n) n`, recomputed with the fast twins, no query.
* **`N`** (`π` exactly `encode (.node c₁ c₂ p₁ p₂)`, the plain node): `c = nodeStmt c₁ c₂` and both
  children accepted by the submission's own `acc` (`accWith`, the contract's `Submission.acc`
  with the fast hashes, `V` recursive on the child's proof, which is shorter). No query.
* **`B`** (`π = encode W ‖ T`, `T` non-empty, `W = .node c₁ c₂ p₁ p₂` decoded from the front; the
  bundle, D-2): with no query, `W` must be a **clear tree** whose every slot has an empty trace,
  the signature `σ0` of slot 1 and a clear leaf or a plain node of clear slots as its proof
  (`clearLeaves`, which lists the clear leaves left to right), `c = nodeStmt c₁ c₂`,
  `SigOk vk (traceDigest []) σ0` (once), every bundled leaf `1 ≤ n ≤ chainCap`,
  `|T| = Σ (32 + leafSize n − 80)` and `Σ qb n ≤ 2^16` (the static query bound). Then
  `runBundle`: for each bundled leaf in order, `h` and `π_S` are read from `T`, the leaf's slot
  statement must be `leafStmt h n`, and the SNARK verifier runs with fresh queries.
* Anything else (under 8 bytes, a tag word other than `0`, `1`, a node that does not decode or is
  neither canonical nor a strict prefix): rejected with no query.

The extractor is the library's copy extractor (`decode π`): `L` and `C` decode to `.leaf s n`,
`N` and `B` to their node witness `W` (`decode` stops before `T`, `decode_append`).

`accV LV vk` is the acceptance predicate of the relation (`accV_eq_acc`: the contract's
`Submission.acc` of every submission whose verifier is `V LV`).
-/
import SpartanSromVerifierTop
import SpartanSromQueries

namespace SpartanSrom
open RecursionFast
open RecursionFast.WitnessSending (encode decode decode_encode size_encode size_eq_length decodeF
  encodeF decodeF_eq encodeF_eq size_child_lt)

variable (LV : LeafVerifier)

/-! ## Parts of the verifier -/

/-- **Acceptance of a signed child under `vk`**, the verifier's program on its proof being
`v ()`: the contract's `Submission.acc` (proof within `proofCap`, queries within `queryCap`,
signature on the trace's digest, `v ()` accepting on the trace used up exactly), with the fast
hashes. (`v` is delayed so that compiled code builds the child's program only after the cheap
checks pass.) -/
def accWith (vk : Digest) (p : Signed) (v : Unit → OProg Bool) : Bool :=
  decide (p.π.size ≤ proofCap) && decide (∀ e ∈ p.tr, e.1.size ≤ queryCap) &&
    SigOkF vk (traceDigestF p.tr) p.σ && decide ((v ()).runSeq p.tr = some true)

/-- **The clear-leaf check** (`C`): the header's length is within `chainCap` and the statement is
the leaf statement of the recomputed chain end, with the fast hashes. -/
def clearLeafOK (c : Digest) (π : Proof) : Bool :=
  decide (leafN π ≤ chainCap) && decide (c = leafStmtF (chainEndF (leafS π) (leafN π)) (leafN π))

/-- A bundled leaf: its slot's statement, its chain start, its chain length. -/
abbrev BLeaf := Digest × Digest × ℕ

/-- **The clear leaves of a clear-tree slot** `(c, p)` whose shared signature is `σ0`, left to
right, or `none` if it is not a clear-tree slot: the slot has an empty trace, the signature
`σ0` and a proof within `proofCap` that is either a clear leaf (48 bytes, tag word `0`: the
slot's statement, the start and the length) or a plain node `encode (.node d₁ d₂ q₁ q₂)` with
statement `nodeStmt d₁ d₂` whose two children are clear-tree slots. -/
def clearLeaves (σ0 : Sig) (c : Digest) (p : Signed) : Option (List BLeaf) :=
  if p.tr.isEmpty = true ∧ p.σ = σ0 ∧ p.π.size ≤ proofCap then
    if p.π.size = 48 ∧ tagWord p.π = 0 then some [(c, leafS p.π, leafN p.π)]
    else
      match decodeF p.π with
      | some (.node d₁ d₂ q₁ q₂) =>
        if _h : encodeF (.node d₁ d₂ q₁ q₂) = p.π then
          if c = nodeStmtF d₁ d₂ then
            match clearLeaves σ0 d₁ q₁, clearLeaves σ0 d₂ q₂ with
            | some l₁, some l₂ => some (l₁ ++ l₂)
            | _, _ => none
          else none
        else none
      | _ => none
  else none
termination_by p.π.size
decreasing_by
  · rw [← _h, encodeF_eq]; exact (size_child_lt _ _ _ _).1
  · rw [← _h, encodeF_eq]; exact (size_child_lt _ _ _ _).2

/-- The bytes of `T` the bundled leaves take: `32 + (leafSize n − 80)` each (`h ‖ π_S`). -/
def bundleBytes (ls : List BLeaf) : ℕ := (ls.map fun x => 32 + (LV.size x.2.2 - 80)).sum

/-- The static query bound of a bundle: the sum of the leaves' SNARK bounds. -/
def bundleQ (ls : List BLeaf) : ℕ := (ls.map fun x => LV.qb x.2.2).sum

/-- **The bundle's SNARK runs** over `T`, from byte `o`: for each bundled leaf `(c, s, n)` in
order, `h` is the next 32 bytes and `π_S` the next `leafSize n − 80`; the statement must be
`leafStmt h n` and the SNARK verifier must accept `(s, n, h, π_S)`. -/
def runBundle (T : ByteArray) : List BLeaf → ℕ → OProg Bool
  | [], _ => .ret true
  | (c, s, n) :: ls, o =>
    if c = leafStmtF (digestFrom T o) n then
      LV.prog s n (digestFrom T o) (T.extract (o + 32) (o + 32 + (LV.size n - 80))) >>= fun b =>
        if b then runBundle T ls (o + 32 + (LV.size n - 80)) else .ret false
    else .ret false

/-- The static checks of a bundle with clear leaves `ls` and trailing bytes `T` (no query). -/
def bundleOK (vk c c₁ c₂ : Digest) (σ0 : Sig) (ls : List BLeaf) (T : ByteArray) : Bool :=
  decide (∀ x ∈ ls, 1 ≤ x.2.2 ∧ x.2.2 ≤ chainCap) && decide (T.size = bundleBytes LV ls) &&
    decide (bundleQ LV ls ≤ 2 ^ 16) && decide (c = nodeStmtF c₁ c₂) &&
    SigOkF vk (traceDigestF []) σ0

/-- **The bundle branch** (`B`) on `π` whose front decodes to `.node c₁ c₂ p₁ p₂`: its encoding
is a strict prefix of `π`, the node is a clear tree under slot 1's signature, the static checks
hold, then the SNARK runs over the rest `T`. -/
def bundleProg (vk c : Digest) (π : Proof) (c₁ c₂ : Digest) (p₁ p₂ : Signed) : OProg Bool :=
  if IsStrictPrefix (encodeF (.node c₁ c₂ p₁ p₂)) π then
    match clearLeaves p₁.σ c₁ p₁, clearLeaves p₁.σ c₂ p₂ with
    | some l₁, some l₂ =>
      let T := π.extract (encodeF (.node c₁ c₂ p₁ p₂)).size π.size
      if bundleOK LV vk c c₁ c₂ p₁.σ (l₁ ++ l₂) T then runBundle LV T (l₁ ++ l₂) 0
      else .ret false
    | _, _ => .ret false
  else .ret false

/-! ## The verifier -/

/-- **The verifier** under the public key `vk` (BLUEPRINT §2): the branches `L`, `C`, `N`, `B`,
decided from `π` before any query; `N` accepts its children with the submission's own `acc`,
recursively on the (shorter) child proofs. -/
def V (vk c : Digest) (π : Proof) : OProg Bool :=
  if π.size < 8 then .ret false
  else if tagWord π = 0 then
    if π.size = 48 then .ret (clearLeafOK c π) else leafProg LV c π
  else
    match decodeF π with
    | some (.node c₁ c₂ p₁ p₂) =>
      if _h : encodeF (.node c₁ c₂ p₁ p₂) = π then
        .ret (decide (c = nodeStmtF c₁ c₂) && accWith vk p₁ (fun _ => V vk c₁ p₁.π) &&
          accWith vk p₂ (fun _ => V vk c₂ p₂.π))
      else bundleProg LV vk c π c₁ c₂ p₁ p₂
    | _ => .ret false
termination_by π.size
decreasing_by
  · rw [← _h, encodeF_eq]; exact (size_child_lt _ _ _ _).1
  · rw [← _h, encodeF_eq]; exact (size_child_lt _ _ _ _).2

/-- **The acceptance predicate of the relation**: `accWith` with the verifier `V LV vk`. -/
def accV (vk c : Digest) (p : Signed) : Bool := accWith vk p fun _ => V LV vk c p.π

/-- **`accV` is the contract's `acc`** of every submission whose verifier is `V LV`. -/
theorem accV_eq_acc (S : Submission) (hV : S.V = V LV) : S.acc = accV LV := by
  funext vk c p
  rw [Submission.acc, accV, accWith, hV, SigOkF_eq, traceDigestF_eq]

/-! ## The branches, unfolded -/

theorem V_short {vk c : Digest} {π : Proof} (h : π.size < 8) : V LV vk c π = .ret false := by
  rw [V]; simp [h]

theorem V_clear {vk c : Digest} {π : Proof} (hs : π.size = 48) (ht : tagWord π = 0) :
    V LV vk c π = .ret (clearLeafOK c π) := by
  rw [V]; simp [hs, ht]

theorem V_leaf {vk c : Digest} {π : Proof} (h8 : 8 ≤ π.size) (hs : π.size ≠ 48)
    (ht : tagWord π = 0) : V LV vk c π = leafProg LV c π := by
  rw [V]; simp [show ¬ π.size < 8 by omega, hs, ht]

/-- Off tag word `0`, `V` reads the node in front of `π`. -/
theorem V_tag {vk c : Digest} {π : Proof} (h8 : 8 ≤ π.size) (ht : tagWord π ≠ 0) :
    V LV vk c π = match decodeF π with
      | some (.node c₁ c₂ p₁ p₂) =>
        if encodeF (.node c₁ c₂ p₁ p₂) = π then
          .ret (decide (c = nodeStmtF c₁ c₂) && accV LV vk c₁ p₁ && accV LV vk c₂ p₂)
        else bundleProg LV vk c π c₁ c₂ p₁ p₂
      | _ => .ret false := by
  rw [V]
  simp only [show ¬ π.size < 8 by omega, ht, ↓reduceIte, accV, dite_eq_ite]

/-! ## The query bound -/

section Queries
open OProg

variable {LV}

theorem atMost_runBundle (T : ByteArray)
    (hq : ∀ s n h π, n ≤ chainCap → AtMost (LV.qb n) (LV.prog s n h π)) :
    ∀ (ls : List BLeaf) (o : ℕ), (∀ x ∈ ls, x.2.2 ≤ chainCap) →
      AtMost (bundleQ LV ls) (runBundle LV T ls o)
  | [], _, _ => atMost_ret _ _
  | (c, s, n) :: ls, o, h => by
    rw [runBundle]
    have hn : n ≤ chainCap := h _ (List.mem_cons_self ..)
    have hb : bundleQ LV ((c, s, n) :: ls) = LV.qb n + bundleQ LV ls := by
      simp [bundleQ]
    rw [hb]
    refine AtMost.ite ((hq _ _ _ _ hn).bind fun b => AtMost.ite ?_ (atMost_ret _ _))
      (atMost_ret _ _)
    exact atMost_runBundle T hq ls _ fun x hx => h x (List.mem_cons_of_mem _ hx)

/-- **`V` asks at most `2^16` queries along every path of answers** (the static bound of the
bundle branch; at most `qb n` on the leaf branch), given the leaf verifier's bounds. -/
theorem atMost_V (hq : ∀ s n h π, n ≤ chainCap → AtMost (LV.qb n) (LV.prog s n h π))
    (hqb : ∀ n ≤ chainCap, LV.qb n ≤ 2 ^ 16) (vk c : Digest) (π : Proof) :
    AtMost (2 ^ 16) (V LV vk c π) := by
  by_cases h8 : π.size < 8
  · rw [V_short LV h8]; exact atMost_ret _ _
  by_cases ht : tagWord π = 0
  · by_cases hs : π.size = 48
    · rw [V_clear LV hs ht]; exact atMost_ret _ _
    rw [V_leaf LV (by omega) hs ht, leafProg]
    split_ifs with hh hn
    · exact atMost_ret _ _
    · have hcap := ((leafHeaderOK_iff LV).mp hh).1
      exact (hq _ _ _ _ hcap).mono (hqb _ hcap)
    · exact atMost_ret _ _
  rw [V_tag LV (by omega) ht]
  split
  · split_ifs
    · exact atMost_ret _ _
    · rw [bundleProg]
      split_ifs
      · split
        · dsimp only
          split_ifs with hok
          · simp only [bundleOK, Bool.and_eq_true, decide_eq_true_eq] at hok
            exact (atMost_runBundle _ hq _ 0 fun x hx => (hok.1.1.1.1 x hx).2).mono hok.1.1.2
          · exact atMost_ret _ _
        · exact atMost_ret _ _
      · exact atMost_ret _ _
  · exact atMost_ret _ _

end Queries

/-! ## Knowledge: what an accepted proof gives (`final`) -/

section Final

variable {LV}

/-- A bundled leaf whose statement holds: its length within `chainCap`, its slot's statement the
leaf statement of its chain's end. -/
def GoodLeaf (x : BLeaf) : Prop :=
  x.2.2 ≤ chainCap ∧ x.1 = leafStmt (chainEnd x.2.1 x.2.2) x.2.2

theorem runBundle_final {T : ByteArray} {L : Log}
    (hleaf : ∀ s n h πS, 1 ≤ n → n ≤ chainCap → πS.size = LV.size n - 80 →
      (LV.prog s n h πS).runLog L = some true → chainEnd s n = h) :
    ∀ (ls : List BLeaf) (o : ℕ), (∀ x ∈ ls, 1 ≤ x.2.2 ∧ x.2.2 ≤ chainCap) →
      o + bundleBytes LV ls ≤ T.size → (runBundle LV T ls o).runLog L = some true →
      ∀ x ∈ ls, GoodLeaf x
  | [], _, _, _, _ => by simp
  | (c, s, n) :: ls, o, hn, hsz, hrun => by
    have hb : bundleBytes LV ((c, s, n) :: ls) = 32 + (LV.size n - 80) + bundleBytes LV ls := by
      simp [bundleBytes]
    rw [runBundle] at hrun
    split_ifs at hrun with hc
    · rw [OProg.runLog_bind] at hrun
      cases hp : (LV.prog s n (digestFrom T o)
          (T.extract (o + 32) (o + 32 + (LV.size n - 80)))).runLog L with
      | none => rw [hp] at hrun; cases hrun
      | some b =>
        rw [hp, Option.bind_some] at hrun
        cases b with
        | false => simp [RecursionFast.OProg.runLog] at hrun
        | true =>
          simp only [↓reduceIte] at hrun
          have hn1 : 1 ≤ n ∧ n ≤ chainCap := hn _ (List.mem_cons_self ..)
          rw [hb] at hsz
          have hend := hleaf _ _ _ _ hn1.1 hn1.2 (by rw [ByteArray.size_extract]; omega) hp
          intro x hx
          rcases List.mem_cons.mp hx with rfl | hx
          · exact ⟨hn1.2, by rw [hc, leafStmtF_eq, hend]⟩
          · exact runBundle_final hleaf ls _ (fun y hy => hn y (List.mem_cons_of_mem _ hy))
              (by omega) hrun x hx
    · simp [RecursionFast.OProg.runLog] at hrun

/-- **Every slot of a clear tree whose bundled leaves hold is accepted** (`accV`): it asks no
query, its trace is empty, its signature is the checked `σ0`, a clear leaf is recomputed by `C`
and a plain node is accepted by `N`, by induction on the tree. -/
theorem clear_acc {vk : Digest} {σ0 : Sig} (hσ : SigOk vk (traceDigest []) σ0 = true) :
    ∀ (m : ℕ) (c : Digest) (p : Signed) (l : List BLeaf), p.π.size = m →
      clearLeaves σ0 c p = some l → (∀ x ∈ l, GoodLeaf x) → accV LV vk c p = true := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
  intro c p l hm hcl hgood
  rw [clearLeaves] at hcl
  split_ifs at hcl with hslot hC
  · obtain ⟨hemp, hsig, hcap⟩ := hslot
    cases hcl
    have hg := hgood _ (List.mem_singleton_self _)
    have htr : p.tr = [] := List.isEmpty_iff.mp hemp
    rw [accV, accWith, V_clear LV hC.1 hC.2]
    simp only [Bool.and_eq_true, decide_eq_true_eq]
    refine ⟨⟨⟨hcap, by simp [htr]⟩, by rw [htr, hsig, SigOkF_eq, traceDigestF_eq]; exact hσ⟩, ?_⟩
    have hok : clearLeafOK c p.π = true := by
      simp only [clearLeafOK, leafStmtF_eq, chainEndF_eq, Bool.and_eq_true, decide_eq_true_eq]
      exact hg
    rw [htr, hok]; rfl
  · obtain ⟨hemp, hsig, hcap⟩ := hslot
    have htr : p.tr = [] := List.isEmpty_iff.mp hemp
    split at hcl
    · rename_i d₁ d₂ q₁ q₂ hd
      split_ifs at hcl with he hc
      split at hcl
      · rename_i l₁ l₂ h₁ h₂
        cases hcl
        have hlt := size_child_lt d₁ d₂ q₁ q₂
        rw [← encodeF_eq, he, hm] at hlt
        have a₁ := ih _ hlt.1 d₁ q₁ l₁ rfl h₁ fun x hx => hgood x (List.mem_append_left _ hx)
        have a₂ := ih _ hlt.2 d₂ q₂ l₂ rfl h₂ fun x hx => hgood x (List.mem_append_right _ hx)
        have h8 : 8 ≤ p.π.size := by
          rw [← he, encodeF_eq]; exact size_encode_node _ _ _ _
        have ht : tagWord p.π ≠ 0 := by rw [← he, encodeF_eq, tagWord_encode_node]; decide
        rw [accV, accWith, V_tag LV h8 ht]
        simp only [hd, he, ↓reduceIte, Bool.and_eq_true, decide_eq_true_eq]
        refine ⟨⟨⟨hcap, by simp [htr]⟩, by rw [htr, hsig, SigOkF_eq, traceDigestF_eq]; exact hσ⟩,
          ?_⟩
        rw [htr]
        simp [RecursionFast.OProg.runSeq, hc, a₁, a₂]
      · cases hcl
    · cases hcl

/-- **`final` for `V`**: a proof `V` accepts on a log decodes (the library's `decode`) to a
witness of the relation of `accV`, given that the SNARK verifier, accepting on the log, proves
its chain (for the entry's SNARK, under `μ L < 1`: `SpartanSromSoundnessKSFinal`). -/
theorem V_final {vk c : Digest} {π : Proof} {L : Log}
    (hleaf : ∀ s n h πS, 1 ≤ n → n ≤ chainCap → πS.size = LV.size n - 80 →
      (LV.prog s n h πS).runLog L = some true → chainEnd s n = h)
    (hacc : (V LV vk c π).runLog L = some true) :
    ∃ w, decode π = some w ∧ Rel (accV LV vk) c w := by
  by_cases h8 : π.size < 8
  · rw [V_short LV h8] at hacc; cases hacc
  by_cases ht : tagWord π = 0
  · by_cases hs : π.size = 48
    · rw [V_clear LV hs ht] at hacc
      have hok : clearLeafOK c π = true := Option.some.inj hacc
      simp only [clearLeafOK, Bool.and_eq_true, decide_eq_true_eq, leafStmtF_eq,
        chainEndF_eq] at hok
      exact ⟨_, decode_leaf (by omega) ht, hok⟩
    rw [V_leaf LV (by omega) hs ht] at hacc
    obtain ⟨hdec, hcap, hc, h0, h1⟩ := leafProg_final LV hacc ht
    obtain ⟨-, hsize, -⟩ := (leafHeaderOK_iff LV).mp (leafProg_header LV hacc rfl)
    refine ⟨_, hdec, hcap, ?_⟩
    by_cases hn : leafN π = 0
    · rw [hc, hn, h0 hn]; rfl
    · rw [hc, hleaf _ _ _ _ (Nat.one_le_iff_ne_zero.mpr hn) hcap
        (by rw [leafSnark, ByteArray.size_extract, hsize]; omega) (h1 hn)]
  rw [V_tag LV (by omega) ht] at hacc
  split at hacc
  · rename_i c₁ c₂ p₁ p₂ hd
    have hdec : decode π = some (.node c₁ c₂ p₁ p₂) := by rw [← decodeF_eq, hd]
    refine ⟨_, hdec, ?_⟩
    split_ifs at hacc with he
    · have hok := Option.some.inj hacc
      simp only [Bool.and_eq_true, decide_eq_true_eq, nodeStmtF_eq] at hok
      exact ⟨hok.1.1, hok.1.2, hok.2⟩
    · rw [bundleProg] at hacc
      split_ifs at hacc with hpre
      swap; · cases hacc
      split at hacc
      · rename_i l₁ l₂ h₁ h₂
        dsimp only at hacc
        split_ifs at hacc with hok
        swap; · cases hacc
        simp only [bundleOK, Bool.and_eq_true, decide_eq_true_eq] at hok
        obtain ⟨⟨⟨⟨hn, hT⟩, -⟩, hc⟩, hσ⟩ := hok
        rw [SigOkF_eq, traceDigestF_eq] at hσ
        have hgood := runBundle_final hleaf _ 0 hn (by rw [Nat.zero_add, hT]) hacc
        refine ⟨by rw [hc, nodeStmtF_eq], ?_, ?_⟩
        · exact clear_acc hσ _ _ _ _ rfl h₁ fun x hx => hgood x (List.mem_append_left _ hx)
        · exact clear_acc hσ _ _ _ _ rfl h₂ fun x hx => hgood x (List.mem_append_right _ hx)
      · cases hacc
  · cases hacc

end Final

/-! ## Completeness of the node branch -/

section Complete

variable {LV}

/-- **An accepted child fits the output format** (so a node witness's honest encoding decodes
back): its proof within `proofCap`, its trace at most `2^16` entries (`V` asks at most that many
queries along every path, and the trace is used up exactly), its queries within `queryCap`, and
`SigOk` fixes the signature's index range and counts. -/
theorem fits_of_accV {vk : Digest} (hq : ∀ c π, OProg.AtMost (2 ^ 16) (V LV vk c π))
    {c : Digest} {p : Signed} (h : accV LV vk c p = true) : p.Fits := by
  simp only [accV, accWith, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨hπ, hqc⟩, hσ⟩, hrun⟩ := h
  rw [SigOkF_eq] at hσ
  simp only [SigOk, Bool.and_eq_true, decide_eq_true_eq] at hσ
  obtain ⟨⟨⟨hi, ho⟩, hp⟩, -⟩ := hσ
  have hl := (hq c p.π).runSeq_length hrun
  refine ⟨hπ.trans_lt (by unfold proofCap; norm_num), hl.trans_lt (by norm_num),
    fun e he => (hqc e he).trans_lt (by unfold queryCap; norm_num),
    hi.trans (by unfold sigHeight; norm_num), ho, hp⟩

/-- **Node completeness**: the encoding of a node witness of the relation is accepted by `N`,
with no query. -/
theorem V_encode_node {vk : Digest} (hq : ∀ c π, OProg.AtMost (2 ^ 16) (V LV vk c π))
    {c c₁ c₂ : Digest} {p₁ p₂ : Signed} (hR : Rel (accV LV vk) c (.node c₁ c₂ p₁ p₂)) :
    V LV vk c (encode (.node c₁ c₂ p₁ p₂)) = .ret true := by
  obtain ⟨hc, h₁, h₂⟩ := hR
  have hfit : (Wit.node c₁ c₂ p₁ p₂).Fits := ⟨fits_of_accV hq h₁, fits_of_accV hq h₂⟩
  rw [V_tag LV (size_encode_node _ _ _ _) (by rw [tagWord_encode_node]; decide), decodeF_eq,
    decode_encode _ hfit]
  simp [encodeF_eq, hc, h₁, h₂, nodeStmtF_eq]

end Complete

end SpartanSrom
