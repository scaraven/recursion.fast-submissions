-- lvm6 C4 (CERT-plan §1 link 9, §2 C4): the extractor specification split at the contract's `Computes` domain,
-- as season 1 (`LvmXTop.EX`: `EdX` on `InDomE`, `EoutX` outside) and A0 (`Lvm6WOnly.EW`) do. On the domain an `S`
-- proof gets the program's denotation (`EX6`'s branch); outside it, the search of `LvmXSearch` under the key in
-- the proof's header. `open6X18D`: `open6X18C`'s conclusions in `Open6D`'s form, without `hlog`.
import Lvm6CertOpen
import Lvm6XIndOk18
import Lvm6VHdr
import LvmXSearch

/-!
# The extractor's domain split: `EX6D`, `open6X18D`

**Why.** `open6X18C` needs `hlog`: every available log has entries below `2^64` bytes and a tape of at most `2^64`
words. `Avail` bounds the log only by `logCap = 2^96` entries, so `hlog` is false. The contract's `Computes` asks
for the program's output only on its domain (`W.InDomW`: `|π| ≤ 8·outCap`, entries below `2^64` bytes, tape at most
`2^64` words), so the specification may differ from the denotation outside it.

* **`EX6D A descX`**: a `W` proof decoded; an `S` proof on the domain: `Eden mem6 mpwX (extIR6 descX)` (`EX6`'s
  branch); an `S` proof outside it: `search A (hdrKey6 π) c`, the first witness of `Rel (A vk) c` under the key
  `vk` in π's header. `EX6D_dom`: on the domain `EX6D A descX = EX6 descX`.
* **Fuel and `progCap`**: the program is still `extX6 descX`. `computes6D` is `computes6` through `EX6D_dom`, since
  `Computes` only reads the domain; the search is a specification term, not part of the program.
* **`extEq6_at`**: `ext_eq6A` for one available log (its `descends` for that log only).
* **`hdrKey6_of_Ex`**: on a replayed log the header key is the scheme's `vk` (`Ex_ok`, `Ex_hdr`, `hdrView_okV`).
* **`open6X18D`**: `XOpen6D` at `prog6 Φ` for `EX6D (accV (VS P18)) D18` and `extX6 D18`. On the domain the right
  disjunct (`extEq6_at` with `descends18`, whose tape facts are now `InDomW`'s); outside it the left one
  (`final_law` gives a witness, `search_spec_acc` finds one).
-/

set_option autoImplicit false

namespace Lvm6.X

open RecursionFast Lvm.X Lvm.Nb Lvm6.FD Finset Lvm6.Whir LeanVM.Parameters LeanVM.Protocol.Whir
  LeanVM.Protocol.Whir.AffineCombiner
open LeanVM.Protocol.Compile (Ev)
open Lvm Lvm.T Lvm.FS
open RecursionFast.WitnessSending (decode)
open scoped NNReal ENNReal

/-! ## The specification -/

/-- **The key in π's header**: `hdrView`'s `vk` of the first `hdrLen P18` bytes. -/
def hdrKey6 (π : Proof) : Digest := (hdrView P18 (π.data.toList.take (hdrLen P18))).vk

/-- **The extractor specification, split at the contract's domain**: a `W` proof decoded; an `S` proof on the
domain: the program's denotation; outside it: the search of `Rel (A vk) c` under the header's key `vk`. -/
def EX6D (A : Digest → Digest → Signed → Bool) (descX : XIR) (c : Digest) (π : Proof) (L : Log) :
    Option Wit :=
  if isS π = true then
    (if W.InDomW c π L then Eden mem6 mpwX (extIR6 descX) c π L else search A (hdrKey6 π) c)
  else decode π

section Spec

variable (A : Digest → Digest → Signed → Bool) (descX : XIR)

/-- On the domain, `EX6D` is `EX6`. -/
theorem EX6D_dom {c : Digest} {π : Proof} {L : Log} (hD : W.InDomW c π L) :
    EX6D A descX c π L = EX6 descX c π L := by
  by_cases hS : isS π = true
  · rw [EX6D, if_pos hS, if_pos hD, EX6, if_pos hS]
  · rw [EX6D, if_neg hS, EX6, if_neg hS]

/-- Outside the domain, an `S` proof is searched. -/
theorem EX6D_out {c : Digest} {π : Proof} {L : Log} (hS : isS π = true) (hD : ¬ W.InDomW c π L) :
    EX6D A descX c π L = search A (hdrKey6 π) c := by
  rw [EX6D, if_pos hS, if_neg hD]

/-- **The `W` branch** (`XOpen6D.wBranch`). -/
theorem wBranch6D (c : Digest) (π : Proof) (L : Log) (hW : isS π = false) : EX6D A descX c π L = decode π := by
  rw [EX6D, if_neg (by simp [hW])]

/-- **`computes6` for `EX6D`**: the same program, the same fuel; `Computes` reads only the domain. -/
theorem computes6D (hD : DescOk6 descX) : Computes (extX6 descX) (EX6D A descX) fuel6 :=
  fun c π L h1 h2 h3 => by
    obtain ⟨o, ho, hl, hd⟩ := computes6 hD c π L h1 h2 h3
    exact ⟨o, ho, hl, hd.trans (EX6D_dom A descX ⟨h1, h2, h3⟩).symm⟩

end Spec

/-! ## The header key of an accepted proof -/

/-- The replayed header passes the scheme's check. -/
theorem Ex_ok {S : Scheme} {c : Digest} {π : Proof} {L : Log} {x : S.Stmt} {h : List Ev}
    (hE : S.Ex (fun _ x h => (x, h)) c π L = some (x, h)) : S.ok c x = true := by
  unfold Scheme.Ex at hE
  rcases hh : S.hdr π with _ | ⟨x', body⟩
  · rw [hh] at hE
    cases hE
  · rw [hh] at hE
    dsimp only at hE
    by_cases hp : S.preOk c x' = true
    · rw [if_pos hp] at hE
      obtain ⟨e₀, -, hE⟩ := Option.bind_eq_some_iff.mp hE
      obtain ⟨e₁, -, hE⟩ := Option.bind_eq_some_iff.mp hE
      obtain ⟨r, -, hr⟩ := Option.bind_eq_some_iff.mp hE
      split_ifs at hr
      simp only [Option.some.injEq, Prod.mk.injEq] at hr
      obtain ⟨rfl, -⟩ := hr
      simp only [Scheme.preOk, Bool.and_eq_true] at hp
      exact hp.1
    · rw [if_neg hp] at hE
      cases hE

/-- **The header key is the scheme's key** on every replayed log. -/
theorem hdrKey6_of_Ex {prog : Shape → Digest → List UInt8 → LeanVM.Protocol.Compile.VerifierProgram Bool}
    {vk c : Digest} {π : Proof} {L : Log} {x : List UInt8} {h : List Ev}
    (hE : (schemeOf prog P18 vk).Ex (fun _ x h => (x, h)) c π L = some (x, h)) : hdrKey6 π = vk := by
  have hok := Ex_ok hE
  obtain ⟨rfl, hH⟩ := Ex_hdr hE
  have hH' : V.hdrLen (toV P18) ≤ π.data.size := hH
  have hlen : (π.data.toList.take (hdrLen P18)).length = hdrLen P18 := by
    rw [List.length_take, Array.length_toList]
    exact Nat.min_eq_left hH'
  exact (hdrView_okV vk c _ hlen hok).2.2

/-- A signed proof `accV VS` accepts is within the search's bounds. -/
theorem sFits_accV {VS : SProg} {vk c : Digest} {p : Signed} (h : accV VS vk c p = true) : SFits p :=
  sFits_of_acc (S := submissionOf VS (fun _ _ _ => none) (extX6 (.blk []))) (show qVlvm ≤ qMax by decide)
    (by rw [submissionOf_acc]; exact h)

/-! ## `ext_eq6` on one log -/

/-- **`ext_eq6A` for one available log**: the descent's fact for this log gives `EX6 = Eideal` on it. -/
theorem extEq6_at {prog : Shape → Digest → List UInt8 → LeanVM.Protocol.Compile.VerifierProgram Bool}
    {vk : Digest} {R : Digest → Wit → Prop} (K : KCert (schemeOf prog P18 vk) R) (I : OpeningIface)
    {descX : XIR} (hK : K.ext = ExtSpec6 I) {c : Digest} {π : Proof} {L : Log} (hA : Avail K c π L)
    (hlen : π.size = pz6)
    (descends : ∀ x h, (schemeOf prog P18 vk).Ex (fun _ x h => (x, h)) c π L = some (x, h) →
      Inv (preOut6 descX (extractorInput c π L)).M ∧ (preOut6 descX (extractorInput c π L)).o = #[] ∧
        HeapHolds (preOut6 descX (extractorInput c π L)).M (pick6 I h)) :
    EX6 descX c π L = Eideal K c π L := by
  obtain ⟨hS, -, hμ, hacc⟩ := hA
  obtain ⟨w, hw, -⟩ := Scheme.final_law K L c π hμ hacc
  rw [Eideal, hw]
  rw [Ex_map] at hw
  obtain ⟨⟨x, h⟩, hp, rfl⟩ := Option.map_eq_some_iff.mp hw
  obtain ⟨hI, hO, hH⟩ := descends x h hp
  obtain ⟨t6, t7, t8, t12⟩ := hdrTape6 c π L x h hp
  rw [EX6, if_pos hS, Eden, den, extIR6, hK]
  set inp := extractorInput c π L
  -- the parse takes the `S` branch at `|π| = pz6`
  have hreg : regs ≤ mem6 := by simp only [regs, mem6]; norm_num
  have h0 : Inv (initSt (mem6 + mpwX * inp.length)).M := inv_initSt (Nat.le_add_right_of_le hreg)
  have hk5 := Lvm6.W.parse_isK pz6 inp.toArray _ h0
  have hz5 := parse_regs pz6 inp.toArray _ h0
  have hb0 : π.data[0]? = some sByte := by
    have hpos : 0 < π.data.size := by
      have : π.size = π.data.size := rfl
      rw [← this, hlen]; simp only [pz6]; norm_num
    have hg : π.data.getD 0 0 = sByte := by simpa [isS] using hS
    rw [Array.getElem?_eq_getElem hpos]
    rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hpos] at hg
    simpa using hg
  have hK5 : inp.toArray.getD 5 0 &&& 0xFF = kindS := by
    apply BitVec.eq_of_toNat_eq
    rw [Lvm6.W.lowByte, getD_toArray, Lvm6.W.tape_byte0 c π L hb0]
    rfl
  have hZ : inp.toArray.getD 4 0 = BitVec.ofNat 64 pz6 := by
    rw [getD_toArray, tape_getD4, hlen]; rfl
  rw [if_pos hK5] at hk5
  rw [if_pos hZ] at hz5
  rw [extIRWith, semXIR_seq, semXIR_ite, if_neg (by rw [hk5]; decide), semXIR_ite,
    if_neg (by rw [hz5]; decide), dec6, semXIR_seq, semXIR_seq]
  rw [show semXIR inp.toArray descX (semXIR inp.toArray frontIR6 (semXIR inp.toArray (parseIR pz6)
    (initSt (mem6 + mpwX * inp.length)))) = preOut6 descX inp from rfl]
  rw [outIR6_sem inp.toArray _ hI t6 (UInt64.toNat_lt _) (hdrView P18 x).c' (hdrView P18 x).h
    (hdrView P18 x).n.toNat t12 t8 t7 (UInt64.toNat_lt _), hO, Array.toList_empty, List.nil_append,
    out_witOf6 hH]
  exact decodeWit_witWords _ (fits_witOf6 childFits6 _ _)

/-! ## The extractor's obligations at `P18` -/

section Assembly

variable {Φ : Phases} {SGood TGood : Hdr → Stack → Prop} (H : PhaseSpecs Φ Whir.I6 SGood TGood)
  (HG : Stmt.openGoodC Whir.GW18c Φ.whir) (hPF : PhasesFollow Φ P18) {VS : Shape → SProg}
  (Xe : ∀ vk, Ext6 (schemeOf (prog6 Φ) P18 vk) (Rel (accV (VS P18) vk)) (G6 SGood TGood))

include H HG hPF in
/-- **The extractor's obligations at `P18`** for `front6 ; fillIR18 ; descX6 (Lv18 F18) finX18` with the
specification `EX6D (accV (VS P18))`: `open6X18C`'s conclusions without `hlog` (only the deployed opening `hw` and
the extraction map `hX`, beside the certificate inputs `H HG hPF Xe`). -/
theorem open6X18D (hw : Φ.whir = whirAt Whir.whirP18) (hX : ∀ vk, (Xe vk).ext = ExtSpec6 (Whir.I6 P18)) :
    XOpen6D (VS P18) (prog6 Φ) (EX6D (accV (VS P18)) (.seq fillIR18 (descX6 (Lv18 F18) finX18)))
      (extX6 (.seq fillIR18 (descX6 (Lv18 F18) finX18))) where
  sound vk := by
    refine ⟨kcertAsmG H HG hPF vk (Xe vk), εFS_kcert6, fun c π L hA => ?_⟩
    have hlen : π.size = pz6 := len6_whirAt hPF hw vk c π L hA.1 hA.2.2.2
    by_cases hD : W.InDomW c π L
    · right
      rw [EX6D_dom _ _ hD]
      exact extEq6_at _ (Whir.I6 P18) (hX vk) hA hlen fun x h hE =>
        descends18 hPF hw hE hlen hD.2.1 hD.2.2 (Scheme.mu_lt_one hA.2.2.1).1
          (goodL6 H HG hPF vk (Xe vk) c π L hA x h hE)
    · left
      rw [EX6D_out _ _ hA.1 hD]
      obtain ⟨w, hw', hR⟩ := Scheme.final_law (kcertAsmG H HG hPF vk (Xe vk)) L c π hA.2.2.1 hA.2.2.2
      rw [Ex_map] at hw'
      obtain ⟨⟨x, h⟩, hp, -⟩ := Option.map_eq_some_iff.mp hw'
      rw [hdrKey6_of_Ex hp]
      exact search_spec_acc (fun _ _ hp' => sFits_accV hp') ⟨w, hR⟩
  wBranch := wBranch6D _ _
  computes := computes6D _ _ descOk6_F18
  size := size_extX6 (sizeIR_F18 F18)

include H HG hPF in
/-- **`Open6D` at `P18`**: `open6X18D` with the verifier's two obligations (`queries`, `refines`). -/
theorem open6D18 (hw : Φ.whir = whirAt Whir.whirP18) (hX : ∀ vk, (Xe vk).ext = ExtSpec6 (Whir.I6 P18))
    (hq : ∀ vk c π (H' : ByteArray → Digest), ((VS P18 vk c π).queries H').length ≤ P18.qS)
    (hr : Refines (VS P18) (schemeV (schemeOf (prog6 Φ) P18))) :
    Open6D VS (prog6 Φ) (EX6D (accV (VS P18)) (.seq fillIR18 (descX6 (Lv18 F18) finX18)))
      (extX6 (.seq fillIR18 (descX6 (Lv18 F18) finX18))) :=
  { open6X18D H HG hPF Xe hw hX with queries := hq, refines := hr }

end Assembly

end Lvm6.X
