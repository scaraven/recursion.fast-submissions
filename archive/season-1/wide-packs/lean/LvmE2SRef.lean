-- New for lvm2 σ_LEAF (SLF-V, SLF-STMT 6): V_S's S2GS decision (`decideProgSG P20S P20 aSP`) refines the pinned S2GS
-- middle phases (`midMk 4 relocU20 (midGS _)`) on the stream with S2GS's read widths, at S2GU's occupied words `occOfU`
-- (`LvmE2LRef`'s chain with the native check `parseOkS`, the public values `pubOfWS` and the tape over a list of
-- `cont` intervals).
import LvmE2LRef
import LvmE2VTopF
import LvmS2GSPlan

/-!
# V_S's S2GS decision refines the pinned middle phases

* **`refines_seqOfGP`**: `refines_seqOfGO` generic in the native check `parse` V_S runs before driving (its size and
  header facts as hypotheses) and in the scheme's statement check `okF` (`schemeSW … with ok := okF vk`).
* `parseOkS`'s facts: `parseOkS_parts`, `hdrSW_of_parseOkS`, `okSL_of_parseOkS` (the header's fields below
  `hdrFixS`), **`pubGS_eq`** (V_S's public values `pubOfWS` are the statement's `pubXTS`).
* The tape over a list of `cont` intervals (`wireUDL`, `tapeUDL`, `refW_tapeUDL`; `LvmE2LRef`'s `b`-twins over `iv`).
* The decision (`ref_decideGS`), S2GS's schedule facts at `P20S` and **`refinesS20_of`**.
-/

set_option autoImplicit false

/-! ## V_S's decision at S2GS (moved verbatim from `LvmS2GSStmtV` for the proof) -/

namespace Lvm.E2S

open RecursionFast Lvm DM Lvm.T Lvm.ASM Lvm.FS Lvm.CT Lvm.E2F Lvm.E2V Lvm.E2T Lvm.E2U Lvm.E2L

/-- **The decision program at S2GS** (`decideProgLG` with `pubOfWS` and the intervals `contIvS a`). -/
def decideProgSG (p pT : Params) (a : Nat) (N : TNatT) (vk c : Vector UInt8 32) : DM Acc := do
  let sig ← read
  let pub := pubOfWS vk c sig
  let m := m3G N p
  skip (nodeBytes * 2 ^ (p.level ⟨.main, 0⟩).cap)
  let pin ← pinD p.nuMain
  let (acc, ti, ζ, bus) ← dTypedLG pT N m pub (typedItemsND N p)
  let tabs := M3.sumcheckTabs N.mbT
  let tp ← tapeUDGc (contIvS a) rowSwitchDR p pub.s pub.n
  dOpenFFL p (TypedV.smallT p pub) pin ti ζ ((List.range 3).map (M3.mbColsN tabs bus))
    (M3.mbValsF tabs bus ζ) (frontItemsU rowAccR p pub tp)
  pure acc

/-- **V_S's decision at S2GS** at `p` (`decideFLG`'s form). -/
def decideFSG (p pT : Params) (a : Nat) (N : TNatT) (vk c : Vector UInt8 32) (sig : ByteArray) : Bool :=
  let (r, s) := DM.runOnH (headerBytesP p) (decideProgSG p pT a N vk c) sig
  (s.ok && s.ent == sig.size && s.msg == 0) && N.phiT (r.pt.map Lvm.e2OfFE) == Lvm.e2OfFE r.y

end Lvm.E2S

/-! ## V ⇒ S.V on a trace for any native check and statement check -/

namespace Lvm.VEq

open RecursionFast Lvm Lvm.FS LeanVM.Parameters LeanVM.Protocol.Compile

/-- **V_S ⇒ S.V on a trace** (`refines_seqOfGO`'s proof, generic in the native check `parse` V_S runs before
driving — through its size fact `hsz` and its header fact `hhdr` — and in the scheme's statement check `okF`). -/
theorem refines_seqOfGP (PS : List UInt8 → VerifierProgram Bool) (nR : ℕ) (p : Params) (fmt : Lvm.ASM.SFmt)
    {occ : ℕ → ℕ → ℕ} (VS : Lvm.T.SProg)
    (parse : RecursionFast.Digest → RecursionFast.Digest → ByteArray → Bool)
    (okF : RecursionFast.Digest → RecursionFast.Digest → List UInt8 → Bool)
    (D : RecursionFast.Digest → RecursionFast.Digest → ByteArray → Bool)
    (prog : RecursionFast.Digest → RecursionFast.Digest → DM Acc) (φ : Acc → Prop)
    (Pre : ByteArray → RecursionFast.Digest → RecursionFast.Digest → List UInt8 → Prop)
    (hVS : ∀ vk c π, VS vk c π = if parse vk c π then drive p π (D vk c) else .ret false)
    (hsz : ∀ vk c π, parse vk c π = true → π.size = piSize p)
    (hhdr : ∀ vk c π, parse vk c π = true → Lvm.ASM.hdrSW (piSize p) (headerBytesP p) π =
      some (xOfH (headerBytesP p) π, (π.data.toList).drop (headerBytesP p)))
    (hD : ∀ vk c sig, D vk c sig = true →
      (runD (prog vk c) sig (RS.startH (headerBytesP p))).2.ok = true ∧
        φ (runD (prog vk c) sig (RS.startH (headerBytesP p))).1)
    (hPre : ∀ vk c π sig, parse vk c π = true →
      (∀ t < headerBytesP p - 8, sig.get! (headerAt 8 + t) = π.get! (8 + t)) →
      Pre sig vk c (xOfH (headerBytesP p) π))
    (href : ∀ (sig : ByteArray) (vk c : RecursionFast.Digest) (x : List UInt8), Pre sig vk c x →
      RefAtPW capS occ shpS fmt.rw sig 0 (prog vk c) (PS x) (fun _ b ↦ b = true) φ nR)
    (hpz : fmt.pz = piSize p) (hhb : fmt.hb = headerBytesP p) (hocc : fmt.occ = occ)
    (hqc : 32 + (headerBytesP p - 8) ≤ queryCap)
    (hokS : ∀ vk c π, parse vk c π = true → okF vk c (xOfH (headerBytesP p) π) = true)
    (hfol : ∀ x, Fol capS shpS idxS (PS x) (atomsOf p (schedule p)) [] fun _ _ ↦ True)
    (hst : stA p (atomsOf p (schedule p)) 0 [] [] occ = true)
    (hw : WAt fmt.rw 0 (widthsA (atomsOf p (schedule p))))
    (vk c : RecursionFast.Digest) (π : ByteArray) (tr : Trace)
    (h : (VS vk c π).runSeq tr = some true) :
    (({ Lvm.ASM.schemeSW fmt vk PS with ok := okF vk } : Scheme).V c π).runSeq tr = some true := by
  -- the header check
  rw [hVS] at h
  by_cases hp : parse vk c π = true
  swap
  · simp only [hp, Bool.false_eq_true, ↓reduceIte] at h; exact absurd (runSeq_ret_true h).2 (by simp)
  simp only [hp, ↓reduceIte] at h
  have hsize : π.size = piSize p := hsz vk c π hp
  have h8 := eight_le_P p
  have hHle : headerBytesP p ≤ π.size := hsize ▸ headerBytesP_le_piSize _
  -- the driver: q₀, the seed, the schedule
  unfold drive at h
  obtain ⟨a₀, tr1, rfl, h1⟩ := runSeq_query_cons h
  obtain ⟨st₀, rest, rfl, h2⟩ := runSeq_query_cons h1
  rw [driveItems_eq] at h2
  obtain ⟨sf, n, hf1, hf2, -, -⟩ := drive_run _ π _ _ _ rest h2
  obtain ⟨hnil, hb⟩ := runSeq_ret_true hf1
  simp only [Bool.and_eq_true, beq_iff_eq] at hb
  obtain ⟨-, hF⟩ := hb
  have hn : rest.take n = rest := List.take_of_length_le (List.drop_eq_nil_iff.mp hnil)
  set hb := headerBytesP p with hbdef
  have hlog : streamOf sf.log = traceBytesB ((q0Query, a₀) :: (seedQuery π a₀ hb, st₀) :: rest) := by
    rw [streamOf, hf2, hn]; simp
  rw [hlog] at hF
  set tr := (q0Query, a₀) :: (seedQuery π a₀ hb, st₀) :: rest with htr
  set x := xOfH hb π with hx
  -- the value refinement: the program read off the stream returns `true`
  have hpre : Pre (traceBytesB tr) vk c x := hPre vk c π _ hp (seed_bytesH π a₀ st₀ rest hHle)
  obtain ⟨hok0, hacc⟩ := hD vk c _ hF
  obtain ⟨b, hb1, -, -, -, rfl⟩ := href (traceBytesB tr) vk c x hpre (RS.startH hb) hok0 hacc
  obtain ⟨⟨o, rs', nW⟩, hW⟩ : ∃ r, ivpW capS occ shpS fmt.rw (PS x) (traceBytesB tr) (RS.startH hb) 0 = r :=
    ⟨_, rfl⟩
  rw [hW] at hb1
  simp only at hb1
  subst hb1
  -- the simulation
  set S : Scheme := { Lvm.ASM.schemeSW fmt vk PS with ok := okF vk } with hSdef
  have hJ0 : J S π tr ⟨hb, hb, st₀, [(seedQuery π a₀ hb, st₀), (q0Query, a₀)], [], []⟩ st₀ [] []
      ((π.data.toList).drop hb) (RS.startH hb) 2 [] :=
    ⟨rfl, le_rfl, hHle, by rw [Nat.sub_self, List.take_zero], rfl, (entOff_twoH π a₀ st₀ rest h8 hHle).symm,
      by show 0 = hb - hb; rw [Nat.sub_self],
      ⟨[], rfl, rfl, rfl, fun j hj ↦ absurd hj (by simp), List.nodup_nil⟩⟩
  obtain ⟨s', st', buf', caps', body', i', cr', hJ', hk', -, hrun⟩ :=
    simW (S := S) (π := π) (tr := tr) (p := p)
      rfl rfl rfl capOfS_eq hocc (atomsOf p (schedule p)) (PS x) [] _ _
      st₀ [] [] _ (RS.startH hb) 2 [] [] _ true rs' 0 nW (hfol x) (by rw [Nat.sub_self]; exact hst) hJ0 rfl
      (fun _ h ↦ by simp at h)
      (fun s'' m hm ↦ by
        obtain ⟨-, hbb⟩ := runSeq_ret_true hm
        simp only [Bool.and_eq_true, beq_iff_eq] at hbb
        rw [hbb.1])
      h2 hw hW
  obtain ⟨hnil', hb'⟩ := runSeq_ret_true hk'
  simp only [Bool.and_eq_true, beq_iff_eq] at hb'
  have hbody' : body' = [] := by
    rw [hJ'.body, hb'.1, List.drop_eq_nil_iff, length_blb]
  -- the compiled verifier
  have hqc' : 32 + x.length ≤ queryCap := by
    rw [hx, length_xOfH π hHle]; exact hqc
  have hS_hdr : S.hdr π = some (x, (π.data.toList).drop hb) := by
    show Lvm.ASM.hdrSW fmt.pz fmt.hb π = _
    rw [hpz, hhb]
    exact hhdr vk c π hp
  have hS_pre : S.preOk c x = true := by
    show (okF vk c x && decide (32 + x.length ≤ queryCap)) = true
    rw [show okF vk c x = true from hokS vk c π hp]
    simp [hqc']
  unfold Scheme.V
  rw [hS_hdr]
  simp only [hS_pre, ↓reduceIte]
  rw [show toQ S.q0 = q0Query from rfl, htr, runSeq_query_eq,
    show S.seedQ a₀ x = seedQuery π a₀ hb from toQ_seedH π a₀ hb, runSeq_query_eq,
    show S.P x = PS x from rfl, runW_eq_runKW,
    show rest = tr.drop 2 from rfl, hrun, hnil', hbody']
  rfl

end Lvm.VEq

/-! ## `parseOkS`: the header, the statement check, the public values -/

namespace Lvm.VEq

open RecursionFast Lvm

theorem parseOkS_parts {p : Params} {vk c : Digest} {π : ByteArray} (h : parseOkS p vk c π = true) :
    π.size = piSize p ∧ π.get! 0 = 0x53 ∧ zeroBytes π 1 7 = true ∧
      ((Header.ofProof π).b = 0 ∨ (Header.ofProof π).b = 1) ∧ (Header.ofProof π).vk = vk ∧
      1 ≤ (Header.ofProof π).n ∧ (Header.ofProof π).n ≤ chainCap ∧ c = (Header.ofProof π).stmt := by
  simp only [parseOkS, Bool.and_eq_true, beq_iff_eq, Bool.or_eq_true, decide_eq_true_eq, and_assoc] at h
  obtain ⟨hs, h0, hz, hb, hvk, hn1, hn2, -, hif⟩ := h
  refine ⟨hs, h0, hz, hb, hvk, hn1, hn2, ?_⟩
  by_cases hb0 : (Header.ofProof π).b = 0
  · simp only [hb0, ↓reduceIte, Bool.and_eq_true, beq_iff_eq] at hif
    exact hif.2
  · simp only [hb0, ↓reduceIte, beq_iff_eq] at hif
    exact hif

theorem hdrSW_of_parseOkS {p : Params} {vk c : Digest} {π : ByteArray} (h : parseOkS p vk c π = true) :
    Lvm.ASM.hdrSW (piSize p) (headerBytesP p) π =
      some (xOfH (headerBytesP p) π, (π.data.toList).drop (headerBytesP p)) := by
  obtain ⟨hs, h0, hz, -⟩ := parseOkS_parts h
  have h8 : 8 ≤ π.size := by rw [hs]; exact le_trans (eight_le_P p) (headerBytesP_le_piSize p)
  simp only [Lvm.ASM.hdrSW, hs, take8_of_parse' h8 h0 hz, and_self, ↓reduceIte]
  rfl

/-- **The statement's header fields below `hdrFixS` are the proof's** (every field but `σ_leaf`). -/
theorem hdrOf_xOfH_fix (π : ByteArray) {hb : ℕ} (hH : hdrFixS ≤ hb) :
    (Lvm.ASM.hdrOf (xOfH hb π)).b = (Header.ofProof π).b ∧ (Lvm.ASM.hdrOf (xOfH hb π)).vk = (Header.ofProof π).vk ∧
      (Lvm.ASM.hdrOf (xOfH hb π)).cL = (Header.ofProof π).cL ∧ (Lvm.ASM.hdrOf (xOfH hb π)).s = (Header.ofProof π).s ∧
      (Lvm.ASM.hdrOf (xOfH hb π)).n = (Header.ofProof π).n ∧ (Lvm.ASM.hdrOf (xOfH hb π)).h = (Header.ofProof π).h := by
  have hF : hdrFixS = 152 := rfl
  have hR : ∀ a n, 8 ≤ a → a + n ≤ 152 → ∀ i, a ≤ i → i < a + n →
      (⟨(List.replicate 8 0 ++ xOfH hb π).toArray⟩ : ByteArray).get! i = π.get! i := by
    intro a n ha hn i h1 h2
    rw [get!_mk, List.getD_append_right _ _ _ _ (by simp only [List.length_replicate]; (clear * - ha h1; omega)),
      List.length_replicate, getD_xOfH π (by (clear * - hF hH ha hn h1 h2; omega)),
      Nat.add_sub_cancel' (by (clear * - ha h1; omega))]
  unfold Lvm.ASM.hdrOf Header.ofProof
  exact ⟨u64At_congr (hR offB 8 (by decide) (by decide)), digestAt_congr (hR offVk 32 (by decide) (by decide)),
    digestAt_congr (hR offCL 32 (by decide) (by decide)), digestAt_congr (hR offS 32 (by decide) (by decide)),
    u64At_congr (hR offN 8 (by decide) (by decide)), digestAt_congr (hR offH 32 (by decide) (by decide))⟩

/-- **`parseOkS p` ⇒ the scheme's statement check at S2GS** (`okSL`: no leaf signature). -/
theorem okSL_of_parseOkS {p : Params} {vk c : Digest} {π : ByteArray} (h : parseOkS p vk c π = true) {hb : ℕ}
    (hH : hdrFixS ≤ hb) : Lvm.ASM.okSL vk c (xOfH hb π) = true := by
  obtain ⟨-, -, -, hb, hvk, hn1, hn2, hc⟩ := parseOkS_parts h
  obtain ⟨eb, evk, ecL, -, en, eh⟩ := hdrOf_xOfH_fix π hH
  unfold Lvm.ASM.okSL
  dsimp only
  rw [eb, evk, ecL, en, eh]
  unfold Header.stmt Header.leaf at hc
  rw [leafStmtF_eq, nodeStmtF_eq] at hc
  generalize Header.ofProof π = hd at *
  rcases hb with hb | hb
  · simp only [hb, ↓reduceIte] at hc
    simp [hb, hvk, hn1, hn2, hc]
  · simp only [hb, one_ne_zero, ↓reduceIte] at hc
    simp [hb, hvk, hn1, hn2, hc]


/-- **`pubOfWS` reads only the stream's header bytes** (to `headerAt 888`: the fixed fields below `hdrFixS`, then
`acc_in`'s 46 entries of 16 B). -/
theorem pubOfWS_congr {vk c : Digest} {sig sig' : ByteArray}
    (h : ∀ o, headerAt 8 ≤ o → o < headerAt 888 → sig.get! o = sig'.get! o) :
    pubOfWS vk c sig = pubOfWS vk c sig' := by
  have hR : ∀ a n, 8 ≤ a → a + n ≤ 888 → ∀ i, headerAt a ≤ i → i < headerAt a + n → sig.get! i = sig'.get! i :=
    fun a n ha hn i h1 h2 ↦ h i (by simp only [headerAt] at h1 ⊢; (clear * - ha h1; omega))
      (by simp only [headerAt] at h2 ⊢; (clear * - ha hn h2; omega))
  have hL : ∀ a m, 8 ≤ a → a + 8 * m ≤ 888 → ∀ k ∈ List.range m, ∀ i, headerAt a + 8 * k ≤ i →
      i < headerAt a + 8 * k + 8 → sig.get! i = sig'.get! i := by
    intro a m ha hm k hk i h1 h2
    have := List.mem_range.mp hk
    exact h i (by simp only [headerAt] at h1 ⊢; (clear * - ha hm h1 this; omega))
      (by simp only [headerAt] at h2 ⊢; (clear * - ha hm h2 this; omega))
  have hE : ∀ i, i ≤ accVT → fe16At sig (headerAt (hdrFixS + 16 * i)) = fe16At sig' (headerAt (hdrFixS + 16 * i)) :=
    fun i hi ↦ fe16At_congr fun j h1 h2 ↦ h j (by simp only [headerAt, hdrFixS] at h1 ⊢; (clear * - h1; omega))
      (by simp only [headerAt, hdrFixS, accVT] at h2 hi ⊢; (clear * - h2 hi; omega))
  simp only [pubOfWS, pubOfW, pubOf]
  rw [laneAt_congr (hR 8 8 (by decide) (by decide)), laneAt_congr (hR 112 8 (by decide) (by decide)),
    List.map_congr_left fun k hk ↦ kAt_congr (hL 48 4 (by decide) (by decide) k hk),
    List.map_congr_left fun k hk ↦ kAt_congr (hL 80 4 (by decide) (by decide) k hk),
    List.map_congr_left fun k hk ↦ kAt_congr (hL 120 4 (by decide) (by decide) k hk),
    List.map_congr_left fun k hk ↦ hE k (List.mem_range.mp hk).le, hE accVT le_rfl]

/-- **V_S's public values at S2GS are the statement's** (`pubOfWS` on the stream is `pubXTS` of the header bytes). -/
theorem pubGS_eq {vk c : Digest} {π : ByteArray} (h : parseOkS P20S vk c π = true) {sig : ByteArray}
    (hsig : ∀ t < headerBytesP P20S - 8, sig.get! (headerAt 8 + t) = π.get! (8 + t)) :
    pubOfWS vk c sig = pubXTS (xOfH (headerBytesP P20S) π) := by
  have h888 : headerBytesP P20S = 888 := headerBytesP_P20S.1
  obtain ⟨-, -, -, -, hvk, -, -, hc⟩ := parseOkS_parts h
  obtain ⟨eb, evk, ecL, -, en, eh⟩ := hdrOf_xOfH_fix π (hb := headerBytesP P20S) (by rw [h888]; decide)
  have hst : (hdX (xOfH (headerBytesP P20S) π)).stmt = c := by
    rw [hc]
    show (Lvm.ASM.hdrOf _).stmt = _
    unfold Header.stmt Header.leaf
    rw [eb, ecL, en, eh]
  unfold pubXTS
  rw [hst, show (hdX (xOfH (headerBytesP P20S) π)).vk = vk from evk.trans hvk]
  refine pubOfWS_congr fun o h1 h2 ↦ ?_
  obtain ⟨t, rfl⟩ : ∃ t, o = headerAt 8 + t := ⟨o - headerAt 8, by (clear * - h1; omega)⟩
  have ht : t < headerBytesP P20S - 8 := by rw [h888]; simp only [headerAt] at h2 ⊢; (clear * - h2; omega)
  rw [hsig t ht, get!_sigOfXH π ht]

end Lvm.VEq

/-! ## The tape over a list of `cont` intervals (`LvmE2LRef`'s `b`-twins over `iv`) -/

namespace Lvm

open DM Lvm.E2V Lvm.E2U

/-- **`wireProgL iv` on `DM` at `FE2`** (`wireUD` with the sponge intervals `iv`). -/
def wireUDL (iv : List (Nat × Nat)) (s : List FK) (n : Nat) (claim : E2V.KClaim FE2) :
    DM ((List FE2 × FE2) × List FE2 × SlotU ((FE × (List FE → FE)) × List FE) ×
      SlotU ((FE × (List FE → FE)) × List FE) × SlotU ((FE × (List FE → FE)) × List FE)) := do
  let sc ← sumcheckD gC2 (wireTargetD (sBitsD s) n claim) 3 (List.replicate 20 none)
  let g ← readE2s 3
  require (sc.2 == E2V.msEvalF claim.point claim.mu sc.1 0 (n - 1) * g.getD 0 0 +
    eTailF 13 20 sc.1 * (kksF (iv) claim.point claim.mu (sc.1.take 13) (2 ^ 20) * g.getD 1 0 +
      E2V.ikEvalP claim.point claim.mu (sc.1.take 13) (2 ^ 20) * g.getD 2 0))
  let d ← slotD 2 1 0 (E2V.dWF claim.weights) sc.1 (g.getD 0 0)
  let y ← slotD 5 5 22 (E2V.yWG claim.weights) (sc.1.take 13) (g.getD 1 0)
  let m ← slotD 5 4 10 (E2V.mWG claim.weights) (sc.1.take 13 ++ [0]) (g.getD 2 0)
  pure (sc, g, d, y, m)

/-- **`tapeProgL iv` on `DM` at `FE2`** (`tapeUD` with the wire `wireUDL iv`). -/
def tapeUDL (iv : List (Nat × Nat)) (s : List FK) (n : Nat) :
    DM (List FE2 × List FE2 × List FE2 × E2V.KClaim FE2 × ((List FE2 × FE2) × List FE2 ×
      SlotU ((FE × (List FE → FE)) × List FE) × SlotU ((FE × (List FE → FE)) × List FE) ×
      SlotU ((FE × (List FE → FE)) × List FE))) := do
  sepE2
  let r ← samplesG gC1 20
  let ab ← readE2s 50
  let r20 ← samplesG gC1 1
  let claim ← tapeGkrD 21 (r ++ r20) (t1ValsF 20 13 (r ++ r20) ab)
  require (decide (1 ≤ n ∧ n ≤ 2 ^ 20))
  let wo ← wireUDL iv s n claim
  pure (r, r20, ab, claim, wo)

end Lvm

namespace Lvm.VEq

open Lvm DM LeanVM.Parameters LeanVM.Protocol.Compile Finset
open Lvm.FE2 (toE2)
open Lvm.E2U

theorem monoD_wireUDL (iv : List (ℕ × ℕ)) (s : List FK) (n : ℕ) (claim : E2V.KClaim FE2) : MonoD (wireUDL iv s n claim) :=
  (monoD_sumcheckD _ _ _ _).bind fun _ ↦ (monoD_readE2s _).bind fun _ ↦ (MonoD.require _).bind fun _ ↦
    (monoD_slotD _ _ _ _ _ _).bind fun _ ↦ (monoD_slotD _ _ _ _ _ _).bind fun _ ↦
      (monoD_slotD _ _ _ _ _ _).bind fun _ ↦ MonoD.pure _

theorem monoD_tapeUDL (iv : List (ℕ × ℕ)) (s : List FK) (n : ℕ) : MonoD (tapeUDL iv s n) :=
  monoD_sepE2.bind fun _ ↦ (monoD_samplesG _ _).bind fun _ ↦ (monoD_readE2s _).bind fun _ ↦
    (monoD_samplesG _ _).bind fun _ ↦ (monoD_tapeGkrD _ _ _).bind fun _ ↦ (MonoD.require _).bind fun _ ↦
      (monoD_wireUDL _ _ _ _).bind fun _ ↦ MonoD.pure _

section Ref

variable {cap : ℕ → ℕ → ℕ} {occ : ℕ → ℕ → ℕ} {shp : ℕ → ℕ × ℕ} {rw : ℕ → ℕ} {sig : ByteArray}

/-- **The wire over `iv`** (`refW_wireUD`'s proof with `iv`). -/
theorem refW_wireUDL (iv : List (ℕ × ℕ)) (s : List FK) (d : RecursionFast.Digest) (hs : sBitsD s = Lvm.KG.digestBits d) (n : ℕ)
    (claim : E2V.KClaim FE2) (hρ : 9 ≤ claim.point.length) {i : ℕ} (hw : WAt rw i wWireU) :
    RefAtW cap occ shp rw sig i (wireUDL iv s n claim) (wireProgL iv d n (cE2 claim)) WireURelW
      (i + wWireU.length) := by
  rw [wWireU, WAt.append, WAt.append, WAt.append, WAt.append] at hw
  obtain ⟨⟨⟨⟨hw1, hw2⟩, hw3⟩, hw4⟩, hw5⟩ := hw
  unfold wireUDL wireProgL
  rw [hs]
  refine RefAtW.bind (fun _ ↦ (monoD_readE2s _).bind fun _ ↦ (MonoD.require _).bind fun _ ↦
    (monoD_slotD _ _ _ _ _ _).bind fun _ ↦ (monoD_slotD _ _ _ _ _ _).bind fun _ ↦
      (monoD_slotD _ _ _ _ _ _).bind fun _ ↦ MonoD.pure _)
    ((refW_sumcheckD E2V.gC2 3 (by norm_num) (List.replicate 20 none)
      (wireTargetD (Lvm.KG.digestBits d) n claim) ?_).congr_prog ?_) ?_
  · simpa using hw1
  · rw [map_replicate_noneE2, E2V.toE2_wireTargetD]
  rintro sc sc' ⟨h1, h2, hl⟩
  have hl' : sc.1.length = 20 := by simpa using hl
  refine RefAtW.bind (fun _ ↦ (MonoD.require _).bind fun _ ↦ (monoD_slotD _ _ _ _ _ _).bind fun _ ↦
    (monoD_slotD _ _ _ _ _ _).bind fun _ ↦ (monoD_slotD _ _ _ _ _ _).bind fun _ ↦ MonoD.pure _)
    (refW_readE2s 3 (WAt.idx_eq hw2 (by simp))) ?_
  intro g g' hg
  subst hg
  refine RefAtW.bind (fun _ ↦ (monoD_slotD _ _ _ _ _ _).bind fun _ ↦ (monoD_slotD _ _ _ _ _ _).bind fun _ ↦
    (monoD_slotD _ _ _ _ _ _).bind fun _ ↦ MonoD.pure _) (RefAtW.require fun h ↦ ?_) fun _ _ _ ↦ ?_
  · have h' := congrArg toE2 (beq_iff_eq.1 h)
    have h13 : 5 ≤ (sc.1.take 13).length := by simp [hl']
    rw [h2, h', Lvm.FE2.toE2_add, Lvm.FE2.fe2_mul_eq, Lvm.FE2.fe2_mul_eq, Lvm.FE2.toE2_add, Lvm.FE2.fe2_mul_eq,
      Lvm.FE2.fe2_mul_eq, E2V.toE2_msEvalF, toE2_getD, toE2_getD, toE2_getD, toE2_eTailF, toE2_kksF, toE2_ikEvalP,
      ikEvalP_eq _ _ _ _ (by simpa using h13) (by simp [hl']; omega), List.map_take, ← h1]
    rfl
  · have hD : (fun o z ↦ toE2 (E2V.dWF claim.weights o z)) = E2V.dWF (claim.weights.map toE2) :=
      funext fun o ↦ funext fun z ↦ E2V.toE2_dWF _ _ _
    have hY : (fun o z ↦ toE2 (E2V.yWG claim.weights o z)) = yWF (claim.weights.map toE2) :=
      funext fun o ↦ funext fun z ↦ (map_yWG E2V.toE2Hom _ _ _).trans rfl
    have hM : (fun o z ↦ toE2 (E2V.mWG claim.weights o z)) = mWF (claim.weights.map toE2) :=
      funext fun o ↦ funext fun z ↦ (map_mWG E2V.toE2Hom _ _ _).trans rfl
    refine RefAtW.bind (fun _ ↦ (monoD_slotD _ _ _ _ _ _).bind fun _ ↦ (monoD_slotD _ _ _ _ _ _).bind fun _ ↦
      MonoD.pure _)
      ((refW_slotD 2 1 0 (E2V.dWF claim.weights) sc.1 (g.getD 0 0)
        (WAt.idx_eq hw3 (by simp [length_wReads]; omega))).congr_prog ?_) fun dd dd' hd ↦ ?_
    · rw [hD, toE2_getD, ← h1]
      rfl
    refine RefAtW.bind (fun _ ↦ (monoD_slotD _ _ _ _ _ _).bind fun _ ↦ MonoD.pure _)
      ((refW_slotD 5 5 22 (E2V.yWG claim.weights) (sc.1.take 13) (g.getD 1 0)
        (WAt.idx_eq hw4 (by simp [wSlot, length_wReads]; omega))).congr_prog ?_) fun yy yy' hy ↦ ?_
    · rw [hY, toE2_getD, List.map_take, ← h1]
      rfl
    refine RefAtW.bind (fun _ ↦ MonoD.pure _)
      ((refW_slotD 5 4 10 (E2V.mWG claim.weights) (sc.1.take 13 ++ [0]) (g.getD 2 0)
        (WAt.idx_eq hw5 (by simp [wSlot, length_wReads]; omega))).congr_prog ?_) fun mm mm' hm ↦ ?_
    · rw [hM, toE2_getD, List.map_append, List.map_take, ← h1, List.map_singleton, Lvm.FE2.toE2_zero]
      rfl
    exact (RefAtW.pure ⟨h1, h2, rfl, hd, hy, hm⟩).idx (by simp [wSlot, wWireU, length_wReads]; omega)

/-- **The tape over `iv`** (`refW_tapeUD`'s proof with `wireUDL iv`). -/
theorem refW_tapeUDL (iv : List (ℕ × ℕ)) (s : List FK) (d : RecursionFast.Digest) (hs : sBitsD s = Lvm.KG.digestBits d)
    (n : ℕ) {i : ℕ} (hw : WAt rw i wTapeU) :
    RefAtW cap occ shp rw sig i (tapeUDL iv s n) (tapeProgL iv d n) TapeURelW (i + wTapeU.length) := by
  rw [wTapeU, WAt.append, WAt.append, WAt.append, WAt.append] at hw
  obtain ⟨⟨⟨⟨hw1, hw2⟩, hw3⟩, hw4⟩, hw5⟩ := hw
  unfold tapeUDL tapeProgL
  refine RefAtW.bind (fun _ ↦ (monoD_samplesG _ _).bind fun _ ↦ (monoD_readE2s _).bind fun _ ↦
    (monoD_samplesG _ _).bind fun _ ↦ (monoD_tapeGkrD _ _ _).bind fun _ ↦ (MonoD.require _).bind fun _ ↦
      (monoD_wireUDL _ _ _ _).bind fun _ ↦ MonoD.pure _) refW_sepE2 fun _ _ _ ↦ ?_
  refine RefAtW.bind (fun _ ↦ (monoD_readE2s _).bind fun _ ↦ (monoD_samplesG _ _).bind fun _ ↦
    (monoD_tapeGkrD _ _ _).bind fun _ ↦ (MonoD.require _).bind fun _ ↦ (monoD_wireUDL _ _ _ _).bind
      fun _ ↦ MonoD.pure _) (refW_samplesGL E2V.gC1 20 hw1) ?_
  rintro r r' ⟨hr, hrl⟩
  subst hr
  refine RefAtW.bind (fun _ ↦ (monoD_samplesG _ _).bind fun _ ↦ (monoD_tapeGkrD _ _ _).bind fun _ ↦
    (MonoD.require _).bind fun _ ↦ (monoD_wireUDL _ _ _ _).bind fun _ ↦ MonoD.pure _)
    (refW_readE2s 50 (WAt.idx_eq hw2 (by simp only [List.length_replicate]))) ?_
  intro ab ab' hab
  subst hab
  refine RefAtW.bind (fun _ ↦ (monoD_tapeGkrD _ _ _).bind fun _ ↦ (MonoD.require _).bind fun _ ↦
    (monoD_wireUDL _ _ _ _).bind fun _ ↦ MonoD.pure _)
    (refW_samplesGL E2V.gC1 1
      (WAt.idx_eq hw3 (by simp only [List.length_append, List.length_replicate, length_wReads]))) ?_
  rintro r20 r20' ⟨h20, h20l⟩
  subst h20
  refine RefAtW.bind (fun _ ↦ (MonoD.require _).bind fun _ ↦ (monoD_wireUDL _ _ _ _).bind fun _ ↦ MonoD.pure _)
    ((refW_tapeGkrD 21 (r ++ r20) (t1ValsF 20 13 (r ++ r20) ab) (by simp [hrl, h20l])
      (WAt.idx_eq hw4 (by simp only [List.length_append, List.length_replicate, length_wReads]))).congr_prog ?_) ?_
  · rw [List.map_append, map_toE2_t1ValsF, List.map_append]
  rintro c c' ⟨hc, hcl⟩
  subst hc
  refine RefAtW.bind (fun _ ↦ (monoD_wireUDL _ _ _ _).bind fun _ ↦ MonoD.pure _)
    (RefAtW.require fun h ↦ of_decide_eq_true h) fun _ _ _ ↦ ?_
  refine RefAtW.bind (fun _ ↦ MonoD.pure _)
    (refW_wireUDL iv s d hs n c (by omega)
      (WAt.idx_eq hw5 (by simp only [List.length_append, List.length_replicate, length_wReads]; omega))) ?_
  intro wo wo' hwo
  exact (RefAtW.pure ⟨by rw [List.map_append], hrl, h20l, rfl, rfl, hwo⟩).idx
    (by simp only [wTapeU, List.length_append, List.length_replicate, length_wReads]; omega)

end Ref

theorem retD_wireUDL (iv : List (ℕ × ℕ)) (s : List FK) (n : ℕ) (claim : E2V.KClaim FE2) :
    RetD (fun wo : (List FE2 × FE2) × List FE2 × SlotC × SlotC × SlotC ↦
      wo.1.1.length = 20 ∧ wo.2.2.1.1.1.length = 2 ∧
        wo.2.2.1.2.2.1.2 = rowWD (wo.1.1 ++ wo.2.2.1.1.1 ++ E2V.selPtF 0 1) wo.2.2.1.2.2.2 ∧
        wo.2.2.2.1.1.1.length = 5 ∧
        wo.2.2.2.1.2.2.1.2 = rowWD (wo.1.1.take 13 ++ wo.2.2.2.1.1.1 ++ E2V.selPtF 22 5) wo.2.2.2.1.2.2.2 ∧
        wo.2.2.2.2.1.1.length = 5 ∧
        wo.2.2.2.2.2.2.1.2 = rowWD (wo.1.1.take 13 ++ [0] ++ wo.2.2.2.2.1.1 ++ E2V.selPtF 10 4) wo.2.2.2.2.2.2.2)
      (wireUDL iv s n claim) :=
  (retD_sumcheckD _ _ _ _).bind fun _ hsc ↦ RetD.bind_true fun _ ↦ RetD.bind_true fun _ ↦
    (retD_slotD _ _ _ _ _ _).bind fun _ hd ↦ (retD_slotD _ _ _ _ _ _).bind fun _ hy ↦
      (retD_slotD _ _ _ _ _ _).bind fun _ hm ↦
        RetD.pure ⟨by simpa using hsc, hd.1, hd.2, hy.1, hy.2, hm.1, hm.2⟩

theorem retD_tapeUDL (iv : List (ℕ × ℕ)) (s : List FK) (n : ℕ) : RetD TapeShapeU (tapeUDL iv s n) :=
  RetD.bind_true fun _ ↦ (retD_samplesG _ _).bind fun _ hr ↦ RetD.bind_true fun _ ↦ RetD.bind_true fun _ ↦
    RetD.bind_true fun _ ↦ RetD.bind_true fun _ ↦ (retD_wireUDL _ _ _ _).bind fun _ hwo ↦
      RetD.pure ⟨hr, hwo⟩

end Lvm.VEq

namespace Lvm.E2U

open Lvm DM E2V
open Lvm.E2L (wireUDGc tapeUDGc)

theorem dSelBits_P20S : dSelBits P20S = 1 := rfl
theorem dSel_P20S : dSel P20S = 0 := by unfold dSel; rw [layout0_P20S, layout0_P20U]; rfl

/-- **V_S's merged tape at `P20S` with the intervals `iv` is `tapeUDL iv`** (`tapeUDG_R`'s proof). -/
theorem tapeUDGc_RS (iv : List (ℕ × ℕ)) (s : List FK) (n : ℕ) :
    mapTU <$> tapeUDGc iv rowSwitchDR P20S s n = tapeUDL iv s n := by
  have hy : (layout0 P20S).ks / 2 ^ (13 + 5) = 22 := by rw [layout0_P20S, layout0_P20U]; rfl
  have hm : (layout0 P20S).s / 2 ^ 19 = 10 := by rw [layout0_P20S, layout0_P20U]; rfl
  unfold tapeUDGc wireUDGc tapeUDL wireUDL
  simp only [slotDFW_yWG, slotDFW_mWG, dSelBits_P20S, dSel_P20S, ← slotDFG_R, ← tapeGkrDF_eq,
    ← wireTargetDF_eq, ← dWA_eq, samplesG_one, map_bind, bind_map_left, map_pure, bind_assoc, pure_bind,
    show P20S.logN = 20 from rfl, show P20S.ksLog = 13 from rfl, show P20S.nuMain = 23 from rfl,
    show P20S.nuRec = 19 from rfl, show (2 : ℕ) * 25 = 50 from rfl, slotBitsU, hy, hm,
    show (23 : ℕ) - (13 + 5) = 5 from rfl, show (23 : ℕ) - 19 = 4 from rfl, show (20 : ℕ) + 1 = 21 from rfl]
  rfl

end Lvm.E2U

namespace Lvm.VEq

open Lvm DM LeanVM.Parameters LeanVM.Protocol.Compile
open Lvm.E2U
open Lvm.E2L (wireUDGc tapeUDGc)

section Ref

variable {cap : ℕ → ℕ → ℕ} {occ : ℕ → ℕ → ℕ} {shp : ℕ → ℕ × ℕ} {rw : ℕ → ℕ} {sig : ByteArray}

/-- **V_S's S2GS tape on the data** refines `tapeProgL iv`, its value through `mapTU`. -/
theorem refW_tapeUDGcS (iv : List (ℕ × ℕ)) (s : List FK) (d : RecursionFast.Digest) (hs : sBitsD s = Lvm.KG.digestBits d) (n : ℕ)
    {i : ℕ} (hw : WAt rw i wTapeU) :
    RefAtW cap occ shp rw sig i (tapeUDGc iv rowSwitchDR P20S s n) (tapeProgL iv d n)
      (fun t o ↦ TapeURelW (mapTU t) o) (i + wTapeU.length) :=
  RefAtW.of_map (by rw [tapeUDGc_RS]; exact refW_tapeUDL iv s d hs n hw)

end Ref

/-- **What V_S's S2GS tape on the data returns**: the closures' shape and the block rows' points. -/
theorem retD_tapeUDGcS (iv : List (ℕ × ℕ)) (s : List FK) (n : ℕ) :
    RetD (fun t : TapeU RowZ ↦ TapeShapeU (mapTU t) ∧ ColsW P20S t.wo)
      (tapeUDGc iv rowSwitchDR P20S s n) := by
  refine RetD.and (RetD.of_map (f := mapTU) ?_) ?_
  · rw [tapeUDGc_RS]; exact retD_tapeUDL iv s n
  · unfold tapeUDGc
    exact RetD.bind_true fun _ ↦ RetD.bind_true fun _ ↦ RetD.bind_true fun _ ↦ RetD.bind_true fun _ ↦
      RetD.bind_true fun _ ↦ RetD.bind_true fun _ ↦ (retD_wireUDGc _ _ _ _ _).bind fun _ h ↦ RetD.pure h

theorem monoD_tapeUDGcS (iv : List (ℕ × ℕ)) (s : List FK) (n : ℕ) : MonoD (tapeUDGc iv rowSwitchDR P20S s n) :=
  MonoD.of_map (f := mapTU) (by rw [tapeUDGc_RS]; exact monoD_tapeUDL iv s n)

end Lvm.VEq

/-! ## S2GS's middle phases follow the schedule -/

namespace Lvm.VEq

open LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.Compile
open Lvm.E2V

section FrontS

variable {cap : ℕ → ℕ → ℕ} {shp : ℕ → ℕ × ℕ} {idx : Ref → ℕ} (p : Params)

/-- **The wire over any `iv`** against `wireU` at a record with `logN = 20` (`folP_wireProgU`'s proof). -/
theorem folP_wireProgL (iv : List (ℕ × ℕ)) (hN : p.logN = 20) (s : RecursionFast.Digest) (n : ℕ) (claim : KClaim E2) :
    FolP cap shp idx (Lvm.E2U.wireProgL iv s n claim) (atomsOf p (wireU p)) fun _ ↦ True := by
  have e : atomsOf p (wireU p) = atomsOf p (sumcheckE2I 20 2) ++ (List.replicate 3 (.rdw e2Bytes) ++
      (atomsOf p (slotRedI 2) ++ (atomsOf p (slotRedI laneBits) ++ atomsOf p (slotRedI laneBits)))) := by
    simp only [wireU, hN, List.flatten_cons, List.flatten_nil, List.append_nil, atomsOf_append, atomsOf_rdE2]
  rw [e]
  unfold Lvm.E2U.wireProgL
  exact (folP_sumcheckE2 p _ rfl (by norm_num) _ 20 _ (List.length_replicate ..)).bind fun _ _ ↦
    (folP_e2Reads 3).bind fun _ _ ↦ (folP_require _).bind fun _ _ ↦
    (folP_slotRedU p 2 _ _ _ _ _).bind fun _ _ ↦ (folP_slotRedU p 5 _ _ _ _ _).bind fun _ _ ↦
    (folP_slotRedU p 5 _ _ _ _ _).bind_ret fun _ _ ↦ trivial

/-- **The merged tape over any `iv`** against `tapeU ++ wireU` at a record with `logN = 20` (`folP_tapeProgU`'s
proof). -/
theorem folP_tapeProgL (iv : List (ℕ × ℕ)) (hN : p.logN = 20) (s : RecursionFast.Digest) (n : ℕ) :
    FolP cap shp idx (Lvm.E2U.tapeProgL iv s n) (atomsOf p (tapeU p) ++ atomsOf p (wireU p)) fun _ ↦ True := by
  have e : atomsOf p (tapeU p) ++ atomsOf p (wireU p) =
      [.sm] ++ ((List.replicate 20 [Atom.rdw nonceBytes, .sm]).flatten ++ (List.replicate 50 (.rdw e2Bytes) ++
        ((List.replicate 1 [Atom.rdw nonceBytes, .sm]).flatten ++
          (atomsOf p (tapeLayersE2I 21) ++ atomsOf p (wireU p))))) := by
    simp only [tapeU, hN, List.flatten_cons, List.flatten_nil, List.append_nil, atomsOf_append, atomsOf_rdE2,
      atomsOf_sepI, atomsOf_gsmpN, atomsOf_gsmp, List.append_assoc]
    rfl
  rw [e]
  unfold Lvm.E2U.tapeProgL
  exact folP_e2Sep.bind fun _ _ ↦ (folP_e2Samples _ 20).bind fun r hr ↦ (folP_e2Reads 50).bind fun _ _ ↦
    (folP_e2Samples _ 1).bind fun r1 hr1 ↦
    (folP_tapeGkrE2 p 21 (r ++ r1) _ (by rw [List.length_append, hr, hr1])).bind fun _ _ ↦
    (folP_require _).bind fun _ _ ↦ (folP_wireProgL p iv hN _ _ _).bind_ret fun _ _ ↦ trivial


end FrontS

section MidS

variable {cap : ℕ → ℕ → ℕ} {shp : ℕ → ℕ × ℕ} {idx : Ref → ℕ}

/-- **S2GS's middle phases** (`midGS Ti`) against the typed and the front items at `P20S`. -/
theorem folP_midGS (Ti : Typed.TInst) (hl : P20S.leafdecReads = 1) (hd : P20S.busDepth = Typed.miniDepth)
    (x : List UInt8) :
    FolP cap shp idx (Lvm.E2S.midGS Ti x) (atomsOf P20S (typedIL P20S ++ (tapeU P20S ++ wireU P20S)))
      fun _ ↦ True := by
  rw [atomsOf_append, atomsOf_append]
  unfold Lvm.E2S.midGS
  exact (folP_typedProgL _ Ti _ rfl hl hd).bind fun _ _ ↦
    (folP_tapeProgL _ _ rfl _ _).bind_ret fun _ _ ↦ trivial

theorem atomsOf_pinIS : atomsOf P20S (pinI P20S) = List.replicate CMain.nu20 .sm ++ [.rd] := by
  rw [pinI, atomsOf_append, atomsOf_smp, atomsOf_rd]
  rfl

/-- **S2GS's pinned middle phases follow `midItemsL`** at `P20S`, for every relocation. -/
theorem folP_midPS (reloc : List UInt8 → VStackClaim → VStackClaim) (Ti : Typed.TInst)
    (hl : P20S.leafdecReads = 1) (hd : P20S.busDepth = Typed.miniDepth) (x : List UInt8) :
    FolP cap shp idx (Lvm.E2F.midP (Lvm.ASM.midMk 4 reloc (Lvm.E2S.midGS Ti)) x) (atomsOf P20S (midItemsL P20S))
      fun _ ↦ True := by
  rw [midItemsL, atomsOf_append, atomsOf_pinIS]
  exact folP_midP _ x _ (folP_midMk 4 reloc _ x _ (folP_midGS Ti hl hd x))

end MidS

end Lvm.VEq

/-! ## The decision at S2GS -/

namespace Lvm.VEq

open Lvm DM LeanVM.Parameters LeanVM.Protocol.Compile Finset
open Lvm.FE2 (toE2)
open Lvm.E2U Lvm.E2T
open Lvm.E2V (selPtF)
open Lvm.E2L (linClaims dOpenFFL mbSumsN typedClaimsL typedProgL dTypedLG)
open Lvm.CT (occOfU)
open LeanVM.Protocol.Whir.Sound (cfgMain23Jq cfgMain24G)

/-- **The pinned middle phases at S2GS as one chain** (`psU_eq`'s twin). -/
theorem psS_eq (Ti : Typed.TInst) (x : List UInt8) :
    Lvm.ASM.PSWithM (Lvm.E2F.midP (Lvm.ASM.midMk 4 relocU20 (Lvm.E2S.midGS Ti))) x =
      VerifierProgram.readCommitment 19 64 >>= fun _ ↦ Lvm.E2F.pinProg >>= fun za ↦
        typedProgL Ti (pubXTS x) >>= fun a ↦ tapeProgL (Lvm.E2S.contIvS Lvm.E2S.aSP) (hdX x).s (pubX x).n >>= fun k ↦
          LeanVM.Protocol.Verifier.verifyStackedJ (cfgMain23Jq 1) (Lvm.E2F.pinClaim za ::
            Lvm.ASM.ordMk 4 ((assembleU₂ x a k).1.map (relocU20 x)) (assembleU₂ x a k).2) >>= fun _ ↦
              pure true := by
  unfold Lvm.ASM.PSWithM Lvm.E2F.midP Lvm.ASM.midMk Lvm.E2S.midGS
  rw [commitRootUd_mainT]
  simp only [bind_assoc, ret_bindM, pure_bind]


section Ref

variable {cap : ℕ → ℕ → ℕ} {occ : ℕ → ℕ → ℕ} {shp : ℕ → ℕ × ℕ} {rw : ℕ → ℕ} {sig : ByteArray}

/-- **V_S's typed phases at S2GS** (items on `P20S`'s layout) refine `typedProgL` (`ref_dTypedLO` at `P20S`). -/
theorem ref_dTypedLS (N : TNatT) (Q : Lvm.Loop.Program) (lay : Typed.Lay) (H : TRefHypT N Q lay) (pub : Pub)
    (hacc : pub.accIn.pt.length = Typed.phiVarsT) {i : ℕ} (hw : WAt rw i wTypedL) :
    RefAtWP cap occ shp rw sig i (dTypedLG P20 N (m3G N P20S) pub (typedItemsND N P20S))
      (typedProgL (N.inst Q lay) pub) (fun r a ↦ TRelTL P20S N Q lay (r.1, r.2.1.flatMap FItem.flat, r.2.2) a)
      (fun r ↦ N.phiT (r.1.pt.map Lvm.e2OfFE) = Lvm.e2OfFE r.1.y) (i + wTypedL.length) := by
  have h := ref_dTypedLO (cap := cap) (occ := occ) (shp := shp) (rw := rw) (sig := sig) P20S N Q lay H
    (m3G N P20S) ((m3G_busFinal N P20S).trans (real_busFinal P20 N.mbT).symm) pub hacc hw
  rw [dTypedLG_items] at h
  have h' := RefAtWP.of_map h
  exact h'

end Ref

theorem skip_P20S : nodeBytes * 2 ^ (P20S.level ⟨.main, 0⟩).cap = 32 * 2 ^ capS 19 64 := by decide

/-- **V_S's S2GS decision refines the pinned S2GS middle phases** at `occOfU`, with read widths `wDecL asO` from
read `0`, under the promise that its value passes `Φ_Q` at `E2` (`ref_decideGU`'s twin with `claimsL_rel`). -/
theorem ref_decideGS (N : TNatT) (Q : Lvm.Loop.Program) (lay : Typed.Lay) (H : TRefHypT N Q lay)
    (hlin : Lvm.M3.mbLinB N.mbT = true)
    (hσ : ∀ g ∈ N.toN.regs, g.src = .sigma → (layout0 P20U).s ≤ g.dst ∧ g.dst + 2 ^ g.log ≤ (layout0 P20U).s + 2 ^ 19)
    (vk c : RecursionFast.Digest) (x : List UInt8) {sig : ByteArray} (hpub : pubOfWS vk c sig = pubXTS x)
    (asO : List Atom) {rw : ℕ → ℕ}
    (hFO : ∀ (cl : List VStackClaim) (pp : List ℕ),
      Fol capS shpS idxS (LeanVM.Protocol.Verifier.verifyStackedJ (cfgMain23Jq 1) cl) asO pp fun _ _ ↦ True)
    (h24O : ∀ w ∈ widthsA asO, w = 24) (hw : WAt rw 0 (wDecL asO))
    (hacc : (pubXTS x).accIn.pt.length = Typed.phiVarsT) (hs : sBitsD (pubXTS x).s = KG.digestBits (hdX x).s) :
    RefAtPW capS occOfU shpS rw sig 0 (Lvm.E2S.decideProgSG P20S P20 Lvm.E2S.aSP N vk c)
      (Lvm.ASM.PSWithM (Lvm.E2F.midP (Lvm.ASM.midMk 4 relocU20 (Lvm.E2S.midGS (N.inst Q lay)))) x)
      (fun _ b ↦ b = true) (fun a ↦ N.phiT (a.pt.map Lvm.e2OfFE) = Lvm.e2OfFE a.y) (wDecL asO).length := by
  rw [wDecL, WAt.append, WAt.append, WAt.append] at hw
  obtain ⟨⟨⟨hw0, hwT⟩, hwF⟩, hwO⟩ := hw
  replace hwF := WAt.idx_eq hwF (j := 0 + [24].length + wTypedL.length)
    (by simp only [List.length_append]; omega)
  replace hwO := WAt.idx_eq hwO (j := 0 + [24].length + wTypedL.length + wTapeU.length)
    (by simp only [List.length_append]; omega)
  have hsc : M3.sumcheckTabs N.mbT = N.mbT := H.toT.sc_eq
  rw [psS_eq]
  unfold Lvm.E2S.decideProgSG
  refine RefAtPW.read_left ?_
  dsimp only
  rw [hpub]
  -- the cap
  refine RefAtPW.bind (Q := fun _ ↦ True) ?_
    ((refW_skip (n := nodeBytes * 2 ^ (P20S.level ⟨.main, 0⟩).cap) (ht := 19) (w := 64) skip_P20S).toPW _)
    (fun _ _ _ ↦ trivial) ?_
  rotate_left
  rintro - - - -
  -- the pin
  refine RefAtPW.bind (Q := fun _ ↦ True) ?_ ((refW_pinD (WAt.cons.mp hw0).1).toPW _) (fun _ _ _ ↦ trivial) ?_
  rotate_left
  rintro pin za ⟨z, a, rfl, rfl⟩ -
  -- the typed phases
  have hT0 : RefAtPW capS occOfU shpS rw sig (0 + [24].length)
      (dTypedLG P20 N (m3G N P20S) (pubXTS x) (typedItemsND N P20S))
      (typedProgL (N.inst Q lay) (pubXTS x)) (fun r a ↦ TRelTL P20S N Q lay (r.1, r.2.1.flatMap FItem.flat, r.2.2) a)
      (fun t ↦ N.phiT (t.1.pt.map Lvm.e2OfFE) = Lvm.e2OfFE t.1.y) (0 + [24].length + wTypedL.length) :=
    ref_dTypedLS N Q lay H (pubXTS x) hacc hwT
  refine RefAtPW.bind (Q := fun t ↦ N.phiT (t.1.pt.map Lvm.e2OfFE) = Lvm.e2OfFE t.1.y) ?_ hT0 ?_ ?_
  rotate_left
  · intro b s hs'
    refine promise_of_retDG (fun a ↦ N.phiT (a.pt.map Lvm.e2OfFE) = Lvm.e2OfFE a.y) ?_ hs'
    exact RetD.bind_true fun _ ↦ RetD.bind_true fun _ ↦ RetD.pure rfl
  rintro ⟨acc, ti, ζ, bus⟩ a' hT -
  dsimp only
  -- the tape
  rw [show (pubXTS x).n = (pubX x).n from rfl]
  have hTp1 := refW_tapeUDGcS (cap := capS) (occ := occOfU) (shp := shpS) (sig := sig) (Lvm.E2S.contIvS Lvm.E2S.aSP) (pubXTS x).s (hdX x).s hs
    (pubX x).n hwF
  have hTp2 := hTp1.retD (retD_tapeUDGcS (Lvm.E2S.contIvS Lvm.E2S.aSP) (pubXTS x).s (pubX x).n)
  have hTp := hTp2.toPW (fun _ ↦ True)
  refine RefAtPW.bind (Q := fun _ ↦ True) ?_ hTp (fun _ _ _ ↦ trivial) ?_
  rotate_left
  rintro tp k ⟨hk, hsh, hcols⟩ -
  -- the opening, on the closures' claims
  have hsh' := hsh
  obtain ⟨-, hl20, -, -, hy5, -, hm5, -⟩ := hsh'
  have hlc : linClaims CMain.nu20 ζ ((List.range 3).map (M3.mbColsN N.mbT bus))
      ((List.range 3).map (M3.mbValueN N.mbT bus ζ)) =
      (mbSumsN N.mbT (ζ, bus)).map fun c ↦ (Com.main, c, (0 : FE)) := Lvm.E2L.linClaims_mb N.mbT (ζ, bus)
  have e : dOpenFFL P20S (TypedV.smallT P20S (pubXTS x)) (BlockClaim.point ⟨CMain.nu20, 0⟩ z a) ti ζ
      ((List.range 3).map (M3.mbColsN (M3.sumcheckTabs N.mbT) bus))
      (M3.mbValsF (M3.sumcheckTabs N.mbT) bus ζ) (frontItemsU rowAccR P20S (pubXTS x) tp) =
      dOpenF P20U (Shape.small x) (BlockClaim.point ⟨CMain.nu20, 0⟩ z a) (ti.flatMap FItem.flat ++
        (mbSumsN N.mbT (ζ, bus)).map (fun c ↦ (Com.main, c, (0 : FE))) ++ frontClaimsUD P20U (pubXT x) (mapTU tp)) := by
    rw [M3.mbValsF_eq, dOpenFFL_eq, hsc]
    show dOpenF P20U (TypedV.smallT P20U (pubXT x)) _ (ti.flatMap FItem.flat ++
      linClaims CMain.nu20 ζ ((List.range 3).map (M3.mbColsN N.mbT bus))
        ((List.range 3).map (M3.mbValueN N.mbT bus ζ)) ++
      (frontItemsU rowAccR P20U (pubXT x) tp).flatMap FItem.flat) = _
    rw [smallT_P20U, hlc]
    refine dOpenF_congr _ _ _ ?_
    rw [List.map_append, List.map_append, List.map_append, List.map_append,
      frontU_stk _ _ tp hcols hl20 hy5 hm5]
  rw [e]
  have hO := RefAtP.toPW (ref_dOpenFO (sig := sig) P20U rfl rfl rfl corrMainU _ _ (screl_pinW z a) (Shape.small x) _ _
    (claimsL_rel N Q lay H hlin hσ x (acc, ti.flatMap FItem.flat, ζ, bus) a' hT (mapTU tp) k hk hsh))
    (cap' := capS) (shp' := shpS) (idx := idxS) (hFO _) hwO h24O
  refine RefAtPW.bind (Q := fun _ ↦ True) (fun _ ↦ MonoD.pure _) hO (fun _ _ _ ↦ trivial) ?_
  rintro - - - -
  exact ((RefAtW.pure (R := fun (_ : Acc) (b : Bool) ↦ b = true) rfl).idx
    (by simp only [wDecL, List.length_append, List.length_singleton])).toPW _
  all_goals repeat' (first
    | (with_reducible exact MonoD.pure _) | (with_reducible exact monoD_skip _)
    | (with_reducible exact monoD_pinD _) | (with_reducible exact monoD_dTypedLG _ _ _ _ _)
    | (with_reducible exact monoD_tapeUDGcS _ _ _) | (with_reducible exact monoD_dOpenFFL _ _ _ _ _ _ _ _)
    | (with_reducible exact monoD_dOpenF _ _ _ _)
    | (with_reducible refine MonoD.bind ?_ fun _ ↦ ?_) | (dsimp only) | split | intro _)

end Lvm.VEq

/-! ## The schedule at S2GS: atoms, follow, static check, read widths; the assembly -/

/-! ## The schedule at S2GS: atoms, follow, static check, read widths; the assembly -/

namespace Lvm.VEq

open Lvm DM LeanVM.Parameters LeanVM.Protocol.Compile
open Lvm.E2U Lvm.E2T
open Lvm.E2S (decideProgSG decideFSG)
open Lvm.CT (occOfU)
open LeanVM.Protocol.Whir.Sound (cfgMain23Jq cfgMain24G)

/-- **S2GS's atoms are `P20`'s** (`P20S`'s levels are `P20U`'s). -/
theorem atomsOf_S (its : List Item) : atomsOf P20S its = atomsOf P20 its :=
  atomsOf_congrL P20S P20 (fun r ↦ by
    obtain ⟨c, lv⟩ := r
    cases c
    · exact withRow0_getD P20.mainLevels 46 lv
    · exact ⟨rfl, rfl⟩) its

theorem atomsOf_scheduleS : atomsOf P20S (schedule P20S) =
    [.cap (P20.level ⟨.main, 0⟩).cap ⟨.main, 0⟩] ++
      (atomsOf P20S (midItemsL P20S) ++ (atomsOf P20 (openMainI P20) ++ [])) := by
  rw [scheduleL_eq _ rfl rfl, atomsOf_append, atomsOf_append, atomsOf_append, atomsOf_nil,
    atomsOf_S (openMainI P20S), atomsOf_S (commitI P20S), show openMainI P20S = openMainI P20 from rfl,
    show commitI P20S = commitI P20 from rfl, atomsOf_commitI]

/-- **S2GS's `P_S` follows the schedule** at `P20S` (`fol_PSOfU`'s proof with `folP_midPS`). -/
theorem fol_PSOfS (reloc : List UInt8 → VStackClaim → VStackClaim) (Ti : Typed.TInst) (x : List UInt8) :
    Fol capS shpS idxS (Lvm.ASM.PSWithM (Lvm.E2F.midP (Lvm.ASM.midMk 4 reloc (Lvm.E2S.midGS Ti))) x)
      (atomsOf P20S (schedule P20S)) [] fun _ _ ↦ True := by
  rw [atomsOf_scheduleS]
  unfold Lvm.ASM.PSWithM
  refine Fol.bindP (folP_commitRootUd cfgMain24G rfl cap_main0 rfl) fun _ _ ↦ ?_
  refine @Fol.bindP capS shpS idxS _ _ (Lvm.E2F.midP (Lvm.ASM.midMk 4 reloc (Lvm.E2S.midGS Ti)) x) _
    (atomsOf P20S (midItemsL P20S)) (atomsOf P20 (openMainI P20) ++ []) _ [] _
    (folP_midPS reloc Ti rfl busDepth_P20 x) fun cl _ ↦ ?_
  exact @Fol.bindQ capS shpS idxS _ _ _ _ (atomsOf P20 (openMainI P20)) [] [] _ _ (@fol_openMain cl [])
    fun _ _ _ ↦ trivial

set_option maxRecDepth 200000 in
/-- **The static check at S2GS** at the occupied words `occOfU` (one kernel evaluation over the items). -/
theorem stA_P20S : stA P20S (atomsOf P20S (schedule P20S)) 0 [] [] occOfU = true := by
  rw [stA_atomsOf]
  decide +kernel

/-- **`rwS20` is the S2GS schedule's read widths** from read `0`. -/
theorem wAt_rwS20 : WAt rwS20 0 (widthsA (atomsOf P20S (schedule P20S))) := by
  rw [← readWidthsP_eqAP]
  exact wAt_getD _ _

/-- **The S2GS schedule's read widths** in V_S's decision order (`wDecL`). -/
theorem widthsA_scheduleS : widthsA (atomsOf P20S (schedule P20S)) = wDecL (atomsOf P20 (openMainI P20)) := by
  have hp : widthsA (List.replicate CMain.nu20 Atom.sm) = [] := by
    generalize CMain.nu20 = n
    induction n with
    | zero => rfl
    | succ n ih => rw [List.replicate_succ]; exact ih
  have hT : widthsA (atomsOf P20S (typedIL P20S)) = wTypedL := by
    have e : typedIL P20S = (zeroIT ++ (wiringIT ++ (relayIT ++ accIT P20S))) ++ miniBusI P20S := by
      simp only [typedIL, List.append_assoc]
    have hm : widthsA (atomsOf P20S (miniBusI P20S)) = List.replicate nMiniRdL 24 := by
      rw [widthsA_eq_replicate _ (mem_widthsA_atomsOf _ _ (by
        simp only [miniBusI, gpI, List.flatten_cons, List.flatten_nil, List.append_nil, noWB_append, noWB_smp,
          noWB_rd, noWB_gpLayersI, Bool.and_self]))]
      rw [atomsOf_S]
      rfl
    rw [e, atomsOf_append, widthsA_append, hm, widthsA_atomsOf]
    simp only [zeroIT, wiringIT, relayIT, accIT, List.flatten_cons, List.flatten_nil, List.append_nil,
      List.flatMap_append, wI_rdE2, wI_gsmpN, wI_gsmp, wI_sumcheckE2I, show sepI.flatMap itemW = [] from rfl,
      wTypedL, wZeroT, wWireT, wRelayT, wAccT, List.append_assoc, List.nil_append]
    rfl
  have hF : widthsA (atomsOf P20S (tapeU P20S ++ wireU P20S)) = wTapeU := by
    rw [widthsA_atomsOf]
    simp only [tapeU, wireU, slotRedI, show P20S.logN = 20 from rfl, List.flatten_cons, List.flatten_nil,
      List.append_nil, List.flatMap_append, wI_rdE2, wI_gsmpN, wI_gsmp, wI_sumcheckE2I, wI_tapeLayersE2I, wI_smp,
      show sepI.flatMap itemW = [] from rfl, wTapeU, wWireU, wTapeGkr, wSlot, List.nil_append, List.append_assoc]
    rfl
  rw [atomsOf_scheduleS, midItemsL, atomsOf_append P20S (pinI _), atomsOf_append P20S (typedIL _), atomsOf_pinIS]
  simp only [widthsA_append, hp, hT, hF, List.append_nil, List.nil_append, List.append_assoc, wDecL]
  rfl

/-- **V_S's S2GS decision refines the pinned S2GS middle phases on the stream with S2GS's read widths** under the
promise that its value passes `Φ_Q` at `E2` (`ref_decideGL` with the opening's atoms and widths). -/
theorem ref_decideGSX (N : TNatT) (Q : Lvm.Loop.Program) (lay : Typed.Lay) (H : TRefHypT N Q lay)
    (hlin : Lvm.M3.mbLinB N.mbT = true)
    (hσ : ∀ g ∈ N.toN.regs, g.src = .sigma → (layout0 P20U).s ≤ g.dst ∧ g.dst + 2 ^ g.log ≤ (layout0 P20U).s + 2 ^ 19)
    (sig : ByteArray) (vk c : RecursionFast.Digest) (x : List UInt8) (hpub : pubOfWS vk c sig = pubXTS x) :
    RefAtPW capS occOfU shpS rwS20 sig 0 (decideProgSG P20S P20 Lvm.E2S.aSP N vk c)
      (Lvm.ASM.PSWithM (Lvm.E2F.midP (Lvm.ASM.midMk 4 relocU20 (Lvm.E2S.midGS (N.inst Q lay)))) x) (fun _ b ↦ b = true)
      (fun a ↦ N.phiT (a.pt.map Lvm.e2OfFE) = Lvm.e2OfFE a.y) (wDecL (atomsOf P20 (openMainI P20))).length := by
  have hw : WAt rwS20 0 (wDecL (atomsOf P20 (openMainI P20))) := by
    have h := wAt_rwS20
    rw [widthsA_scheduleS] at h
    exact h
  have hacc : (pubXTS x).accIn.pt.length = Typed.phiVarsT := by
    simp only [pubXTS, pubOfWS, List.length_map, List.length_range]; rfl
  have hs : sBitsD (pubXTS x).s = KG.digestBits (hdX x).s := by
    rw [show (pubXTS x).s = (pubX x).s from rfl, pubX_s, E2V.sBitsD_digestLanes]
  exact ref_decideGS N Q lay H hlin hσ vk c x hpub _ (fun cl pp ↦ fol_openMain cl pp)
    (fun w hw' ↦ mem_widthsA_openF w (by rw [openMainI_F, atomsOf_F]; exact hw')) hw hacc hs

private theorem stRunLS {α : Type} (x : StateM RS α) (s : RS) : x.run s = x s := (rfl : x.run s = x s).trans rfl

/-- `decideFSG` at `P20S` holds: the run's checks held and its folded claim passes `Φ_Q` at `E2` (`decideFLG_ok`'s
golfed form: `delta` and a non-`rfl` run step). -/
theorem decideFSG_ok {N : TNatT} {vk c : RecursionFast.Digest} {sig : ByteArray}
    (h : decideFSG P20S P20 Lvm.E2S.aSP N vk c sig = true) :
    (runD (decideProgSG P20S P20 Lvm.E2S.aSP N vk c) sig (RS.startH (headerBytesP P20S))).2.ok = true ∧
      N.phiT ((runD (decideProgSG P20S P20 Lvm.E2S.aSP N vk c) sig (RS.startH (headerBytesP P20S))).1.pt.map
        Lvm.e2OfFE) =
        Lvm.e2OfFE (runD (decideProgSG P20S P20 Lvm.E2S.aSP N vk c) sig (RS.startH (headerBytesP P20S))).1.y := by
  have eD : @decideFSG = @decideFSG := rfl
  conv at eD => rhs; delta decideFSG
  rw [eD] at h
  beta_reduce at h
  rw [DM.runOnH, stRunLS] at h
  rcases hr : runD (decideProgSG P20S P20 Lvm.E2S.aSP N vk c) sig (RS.startH (headerBytesP P20S)) with ⟨a, s⟩
  rw [show decideProgSG P20S P20 Lvm.E2S.aSP N vk c sig (RS.startH (headerBytesP P20S)) = (a, s) from hr] at h
  simp only [Bool.and_eq_true] at h
  exact ⟨h.1.1.1, fe2_beq h.2⟩

/-- **SLF-STMT 6's proof**: a `V_S` driving `decideFSG P20S P20 aSP N` after `parseOkS P20S` refines the
specification's scheme at `fmtS20` with the native check `okSL` (`schemeSWS`), the middle phases
`midMk 4 relocU20 (midGS _)` (`refines_seqOfGP` at `occOfU` with `ref_decideGSX`, `fol_PSOfS`, `stA_P20S`,
`wAt_rwS20`). -/
theorem refinesS20_of (N : TNatT) (Q : Lvm.Loop.Program) (lay : Typed.Lay) (H : TRefHypT N Q lay)
    (hσ : ∀ g ∈ N.toN.regs, g.src = .sigma → (layout0 P20U).s ≤ g.dst ∧ g.dst + 2 ^ g.log ≤ (layout0 P20U).s + 2 ^ 19)
    (hlin : Lvm.M3.mbLinB N.mbT = true) (VS : Lvm.T.SProg)
    (hVS : ∀ vk c π, VS vk c π =
      if parseOkS P20S vk c π then drive P20S π (decideFSG P20S P20 Lvm.E2S.aSP N vk c) else .ret false) :
    ∀ (vk : RecursionFast.Digest) (L : RecursionFast.Log) (c : RecursionFast.Digest) (π : RecursionFast.Proof),
      Lvm.T.isS π = true → (VS vk c π).runLog L = some true →
      ((Lvm.ASM.schemeSWS Lvm.CT.fmtS20 vk
        (Lvm.ASM.PSWithM (Lvm.E2F.midP (Lvm.ASM.midMk 4 relocU20 (Lvm.E2S.midGS (N.inst Q lay)))))).V c π).runLog L =
        some true :=
  fun vk L c π _ h ↦ runLog_of_seq (fun tr ht ↦ refines_seqOfGP
    (Lvm.ASM.PSWithM (Lvm.E2F.midP (Lvm.ASM.midMk 4 relocU20 (Lvm.E2S.midGS (N.inst Q lay)))))
    (wDecL (atomsOf P20 (openMainI P20))).length P20S Lvm.CT.fmtS20 VS (parseOkS P20S) Lvm.ASM.okSL
    (fun vk c ↦ decideFSG P20S P20 Lvm.E2S.aSP N vk c) (decideProgSG P20S P20 Lvm.E2S.aSP N)
    (fun a ↦ N.phiT (a.pt.map Lvm.e2OfFE) = Lvm.e2OfFE a.y) (fun sig vk c x ↦ pubOfWS vk c sig = pubXTS x) hVS
    (fun _ _ _ hp ↦ (parseOkS_parts hp).1) (fun _ _ _ hp ↦ hdrSW_of_parseOkS hp)
    (fun _ _ _ hF ↦ decideFSG_ok hF) (fun _ _ _ _ hp hs ↦ pubGS_eq hp hs)
    (fun sig vk c x hpub ↦ ref_decideGSX N Q lay H hlin hσ sig vk c x hpub) rfl rfl rfl
    (by rw [headerBytesP_P20S.1]; decide) (fun _ _ _ hp ↦ okSL_of_parseOkS hp (hdrFixS_le_P _))
    (fol_PSOfS relocU20 (N.inst Q lay)) stA_P20S wAt_rwS20 vk c π tr ht) L h

end Lvm.VEq
