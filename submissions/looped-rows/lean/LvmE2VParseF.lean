-- New for lvm2 E2-FT (E2F-V2-TOP): roll 11's header lemmas (`LvmVEqParse`, `LvmVEqMain`) at a header of `hb` bytes
-- (S2GF: `headerBytesP (P20F.withF accVF) = headerF accVF = 6,008`): `parseOk p` ⇒ `hdrSW`, `okS`, `pubOfA = pubXF`,
-- and the seed entry of the trace (`entOff` of entry 2 is `RS.startH hb`'s cursor).
import LvmTypedVEqTop
import LvmE2VPub
import LvmMPCert

/-!
# The header at a stage

`xOfH hb π` is the statement of an `S` proof whose header has `hb` bytes (bytes `8 … hb - 1`; `xOf = xOfH headerBytes`).

* `hdrOf_xOfH`: the header fields of the statement are the proof's (`hb ≥ headerBytes`);
* **`hdrSW_of_parseOk`**, **`okS_of_parseOkH`**, **`pubOfA_eq_pubXF`** (`pubOfA_congr`: `pubOfA accV` reads the
  stream's header bytes to `headerF accV`);
* `headerF_eq`, `headerBytesP_P20F`: S2GF's header is `headerBytesP (P20F.withF accVF) = 6,008` bytes;
* the trace: `entOff_oneH`, `size_seedQueryH`, **`entOff_twoH`** (`= (RS.startH hb).ent`), `seed_bytesH`.
-/

set_option autoImplicit false

namespace Lvm.VEq

open RecursionFast Lvm

/-- The statement bytes of an `S` proof with a header of `hb` bytes. -/
def xOfH (hb : ℕ) (π : ByteArray) : List UInt8 := ((π.data.toList).drop 8).take (hb - 8)

theorem xOfH_headerBytes (π : ByteArray) : xOfH headerBytes π = xOf π := rfl

theorem getD_xOfH (π : ByteArray) {hb t : ℕ} (ht : t < hb - 8) : (xOfH hb π).getD t 0 = π.get! (8 + t) := by
  simp only [get!_eq_getD, xOfH, List.getD_eq_getElem?_getD, List.getElem?_take, ht, ↓reduceIte,
    List.getElem?_drop]

theorem length_xOfH (π : ByteArray) {hb : ℕ} (h : hb ≤ π.size) : (xOfH hb π).length = hb - 8 := by
  rw [xOfH, List.length_take, List.length_drop, length_blb]; omega

theorem get!_hdrBytesH (π : ByteArray) {hb o : ℕ} (hH : hdrFix ≤ hb) (h1 : 8 ≤ o) (h2 : o < hdrFix) :
    (⟨(List.replicate 8 0 ++ xOfH hb π).toArray⟩ : ByteArray).get! o = π.get! o := by
  rw [get!_mk, List.getD_append_right _ _ _ _ (by simp only [List.length_replicate]; omega),
    List.length_replicate, getD_xOfH π (by omega)]
  congr 1
  omega

theorem get!_sigOfXH (π : ByteArray) {hb t : ℕ} (ht : t < hb - 8) :
    (sigOfX (xOfH hb π)).get! (headerAt 8 + t) = π.get! (8 + t) := by
  rw [sigOfX, get!_mk, List.getD_append_right _ _ _ _ (by simp only [List.length_replicate]; omega),
    List.length_replicate, Nat.add_sub_cancel_left, getD_xOfH π ht]

/-- **The statement's header fields are the proof's** (a header of at least its fixed part `hdrFix`; every header
field ends there). -/
theorem hdrOf_xOfH (π : ByteArray) {hb : ℕ} (hH : hdrFix ≤ hb) : Lvm.ASM.hdrOf (xOfH hb π) = Header.ofProof π :=
  ofProof_congrF fun _ h1 h2 ↦ get!_hdrBytesH π hH h1 h2

/-! ## The header's length -/

theorem headerBytes_le_P {p : Params} (hS : p.stage ≠ 2) : headerBytes ≤ headerBytesP p := by
  rw [headerBytesP_ne2 hS]; exact Nat.le_add_right _ _

theorem eight_le_P (p : Params) : 8 ≤ headerBytesP p := eight_le_hdrP p

/-- A `withF` record is at stage `1`. -/
theorem stage_withF_ne2 (p : Params) (accV : ℕ) : (p.withF accV).stage ≠ 2 := by
  simp [Params.withF]

theorem headerBytesP_le_piSize (p : Params) : headerBytesP p ≤ piSize p := by
  simp only [piSize]
  omega

/-- **`headerF` is the stage's header** (`accV ≥ accVars`). -/
theorem headerF_eq (p : Params) {accV : ℕ} (h : accVars ≤ accV) : headerF accV = headerBytesP (p.withF accV) := by
  rw [headerBytesP_ne2 (stage_withF_ne2 p accV)]
  simp only [headerF, headerBytes, Params.withF, eBytes, accVars] at h ⊢
  omega

/-- S2GF's header: 6,008 bytes. -/
theorem headerBytesP_P20F : headerBytesP (P20F.withF accVF) = 6008 := by decide

/-! ## `parseOk` at a stage -/

/-- **`parseOk p` ⇒ the compiled verifier's header parse** at `p`'s size and header. -/
theorem hdrSW_of_parseOk {p : Params} {vk c : Digest} {π : ByteArray} (h : parseOk p vk c π = true) :
    Lvm.ASM.hdrSW (piSize p) (headerBytesP p) π =
      some (xOfH (headerBytesP p) π, (π.data.toList).drop (headerBytesP p)) := by
  obtain ⟨hs, h0, hz, -⟩ := parseOk_parts h
  have h8 : 8 ≤ π.size := by rw [hs]; exact le_trans (eight_le_P p) (headerBytesP_le_piSize p)
  simp only [Lvm.ASM.hdrSW, hs, take8_of_parse' h8 h0 hz, and_self, ↓reduceIte]
  rfl

/-- **`parseOk p` ⇒ the compiled verifier's statement check** (the fast hashes are the specification's). -/
theorem okS_of_parseOkH {p : Params} {vk c : Digest} {π : ByteArray} (h : parseOk p vk c π = true) {hb : ℕ}
    (hH : hdrFix ≤ hb) : Lvm.ASM.okS vk c (xOfH hb π) = true := by
  obtain ⟨-, -, -, hb, hvk, hn1, hn2, hc, hsig⟩ := parseOk_parts h
  unfold Lvm.ASM.okS
  rw [hdrOf_xOfH π hH]
  unfold Header.stmt Header.leaf at hc
  rw [leafStmtF_eq, nodeStmtF_eq] at hc
  rw [SigOkF_eq, traceDigestF_eq] at hsig
  generalize Header.ofProof π = hd at *
  rcases hb with hb | hb
  · simp only [hb, ↓reduceIte] at hc
    simp [hb, hvk, hn1, hn2, hc]
  · simp only [hb, one_ne_zero, ↓reduceIte] at hc hsig
    simp [hb, hvk, hn1, hn2, hc, hsig]

/-! ## The public values -/

theorem feAt_congr {b b' : ByteArray} {o : ℕ} (h : ∀ i, o ≤ i → i < o + 24 → b.get! i = b'.get! i) :
    feAt b o = feAt b' o := by
  unfold feAt
  rw [kAt_congr fun j h1 h2 ↦ h j h1 (by omega), kAt_congr fun j h1 h2 ↦ h j (by omega) (by omega),
    kAt_congr fun j h1 h2 ↦ h j (by omega) (by omega)]

/-- **`pubOfA accV` reads only the stream's header bytes** (to `headerF accV`). -/
theorem pubOfA_congr {accV : ℕ} (hA : accVars ≤ accV) {vk c : Digest} {sig sig' : ByteArray}
    (h : ∀ o, headerAt 8 ≤ o → o < headerAt 8 + (headerF accV - 8) → sig.get! o = sig'.get! o) :
    pubOfA accV vk c sig = pubOfA accV vk c sig' := by
  have hF : headerBytes ≤ headerF accV := by
    rw [headerF_eq P20 hA]; exact headerBytes_le_P (stage_withF_ne2 _ _)
  have hE : ∀ i, i ≤ accV → feAt sig (headerAt (offAcc + eBytes * i)) =
      feAt sig' (headerAt (offAcc + eBytes * i)) := by
    intro i hi
    refine feAt_congr fun j h1 h2 ↦ h j ?_ ?_ <;>
      simp only [headerAt, offAcc, eBytes, sigBytes, headerF] at h1 h2 ⊢ <;> omega
  unfold pubOfA
  rw [pubOf_congr fun o h1 h2 ↦ h o h1 (by omega),
    List.map_congr_left fun k hk ↦ hE k (List.mem_range.mp hk).le, hE accV le_rfl]

/-- **`pubOf`'s fixed fields read only the header's fixed part** (to `hdrFix`), whatever `acc_in` replaces its own. -/
theorem pubOf_congrFix {vk c : Digest} {sig sig' : ByteArray}
    (h : ∀ o, headerAt 8 ≤ o → o < headerAt 8 + (hdrFix - 8) → sig.get! o = sig'.get! o) (A : Acc) :
    { pubOf vk c sig with accIn := A } = { pubOf vk c sig' with accIn := A } := by
  have hH : hdrFix = 4928 := rfl
  have hR : ∀ a n, 8 ≤ a → a + n ≤ 4928 → ∀ i, headerAt a ≤ i → i < headerAt a + n →
      sig.get! i = sig'.get! i :=
    fun a n ha hn i h1 h2 ↦ h i (by simp only [headerAt] at h1 ⊢; (clear * - h1; omega))
      (by simp only [headerAt] at h2 ⊢; (clear * - hH ha hn h2; omega))
  have hL : ∀ a m, 8 ≤ a → a + 8 * m ≤ 4928 → ∀ k ∈ List.range m, ∀ i, headerAt a + 8 * k ≤ i →
      i < headerAt a + 8 * k + 8 → sig.get! i = sig'.get! i := by
    intro a m ha hm k hk i h1 h2
    have := List.mem_range.mp hk
    exact h i (by simp only [headerAt] at h1 ⊢; (clear * - ha hm h1 this; omega))
      (by simp only [headerAt] at h2 ⊢; (clear * - hH ha hm h2 this; omega))
  have hs : sigBytes / 8 = 597 := rfl
  unfold pubOf
  rw [laneAt_congr (hR 8 8 (by decide) (by decide)), laneAt_congr (hR 112 8 (by decide) (by decide)),
    List.map_congr_left fun k hk ↦ kAt_congr (hL 48 4 (by decide) (by decide) k hk),
    List.map_congr_left fun k hk ↦ kAt_congr (hL 80 4 (by decide) (by decide) k hk),
    List.map_congr_left fun k hk ↦ kAt_congr (hL 120 4 (by decide) (by decide) k hk), hs,
    List.map_congr_left fun k hk ↦ kAt_congr (hL 152 597 (by decide) (by decide) k hk)]

/-- **`pubOfW rd ew accV` reads only the stream's header bytes** (to the end of `acc_in`), for a reader `rd` of `ew`
bytes. -/
theorem pubOfW_congr (rd : ByteArray → ℕ → FE) (ew accV : ℕ)
    (hrd : ∀ (b b' : ByteArray) (o : ℕ), (∀ i, o ≤ i → i < o + ew → b.get! i = b'.get! i) → rd b o = rd b' o)
    {vk c : Digest} {sig sig' : ByteArray}
    (h : ∀ o, headerAt 8 ≤ o → o < headerAt (offAcc + ew * (accV + 1)) → sig.get! o = sig'.get! o) :
    pubOfW rd ew accV vk c sig = pubOfW rd ew accV vk c sig' := by
  have hE : ∀ i, i ≤ accV → rd sig (headerAt (offAcc + ew * i)) = rd sig' (headerAt (offAcc + ew * i)) := by
    intro i hi
    have hm : ew * i + ew ≤ ew * (accV + 1) := by
      rw [Nat.mul_succ]; exact Nat.add_le_add_right (Nat.mul_le_mul_left _ hi) _
    refine hrd _ _ _ fun j h1 h2 ↦ h j ?_ ?_ <;>
      simp only [headerAt, offAcc, sigBytes] at h1 h2 hm ⊢ <;> omega
  unfold pubOfW
  rw [List.map_congr_left fun k hk ↦ hE k (List.mem_range.mp hk).le, hE accV le_rfl]
  exact pubOf_congrFix (fun o h1 h2 ↦ h o h1 (by simp only [headerAt, hdrFix, offAcc, sigBytes] at h2 ⊢; omega)) _

/-- **V_S's public values at a stage are the statement's**, for `acc_in` read by `rd` in scalars of `ew` bytes (on a
stream holding the proof's header bytes where the seed query puts them). -/
theorem pubOfW_eq {p : Params} {vk c : Digest} {π : ByteArray} (h : parseOk p vk c π = true)
    (rd : ByteArray → ℕ → FE) (ew accV : ℕ)
    (hrd : ∀ (b b' : ByteArray) (o : ℕ), (∀ i, o ≤ i → i < o + ew → b.get! i = b'.get! i) → rd b o = rd b' o)
    {hb : ℕ} (hH : hdrFix ≤ hb) (hF : offAcc + ew * (accV + 1) ≤ hb) {sig : ByteArray}
    (hsig : ∀ t < hb - 8, sig.get! (headerAt 8 + t) = π.get! (8 + t)) :
    pubOfW rd ew accV vk c sig =
      pubOfW rd ew accV (hdX (xOfH hb π)).vk (hdX (xOfH hb π)).stmt (sigOfX (xOfH hb π)) := by
  obtain ⟨-, -, -, -, hvk, -, -, hc, -⟩ := parseOk_parts h
  have hx : hdX (xOfH hb π) = Header.ofProof π := hdrOf_xOfH π hH
  rw [hx, hvk, ← hc]
  refine pubOfW_congr rd ew accV hrd fun o h1 h2 ↦ ?_
  obtain ⟨t, rfl⟩ : ∃ t, o = headerAt 8 + t := ⟨o - headerAt 8, by omega⟩
  have ht : t < hb - 8 := by simp only [headerAt] at h2 ⊢; omega
  rw [hsig t ht, get!_sigOfXH π ht]

/-- **V_S's public values at a stage are the statement's** (`pubOfW_eq` with 24-B scalars, `feAt`). -/
theorem pubOfA_eq {p : Params} {vk c : Digest} {π : ByteArray} (h : parseOk p vk c π = true) {accV hb : ℕ}
    (_hA : accVars ≤ accV) (hF : headerF accV ≤ hb) {sig : ByteArray}
    (hsig : ∀ t < hb - 8, sig.get! (headerAt 8 + t) = π.get! (8 + t)) :
    pubOfA accV vk c sig = pubOfA accV (hdX (xOfH hb π)).vk (hdX (xOfH hb π)).stmt (sigOfX (xOfH hb π)) :=
  pubOfW_eq h feAt eBytes accV (fun _ _ _ h ↦ feAt_congr h)
    (le_trans (by simp only [hdrFix, headerF]; omega) hF) (le_trans (by simp only [offAcc, headerF]; omega) hF) hsig

/-- **At S2GF**: `pubOfA accVF` on the stream is `pubXF` of the statement. -/
theorem pubOfA_eq_pubXF {vk c : Digest} {π : ByteArray} (h : parseOk (P20F.withF accVF) vk c π = true)
    {sig : ByteArray}
    (hsig : ∀ t < headerBytesP (P20F.withF accVF) - 8, sig.get! (headerAt 8 + t) = π.get! (8 + t)) :
    pubOfA accVF vk c sig = pubXF (xOfH (headerBytesP (P20F.withF accVF)) π) :=
  pubOfA_eq h (by decide) (le_of_eq (headerF_eq P20F (by decide))) hsig

/-! ## The seed entry of the trace -/

theorem entOff_oneH (a₀ : Digest) (e : ByteArray × Digest) (rest : Trace) :
    entOff ((q0Query, a₀) :: e :: rest) 1 = 48 := by
  simp [entOff, traceBytes_cons, traceBytes_nil, size_q0Query]

theorem size_seedQueryH (π : ByteArray) (a₀ : Digest) {hb : ℕ} (hH : hb ≤ π.size) :
    (seedQuery π a₀ hb).size = 32 + (hb - 8) := by
  rw [seedQuery, ByteArray.size_append, size_digestBytes, ← length_blb, blb_extract]
  simp; omega

/-- **The cursor after the seed** of a header of `hb` bytes is `RS.startH hb`'s. -/
theorem entOff_twoH (π : ByteArray) (a₀ st₀ : Digest) (rest : Trace) {hb : ℕ} (h8 : 8 ≤ hb)
    (hH : hb ≤ π.size) :
    entOff ((q0Query, a₀) :: (seedQuery π a₀ hb, st₀) :: rest) 2 = (RS.startH hb).ent := by
  have hd1 : ((q0Query, a₀) :: (seedQuery π a₀ hb, st₀) :: rest).drop 1 = (seedQuery π a₀ hb, st₀) :: rest := rfl
  rw [(stream_entry hd1).2.2, entOff_oneH, size_seedQueryH π a₀ hH]
  show _ = 1 + 47 + (8 + (32 + hb - 8) + 32)
  omega

/-- The header bytes in the stream: the seed entry holds `π`'s bytes `8 … hb - 1`. -/
theorem seed_bytesH (π : ByteArray) (a₀ st₀ : Digest) (rest : Trace) {hb : ℕ} (hH : hb ≤ π.size) :
    ∀ t < hb - 8, (traceBytesB ((q0Query, a₀) :: (seedQuery π a₀ hb, st₀) :: rest)).get!
      (headerAt 8 + t) = π.get! (8 + t) := by
  intro t ht
  have hd1 : ((q0Query, a₀) :: (seedQuery π a₀ hb, st₀) :: rest).drop 1 = (seedQuery π a₀ hb, st₀) :: rest := rfl
  have he := (stream_entry hd1).1 (32 + t) 1 (by rw [size_seedQueryH π a₀ hH]; omega)
  rw [entOff_oneH, show 48 + 8 + (32 + t) = headerAt 8 + t by simp [headerAt]; omega] at he
  have hg := getD_sb (traceBytesB ((q0Query, a₀) :: (seedQuery π a₀ hb, st₀) :: rest)) (headerAt 8 + t) 1 0
    (by omega)
  rw [Nat.add_zero] at hg
  rw [← hg, show sb = sbs from rfl, he, get!_blb]
  rw [List.getD_eq_getElem?_getD, List.getElem?_take_of_lt (by omega), List.getElem?_drop, Nat.add_zero,
    seedQuery, blb_append, blb_digestBytes, List.getElem?_append_right (by simp),
    show 32 + t - (Vector.toList a₀).length = t by simp, blb_extract, List.getElem?_take_of_lt (by omega),
    List.getElem?_drop, ← List.getD_eq_getElem?_getD]

/-- The seed query of the statement is the trace's (`hb ≤ |π|`). -/
theorem toQ_seedH (π : ByteArray) (a₀ : Digest) (hb : ℕ) :
    Lvm.FS.toQ (a₀.toList ++ xOfH hb π) = seedQuery π a₀ hb :=
  toQ_eq (by rw [seedQuery, blb_append, blb_digestBytes, blb_extract]; rfl)

end Lvm.VEq
