-- New for lvm2 E2-FT (E2F-V2-FOL): the `E2` front's programs (stage S2GF) follow the S2GF schedule's items
-- (`FolP`, LvmVEqFol): the reads and ground challenges, the rounds, the Keccak GKR at `E2`, the tape caller, the
-- `KS` caller and link, and the whole front `kgProgF` against S2GF's tape, wire, `KS` and `KS`-link items.
import LvmVEqFolMid
import LvmE2VMid

/-!
# The `E2` front follows the S2GF schedule

The S2GF builders (`LvmSchedule`): `rdE2 m` is `m` reads of 16 B (`.rdw e2Bytes`), `gsmp` a nonce read of 8 B and a
sample, `gsmpN n` `n` of them, `sepI` one sample; `sumcheckE2I`, `keccakLayerE2I`, `tapeLayersE2I`, `keccakE2I`;
the row switch `smp rowSwitchStages`. Per program a `FolP` (from every `pp`, the program follows the atoms and keeps
`pp`), the same recursion as roll 11's `E3` lemmas (`LvmVEqFol`, `LvmVEqFolMid`):

* `folP_e2Read`, `folP_e2Reads`, `folP_e2Sample`, `folP_e2Samples`, `folP_e2Sep`, `folP_rowSwitch`;
* `folP_sumcheckE2`, `folP_packRoundsE2` against `sumcheckE2I`;
* `folP_verifyKeccakLayerE2`, `folP_keccakLayersE2`, `folP_tapeGkrE2`, `folP_verifyKeccakE2`;
* `folP_slotProgE2`, `folP_wireChProgE2`, `folP_tapeProgE2`, `folP_callerProgE2`, `folP_ksLinkProgE2`;
* **`folP_kgProgF`**: `kgProgF s n` against `tapeIF ++ wireIF ++ ksIF ++ ksLinkIF` at `P20F.withF accVF`.
-/

set_option autoImplicit false

namespace Lvm.VEq

open LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open Lvm.E2V

/-! ## The S2GF front's items -/

section Items

variable (p : Params)

/-- The tape (S2GF `CHtape`): the separator, `r` (`logN` ground coordinates), 25 scalars, the GKR. -/
def tapeIF : List Item := List.flatten [sepI, gsmpN p.logN, rdE2 lanes, tapeLayersE2I p.logN]
/-- The wire (S2GF `CHwire`): the wiring rounds, `g_D`, the slot rounds, 64 slices, the row switch. -/
def wireIF : List Item :=
  List.flatten [sumcheckE2I p.logN 2, rdE2 1, sumcheckE2I 2 2, rdE2 kBits, smp rowSwitchStages]
/-- `KS`'s Keccak GKR at `E2`, then the row switch. -/
def ksIF : List Item := List.flatten [gsmpN p.ksLog, rdE2 lanes, keccakE2I p.ksLog, smp rowSwitchStages]
/-- The `KS` link at `E2`. -/
def ksLinkIF : List Item := List.flatten [gsmpN (p.ksLog + laneBits), sumcheckE2I p.ksLog 2, rdE2 4]

end Items

/-! ## Atoms of the `E2` builders -/

section Atoms

variable (p : Params)

theorem atomsOf_rdE2 (m : ℕ) : atomsOf p (rdE2 m) = List.replicate m (.rdw e2Bytes) := by
  unfold rdE2; split <;> simp_all [atomsOf, itemAtoms]

theorem atomsOf_gsmp : atomsOf p gsmp = [.rdw nonceBytes, .sm] := rfl

theorem atomsOf_sepI : atomsOf p sepI = [.sm] := rfl

theorem atomsOf_gsmpN (n : ℕ) : atomsOf p (gsmpN n) = (List.replicate n [Atom.rdw nonceBytes, .sm]).flatten := by
  rw [gsmpN, atomsOf_replicate, atomsOf_gsmp]

theorem gsmpN_add (a b : ℕ) : gsmpN (a + b) = gsmpN a ++ gsmpN b := by
  rw [gsmpN, gsmpN, gsmpN, List.replicate_add, List.flatten_append]

theorem atomsOf_sumcheckE2I_succ (n d : ℕ) :
    atomsOf p (sumcheckE2I (n + 1) d) =
      List.replicate d (.rdw e2Bytes) ++ ([.rdw nonceBytes, .sm] ++ atomsOf p (sumcheckE2I n d)) := by
  show atomsOf p ((rdE2 d ++ gsmp) ++ sumcheckE2I n d) = _
  rw [atomsOf_append, atomsOf_append, atomsOf_rdE2, atomsOf_gsmp, List.append_assoc]

end Atoms

/-! ## Reads, ground challenges, rounds -/

section Prim

variable {cap : ℕ → ℕ → ℕ} {shp : ℕ → ℕ × ℕ} {idx : Ref → ℕ} (p : Params)

theorem folP_readScalarW (w : ℕ) : FolP cap shp idx VerifierProgram.readScalar [.rdw w] fun _ ↦ True :=
  FolP.readW fun _ ↦ FolP.ret trivial

theorem folP_e2Read : FolP cap shp idx e2Read [.rdw e2Bytes] fun _ ↦ True := by
  unfold e2Read
  exact (folP_readScalarW e2Bytes).bind_ret fun _ _ ↦ trivial

theorem folP_e2Reads : ∀ n, FolP cap shp idx (e2Reads n) (List.replicate n (.rdw e2Bytes)) fun xs ↦ xs.length = n
  | 0 => FolP.ret rfl
  | n + 1 => by
    rw [e2Reads]
    exact folP_e2Read.bind fun _ _ ↦ (folP_e2Reads n).bind_ret fun xs h ↦ by rw [List.length_cons, h]

/-- **A ground challenge**: its nonce (8 B), the sample. -/
theorem folP_e2Sample (g : ℕ) : FolP cap shp idx (e2Sample g) [.rdw nonceBytes, .sm] fun _ ↦ True := by
  unfold e2Sample
  exact (folP_readScalarW nonceBytes).bind fun _ _ ↦ folP_sampleChallenge.bind fun _ _ ↦
    (folP_require _).bind_nil fun _ _ ↦ FolP.ret trivial

theorem folP_e2Samples (g : ℕ) : ∀ n, FolP cap shp idx (e2Samples g n)
    (List.replicate n [Atom.rdw nonceBytes, .sm]).flatten fun xs ↦ xs.length = n
  | 0 => FolP.ret rfl
  | n + 1 => by
    rw [e2Samples, List.replicate_succ, List.flatten_cons]
    exact (folP_e2Sample g).bind fun _ _ ↦ (folP_e2Samples g n).bind_ret fun xs h ↦ by rw [List.length_cons, h]

theorem folP_e2Sep : FolP cap shp idx e2Sep [.sm] fun _ ↦ True := by
  unfold e2Sep
  exact folP_sampleChallenge.bind_ret fun _ _ ↦ trivial

/-- **The row switch**: seven samples. -/
theorem folP_rowSwitch (z sv : List E2) :
    FolP cap shp idx (rowSwitch z sv) (List.replicate rowSwitchStages .sm) fun _ ↦ True := by
  unfold rowSwitch
  exact (folP_sampleChallenges _).bind_ret fun _ _ ↦ trivial

/-- A round's message at `E2` of `d + 1` coefficients: `d` scalars, in either mode. -/
theorem folP_roundPolyE2 {count d : ℕ} (hc : count = d + 1) (hd : 1 ≤ d) (claim : E2) (e : Option E2) :
    FolP cap shp idx (roundPolyE2 count claim e) (List.replicate d (.rdw e2Bytes)) fun _ ↦ True := by
  subst hc
  cases e with
  | none =>
    obtain ⟨c, rfl⟩ : ∃ c, d = c + 1 := ⟨d - 1, by omega⟩
    rw [roundPolyE2]
    exact folP_e2Read.bind fun _ _ ↦ (folP_e2Reads c).bind_ret fun _ _ ↦ trivial
  | some r =>
    rw [roundPolyE2]
    exact (folP_e2Reads d).bind_ret fun _ _ ↦ trivial

/-- **`sumcheckE2` against `sumcheckE2I`**: `n` rounds of `d` scalars and a ground challenge. -/
theorem folP_sumcheckE2 (g : ℕ) {count d : ℕ} (hc : count = d + 1) (hd : 1 ≤ d) :
    ∀ (modes : List (Option E2)) (n : ℕ) (claim : E2), modes.length = n →
      FolP cap shp idx (sumcheckE2 g claim count modes) (atomsOf p (sumcheckE2I n d)) fun r ↦ r.1.length = n
  | [], _, _, rfl => FolP.ret rfl
  | e :: es, _, claim, rfl => by
    rw [List.length_cons, atomsOf_sumcheckE2I_succ, sumcheckE2]
    exact (folP_roundPolyE2 hc hd claim e).bind fun _ _ ↦ (folP_e2Sample g).bind fun _ _ ↦
      (folP_sumcheckE2 g hc hd es _ _ rfl).bind_ret fun r hr ↦ by rw [List.length_cons, hr]

/-- **The equality-mode rounds at `E2`** against `sumcheckE2I · 2`. -/
theorem folP_packRoundsE2 (g : ℕ) : ∀ (rs : List E2) (value scale : E2),
    FolP cap shp idx (packRoundsE2 g rs value scale) (atomsOf p (sumcheckE2I rs.length 2))
      fun r ↦ r.2.2.length = rs.length
  | [], _, _ => FolP.ret rfl
  | r :: rs, value, scale => by
    rw [List.length_cons, atomsOf_sumcheckE2I_succ, packRoundsE2]
    exact (folP_roundPolyE2 rfl (by norm_num) value (some r)).bind fun _ _ ↦ (folP_e2Sample g).bind fun _ _ ↦
      (folP_packRoundsE2 g rs _ _).bind_ret fun x hx ↦ by rw [List.length_cons, hx]

end Prim

/-! ## The Keccak GKR at `E2` -/

section Keccak

variable {cap : ℕ → ℕ → ℕ} {shp : ℕ → ℕ × ℕ} {idx : Ref → ℕ} (p : Params)

/-- **A Keccak layer at `E2`** against `keccakLayerE2I`. -/
theorem folP_verifyKeccakLayerE2 (sh : KeccakGkr.Shape) (logSteps step : ℕ) (claim : KClaim E2) :
    FolP cap shp idx (verifyKeccakLayerE2 sh logSteps step claim)
      (atomsOf p (keccakLayerE2I claim.point.length)) fun c ↦ c.point.length = claim.point.length := by
  simp only [keccakLayerE2I, List.flatten_cons, List.flatten_nil, List.append_nil, atomsOf_append,
    atomsOf_rdE2, atomsOf_sepI, atomsOf_gsmp]
  unfold verifyKeccakLayerE2
  exact (folP_e2Reads _).bind fun _ _ ↦ (folP_require _).bind fun _ _ ↦ folP_e2Sep.bind fun _ _ ↦
    (folP_e2Sample _).bind fun _ _ ↦ (folP_packRoundsE2 p _ claim.point _ _).bind fun x hx ↦
    (folP_sumcheckE2 p _ rfl (by norm_num) _ localBits _ (List.length_replicate ..)).bind fun _ _ ↦
    (folP_e2Reads 3).bind fun _ _ ↦ (folP_require _).bind fun _ _ ↦
    (folP_e2Sample _).bind_ret fun _ _ ↦ hx

theorem folP_keccakLayersE2 (sh : KeccakGkr.Shape) (logSteps : ℕ) :
    ∀ (steps : List ℕ) (claim : KClaim E2),
    FolP cap shp idx (keccakLayersE2 sh logSteps steps claim)
      (List.replicate steps.length (atomsOf p (keccakLayerE2I claim.point.length))).flatten
      fun c ↦ c.point.length = claim.point.length
  | [], _ => FolP.ret rfl
  | st :: steps, claim => by
    rw [List.length_cons, List.replicate_succ, List.flatten_cons, keccakLayersE2]
    exact (folP_verifyKeccakLayerE2 p sh logSteps st claim).bind fun c hc ↦ by
      rw [← hc]
      exact folP_keccakLayersE2 sh logSteps steps c

/-- **The tape's GKR at `E2`** against `tapeLayersE2I`, the instance point of `h` coordinates. -/
theorem folP_tapeGkrE2 (h : ℕ) (inst output : List E2) (hinst : inst.length = h) :
    FolP cap shp idx (tapeGkrE2 h inst output) (atomsOf p (tapeLayersE2I h)) fun _ ↦ True := by
  rw [tapeLayersE2I, atomsOf_append, atomsOf_gsmpN, atomsOf_flatten, List.map_replicate]
  unfold tapeGkrE2
  refine (folP_e2Samples _ _).bind fun lp _ ↦ ?_
  have hpt : (firstClaimSF KeccakGkr.Shape.tape inst [] lp output 0).point.length = h - packBits := by
    simp only [firstClaimSF, List.length_append, List.length_drop, hinst, List.length_nil, Nat.add_zero]; rfl
  rw [← hpt, show tapeDepth = (List.range 24).length by simp; rfl]
  exact (folP_keccakLayersE2 p _ _ _ _).mono fun _ _ ↦ trivial

theorem folP_keccakOpenE2 (logSteps : ℕ) (claim : KClaim E2) (first count : ℕ) (value : E2) :
    FolP cap shp idx (keccakOpenE2 logSteps claim first count value) (atomsOf p (sumcheckE2I slotLog 2))
      fun _ ↦ True := by
  unfold keccakOpenE2
  exact (folP_sumcheckE2 p _ rfl (by norm_num) _ slotLog _ (by simp; decide)).bind_ret fun _ _ ↦ trivial

/-- The committed output's opening (`verifyKeccakE2`'s second segment). -/
theorem folP_keccakOutE2 (logSteps : ℕ) (claim : KClaim E2) (first count : ℕ) (committed : E2)
    (f : List E2 × List E2 × E2 → E2 → List ColClaimE2) :
    FolP cap shp idx (keccakOpenE2 logSteps claim first count committed >>= fun o ↦
      e2Read >>= fun word ↦ VerifierProgram.require (o.2.1.headD 0 * word = o.2.2) >>= fun _ ↦ pure (f o word))
      (atomsOf p (sumcheckE2I slotLog 2) ++ [.rdw e2Bytes]) fun _ ↦ True :=
  (folP_keccakOpenE2 p _ _ _ _ _).bind fun _ _ ↦ folP_e2Read.bind_nil fun _ _ ↦
    (folP_require _).bind_ret fun _ _ ↦ trivial

/-- **`verify_keccak` at `E2`** against `keccakE2I`, the instance point of `logSteps` coordinates. -/
theorem folP_verifyKeccakE2 (logSteps : ℕ) (inst output : List E2) (hinst : inst.length = logSteps) :
    FolP cap shp idx (verifyKeccakE2 logSteps inst output) (atomsOf p (keccakE2I logSteps)) fun _ ↦ True := by
  have hseg : 1 < keccakSegments := by decide
  have e : atomsOf p (keccakE2I logSteps) =
      (List.replicate segmentBits [Atom.rdw nonceBytes, .sm]).flatten ++
        ((List.replicate laneBits [Atom.rdw nonceBytes, .sm]).flatten ++ ([.rdw e2Bytes] ++
        ((List.replicate gkrDepth (atomsOf p (keccakLayerE2I (logSteps - packBits + segmentBits)))).flatten ++
        ((atomsOf p (sumcheckE2I slotLog 2) ++ [.rdw e2Bytes]) ++
        (atomsOf p (sumcheckE2I packBits 2) ++ (atomsOf p (sumcheckE2I slotLog 2) ++
          List.replicate kBits (.rdw e2Bytes))))))) := by
    simp only [keccakE2I, List.flatten_cons, List.flatten_nil, List.append_nil, atomsOf_append, gsmpN_add,
      atomsOf_gsmpN, atomsOf_rdE2, atomsOf_replicate, List.append_assoc]
    rfl
  rw [e]
  unfold verifyKeccakE2
  simp only [hseg, ↓reduceIte]
  refine (folP_e2Samples _ _).bind fun seg hseg' ↦ (folP_e2Samples _ _).bind fun lp _ ↦
    folP_e2Read.bind fun cm _ ↦ ?_
  have hpt : (firstClaimSF KeccakGkr.Shape.v1 inst seg lp output cm).point.length =
      logSteps - packBits + segmentBits := by
    simp only [firstClaimSF, List.length_append, List.length_drop, hinst, hseg']; rfl
  rw [← hpt, show gkrDepth = (List.range keccakDepth).length by simp; rfl]
  exact (folP_keccakLayersE2 p _ _ _ _).bind fun _ _ ↦ (folP_keccakOutE2 p _ _ _ _ _ _).bind fun _ _ ↦
    (folP_sumcheckE2 p _ rfl (by norm_num) _ packBits _ (List.length_replicate ..)).bind fun _ _ ↦
    (folP_keccakOpenE2 p _ _ _ _ _).bind fun _ _ ↦ (folP_e2Reads _).bind_nil fun _ _ ↦
    (folP_require _).bind_ret fun _ _ ↦ trivial

end Keccak

/-! ## The tape caller, the `KS` caller and link, the front -/

section Front

variable {cap : ℕ → ℕ → ℕ} {shp : ℕ → ℕ × ℕ} {idx : Ref → ℕ} (p : Params)

/-- **`D`'s slot reduction at `E2`** (two lane bits) against its items. -/
theorem folP_slotProgE2 (sb blk : ℕ) (W : ℕ → ℕ → E2) (pt : List E2) (v : E2) :
    FolP cap shp idx (slotProgE2 2 sb blk W pt v)
      (atomsOf p (List.flatten [sumcheckE2I 2 2, rdE2 kBits, smp rowSwitchStages])) fun _ ↦ True := by
  simp only [List.flatten_cons, List.flatten_nil, List.append_nil, atomsOf_append, atomsOf_smp, atomsOf_rdE2]
  unfold slotProgE2
  exact (folP_sumcheckE2 p _ rfl (by norm_num) _ 2 _ (List.length_replicate ..)).bind fun _ _ ↦
    (folP_e2Reads 64).bind fun _ _ ↦ (folP_require _).bind fun _ _ ↦
    (folP_rowSwitch _ _).bind_ret fun _ _ ↦ trivial

/-- **The chain wiring at `E2`** against `w` wiring rounds, `g_D`, the slot reduction's items. -/
theorem folP_wireChProgE2 (w sb dsel : ℕ) (s : RecursionFast.Digest) (n : ℕ) (claim : KClaim E2) :
    FolP cap shp idx (wireChProgE2 w sb dsel s n claim)
      (atomsOf p (List.flatten [sumcheckE2I w 2, rdE2 1, sumcheckE2I 2 2, rdE2 kBits, smp rowSwitchStages]))
      fun _ ↦ True := by
  have e : atomsOf p (List.flatten [sumcheckE2I w 2, rdE2 1, sumcheckE2I 2 2, rdE2 kBits, smp rowSwitchStages]) =
      atomsOf p (sumcheckE2I w 2) ++ (List.replicate 1 (.rdw e2Bytes) ++
        atomsOf p (List.flatten [sumcheckE2I 2 2, rdE2 kBits, smp rowSwitchStages])) := by
    simp only [List.flatten_cons, List.flatten_nil, List.append_nil, atomsOf_append, atomsOf_rdE2]
  rw [e]
  unfold wireChProgE2
  exact (folP_sumcheckE2 p _ rfl (by norm_num) _ w _ (List.length_replicate ..)).bind fun _ _ ↦
    (folP_e2Reads 1).bind fun _ _ ↦ (folP_require _).bind fun _ _ ↦
    (folP_slotProgE2 p _ _ _ _ _).bind_ret fun _ _ ↦ trivial

/-- **The tape caller at `E2`** (S2GF's `CHtape`, `CHwire`) against the tape's and the wire's items. -/
theorem folP_tapeProgE2 (w sb dsel : ℕ) (s : RecursionFast.Digest) (n : ℕ) :
    FolP cap shp idx (tapeProgE2 w sb dsel s n)
      (atomsOf p (List.flatten [sepI, gsmpN w, rdE2 lanes, tapeLayersE2I w]) ++
        atomsOf p (List.flatten [sumcheckE2I w 2, rdE2 1, sumcheckE2I 2 2, rdE2 kBits, smp rowSwitchStages]))
      fun _ ↦ True := by
  have e : atomsOf p (List.flatten [sepI, gsmpN w, rdE2 lanes, tapeLayersE2I w]) ++
        atomsOf p (List.flatten [sumcheckE2I w 2, rdE2 1, sumcheckE2I 2 2, rdE2 kBits, smp rowSwitchStages]) =
      [.sm] ++ ((List.replicate w [Atom.rdw nonceBytes, .sm]).flatten ++ (List.replicate lanes (.rdw e2Bytes) ++
        (atomsOf p (tapeLayersE2I w) ++
        atomsOf p (List.flatten [sumcheckE2I w 2, rdE2 1, sumcheckE2I 2 2, rdE2 kBits, smp rowSwitchStages])))) := by
    simp only [List.flatten_cons, List.flatten_nil, List.append_nil, atomsOf_append, atomsOf_rdE2,
      atomsOf_sepI, atomsOf_gsmpN, List.append_assoc]
  rw [e]
  unfold tapeProgE2
  exact folP_e2Sep.bind fun _ _ ↦ (folP_e2Samples _ w).bind fun r hr ↦ (folP_e2Reads 25).bind fun v _ ↦
    (folP_tapeGkrE2 p w r v hr).bind fun _ _ ↦ (folP_require _).bind fun _ _ ↦
    (folP_wireChProgE2 p _ _ _ _ _ _).bind_ret fun _ _ ↦ trivial

/-- **The `KS` caller at `E2`** against `KS`'s items: `h` ground coordinates, 25 scalars, `verify_keccak`, the
row switch. -/
theorem folP_callerProgE2 (h : ℕ) :
    FolP cap shp idx (callerProgE2 h)
      (atomsOf p (List.flatten [gsmpN h, rdE2 lanes, keccakE2I h, smp rowSwitchStages])) fun _ ↦ True := by
  simp only [List.flatten_cons, List.flatten_nil, List.append_nil, atomsOf_append, atomsOf_smp, atomsOf_rdE2,
    atomsOf_gsmpN]
  unfold callerProgE2
  exact (folP_e2Samples _ h).bind fun r hr ↦ (folP_e2Reads 25).bind fun v _ ↦
    (folP_verifyKeccakE2 p h r v hr).bind fun _ _ ↦ (folP_rowSwitch _ _).bind_ret fun _ _ ↦ trivial

/-- **The `KS` link at `E2`** against its items. -/
theorem folP_ksLinkProgE2 (hk xl : ℕ) (rows : List ℕ) :
    FolP cap shp idx (ksLinkProgE2 hk xl rows)
      (atomsOf p (List.flatten [gsmpN (hk + laneBits), sumcheckE2I hk 2, rdE2 4])) fun _ ↦ True := by
  simp only [List.flatten_cons, List.flatten_nil, List.append_nil, atomsOf_append, atomsOf_rdE2, atomsOf_gsmpN]
  unfold ksLinkProgE2
  exact (folP_e2Samples _ _).bind fun _ _ ↦
    (folP_sumcheckE2 p _ rfl (by norm_num) _ hk _ (List.length_replicate ..)).bind fun _ _ ↦
    (folP_e2Reads 4).bind_nil fun _ _ ↦ (folP_require _).bind_ret fun _ _ ↦ trivial

/-- **The `E2` front with continuation rows `rows`** against the tape, the wire, `KS` and the `KS` link at a
record with `logN = 20`, `ksLog = 13`. -/
theorem folP_kgProgFR (hN : p.logN = 20) (hK : p.ksLog = 13) (rows : List ℕ) (s : RecursionFast.Digest)
    (n : ℕ) :
    FolP cap shp idx (kgProgFR rows s n) (atomsOf p (tapeIF p ++ (wireIF p ++ (ksIF p ++ ksLinkIF p))))
      fun _ ↦ True := by
  have e : atomsOf p (tapeIF p ++ (wireIF p ++ (ksIF p ++ ksLinkIF p))) =
      (atomsOf p (tapeIF p) ++ atomsOf p (wireIF p)) ++ (atomsOf p (ksIF p) ++ atomsOf p (ksLinkIF p)) := by
    simp only [atomsOf_append, List.append_assoc]
  rw [e, tapeIF, wireIF, ksIF, ksLinkIF, hN, hK]
  unfold kgProgFR
  exact (folP_tapeProgE2 p 20 1 0 s n).bind fun _ _ ↦ (folP_callerProgE2 p (9 + 4)).bind fun _ _ ↦
    (folP_ksLinkProgE2 p (9 + 4) 9 rows).bind_ret fun _ _ ↦ trivial

/-- **The `E2` front follows S2GF's front items** (`kgProgF`, at `P20F.withF accVF`). -/
theorem folP_kgProgF (s : RecursionFast.Digest) (n : ℕ) :
    FolP cap shp idx (kgProgF s n)
      (atomsOf (P20F.withF accVF) (tapeIF (P20F.withF accVF) ++ (wireIF (P20F.withF accVF) ++
        (ksIF (P20F.withF accVF) ++ ksLinkIF (P20F.withF accVF))))) fun _ ↦ True :=
  folP_kgProgFR _ rfl rfl contRowsF s n

end Front

end Lvm.VEq
