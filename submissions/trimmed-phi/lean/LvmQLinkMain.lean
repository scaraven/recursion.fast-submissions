-- New for lvm (WP-11b-QL): Q_link end to end — its static checks as one Boolean, replay from Q_link's
-- rows, the bridge to WP-8's sponge hypotheses, and the instances at P20 and P8.
import LvmQLinkSigma
import LvmQBuildWf
import LvmReplay
import LvmSpongeTable
import LvmPlanP20

-- (GOLF2: 13 declarations that `certified` does not use moved verbatim to `LvmE2QNodeFOff`, outside its import closure.)

/-!
# Q_link end to end

* `qOk_of`: Q_link's static conditions `QOk` from one decidable Boolean `qOkB` (the bounds of the
  QLT entries are proved, not checked).
* **`qlink_replay`**: where Q_link's rows and assertions hold (any memory: the committed one by
  `loopir_sound`, or the interpreter's), with its inputs in place, `V_S` on the proof the stream's
  trace reassembles runs exactly that trace and returns `V_S`'s decision `F` on the hashed bytes `Σ`
  of the stream; and the padding of `Σ`'s last sponge block is pinned.
  `qlink_interp_replay`: the same from `interp (Q_link) = ok` (BLUEPRINT §4.6's `replay`).
* **`padOk_KS`, `streamOf_KS`**: WP-8's `traceDigest_of_KS` hypotheses `PadOk (msgBytes msg) L` and
  `streamOf (msgBytes msg) L = tagTrace :: traceBytes tr`, for `KS` message lanes holding the stream
  (`msg i l` = lane `17 i + l`).
* At `P20`/`P8`: the layouts `lay20`/`lay8`, `StreamOk`, `QOk` and the program check (`segsOk`, hence
  `wf`) decided; `ksLog = recRowsLog + 1` at `P8`, `ksLog = recRowsLog` at `P20` (KS14).
-/

set_option autoImplicit false

namespace Lvm.QLink

open RecursionFast Lvm Lvm.Replay Lvm.Loop Lvm.Loop.Build

/-! ## The static conditions as one Boolean -/

/-- Q_link's static conditions, decidable (the QLT bounds follow from `StreamOk`). -/
def qOkB (p : Params) (lay : Layout) : Bool :=
  decide ((qltEntries p lay).length ≤ 2 ^ lay.aQ) && decide (hashedLen p / 8 + 17 ≤ 2 ^ lay.m) &&
    decide (17 * nBlk (hashedLen p) + 4 ≤ 2 ^ lay.m) && decide (hashedLen p < 2 ^ 64) &&
    ((opens p).all fun o => decide (1 ≤ o.L.path) && decide (o.L.path < o.L.height) &&
      (pchunks o.L.t).all (fun c => decide (c.2 ≤ lay.K)) &&
      decide (eLane p o.ce + 1 + o.co / 8 + 4 * 2 ^ (o.L.height - o.L.path) ≤ 2 ^ lay.m) &&
      decide (o.L.row < 2 ^ 64)) &&
    decide (((opens p).map fun o => o.L.t).sum ≤ 2 ^ lay.pa)

theorem lane1C_lt : lane1C < 2 ^ 64 := lt_of_lt_of_le (ofLE_lt _) (by simp [q0Bytes])

theorem padLane_lt (L q : Nat) : padLane L q < 2 ^ 64 := lt_of_lt_of_le (ofLE_lt _) (by simp)

section
variable {p : Params} {lay : Layout}

theorem hashedLen_mod (hS : StreamOk p) : hashedLen p % 8 = 0 := by
  have := bOff_mod hS.1 (plan p).length (by have := plan_length_ge p; (clear * - p this; omega)) le_rfl
  rw [bOff_end, ← hS.2] at this; exact this

/-- **The QLT entries' bounds**, from the plan's stream facts. -/
theorem qbound_of (hS : StreamOk p) (hT2 : 17 * nBlk (hashedLen p) + 4 ≤ 2 ^ lay.m) (h64 : hashedLen p < 2 ^ 64) :
    ∀ e ∈ qltEntries p lay, lay.sb ≤ e.1 ∧ lay.sb ≤ e.2.1 ∧ e.1 + 5 ≤ lay.sb + 2 ^ lay.m ∧
      e.2.1 + 4 ≤ lay.sb + 2 ^ lay.m ∧ e.2.2 < 2 ^ 64 := by
  have hL8 := hashedLen_mod hS
  have hL48 := hashedLen_ge hS
  have hLb : hashedLen p / 8 + 5 ≤ 2 ^ lay.m := by simp only [nBlk] at hT2; (clear * - p lay hT2 hL8; omega)
  intro e he
  simp only [qltEntries, List.mem_append] at he
  rcases he with (h01 | hmid) | hpad
  · simp only [List.mem_cons, List.mem_nil_iff, or_false] at h01
    rcases h01 with rfl | rfl <;> dsimp only
    · exact ⟨le_rfl, by (clear * - lay p; omega), by (clear * - lay p h64 hL8 hL48 hLb; omega), by (clear * - lay p h64 hL8 hL48 hLb; omega), by simp [lane0C]⟩
    · exact ⟨by (clear * - lay p; omega), by (clear * - lay p; omega), by (clear * - lay p h64 hL8 hL48 hLb; omega), by (clear * - lay p h64 hL8 hL48 hLb; omega), lane1C_lt⟩
  · obtain ⟨⟨pe, i⟩, hx, hf⟩ := List.mem_filterMap.mp hmid
    have hgi := List.mem_zipIdx_iff_getElem?.mp hx
    simp only at hgi hf
    have hi : i < (plan p).length := by
      by_contra hc; rw [List.getElem?_eq_none (by (clear * - p i lay hc; omega))] at hgi; cases hgi
    have hpe : (plan p).getD i default = pe := by
      rw [List.getD_eq_getElem?_getD, hgi, Option.getD_some]
    split at hf
    · next st hk =>
      cases hf
      have hok := streamOk_entry hS.1 hi
      rw [hpe] at hok
      simp only [entryOk, hk, Bool.and_eq_true, decide_eq_true_eq] at hok
      obtain ⟨⟨h32, hst⟩, h1⟩ := hok
      have hin := lanes_in hS h1 hi
      rw [hpe] at hin
      have h8 := streamOk_len hS.1 h1 hi
      rw [hpe] at h8
      have hans : ansLane p st + 4 ≤ hashedLen p / 8 := by
        by_cases h0 : st = 0
        · subst h0; simp only [ansLane, ite_true]; (clear * - p lay h64 hL8 hL48 pe i; omega)
        · have := lanes_in hS (i := st) (by (clear * - st p lay pe i h0; omega)) (by (clear * - st p lay pe i hi hst; omega))
          simp only [ansLane, h0, ite_false]; (clear * - p st lay pe i this; omega)
      dsimp only
      exact ⟨by (clear * - lay p i pe st; omega), by (clear * - lay p st pe i; omega), by (clear * - lay p i hLb pe st h32 hin h8; omega), by (clear * - lay p st hLb pe i hans; omega), by (clear * - pe p lay h64 hL8 hL48 i st hin h8; omega)⟩
    · cases hf
  · obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hpad
    rw [List.mem_range] at hk
    simp only [nBlk] at hT2 hk ⊢
    exact ⟨by (clear * - lay p k h64 hL8 hL48; omega), by (clear * - lay p k h64 hL8 hL48; omega), by (clear * - lay p k hT2 hL8 hk; omega), by (clear * - lay p k hT2 hL8 hk; omega), padLane_lt _ _⟩

theorem qOk_of (hS : StreamOk p) (h : qOkB p lay = true) : QOk p lay := by
  simp only [qOkB, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at h
  obtain ⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩ := h
  refine ⟨h1, qbound_of hS h3 h4, h2, fun o ho => ?_, h6⟩
  obtain ⟨⟨⟨⟨a1, a2⟩, a3⟩, a4⟩, a5⟩ := h5 o ho
  exact ⟨a1, a2, a3, a4, a5⟩

end

/-! ## Replay from Q_link's rows -/

-- `sigma` (`Σ`, the hashed bytes of the stream) is in `LvmQLinkSigma` (lvm2 roll 8: off the B program's build path).

theorem traceBytesB_decode {p : Params} {ws : List Word} (hS : StreamOk p) (hL : LaneLink p ws) :
    traceBytesB (decode p ws) = sigma p ws := by
  apply ba_ext
  rw [sigma, bl_mk, stream_of_laneLink hS hL]
  exact traceBytesB_data _

theorem ctxOf_cells (Q : Program) : (ctxOf Q).cells = Q.cells := rfl

section
variable {p : Params} {lay : Layout} {ws : List Word} {c : Ctx} {M : Mem}

end

/-! ## WP-8's sponge hypotheses (`traceDigest_of_KS`) -/

section
variable {ws : List Word} {msg : ℕ → ℕ → LeanVM.Parameters.K}

end

/-! ## The instances at `P20` and `P8` -/

/-- WP-16b: from the plan's one-pass decision (`LvmPlanP20`) and `sizes_P20`'s hashed length. -/
theorem streamOk_P20 : StreamOk P20 :=
  ⟨Lvm.PlanChk.streamOkL_P20, by rw [sizes_P20.2.2.2.2.2.1, Lvm.PlanChk.slen_P20]⟩

-- (lvm2 GOLF: `streamOk_P8`, `qOk_P20`/`qOk_P8`, `segsOk_P20`/`segsOk_P8` and the replays `qlink20_replay`/
-- `qlink8_replay` moved to `LvmQLinkMainP`, outside `Solution`'s import closure: nothing in it uses them, and their
-- kernel decisions cost ≈ 49 s of the certificate's build.)

end Lvm.QLink
