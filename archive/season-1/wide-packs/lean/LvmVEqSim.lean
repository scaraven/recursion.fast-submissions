-- New for lvm (WP-14a): the query correspondence: V_S's driver, the compiled verifier's run and the
-- program read off the stream move in lockstep over the schedule's atoms. lvm2 E2F (E2F-V2): with read widths
-- (`rdw w` atoms, `ivpW`, `runKW`; roll 11's 24-byte reads are the instance `rw = 24`).
import LvmVEqStream
import LvmReplayBase

-- ===== merged from `LvmVEqSimOpen` (GOLF module merge: `LvmVEqSimOpen.lean` is now a stub importing `LvmVEqSim`) =====
section
-- New for lvm (WP-14a): the query correspondence for an opening: V_S's driver (`openLoop`,
-- `climb`) and the compiled verifier (`openAll`, `openOne`, `climb`) ask the same leaf and node
-- queries on the same trace, and the rows the compiled verifier returns are the ones the program on
-- the stream reads (`opRows`).

/-!
# Openings: the driver and the compiled verifier in lockstep

`climb_sim`: a Merkle climb of `j` levels: the same node queries (`cur ‖ sib` iff the position's bit
is `0`), the body cursor `32·j` further, the stream cursor `104·j` further. `openAll_sim`: the
openings of a list of positions of one commitment (leaf query = the row's occupied words, the
climb, the cap compare), with the compiled verifier's rows (`padRow`) = the rows on the stream at
the leaf entries (`padAt`).
-/

set_option autoImplicit false

namespace Lvm.VEq

open RecursionFast Lvm Lvm.FS LeanVM.Parameters LeanVM.Protocol.Compile

/-! ## Bytes -/

theorem toQ_eq {l : List UInt8} {b : ByteArray} (h : blb b = l) : toQ l = b := by
  rw [← h]; exact toQ_qb b

theorem blb_extract (b : ByteArray) (i j : ℕ) : blb (b.extract i j) = ((blb b).drop i).take (j - i) :=
  Lvm.Replay.bl_extract b i j

theorem blb_digestBytes (d : Digest) : blb (digestBytes d) = d.toList := Lvm.Replay.bl_digestBytes d

theorem blb_append (a b : ByteArray) : blb (a ++ b) = blb a ++ blb b := Lvm.Replay.bl_append a b

theorem length_blb (b : ByteArray) : (blb b).length = b.size := by
  simp only [blb, Array.length_toList]; rfl

theorem size_extract_of {b : ByteArray} {i n : ℕ} (h : i + n ≤ b.size) : (b.extract i (i + n)).size = n := by
  rw [← length_blb, blb_extract]; simp [length_blb]; (clear * - n b i h; omega)

theorem size_digestBytes (d : Digest) : (digestBytes d).size = 32 := by
  rw [← length_blb, blb_digestBytes]; simp

theorem take_drop_blb {b : ByteArray} {o n : ℕ} (h : o + n ≤ b.size) :
    (((blb b).drop o).take n).length = n := by simp [length_blb]; omega

theorem opRows_succ (sig : ByteArray) (wd oc path n e : ℕ) :
    opRows sig wd oc path (n + 1) e =
      (padAt sig (e + 8) wd oc :: (opRows sig wd oc path n (e + 40 + 8 * min oc wd + 104 * path)).1,
        (opRows sig wd oc path n (e + 40 + 8 * min oc wd + 104 * path)).2) := rfl

/-! ## Climbing -/

section Climb

variable (π : ByteArray) (tr : Trace) (q : ℕ)

/-- **A Merkle climb in lockstep.** -/
theorem climb_sim : ∀ (j lvl : ℕ) (cur : Digest) (s : DSt) (i : ℕ) (kc : DSt → Digest → OProg Bool),
    (∀ s' d n, (kc s' d).runSeq (tr.drop n) = some true → s'.off ≤ π.size) →
    (climb π q j lvl cur s kc).runSeq (tr.drop i) = some true →
    ∃ s' top n, (kc s' top).runSeq (tr.drop (i + n)) = some true ∧ s'.off = s.off + nodeBytes * j ∧
      s'.st = s.st ∧ s'.pend = s.pend ∧ s'.caps = s.caps ∧ s'.pos = s.pos ∧
      entOff tr (i + n) = entOff tr i + 104 * j ∧
      ∀ K : Option (Digest × List UInt8) → OProg Bool,
      ((Scheme.climb j cur (q >>> lvl) ((blb π).drop s.off)).bind K).runSeq (tr.drop i) =
        (K (some (top, (blb π).drop s'.off))).runSeq (tr.drop (i + n))
  | 0, lvl, cur, s, i, kc, _, h => ⟨s, cur, 0, h, by simp, rfl, rfl, rfl, rfl, by simp, fun K ↦ by
      simp [Scheme.climb, OProg.bind]⟩
  | j + 1, lvl, cur, s, i, kc, hb, h => by
    rw [climb] at h
    obtain ⟨a, rest, hdrop, h'⟩ := ask_run h
    -- the bound: the climb goes on to the end
    obtain ⟨s₂, d₂, n₂, h₂, -, ho₂, -⟩ := climb_run π q j (lvl + 1) a _ kc rest h'
    have hle : s.off + nodeBytes * (j + 1) ≤ π.size := by
      have := hb s₂ d₂ (i + 1 + n₂) (by rw [← List.drop_drop, ← List.drop_drop, hdrop]; exact h₂)
      rw [ho₂] at this; simp only [nodeBytes] at this ⊢; ring_nf at this ⊢; (clear * - this; omega)
    have h32 : s.off + 32 ≤ π.size := by simp only [nodeBytes] at hle; (clear * - hle; omega)
    have hrest : tr.drop (i + 1) = rest := by rw [← List.drop_drop, hdrop]; rfl
    obtain ⟨s', top, n, h1, h2, h3, h4, h5, h6, h7, h8⟩ := climb_sim j (lvl + 1) a _ (i + 1) kc
      hb
      (by rw [hrest]; exact h')
    refine ⟨s', top, n + 1, by rw [show i + (n + 1) = i + 1 + n by (clear * -; first | decide | (simp only [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]; done) | ring1 | omega)]; exact h1, ?_, h3, h4, h5, h6, ?_, ?_⟩
    · rw [h2]; simp only [nodeBytes]; ring
    · -- the node entry is 104 bytes
      have hsz : (if (q >>> lvl) % 2 = 0 then digestBytes cur ++ π.extract s.off (s.off + 32)
          else π.extract s.off (s.off + 32) ++ digestBytes cur).size = 64 := by
        split <;> rw [ByteArray.size_append, size_extract_of h32, size_digestBytes]
      have he := (stream_entry hdrop).2.2
      rw [show i + (n + 1) = i + 1 + n by (clear * -; first | decide | (simp only [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]; done) | ring1 | omega), h7, he, hsz]; ring
    · -- the compiled climb asks the same node query
      intro K
      have hlen : ¬ ((blb π).drop s.off).length < 32 := by simp [length_blb]; (clear * - h32; omega)
      have hq : toQ (if (q >>> lvl) % 2 = 0 then cur.toList ++ ((blb π).drop s.off).take 32
          else ((blb π).drop s.off).take 32 ++ cur.toList) =
          (if (q >>> lvl) % 2 = 0 then digestBytes cur ++ π.extract s.off (s.off + 32)
            else π.extract s.off (s.off + 32) ++ digestBytes cur) := by
        apply toQ_eq
        split <;> simp [blb_append, blb_extract, blb_digestBytes]
      simp only [Scheme.climb, hlen, ↓reduceIte, OProg.bind, hq, hdrop, OProg.runSeq, ↓reduceIte]
      rw [show (q >>> lvl) / 2 = q >>> (lvl + 1) by rw [Nat.shiftRight_succ],
        show ((blb π).drop s.off).drop 32 = (blb π).drop (s.off + 32) by rw [List.drop_drop]]
      rw [← hrest, show i + (n + 1) = i + 1 + n by (clear * -; first | decide | (simp only [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]; done) | ring1 | omega)]
      exact h8 K

end Climb

/-! ## Opening -/

theorem oprog_bind_assoc {α β γ : Type} (p : OProg α) (f : α → OProg β) (g : β → OProg γ) :
    (p.bind f).bind g = p.bind fun a ↦ (f a).bind g := by
  induction p with
  | ret a => rfl
  | query q k ih => simp only [OProg.bind, ih]

theorem bind_query' {α β : Type} (q : ByteArray) (f : Digest → OProg α) (g : α → OProg β) :
    (OProg.query q f).bind g = .query q fun d ↦ (f d).bind g := rfl

theorem bind_ret' {α β : Type} (a : α) (g : α → OProg β) : (OProg.ret a).bind g = g a := rfl

theorem runSeq_query_eq {α : Type} (q : ByteArray) (f : Digest → OProg α) (a : Digest) (rest : Trace) :
    (OProg.query q f).runSeq ((q, a) :: rest) = (f a).runSeq rest := by simp [OProg.runSeq]

@[simp] theorem capI_wd (S : Scheme) (ht wd : ℕ) (b : List UInt8) : (S.capI ht wd b).wd = wd := rfl
@[simp] theorem capI_ht (S : Scheme) (ht wd : ℕ) (b : List UInt8) : (S.capI ht wd b).ht = ht := rfl
@[simp] theorem capI_lv (S : Scheme) (ht wd : ℕ) (b : List UInt8) : (S.capI ht wd b).lv = S.capOf ht wd := rfl

theorem get!_blb (b : ByteArray) (i : ℕ) : b.get! i = (blb b).getD i 0 := Lvm.Replay.get!_bl b i

/-- A cap node of a commitment record. -/
theorem cap_get (S : Scheme) (π : ByteArray) (ht wd capOff k : ℕ) (hk : k < 2 ^ S.capOf ht wd) :
    (S.capI ht wd ((blb π).drop capOff)).cap[k]? = some (digestAt π (capOff + nodeBytes * k)) := by
  simp only [Scheme.capI, digestsOf, Scheme.capBytes]
  rw [List.getElem?_map, List.getElem?_range hk, Option.map_some]
  refine congrArg some ?_
  apply Vector.ext
  intro t ht'
  simp only [dg, digestAt, Vector.getElem_ofFn, get!_blb, nodeBytes]
  rw [List.getD_eq_getElem?_getD, List.getElem?_drop, List.getElem?_take_of_lt (by
    have : k + 1 ≤ 2 ^ S.capOf ht wd := hk
    nlinarith), List.getElem?_drop, ← List.getD_eq_getElem?_getD]
  rw [show capOff + 32 * k + t = capOff + (32 * k + t) by ring]

section Open

variable (S : Scheme) (π : ByteArray) (tr : Trace)

/-- **An opening in lockstep**: the driver's `openLoop` (leaves of `L.row` bytes) and the compiled
`openAll` (leaves of the occupied words, `Scheme.lb`) ask the same queries, and the compiled rows are
the stream's (`opRows`). -/
theorem openAll_sim (hdecK : S.decK = kOfBytes) (L : Level) (capOff ht wd : ℕ)
    (hht : L.height = ht) (hrow : L.row = 8 * min (S.occ ht wd) wd) (hpath : L.path = ht - S.capOf ht wd)
    (hlv : S.capOf ht wd ≤ ht) :
    ∀ (ps : List ℕ) (s : DSt) (i : ℕ) (k'' : DSt → OProg Bool),
      (∀ q ∈ ps, q < 2 ^ ht) →
      (∀ s' n, (k'' s').runSeq (tr.drop n) = some true → s'.off ≤ π.size) →
      (openLoop π L capOff ps s k'').runSeq (tr.drop i) = some true →
      ∃ s' n, (k'' s').runSeq (tr.drop (i + n)) = some true ∧ s'.st = s.st ∧ s'.pend = s.pend ∧
        s'.caps = s.caps ∧ s'.pos = s.pos ∧ s.off ≤ s'.off ∧
        (opRows (traceBytesB tr) wd (S.occ ht wd) L.path ps.length (entOff tr i)).2 = entOff tr (i + n) ∧
        ∀ Kc : Option (List (List K) × List UInt8) → OProg Bool,
        ((S.openAll (S.capI ht wd ((blb π).drop capOff)) ps ((blb π).drop s.off)).bind Kc).runSeq
            (tr.drop i) =
          (Kc (some ((opRows (traceBytesB tr) wd (S.occ ht wd) L.path ps.length (entOff tr i)).1,
            (blb π).drop s'.off))).runSeq (tr.drop (i + n)) := by
  intro ps
  induction ps with
  | nil =>
    intro s i k'' _ _ h
    exact ⟨s, 0, h, rfl, rfl, rfl, rfl, le_rfl, rfl, fun Kc ↦ by simp [Scheme.openAll, OProg.bind, opRows]⟩
  | cons q qs ih =>
    intro s i k'' hps hk h
    obtain ⟨d₀, rest, hdrop, h'⟩ := ask_run h
    have hrest : tr.drop (i + 1) = rest := by rw [← List.drop_drop, hdrop]; rfl
    -- the climb's continuation reaches the next positions, whose run bounds the body
    have hkc : ∀ s' d n, ((fun s top ↦ if top == digestAt π (capOff + nodeBytes * (q >>> L.path)) then
        openLoop π L capOff qs s k'' else OProg.ret false) s' d).runSeq (tr.drop n) = some true →
        s'.off ≤ π.size := by
      intro s' d n hh
      simp only at hh
      split at hh
      · obtain ⟨s'', n', h1, -, h3, -⟩ := openLoop_run π L capOff qs s' k'' _ hh
        have := hk s'' (n + n') (by rw [← List.drop_drop]; exact h1)
        (clear * - h3 this; omega)
      · exact absurd (runSeq_ret_true hh).2 (by simp)
    obtain ⟨s₁, top, n₁, h1, ho1, hst1, hpe1, hca1, hpo1, he1, hc1⟩ :=
      climb_sim π tr q L.path 0 d₀ _ (i + 1) _
        hkc (by rw [hrest]; exact h')
    have hb1 := hkc _ _ _ h1
    simp only at ho1
    have hoff : s.off + L.row ≤ π.size := by rw [ho1] at hb1; (clear * - hrow hb1; omega)
    -- the cap check held
    split at h1
    · rename_i hcap
      have htop : top = digestAt π (capOff + nodeBytes * (q >>> L.path)) := by simpa using hcap
      obtain ⟨s', n, h2, hst, hpe, hca, hpo, hle, he2, hc2⟩ := ih s₁ (i + 1 + n₁) k'' (fun q' hq' ↦ hps q' (List.mem_cons_of_mem _ hq')) hk h1
      refine ⟨s', n₁ + 1 + n, by rw [show i + (n₁ + 1 + n) = i + 1 + n₁ + n by (clear * -; first | decide | (simp only [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]; done) | ring1 | omega)]; exact h2,
        by rw [hst, hst1], by rw [hpe, hpe1], by rw [hca, hca1], by rw [hpo, hpo1], ?_, ?_, ?_⟩
      · have : s₁.off ≤ s'.off := hle
        (clear * - hrow ho1 hle; omega)
      · have hsz : (π.extract s.off (s.off + L.row)).size = 8 * min (S.occ ht wd) wd := by rw [size_extract_of hoff, hrow]
        have he0 := (stream_entry hdrop).2.2
        rw [List.length_cons, opRows_succ]
        dsimp only
        rw [show i + (n₁ + 1 + n) = i + 1 + n₁ + n by (clear * -; first | decide | (simp only [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]; done) | ring1 | omega), ← he2, he1, he0, hsz]
        exact congrArg (fun e ↦ (opRows (traceBytesB tr) wd (S.occ ht wd) L.path qs.length e).2) (by ring)
      · intro Kc
        have hlen : ¬ ((blb π).drop s.off).length < 8 * min (S.occ ht wd) wd := by
          rw [List.length_drop, length_blb]; rw [hrow] at hoff; (clear * - hrow hoff; omega)
        have hq : toQ (((blb π).drop s.off).take (8 * min (S.occ ht wd) wd)) = π.extract s.off (s.off + L.row) := by
          apply toQ_eq; rw [blb_extract, hrow, show s.off + 8 * min (S.occ ht wd) wd - s.off = 8 * min (S.occ ht wd) wd by (clear * - hrow; omega)]
        have hq0 : q < 2 ^ ht := hps q List.mem_cons_self
        have hqmod : q % 2 ^ ht = q >>> 0 := by rw [Nat.mod_eq_of_lt hq0]; rfl
        have hcapk : (S.capI ht wd ((blb π).drop capOff)).cap[q % 2 ^ ht / 2 ^ (ht - S.capOf ht wd)]? =
            some top := by
          rw [Nat.mod_eq_of_lt hq0, cap_get, htop, Nat.shiftRight_eq_div_pow, hpath]
          rw [Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _), ← pow_add, Nat.add_comm,
            Nat.sub_add_cancel hlv]
          exact hq0
        have hrow0 : padRowOf S.decK wd (S.occ ht wd) (((blb π).drop s.off).take (8 * min (S.occ ht wd) wd)) =
            padAt (traceBytesB tr) (entOff tr i + 8) wd (S.occ ht wd) := by
          have hsz : (π.extract s.off (s.off + L.row)).size = 8 * min (S.occ ht wd) wd := by
            rw [size_extract_of hoff, hrow]
          have := (stream_entry hdrop).1 0 (8 * min (S.occ ht wd) wd) (by rw [hsz]; (clear * -; first | decide | (simp only [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]; done) | ring1 | (clear * - S ht wd; omega)))
          simp only [Nat.add_zero, List.drop_zero] at this
          rw [padAt, hdecK, this, blb_extract, hrow, show s.off + 8 * min (S.occ ht wd) wd - s.off = 8 * min (S.occ ht wd) wd by (clear * - hsz; omega),
            List.take_take, min_self]
        rw [hqmod, ← hpath] at hcapk
        have hdd : ((blb π).drop s.off).drop (8 * min (S.occ ht wd) wd) = (blb π).drop (s.off + L.row) := by
          rw [List.drop_drop, hrow]
        rw [Scheme.openAll, oprog_bind_assoc, Scheme.openOne,
          if_neg (show ¬ ((blb π).drop s.off).length < S.lb (S.capI ht wd ((blb π).drop capOff)) from hlen)]
        simp only [Scheme.lb, Scheme.padRow, capI_wd, capI_ht, capI_lv, bind_query', hq, hdrop, runSeq_query_eq,
          oprog_bind_assoc, hqmod, ← hpath, hdd]
        simp only at hc1
        rw [← hrest, hc1]
        simp only [bind_ret', hcapk, ↓reduceIte, hrow0]
        rw [oprog_bind_assoc, hc2, bind_ret', List.length_cons, opRows_succ,
          show i + (n₁ + 1 + n) = i + 1 + n₁ + n by (clear * -; first | decide | (simp only [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]; done) | ring1 | omega)]
        have hent : entOff tr (i + 1 + n₁) = entOff tr i + 40 + 8 * min (S.occ ht wd) wd + 104 * L.path := by
          rw [he1, (stream_entry hdrop).2.2, size_extract_of hoff, hrow]; ring
        rw [hent]
    · exact absurd (runSeq_ret_true h1).2 (by simp)

end Open

end Lvm.VEq
end
-- ===== end of `LvmVEqSimOpen` =====

/-!
# The simulation

For a program `P` that follows the atoms `as` (`Fol`), a run of V_S's driver over `as` that the
trace `tr` accepts, and the program read off `Σ = traceBytesB tr` (`ivpW`, the `n`-th read of
`S.rw n` bytes, which are the atoms' read widths) returning `a`: the compiled verifier's run of `P`
(`runKW`) asks the same queries on `tr`, reads the same values, and reaches its continuation with `a`, at
a state that again matches the driver's (`J`) — `simW`.

`J`: the compiled run's state is the driver's (`st`, the absorbed-but-unsqueezed bytes
`π[pend, off)`, the rest of the body `π[off..]`, the commitment records of the caps read at the
driver's cap offsets, `CapsJ`), and the stream cursor is at entry `i` with `off − pend` message
bytes read.
-/

set_option autoImplicit false

namespace Lvm.VEq

open RecursionFast Lvm Lvm.FS LeanVM.Parameters LeanVM.Protocol.Compile

section Sim

variable (S : Scheme) (π : ByteArray) (tr : Trace) (p : Params)

/-- The compiled verifier's commitment records against the driver's caps. -/
def CapsJ (caps : List CapI) (dcaps : List (Ref × ℕ)) (cr : List Ref) : Prop :=
  ∃ offs : List ℕ, offs.length = cr.length ∧ dcaps = (cr.zip offs).reverse ∧
    caps = (cr.zip offs).map (fun ro ↦ S.capI (shpS (idxS ro.1)).1 (shpS (idxS ro.1)).2
      ((blb π).drop ro.2)) ∧
    (∀ j (hj : j < cr.length), idxS cr[j] = j) ∧ cr.Nodup

/-- **The states match.** -/
structure J (s : DSt) (st : Digest) (buf : List UInt8) (caps : List CapI) (body : List UInt8)
    (rs : RS) (i : ℕ) (cr : List Ref) : Prop where
  st : st = s.st
  pend : s.pend ≤ s.off
  off : s.off ≤ π.size
  buf : buf = ((blb π).drop s.pend).take (s.off - s.pend)
  body : body = (blb π).drop s.off
  ent : rs.ent = entOff tr i
  msg : rs.msg = s.off - s.pend
  caps : CapsJ S π caps s.caps cr

/-- The pending positions are below `2^h` for a height `h` of the position samples. -/
def PosOK (pp hs : List ℕ) : Prop := ∀ q ∈ pp, ∃ h ∈ hs, q < 2 ^ h

variable {S π tr p}

/-- The body cursor bound from an accepting run. -/
theorem bound_of_drive {as : List Atom} {s : DSt} {k : DSt → OProg Bool} {i : ℕ}
    (hk : ∀ s' n, (k s').runSeq (tr.drop n) = some true → s'.off ≤ π.size)
    (h : (driveAtoms p π as s k).runSeq (tr.drop i) = some true) : s.off + pendA as ≤ π.size := by
  obtain ⟨s', n, h1, -, h3, -⟩ := drive_run p π as s k _ h
  have := hk s' (i + n) (by rw [← List.drop_drop]; exact h1)
  (clear * - h3 this; omega)

/-- After pending bytes, a Fiat–Shamir query comes. -/
theorem nextFS_of_stA {occ : ℕ → ℕ → ℕ} : ∀ (as : List Atom) (pend : ℕ) (cr : List Ref) (hs : List ℕ),
    stA p as pend cr hs occ = true → 0 < pend → NextFS as
  | [], pend, _, _, h, hp => by simp only [stA, beq_iff_eq] at h; omega
  | .rd :: as, pend, cr, hs, h, _ => nextFS_of_stA as _ cr hs h (by simp [eBytes])
  | .rdw _ :: as, _, cr, hs, h, hp => nextFS_of_stA as _ cr hs h (by omega)
  | .cap c r :: as, pend, cr, hs, h, _ => by
    simp only [stA, Bool.and_eq_true] at h
    exact nextFS_of_stA as _ _ hs h.2 (by simp only [nodeBytes]; positivity)
  | .sm :: _, _, _, _, _, _ => trivial
  | .pclr :: as, pend, cr, hs, h, hp => nextFS_of_stA as pend cr [] h hp
  | .ps _ _ :: _, _, _, _, _, _ => trivial
  | .op r :: as, pend, cr, hs, h, hp => by
    simp only [stA, Bool.and_eq_true, beq_iff_eq] at h; (clear * - r as p occ pend cr hs hp h; omega)

/-- **The message bytes on the stream**: under a lookahead entry `st ‖ π[pend, E)`, the message
bytes from `off` are `π`'s. -/
theorem msg_bytes {i : ℕ} {st : Digest} {pend off E n : ℕ} {a₀ : Digest} {rest : Trace}
    (hdrop : tr.drop i = (digestBytes st ++ π.extract pend E, a₀) :: rest) (hE : E ≤ π.size)
    (hpo : pend ≤ off) (hoE : off + n ≤ E) :
    sbs (traceBytesB tr) (entOff tr i + 40 + (off - pend)) n = ((blb π).drop off).take n := by
  have hsz : (digestBytes st ++ π.extract pend E).size = 32 + (E - pend) := by
    rw [ByteArray.size_append, size_digestBytes, ← length_blb, blb_extract]; simp [length_blb]; (clear * - hE; omega)
  have := (stream_entry hdrop).1 (32 + (off - pend)) n (by rw [hsz]; (clear * - hpo hoE; omega))
  rw [show entOff tr i + 40 + (off - pend) = entOff tr i + 8 + (32 + (off - pend)) by (clear * -; first | decide | (simp only [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]; done) | ring1 | omega), this,
    blb_append, blb_digestBytes, blb_extract, drop_app_len (show st.toList.length = 32 by simp),
    List.drop_take, List.drop_drop, show pend + (off - pend) = off by (clear * - hpo; omega), List.take_take]
  congr 1; (clear * - hpo hoE; omega)

end Sim

theorem find_unique {l : List (Ref × ℕ)} {r : Ref} {o : ℕ} (hmem : (r, o) ∈ l)
    (hu : ∀ x ∈ l, x.1 = r → x.2 = o) : (l.find? (·.1 == r)).map (·.2) = some o := by
  induction l with
  | nil => simp at hmem
  | cons x l ih =>
    by_cases hx : x.1 = r
    · simp [List.find?_cons, hx, hu x List.mem_cons_self hx]
    · have hx' : (x.1 == r) = false := by simpa using hx
      rw [List.find?_cons, hx']
      rcases List.mem_cons.mp hmem with h | h
      · exact absurd (by rw [← h]) hx
      · exact ih h fun y hy ↦ hu y (List.mem_cons_of_mem _ hy)

/-- A committed oracle's cap: the driver finds its offset, the compiled verifier its record. -/
theorem capsJ_lookup {S : Scheme} {π : ByteArray} {caps : List CapI} {dcaps : List (Ref × ℕ)} {cr : List Ref} {r : Ref}
    (h : CapsJ S π caps dcaps cr) (hr : r ∈ cr) :
    ∃ capOff, (dcaps.find? (·.1 == r)).map (·.2) = some capOff ∧
      caps[idxS r]? = some (S.capI (shpS (idxS r)).1 (shpS (idxS r)).2 ((blb π).drop capOff)) := by
  obtain ⟨offs, hlen, hd, hc, hidx, hnd⟩ := h
  obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hr
  have hjo : j < offs.length := by (clear * - hlen hj; omega)
  refine ⟨offs[j], ?_, ?_⟩
  · rw [hd]
    apply find_unique
    · rw [List.mem_reverse]
      exact List.mem_iff_getElem.mpr ⟨j, by simp [hlen]; (clear * - hj; omega), by simp⟩
    · intro x hx hxr
      rw [List.mem_reverse] at hx
      obtain ⟨j', hj', hx'⟩ := List.mem_iff_getElem.mp hx
      simp only [List.length_zip, Nat.lt_min] at hj'
      rw [← hx'] at hxr ⊢
      simp only [List.getElem_zip] at hxr ⊢
      have := (List.Nodup.getElem_inj_iff hnd).mp hxr
      subst this; rfl
  · have hz : (cr.zip offs)[j]? = some (cr[j], offs[j]) := by
      rw [List.getElem?_eq_getElem (by simp; (clear * - hlen hj; omega))]; simp
    rw [hc, hidx j hj, List.getElem?_map, hz, Option.map_some, hidx j hj]

theorem buf_ext (l : List UInt8) {pend off : ℕ} (h : pend ≤ off) (n : ℕ) :
    (l.drop pend).take (off - pend) ++ (l.drop off).take n = (l.drop pend).take (off + n - pend) := by
  rw [show off + n - pend = (off - pend) + n by (clear * - off n pend h; omega), List.take_add, List.drop_drop,
    show pend + (off - pend) = off by (clear * - pend off h; omega)]

theorem capS_le (i : ℕ) : capS (shpS i).1 (shpS i).2 ≤ (shpS i).1 := by
  rcases i with _ | _ | _ | _ | _ | i <;> simp [capS, shpS]

section FS

variable {S : Scheme} {π : ByteArray} {tr : Trace}

theorem J.fsQ {s : DSt} {st : Digest} {buf : List UInt8} {caps : List CapI} {body : List UInt8}
    {rs : RS} {i : ℕ} {cr : List Ref} (hJ : J S π tr s st buf caps body rs i cr) :
    toQ (st.toList ++ buf) = digestBytes s.st ++ π.extract s.pend s.off ∧
      buf.length = s.off - s.pend := by
  have hpo := hJ.pend
  have hoff := hJ.off
  refine ⟨toQ_eq ?_, ?_⟩
  · rw [blb_append, blb_digestBytes, blb_extract, hJ.st, hJ.buf]
  · rw [hJ.buf]; simp [length_blb]; (clear * - hoff; omega)

/-- **A Fiat–Shamir query in lockstep**: the stream's answer, and the states after it. -/
theorem J.fs {s : DSt} {st : Digest} {buf : List UInt8} {caps : List CapI} {body : List UInt8}
    {rs : RS} {i : ℕ} {cr : List Ref} {a₀ : Digest} {rest : Trace}
    (hJ : J S π tr s st buf caps body rs i cr)
    (hdrop : tr.drop i = (digestBytes s.st ++ π.extract s.pend s.off, a₀) :: rest) :
    digestAt (traceBytesB tr) (rs.ent + 40 + rs.msg) = a₀ ∧ tr.drop (i + 1) = rest ∧
      ∀ s₁ : DSt, s₁.off = s.off → s₁.pend = s.off → s₁.st = a₀ → s₁.caps = s.caps →
        J S π tr s₁ a₀ [] caps body { rs with ent := rs.ent + 72 + rs.msg, msg := 0 } (i + 1) cr := by
  have hpo := hJ.pend
  have hoff := hJ.off
  have hsz : (digestBytes s.st ++ π.extract s.pend s.off).size = 32 + (s.off - s.pend) := by
    rw [ByteArray.size_append, size_digestBytes, ← length_blb, blb_extract]; simp [length_blb]; (clear * - hoff; omega)
  have he := stream_entry hdrop
  refine ⟨?_, by rw [← List.drop_drop, hdrop]; rfl, fun s₁ h1 h2 h3 h4 ↦ ?_⟩
  · rw [hJ.ent, hJ.msg, show entOff tr i + 40 + (s.off - s.pend) = entOff tr i + 8 + (32 + (s.off - s.pend)) by
      (clear * -; first | decide | (simp only [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]; done) | ring1 | omega), ← hsz]
    exact he.2.1
  · refine ⟨h3.symm, by (clear * - h1 h2; omega), by (clear * - hoff h1 h2; omega), by rw [h1, h2]; simp, by rw [h1]; exact hJ.body, ?_, ?_, ?_⟩
    · show rs.ent + 72 + rs.msg = _
      rw [he.2.2, hJ.ent, hJ.msg, hsz]; (clear * -; first | decide | (simp only [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]; done) | ring1 | omega)
    · show 0 = _; (clear * - h1 h2; omega)
    · rw [h4]; exact hJ.caps

end FS

section Main

variable {S : Scheme} {π : ByteArray} {tr : Trace} {p : Params}

theorem take_drop_append (l : List UInt8) (a m n : ℕ) (h : a + m + n ≤ l.length) :
    (l.drop a).take m ++ (l.drop (a + m)).take n = (l.drop a).take (m + n) := by
  rw [List.take_add, List.drop_drop]

/-- **The simulation** (read widths: the `n`-th read of the program takes `S.rw n` bytes, as the atoms' read
widths say, `WAt S.rw n (widthsA as)`; the scheme's occupied words `occ`, the static check's). -/
theorem simW (hdecE : S.decE = eOfBytes) (hchal : S.chal = chalOf) (hdecK : S.decK = kOfBytes)
    (hcap : S.capOf = capS) {occ : ℕ → ℕ → ℕ} (hocc : S.occ = occ) : ∀ (as : List Atom) {α : Type} (P : VerifierProgram α) (pp : List ℕ)
    (Q : α → List ℕ → Prop) (s : DSt) (st : Digest) (buf : List UInt8) (caps : List CapI)
    (body : List UInt8) (rs : RS) (i : ℕ) (cr : List Ref) (hs : List ℕ) (k : DSt → OProg Bool)
    (a : α) (rs' : RS) (ri ri' : ℕ),
    Fol capS shpS idxS P as pp Q → stA p as (s.off - s.pend) cr hs occ = true →
    J S π tr s st buf caps body rs i cr → s.pos = pp → PosOK pp hs →
    (∀ s' n, (k s').runSeq (tr.drop n) = some true → s'.off ≤ π.size) →
    (driveAtoms p π as s k).runSeq (tr.drop i) = some true → WAt S.rw ri (widthsA as) →
    ivpW capS occ shpS S.rw P (traceBytesB tr) rs ri = (some a, rs', ri') →
    ∃ s' st' buf' caps' body' i' cr', J S π tr s' st' buf' caps' body' rs' i' cr' ∧
      (k s').runSeq (tr.drop i') = some true ∧ Q a s'.pos ∧
      ∀ kS : α → Digest → List UInt8 → List CapI → List UInt8 → OProg Bool,
        (runKW S ri P st buf caps body kS).runSeq (tr.drop i) = (kS a st' buf' caps' body').runSeq (tr.drop i')
  | [], α, P, pp, Q, s, st, buf, caps, body, rs, i, cr, hs, k, a, rs', ri, ri', hF, hst, hJ, hpos, _, _, hd, _, hiv => by
    cases P with
    | ret b =>
      simp only [ivpW, Prod.mk.injEq, Option.some.injEq] at hiv
      obtain ⟨rfl, rfl, -⟩ := hiv
      exact ⟨s, st, buf, caps, body, i, cr, hJ, hd, hpos ▸ hF, fun kS ↦ rfl⟩
    | fail => simp [ivpW] at hiv
    | _ => exact absurd hF (by simp [Fol])
  | .rd :: as, α, P, pp, Q, s, st, buf, caps, body, rs, i, cr, hs, k, a, rs', ri, ri', hF, hst, hJ, hpos, hpk, hk, hd, hw, hiv => by
    cases P with
    | read k' =>
      obtain ⟨hw0, hw'⟩ := WAt.cons.mp hw
      have hF' : ∀ y, Fol capS shpS idxS (k' y) as pp Q := hF
      have hpo := hJ.pend
      have hst' : stA p as (s.off - s.pend + eBytes) cr hs occ = true := hst
      have hd' : (driveAtoms p π as { s with off := s.off + eBytes } k).runSeq (tr.drop i) = some true := hd
      have hb := bound_of_drive hk hd'
      simp only at hb
      have hnext : NextFS (Atom.rd :: as) :=
        nextFS_of_stA (p := p) as _ cr hs hst' (by simp [eBytes])
      obtain ⟨a₀, rest, hdrop⟩ := drive_next p π (Atom.rd :: as) s k _ hnext hd
      have hval : sbs (traceBytesB tr) (rs.ent + 40 + rs.msg) 24 = ((blb π).drop s.off).take 24 := by
        rw [hJ.ent, hJ.msg]
        exact msg_bytes hdrop (by simp only [pendA, eBytes] at hb ⊢; (clear * - s as π S ri hb; omega)) hpo
          (by simp only [pendA, eBytes]; (clear * - s as S π ri; omega))
      have hiv' : ivpW capS occ shpS S.rw (k' (eOfBytes (((blb π).drop s.off).take 24))) (traceBytesB tr)
          { rs with msg := rs.msg + 24 } (ri + 1) = (some a, rs', ri') := by
        simp only [ivpW, hw0, hval] at hiv; exact hiv
      have h24 : s.off + 24 ≤ π.size := by simp only [eBytes] at hb; (clear * - s π S as ri hb; omega)
      have hJ' : J S π tr { s with off := s.off + eBytes } st (buf ++ body.take 24) caps (body.drop 24)
          { rs with msg := rs.msg + 24 } i cr := by
        refine ⟨hJ.st, by simp only; (clear * - hpo; omega), by simp only [eBytes]; omega, ?_, ?_, hJ.ent, ?_, hJ.caps⟩
        · simp only [eBytes]
          rw [hJ.buf, hJ.body, buf_ext _ hpo]
        · simp only; rw [hJ.body, List.drop_drop]; simp [eBytes]
        · simp only [eBytes]; rw [hJ.msg]; (clear * - hpo; omega)
      obtain ⟨s', st', buf', caps', body', i', cr', h1, h2, h3, h4⟩ :=
        simW hdecE hchal hdecK hcap hocc as (k' _) pp Q _ st _ caps _ _ i cr hs k a rs' (ri + 1) ri' (hF' _)
          (by simp only; rw [show s.off + eBytes - s.pend = s.off - s.pend + eBytes by (clear * - s S π as ri hpo; omega)]; exact hst')
          hJ' hpos hpk hk hd' hw' hiv'
      refine ⟨s', st', buf', caps', body', i', cr', h1, h2, h3, fun kS ↦ ?_⟩
      have hlen : ¬ body.length < 24 := by rw [hJ.body, List.length_drop, length_blb]; (clear * - π s S as ri h24; omega)
      simp only [runKW, hw0, hlen, ↓reduceIte, hdecE]
      rw [hJ.body] at h4 ⊢
      exact h4 kS
    | fail => simp [ivpW] at hiv
    | _ => exact absurd hF (by simp [Fol])
  | .rdw w :: as, α, P, pp, Q, s, st, buf, caps, body, rs, i, cr, hs, k, a, rs', ri, ri', hF, hst, hJ, hpos, hpk, hk, hd, hw, hiv => by
    cases P with
    | read k' =>
      obtain ⟨hw0, hw'⟩ := WAt.cons.mp hw
      have hF' : ∀ y, Fol capS shpS idxS (k' y) as pp Q := hF
      have hpo := hJ.pend
      have hst' : stA p as (s.off - s.pend + w) cr hs occ = true := hst
      have hd' : (driveAtoms p π as { s with off := s.off + w } k).runSeq (tr.drop i) = some true := hd
      have hb := bound_of_drive hk hd'
      simp only at hb
      have hnext : NextFS (Atom.rdw w :: as) :=
        nextFS_of_stA (p := p) as _ cr hs hst' (by have := S.rw_pos ri; (clear * - s w S π as ri hw0 this; omega))
      obtain ⟨a₀, rest, hdrop⟩ := drive_next p π (Atom.rdw w :: as) s k _ hnext hd
      have hval : sbs (traceBytesB tr) (rs.ent + 40 + rs.msg) w = ((blb π).drop s.off).take w := by
        rw [hJ.ent, hJ.msg]
        exact msg_bytes hdrop (by simp only [pendA] at hb ⊢; (clear * - s w as π S ri hb; omega)) hpo
          (by simp only [pendA]; (clear * - s w as S π ri; omega))
      have hiv' : ivpW capS occ shpS S.rw (k' (eOfBytes (((blb π).drop s.off).take w))) (traceBytesB tr)
          { rs with msg := rs.msg + w } (ri + 1) = (some a, rs', ri') := by
        simp only [ivpW, hw0, hval] at hiv; exact hiv
      have h24 : s.off + w ≤ π.size := by (clear * - s w π S as ri hb; omega)
      have hJ' : J S π tr { s with off := s.off + w } st (buf ++ body.take w) caps (body.drop w)
          { rs with msg := rs.msg + w } i cr := by
        refine ⟨hJ.st, by simp only; (clear * - s w S π as ri hw0 hpo; omega), by simp only; (clear * - h24; omega), ?_, ?_, hJ.ent, ?_, hJ.caps⟩
        · simp only
          rw [hJ.buf, hJ.body, buf_ext _ hpo]
        · simp only; rw [hJ.body, List.drop_drop, Nat.add_comm]
        · simp only; rw [hJ.msg]; (clear * - s w S π as ri hw0 hpo; omega)
      obtain ⟨s', st', buf', caps', body', i', cr', h1, h2, h3, h4⟩ :=
        simW hdecE hchal hdecK hcap hocc as (k' _) pp Q _ st _ caps _ _ i cr hs k a rs' (ri + 1) ri' (hF' _)
          (by simp only; rw [show s.off + w - s.pend = s.off - s.pend + w by (clear * - s w S π as ri hw0 hpo; omega)]; exact hst')
          hJ' hpos hpk hk hd' hw' hiv'
      refine ⟨s', st', buf', caps', body', i', cr', h1, h2, h3, fun kS ↦ ?_⟩
      have hlen : ¬ body.length < w := by rw [hJ.body, List.length_drop, length_blb]; (clear * - π s w S as ri hw0 hb h24; omega)
      simp only [runKW, hw0, hlen, ↓reduceIte, hdecE]
      rw [hJ.body] at h4 ⊢
      exact h4 kS
    | fail => simp [ivpW] at hiv
    | _ => exact absurd hF (by simp [Fol])
  | .cap c r :: as, α, P, pp, Q, s, st, buf, caps, body, rs, i, cr, hs, k, a, rs', ri, ri', hF, hst, hJ, hpos, hpk, hk, hd, hw, hiv => by
    cases P with
    | commit ht w k' =>
      obtain ⟨hc, hshp, hF'⟩ := hF
      have hpo := hJ.pend
      simp only [stA, Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true'] at hst
      obtain ⟨⟨hidx, hnot⟩, hst'⟩ := hst
      have hnot' : r ∉ cr := by simpa using hnot
      have hd' : (driveAtoms p π as { s with caps := (r, s.off) :: s.caps, off := s.off + nodeBytes * 2 ^ c } k).runSeq (tr.drop i) = some true := hd
      have hb := bound_of_drive hk hd'
      simp only at hb
      have hcb : S.capBytes ht w = nodeBytes * 2 ^ c := by
        simp only [Scheme.capBytes, hcap, hc, nodeBytes]
      have hoff : s.off + nodeBytes * 2 ^ c ≤ π.size := by (clear * - s c π S r as cr ht w hb hcb; omega)
      have hiv' : ivpW capS occ shpS S.rw k' (traceBytesB tr) { rs with msg := rs.msg + nodeBytes * 2 ^ c } ri =
          (some a, rs', ri') := by
        simp only [ivpW, hc] at hiv; exact hiv
      have hJ' : J S π tr { s with caps := (r, s.off) :: s.caps, off := s.off + nodeBytes * 2 ^ c } st (buf ++ body.take (S.capBytes ht w)) (caps ++ [S.capI ht w body])
          (body.drop (S.capBytes ht w)) { rs with msg := rs.msg + nodeBytes * 2 ^ c } i (cr ++ [r]) := by
        refine ⟨hJ.st, by simp only; (clear * - hpo hcb; omega), by simp only; omega, ?_, ?_, hJ.ent, ?_, ?_⟩
        · simp only; rw [hcb, hJ.buf, hJ.body, buf_ext _ hpo]
        · simp only; rw [hJ.body, List.drop_drop, hcb]
        · simp only; rw [hJ.msg]; (clear * - hpo hcb; omega)
        · obtain ⟨offs, hlen, hdc, hcs, hix, hnd⟩ := hJ.caps
          refine ⟨offs ++ [s.off], by simp [hlen], ?_, ?_, ?_, ?_⟩
          · simp only; rw [hdc, List.zip_append hlen.symm]; simp
          · rw [hcs, List.zip_append hlen.symm, List.map_append, hJ.body]
            simp [hshp]
          · intro j hj
            simp only [List.length_append, List.length_singleton] at hj
            rcases Nat.lt_or_ge j cr.length with hj' | hj'
            · rw [List.getElem_append_left hj']; exact hix j hj'
            · rw [List.getElem_append_right (by (clear * - hj'; omega))]
              simp only [show j - cr.length = 0 by (clear * - hlen hj hj'; omega), List.getElem_singleton]
              (clear * - hidx hlen hj hj'; omega)
          · exact List.nodup_append.mpr ⟨hnd, List.nodup_singleton r, by
              intro a ha b hb; rw [List.mem_singleton] at hb; rw [hb]; intro hab; rw [hab] at ha; exact hnot' ha⟩
      obtain ⟨s', st', buf', caps', body', i', cr', h1, h2, h3, h4⟩ :=
        simW hdecE hchal hdecK hcap hocc as k' pp Q _ st _ _ _ _ i (cr ++ [r]) hs k a rs' ri ri' hF'
          (by simp only; rw [show s.off + nodeBytes * 2 ^ c - s.pend = s.off - s.pend + nodeBytes * 2 ^ c by
            (clear * - s c S π r as cr ht w hpo hcb; omega)]; exact hst')
          hJ' hpos hpk hk hd' hw hiv'
      refine ⟨s', st', buf', caps', body', i', cr', h1, h2, h3, fun kS ↦ ?_⟩
      have hlen : ¬ body.length < S.capBytes ht w := by rw [hJ.body, List.length_drop, length_blb, hcb]; (clear * - π s c S r as cr ht w hcb hoff; omega)
      simp only [runKW, hlen, ↓reduceIte]
      exact h4 kS
    | fail => simp [ivpW] at hiv
    | _ => exact absurd hF (by simp [Fol])
  | .sm :: as, α, P, pp, Q, s, st, buf, caps, body, rs, i, cr, hs, k, a, rs', ri, ri', hF, hst, hJ, hpos, hpk, hk, hd, hw, hiv => by
    cases P with
    | sample k' =>
      have hF' : ∀ y, Fol capS shpS idxS (k' y) as pp Q := hF
      simp only [stA, Bool.and_eq_true, decide_eq_true_eq] at hst
      obtain ⟨hcap32, hst'⟩ := hst
      rw [driveAtoms, fsQuery] at hd
      obtain ⟨a₀, rest, hdrop, hd'⟩ := ask_run hd
      obtain ⟨hq, hbl⟩ := hJ.fsQ
      obtain ⟨hans, hrest, hJ1⟩ := hJ.fs hdrop
      have hiv' : ivpW capS occ shpS S.rw (k' (chalOf a₀)) (traceBytesB tr)
          { rs with ent := rs.ent + 72 + rs.msg, msg := 0 } ri = (some a, rs', ri') := by
        simp only [ivpW, hans] at hiv; exact hiv
      obtain ⟨s', st', buf', caps', body', i', cr', h1, h2, h3, h4⟩ :=
        simW hdecE hchal hdecK hcap hocc as (k' _) pp Q
          { s with log := (digestBytes s.st ++ π.extract s.pend s.off, a₀) :: s.log, st := a₀, pend := s.off }
          a₀ [] caps body _ (i + 1) cr hs k a rs' ri ri' (hF' _)
          (by show stA p as (s.off - s.off) cr hs occ = true; rw [Nat.sub_self]; exact hst')
          (hJ1 _ rfl rfl rfl rfl) hpos hpk hk (by rw [hrest]; exact hd') hw hiv'
      refine ⟨s', st', buf', caps', body', i', cr', h1, h2, h3, fun kS ↦ ?_⟩
      have hle : 32 + buf.length ≤ queryCap := by rw [hbl]; exact hcap32
      simp only [runKW, hle, ↓reduceIte, hq, hdrop, runSeq_query_eq, hchal]
      rw [← hrest]
      exact h4 kS
    | fail => simp [ivpW] at hiv
    | _ => exact absurd hF (by simp [Fol])
  | .pclr :: as, α, P, pp, Q, s, st, buf, caps, body, rs, i, cr, hs, k, a, rs', ri, ri', hF, hst, hJ, hpos, hpk, hk, hd, hw, hiv => by
    rw [fol_pclr] at hF
    exact simW hdecE hchal hdecK hcap hocc as P [] Q { s with pos := [] } st buf caps body rs i cr [] k a rs' ri ri'
      hF hst ⟨hJ.1, hJ.2, hJ.3, hJ.4, hJ.5, hJ.6, hJ.7, hJ.8⟩ rfl (fun _ h ↦ by simp at h) hk hd hw hiv
  | .ps h n :: as, α, P, pp, Q, s, st, buf, caps, body, rs, i, cr, hs, k, a, rs', ri, ri', hF, hst, hJ, hpos, hpk, hk, hd, hw, hiv => by
    cases P with
    | sample k' =>
      have hF' : ∀ y, Fol capS shpS idxS (k' y) as
          (pp ++ chunk h n (LeanVM.Protocol.Verifier.eToNat y)) Q := hF
      simp only [stA, Bool.and_eq_true, decide_eq_true_eq] at hst
      obtain ⟨hcap32, hst'⟩ := hst
      rw [driveAtoms, fsQuery] at hd
      obtain ⟨a₀, rest, hdrop, hd'⟩ := ask_run hd
      obtain ⟨hq, hbl⟩ := hJ.fsQ
      obtain ⟨hans, hrest, hJ1⟩ := hJ.fs hdrop
      have hiv' : ivpW capS occ shpS S.rw (k' (chalOf a₀)) (traceBytesB tr)
          { rs with ent := rs.ent + 72 + rs.msg, msg := 0 } ri = (some a, rs', ri') := by
        simp only [ivpW, hans] at hiv; exact hiv
      have hpos' : (pp ++ chunk h n (answerBits a₀)) =
          pp ++ chunk h n (LeanVM.Protocol.Verifier.eToNat (chalOf a₀)) := by rw [answerBits_eq]
      obtain ⟨s', st', buf', caps', body', i', cr', h1, h2, h3, h4⟩ :=
        simW hdecE hchal hdecK hcap hocc as (k' _) _ Q
          { s with log := (digestBytes s.st ++ π.extract s.pend s.off, a₀) :: s.log, st := a₀, pend := s.off, pos := s.pos ++ chunk h n (answerBits a₀) }
          a₀ [] caps body _ (i + 1) cr (h :: hs) k a rs' ri ri' (hF' _)
          (by show stA p as (s.off - s.off) cr (h :: hs) occ = true; rw [Nat.sub_self]; exact hst')
          (hJ1 _ rfl rfl rfl rfl)
          (by show s.pos ++ chunk h n (answerBits a₀) = _; rw [hpos, ← hpos']) (by
            intro q hq'
            rcases List.mem_append.mp hq' with hq'' | hq''
            · obtain ⟨h', hh', hlt⟩ := hpk q hq''
              exact ⟨h', List.mem_cons_of_mem _ hh', hlt⟩
            · refine ⟨h, List.mem_cons_self, ?_⟩
              obtain ⟨j, -, rfl⟩ := List.mem_map.mp hq''
              exact Nat.mod_lt _ (Nat.two_pow_pos _)) hk
          (by rw [hrest]; exact hd') hw hiv'
      refine ⟨s', st', buf', caps', body', i', cr', h1, h2, h3, fun kS ↦ ?_⟩
      have hle : 32 + buf.length ≤ queryCap := by rw [hbl]; exact hcap32
      simp only [runKW, hle, ↓reduceIte, hq, hdrop, runSeq_query_eq, hchal]
      rw [← hrest]
      exact h4 kS
    | fail => simp [ivpW] at hiv
    | _ => exact absurd hF (by simp [Fol])
  | .op r :: as, α, P, pp, Q, s, st, buf, caps, body, rs, i, cr, hs, k, a, rs', ri, ri', hF, hst, hJ, hpos, hpk, hk, hd, hw, hiv => by
    cases P with
    | query ix ps k' =>
      obtain ⟨hix, hps, hF'⟩ := hF
      subst hix hps
      have hpo := hJ.pend
      simp only [stA, Bool.and_eq_true, beq_iff_eq, List.contains_iff_mem, List.all_eq_true] at hst
      obtain ⟨⟨⟨⟨hp0, hrc⟩, hgeo⟩, hhs⟩, hst'⟩ := hst
      have hoffp : s.off = s.pend := by (clear * - hpo hp0; omega)
      simp only [geomOk, Bool.and_eq_true, beq_iff_eq] at hgeo
      obtain ⟨⟨hht, hrow⟩, hpath⟩ := hgeo
      obtain ⟨capOff, hco, hcaps⟩ := capsJ_lookup hJ.caps hrc
      set ht := (shpS (idxS r)).1 with hhtdef
      set wd := (shpS (idxS r)).2 with hwddef
      -- the driver's opening
      simp only [driveAtoms, capOffset, hco] at hd
      split at hd
      · rename_i hrq
        have hk'' : ∀ (s' : DSt) (n : ℕ), ((fun s : DSt ↦ driveAtoms p π as { s with pend := s.off } k) s').runSeq
            (tr.drop n) = some true → s'.off ≤ π.size := fun s' n h ↦ by
          have := bound_of_drive hk h; simp only at this; (clear * - this; omega)
        have hlt : ∀ q ∈ ps, q < 2 ^ ht := by
          intro q hq
          obtain ⟨h', hh', hlt⟩ := hpk q (hpos ▸ hq)
          have := hhs h' hh'
          rw [this] at hlt; exact hlt
        rw [hpos] at hd
        obtain ⟨s', n, h1, hst1, hpe1, hca1, hpo1, hle1, hent1, hrun1⟩ :=
          openAll_sim S π tr hdecK (p.level r) capOff ht wd hht (by rw [hrow, hocc]) (by rw [hpath, hcap])
            (by rw [hcap]; exact capS_le _) ps s i _ hlt hk'' hd
        have hoff' : s'.off ≤ π.size := hk'' s' (i + n) h1
        set rows := (opRows (traceBytesB tr) wd (S.occ ht wd) (p.level r).path ps.length (entOff tr i)).1
        have hiv' : ivpW capS occ shpS S.rw (k' rows) (traceBytesB tr) { rs with ent := entOff tr (i + n) } ri =
            (some a, rs', ri') := by
          simp only [ivpW] at hiv
          rw [← hhtdef, ← hwddef, ← hpath, show occ ht wd = S.occ ht wd by rw [hocc], hJ.ent, hent1] at hiv
          exact hiv
        have hJ' : J S π tr { s' with pend := s'.off } st [] caps ((blb π).drop s'.off)
            { rs with ent := entOff tr (i + n) } (i + n) cr := by
          refine ⟨by rw [hJ.st]; exact hst1.symm, le_rfl, hoff', by simp, rfl, rfl, ?_, ?_⟩
          · show rs.msg = s'.off - s'.off; rw [hJ.msg, hoffp]; simp
          · show CapsJ S π caps s'.caps cr; rw [hca1]; exact hJ.caps
        obtain ⟨s'', st', buf', caps', body', i', cr', h2, h3, h4, h5⟩ :=
          simW hdecE hchal hdecK hcap hocc as (k' rows) ps Q { s' with pend := s'.off } st [] caps _ _ (i + n)
            cr hs k a rs' ri ri' (hF' rows) (by show stA p as (s'.off - s'.off) cr hs occ = true; rw [Nat.sub_self]; exact hst')
            hJ' (by show s'.pos = ps; rw [hpo1, hpos]) hpk hk h1 hw hiv'
        refine ⟨s'', st', buf', caps', body', i', cr', h2, h3, h4, fun kS ↦ ?_⟩
        have hbuf : buf = [] := by rw [hJ.buf, hoffp]; simp
        simp only [runKW, hcaps, hJ.body]
        rw [hrun1]
        simp only [hbuf] at h5 ⊢
        exact h5 kS
      · exact absurd (runSeq_ret_true hd).2 (by simp)
    | fail => simp [ivpW] at hiv
    | _ => exact absurd hF (by simp [Fol])

end Main

end Lvm.VEq
