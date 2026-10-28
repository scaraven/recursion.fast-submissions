-- New for `flock-recursive` (BLUEPRINT revision 4.1, §5.4, A.9, A.10; stage R4).
import FRSoundness4R4Chain
import FRSoundness4Pos
import FRSoundnessFrRun

/-!
# An accepted `gen4` run: its chain (`runLog_chain4`) and its register files (`accept_chain4`)

* **The message table of `seq4`** (certificates): 482 messages (`fsMsgs4_len`), whose item kinds are
  `fsItems4` (`fsMsgs4_items`) and which fit in a proof of `piSizeOf seq4` bytes (`fsMsgs4_fit`).
* **`matches_fsQ4`**: the 482 Fiat–Shamir entries of an accepted run match `fsItems4` (`G.Matches`
  at `fsSeq4`) and are linked; **`runLog_chain4`**: an accepted run on a log without bad events
  has a chain `j` (`G.IsChain L j`) whose entries are the run's Fiat–Shamir entries.
* **`relocFin R fin`**: a `Finals` with every field's ops relocated to `R`'s format; its ops are
  `fin`'s relocated (`relocFin_ops`), so `finOps4 P = (relocFin P.S (finalsOf P)).ops`.
* **`accept_chain4`** (3.x's `accept_chain`): on an accepted run of `gen4 S p (relocFin R fin).ops`,
  every phase passes, the skeleton's registers are `R₀`, `finRS` runs from `R₀` to `L₀`, and field
  `k` of the rest runs from `Rs k`, with `Rs 0 = R₀ ++ L₀` and `Rs (k + 1) = Rs k ++ L_k`.
-/

namespace FR.Snd.R4
open RecursionFast Rev4

/-! ## `seq4`'s message table -/

theorem fsMsgs4_len : (fsMsgs4 seq4).length = 482 := by
  rw [fsMsgs4, seq4_eq]; decide +kernel

/-- **The item kinds of `seq4`'s messages are `fsItems4`** (a linear certificate: `X.msgItem` reads
only whether the position is `0`). -/
theorem fsMsgs4_items : .seed :: (fsMsgs4 seq4).tail.map (X.msgItem 1) = fsItems4 := by
  rw [fsMsgs4, fsItems4, seq4_eq]; decide +kernel

theorem fsMsgs4_fit :
    (fsMsgs4 seq4).all (fun m => m.all fun ol => decide (ol.1 + ol.2 ≤ piSizeOf seq4)) = true := by
  rw [fsMsgs4, seq4_eq]; decide +kernel

/-- Message `0` is the seed's (for every `S`; proved without evaluating the table). -/
theorem fsMsgs4_head (S : Seq) : ∃ ms, fsMsgs4 S = some (0, 48) :: ms := by
  obtain ⟨ps, hps⟩ : ∃ ps, phasesOf S = ("seed", .seed) :: ps := ⟨_, rfl⟩
  exact ⟨_, by rw [fsMsgs4, hps, msgsFrom4]; rfl⟩

theorem msgItem_succ (q : ℕ) (m : Option (ℕ × ℕ)) : X.msgItem (q + 1) m = X.msgItem 1 m := by
  cases m <;> rfl

theorem fsItems4_getElem {q : ℕ} (hq : q < fsItems4.length) :
    fsItems4[q] = X.msgItem q ((fsMsgs4 seq4).getD q none) := by
  obtain ⟨ms, hms⟩ := fsMsgs4_head seq4
  have hl : fsItems4.length = ms.length + 1 := by rw [← fsMsgs4_items, hms]; simp
  simp only [← fsMsgs4_items, hms, List.tail_cons]
  rcases q with _ | q
  · rfl
  · rw [List.getElem_cons_succ, List.getElem_map, List.getD_cons_succ,
      List.getD_eq_getElem _ _ (by omega), msgItem_succ q]

theorem fit_getD {q o len : ℕ} (h : (fsMsgs4 seq4).getD q none = some (o, len)) :
    o + len ≤ piSizeOf seq4 := by
  have hq : q < (fsMsgs4 seq4).length := by
    by_contra hq; rw [List.getD_eq_default _ _ (by omega)] at h; cases h
  have hm := List.all_eq_true.mp fsMsgs4_fit _ (List.getElem_mem hq)
  rw [List.getD_eq_getElem _ _ hq] at h
  rw [h] at hm
  simpa using hm

/-- **The query of position `q` passes position `q`'s item check** on a proof of `piSizeOf seq4`
bytes. -/
theorem fsCheck_qOf (inp : Input) (hπ : inp.π.size = piSizeOf seq4) {q : ℕ} (hq : q < 482)
    (st : Digest) :
    fsCheck (fsItems4[q]'(by rw [fsItems4_length]; exact hq)) (qOf inp q ((fsMsgs4 seq4).getD q none) st) =
      true := by
  rw [fsItems4_getElem]
  rcases hm : (fsMsgs4 seq4).getD q none with _ | ⟨o, len⟩
  · rcases q with _ | q
    · obtain ⟨ms, hms⟩ := fsMsgs4_head seq4; rw [hms] at hm; cases hm
    · exact fsCheck_squeezeQ st
  · have hs := size_extract_of_le (π := inp.π) (o := o) (len := len) (by rw [hπ]; exact fit_getD hm)
    rcases q with _ | q
    · obtain ⟨ms, hms⟩ := fsMsgs4_head seq4
      rw [hms, List.getD_cons_zero, Option.some.injEq, Prod.mk.injEq] at hm
      obtain ⟨rfl, rfl⟩ := hm
      exact fsCheck_seedQ inp.vk inp.c _ hs
    · simp only [qOf, X.msgItem, Nat.add_one_ne_zero, ite_false]
      have := fsCheck_absorbQ st (inp.π.extract o (o + len))
      rwa [hs] at this

theorem stateIn_qOf (inp : Input) {q : ℕ} (hq : q ≠ 0) (m : Option (ℕ × ℕ)) (st : Digest) :
    stateIn (qOf inp q m st) = some st := by
  unfold qOf
  split
  · rw [if_neg hq]; exact stateIn_absorbQ st _
  · exact stateIn_squeezeQ st

/-- **The run's Fiat–Shamir entries match `fsItems4`**, and are linked. -/
theorem matches_fsQ4 (inp : Input) (hπ : inp.π.size = piSizeOf seq4) {es : Log} (hl : es.length = 482)
    (hq : ∀ q < 482, (es.getD q default).1 = qOf inp q ((fsMsgs4 seq4).getD q none) (es.getD (q - 1) default).2) :
    G.Matches es ∧ (∀ h : 0 < es.length, stateIn (es[0]'h).1 = none) ∧
      ∀ n (h : n + 1 < es.length), stateIn (es[n + 1]'h).1 = some (es[n]'(by omega)).2 := by
  have hq' : ∀ q (h : q < es.length), (es[q]'h).1 =
      qOf inp q ((fsMsgs4 seq4).getD q none) (es.getD (q - 1) default).2 :=
    fun q h => by rw [← hq q (by omega), List.getD_eq_getElem _ _ h]
  have hck : ∀ q (h : q < es.length), fsCheck (fsItems4[q]'(by rw [fsItems4_length]; omega))
      (es[q]'h).1 = true := fun q h => by rw [hq' q h]; exact fsCheck_qOf inp hπ (by omega) _
  have hlink : ∀ n (h : n + 1 < es.length), stateIn (es[n + 1]'h).1 = some (es[n]'(by omega)).2 :=
    fun n h => by
      rw [hq' _ h, stateIn_qOf inp (by omega), Nat.add_sub_cancel, List.getD_eq_getElem _ _ (by omega)]
  have h0 : ∀ h : 0 < es.length, fsCheck .seed (es[0]'h).1 = true := fun h => by
    have := hck 0 h
    rwa [fsItems4_getElem, X.msgItem] at this
  refine ⟨⟨?_, ⟨by rw [fs_eq4, hl, fsItems4_length], fun i hi => ⟨hlink i hi, hck (i + 1) hi⟩⟩⟩,
    fun h => stateIn_of_seed (h0 h), hlink⟩
  rcases es with _ | ⟨e, es⟩
  · simp at hl
  · simp only [List.head?_cons, Option.map_some]
    exact congrArg some (h0 (by simp))

/-- **`runLog_chain4`**: an accepted run of `gen4 seq4 p fin` on a log without bad events has a chain
`j` whose entries are the run's 482 Fiat–Shamir entries. -/
theorem runLog_chain4 (impl : OpImpl) (p : KindP) (fin : FinOps) {inp : Input} {L : Log}
    (hb : ¬ Bad L) (hπ : inp.π.size = piSizeOf seq4)
    (hrun : (runIR impl (gen4 seq4 p fin) inp).runLog L = some true) :
    ∃ tr : Trace, semIR impl (gen4 seq4 p fin) inp tr = some true ∧
      (∀ e ∈ tr, e ∈ L) ∧ ∃ j, G.IsChain L j ∧ entriesOf L (pathOf L j) = fsOf tr (itemsOf seq4) ∧
        (entriesOf L (pathOf L j)).length = 482 := by
  obtain ⟨tr, h1, h2⟩ := runLog_trace _ hrun
  rw [runSeq_runIR] at h1
  obtain ⟨hl, hq⟩ := fsQ_gen4 impl inp seq4 p shOK_seq4 fin h1
  rw [fsMsgs4_len] at hl hq
  obtain ⟨hm, h0, hs⟩ := matches_fsQ4 inp hπ hl hq
  have hin : ∀ e ∈ fsOf tr (itemsOf seq4), e ∈ L := fun e he => h2 e (mem_fsOf he)
  obtain ⟨j, hj, -, hp⟩ := path_of_links hb hin h0 hs 481 (by omega)
  rw [show 481 + 1 = (fsOf tr (itemsOf seq4)).length by omega, List.take_length] at hp
  exact ⟨tr, h1, h2, j, ⟨hj, hp ▸ hm⟩, hp, by rw [hp, hl]⟩

/-! ## The finals, relocated -/

/-- A field with its ops relocated to `R`'s format. -/
def relocF (R : Seq) (f : FinField) : FinField := fun fi b => ((f fi b).1.map (reloc R), (f fi b).2)

/-- **The finals with every field relocated.** -/
def relocFin (R : Seq) (fin : Finals) : Finals :=
  ⟨relocF R fin.finRS, relocF R fin.finZ, relocF R fin.finLc, relocF R fin.finSh, relocF R fin.finLr,
    relocF R fin.finE, relocF R fin.finB', fun i => relocF R (fin.finP i), relocF R fin.finPf⟩

theorem relocFin_rest (R : Seq) (fin : Finals) : (relocFin R fin).rest = fin.rest.map (relocF R) := by
  simp [relocFin, Finals.rest, List.map_append, Function.comp_def]

theorem runFields_reloc (R : Seq) (outs : Array (List Reg)) (zh : List Reg) :
    ∀ (fs : List FinField) (b : ℕ) (ex : Array (List Reg)),
      runFields outs zh (fs.map (relocF R)) b ex = (runFields outs zh fs b ex).map (reloc R)
  | [], _, _ => rfl
  | f :: fs, b, ex => by
    simp only [List.map_cons, runFields, relocF, opsOut_reloc, List.map_append]
    rw [runFields_reloc R outs zh fs]

/-- **The relocated finals' ops are the finals' ops relocated.** -/
theorem relocFin_ops (R : Seq) (fin : Finals) (outs : Array (List Reg)) (b : ℕ) :
    (relocFin R fin).ops outs b = (fin.ops outs b).map (reloc R) := by
  rw [finals_ops_eq, finals_ops_eq, relocFin_rest, List.map_append]
  have h1 := runFields_reloc R outs [] [fin.finRS] b #[]
  simp only [List.map_cons, List.map_nil] at h1
  have e : (relocFin R fin).finRS = relocF R fin.finRS := rfl
  rw [e, h1]
  simp only [relocF, opsOut_reloc]
  rw [runFields_reloc]

/-- `finOps4 P` is the relocated finals' ops. -/
theorem finOps4_eq (P : FinP) : finOps4 P = (relocFin P.S (finalsOf P)).ops := by
  funext outs b; rw [relocFin_ops]; rfl

theorem noAsk_relocFin (R : Seq) {fin : Finals}
    (hna : ∀ f ∈ fin.finRS :: fin.rest, ∀ fi b, (f fi b).1.filterMap Op.item? = []) :
    ∀ f ∈ (relocFin R fin).finRS :: (relocFin R fin).rest, ∀ fi b, (f fi b).1.filterMap Op.item? = [] := by
  intro f hf fi b
  rw [relocFin_rest] at hf
  obtain ⟨g, hg, rfl⟩ : ∃ g ∈ fin.finRS :: fin.rest, f = relocF R g := by
    rcases List.mem_cons.1 hf with rfl | hf
    · exact ⟨_, List.mem_cons_self .., rfl⟩
    · obtain ⟨g, hg, rfl⟩ := List.mem_map.1 hf
      exact ⟨g, List.mem_cons_of_mem _ hg, rfl⟩
  simp only [relocF, List.filterMap_map, Function.comp_def, item_reloc]
  exact hna g hg fi b

/-! ## `accept_chain4` -/

section Accept
variable (impl : OpImpl) (S : Seq) (p : KindP) (inp : Input)

/-- **An accepted `gen4` run, with its register files** (3.x's `accept_chain`): the skeleton's
registers `R₀ = #[] ++ y.1`; `finRS` runs from `R₀` to `L₀`; field `k` of the rest runs from
`Rs k`, `Rs 0 = R₀ ++ L₀`, `Rs (k + 1) = Rs k ++ L_k`. -/
theorem accept_chain4 (fin : Finals) {tr : Trace}
    (hna : ∀ f ∈ fin.finRS :: fin.rest, ∀ fi b, (f fi b).1.filterMap Op.item? = [])
    (h : semIR impl (gen4 S p fin.ops) inp tr = some true) :
    ∃ y, refPhases4 impl p.tix inp S p (phasesOf S) 0 ctx0 #[] tr = some y ∧ (∀ b ∈ y.2.1, b = true) ∧
      (skeleton4 S p).2.next = (#[] ++ y.1.toArray).size ∧
      ∃ L₀, pureRun impl p.tix inp (fin.finRS ⟨(skeleton4 S p).2.outs, [], #[]⟩ (skeleton4 S p).2.next).1
          (#[] ++ y.1.toArray) [] = some (L₀, true) ∧
        ∃ Rs : ℕ → Array Val, Rs 0 = (#[] ++ y.1.toArray) ++ L₀.toArray ∧
          ∀ k (hk : k < fin.rest.length), ∃ L, pureRun impl p.tix inp ((fin.rest[k]'hk)
            ⟨(skeleton4 S p).2.outs, (fin.finRS ⟨(skeleton4 S p).2.outs, [], #[]⟩ (skeleton4 S p).2.next).2,
              exAt (skeleton4 S p).2.outs
                (fin.finRS ⟨(skeleton4 S p).2.outs, [], #[]⟩ (skeleton4 S p).2.next).2 fin.rest
                ((skeleton4 S p).2.next +
                  opsOut (fin.finRS ⟨(skeleton4 S p).2.outs, [], #[]⟩ (skeleton4 S p).2.next).1)
                #[(fin.finRS ⟨(skeleton4 S p).2.outs, [], #[]⟩ (skeleton4 S p).2.next).2] k⟩
              (Rs k).size).1 (Rs k) [] = some (L, true) ∧ Rs (k + 1) = Rs k ++ L.toArray := by
  unfold semIR at h
  split at h
  · next s hs =>
    simp only [Option.some.injEq] at h
    rw [show (gen4 S p fin.ops).ops = (skeleton4 S p).1 ++
        (fin.ops (skeleton4 S p).2.outs (skeleton4 S p).2.next ++ [.accept]) by simp [gen4],
      show (gen4 S p fin.ops).kindOn inp = p.tix from rfl, St.init, exec_skeleton4] at hs
    obtain ⟨y, hy, hs'⟩ := Option.bind_eq_some_iff.1 hs
    have hn := skeleton4_next impl p.tix inp S p hy
    rw [hn, finals_ops_eq] at hs'
    simp only [List.append_assoc] at hs'
    obtain ⟨hok, -⟩ := fields_ok impl p.tix inp (skeleton4 S p).2.outs [] [fin.finRS] _ #[] _ _ _ s []
      (fun f hf => hna f (by simp_all)) hs' h
    obtain ⟨L, hL, -, h2⟩ := field_flag impl p.tix inp
      (hna _ (List.mem_cons_self ..) _ _) (by simpa only [runFields, List.append_nil] using hs') h
    have hsz : ((#[] ++ y.1.toArray) ++ L.toArray).size = (#[] ++ y.1.toArray).size +
        opsOut (fin.finRS ⟨(skeleton4 S p).2.outs, [], #[]⟩ (#[] ++ y.1.toArray).size).1 := by
      have hl := pureRun_len impl p.tix inp _ _ [] L true hL
      simp [hl]
    rw [← hsz] at h2
    obtain ⟨Rs, h0, hrest⟩ := fields_chain impl p.tix inp (skeleton4 S p).2.outs _ fin.rest _ _ true _ _
      s [] (fun f hf => hna f (List.mem_cons_of_mem _ hf)) h2 h
    refine ⟨y, hy, by simpa using hok, hn, L, by rw [hn]; exact hL, Rs, h0, fun k hk => ?_⟩
    obtain ⟨Lk, hp, he⟩ := hrest k hk
    rw [hsz] at hp
    rw [hn]
    exact ⟨Lk, hp, he⟩
  · cases h

end Accept

end FR.Snd.R4
