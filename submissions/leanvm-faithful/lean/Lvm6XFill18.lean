-- lvm6 EXF phase 2 (F-EXG-2): the fill block at `P18`. After the front, `fillIR18` copies the round challenges
-- (chain answers) and the high parts and final scalars (proof words on the tape) into EXG's `FrontA` cells `F18`
-- in `[2^25, 2^26)`; `fill_front`/`frontIn18`: the heap then holds them as the opening's runs return them. New.
import Lvm6XFill
import Lvm6XLv18

/-!
# The fill block at `P18`

* **`F18`**: the `FrontA` cells: `ch i k = 2^25 + 32i + 4k` (`α` at `+0`, `β` at `+2`), `hi i = 2^25 + 256 + 16i`,
  `s = 2^25 + 512`.
* **`N18`**, **`base18 i`**: the opening's first event (`|ops| − |ops18|`) and level `i`'s offset in it.
  **`reqs18`**: the requests `(event index, cell)`: round `k` of level `i` draws `α`, `β` at events
  `N18 + base18 i + 7k + 5, + 6`; tail `i`'s high part `k` is event `N18 + base18 i + 7 rnd18 i + k`; the final
  scalar `k` is event `N18 + base18 4 + 28 + k`. **`fillTab18`**: two word copies a request, from the chain
  answer (`srcs18`'s `.smp p`) or from the tape (`.rd off 16`). **`fillIR18 := cpsIR fillTab18`**.
* **`fill18_ok`**: the copies' static facts, the requests' sources, the counts. Kernel-cheap (KDX): `srcs18` is
  evaluated once (`srcs18_facts`, its last 316 sources `srcsO18`), the table is the literal `fillTabL18`
  (`fillTab18_eq`) and its destinations increase (`sortedLt`, linear, for `Nodup`).
* **`RunMidE`/`RunFinE`** (EXI's `RunMid`/`RunFin`, same bodies), **`FrontSeg18`**: for every decomposition of the
  opening's log `h.drop N18` into the levels' runs, the cells hold the rounds' `(α, β)`, the tails' high parts and the
  final scalars, in the forms `trIR_sem`'s `hch`, `glueIR_cols`' `hhi` and `startIR_cols`' `hs` read.
* **`fill_front`**, **`frontIn18`** (under `¬ Bad L`): `Inv`, no output, the rows (`Rows18`), `FrontSeg18`, every cell
  outside `[2^25, 2^26)` as the front left it, and `N₀ = N18` for the opening's start.
-/

set_option autoImplicit false

namespace Lvm6.X

open RecursionFast Lvm Lvm.X Lvm.FS Lvm6.Whir
open LeanVM.Protocol.Compile (Ev VerifierProgram commits)
open LeanVM.Parameters (E E2 e2OfE)

/-! ## The cells and the requests -/

/-- **The cells the front fills** (EXG's `FrontA`), in `[2^25, 2^26)`. -/
def F18 : FrontA := ⟨fun i k ↦ 33554432 + 32 * i + 4 * k, fun i ↦ 33554688 + 16 * i, 33554944⟩

/-- The events of tail `i`. -/
def tl18 : ℕ → ℕ
  | 0 => (tailOps 6 20 32 18 18 0).length
  | 1 => (tailOps 4 19 32 14 7 1).length
  | 2 => (tailOps 4 18 32 10 4 2).length
  | _ => (tailOps 4 17 32 6 2 3).length

/-- Level `i`'s first event in the opening's log. -/
def base18 : ℕ → ℕ
  | 0 => 0
  | i + 1 => base18 i + 7 * rnd18 i + tl18 i

/-- The opening's first event in the history. -/
def N18 : ℕ := (opsOf P18.levs (sched6 P18)).length - ops18.length

/-- **The requests**: `(event index, cell)`. -/
def reqs18 : List (ℕ × ℕ) :=
  ((List.range 5).flatMap fun i ↦ (List.range (rnd18 i)).flatMap fun k ↦
    [(N18 + base18 i + 7 * k + 5, F18.ch i k), (N18 + base18 i + 7 * k + 6, F18.ch i k + 2)]) ++
  ((List.range 4).flatMap fun i ↦ (List.range (rnd18 i)).map fun k ↦
    (N18 + base18 i + 7 * rnd18 i + k, F18.hi i + 2 * k)) ++
  ((List.range 12).map fun k ↦ (N18 + base18 4 + 7 * 4 + k, F18.s + 2 * k))

/-- The two word copies of a request from its event's source. -/
def cpOf : Src → ℕ → List (Bool × ℕ × ℕ)
  | .smp p, dst => [(true, ansB + 4 * p, dst), (true, ansB + 4 * p + 1, dst + 1)]
  | .rd off _, dst => [(false, 5 + off / 8, dst), (false, 5 + off / 8 + 1, dst + 1)]
  | _, _ => []

/-- **The copies.** -/
def fillTab18 : List (Bool × ℕ × ℕ) := reqs18.flatMap fun r ↦ cpOf (srcs18.getD r.1 default) r.2

/-- **The fill block.** -/
def fillIR18 : XIR := cpsIR fillTab18

/-- A request's source: a draw inside the chain, or a 16-byte read of π, word-aligned. -/
def reqOK (r : ℕ × ℕ) : Bool :=
  match srcs18.getD r.1 default with
  | .smp p => decide (p < nCh6 P18)
  | .rd off w => decide (w = 16) && decide (off % 8 = 0) && decide (off + 16 ≤ pz6)
  | _ => false

/-! ## The static facts, without re-evaluating the replay

`fillTab18` looks each request up in `srcs18`, a walk over all 5,353 events, and the kernel re-evaluated that walk
on every lookup (about a minute of replay). The proofs below evaluate `srcs18` once, through its last 316 sources
(`srcsO18`, the opening's), and read the requests from that short literal; `fillTabL18` is the table itself. -/

/-- `getD` past a prefix is `getD` of the `drop`. -/
theorem getD_eq_getD_drop {α : Type*} (l : List α) (d : α) {n i : ℕ} (h : n ≤ i) :
    l.getD i d = (l.drop n).getD (i - n) d := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_drop, Nat.add_sub_cancel' h]

/-- `flatMap` of lookups past a prefix reads the `drop`. -/
theorem flatMap_getD_drop {α β : Type*} (l : List α) (d : α) (n : ℕ) (f : α → ℕ → List β) :
    ∀ rs : List (ℕ × ℕ), rs.all (fun r => decide (n ≤ r.1)) = true →
      rs.flatMap (fun r => f (l.getD r.1 d) r.2) = rs.flatMap (fun r => f ((l.drop n).getD (r.1 - n) d) r.2)
  | [], _ => rfl
  | r :: rs, h => by
    simp only [List.all_cons, Bool.and_eq_true, decide_eq_true_eq] at h
    rw [List.flatMap_cons, List.flatMap_cons, getD_eq_getD_drop l d h.1, flatMap_getD_drop l d n f rs h.2]

/-- `all` of lookups past a prefix reads the `drop`. -/
theorem all_getD_drop {α : Type*} (l : List α) (d : α) (n : ℕ) (g : α → Bool) :
    ∀ rs : List (ℕ × ℕ), rs.all (fun r => decide (n ≤ r.1)) = true →
      rs.all (fun r => g (l.getD r.1 d)) = rs.all (fun r => g ((l.drop n).getD (r.1 - n) d))
  | [], _ => rfl
  | r :: rs, h => by
    simp only [List.all_cons, Bool.and_eq_true, decide_eq_true_eq] at h
    rw [List.all_cons, List.all_cons, getD_eq_getD_drop l d h.1, all_getD_drop l d n g rs h.2]

/-- **One source per operation.** -/
theorem length_srcsOp (cO oc : ℕ → ℕ → ℕ) (t : ℕ → ℕ) :
    ∀ (cs : List (ℕ × ℕ × ℕ)) (ws : List ℕ) (o P : ℕ) (os : List Op),
      (srcsOp cO oc t cs ws o P os).length = os.length
  | _, _, _, _, [] => rfl
  | cs, ws, o, P, .rd :: os => by
    rw [srcsOp, List.length_cons, List.length_cons, length_srcsOp cO oc t _ _ _ _ os]
  | cs, ws, o, P, .smp :: os => by
    rw [srcsOp, List.length_cons, List.length_cons, length_srcsOp cO oc t _ _ _ _ os]
  | cs, ws, o, P, .cap ht w :: os => by
    rw [srcsOp, List.length_cons, List.length_cons, length_srcsOp cO oc t _ _ _ _ os]
  | cs, ws, o, P, .opn i :: os => by
    rw [srcsOp, List.length_cons, List.length_cons, length_srcsOp cO oc t _ _ _ _ os]

/-- The opening's sources: `srcs18` from event `N18 = 5037` on (`srcs18_facts`). -/
def srcsO18 : List Src :=
  [.rd 63928 16, .rd 63944 16, .rd 63960 16, .rd 63976 16, .rd 63992 8, .smp 931, .smp 932, .rd 64000 16,
   .rd 64016 16, .rd 64032 16, .rd 64048 16, .rd 64064 8, .smp 933, .smp 934, .rd 64072 16, .rd 64088 16,
   .rd 64104 16, .rd 64120 16, .rd 64136 8, .smp 935, .smp 936, .rd 64144 16, .rd 64160 16, .rd 64176 16,
   .rd 64192 16, .rd 64208 8, .smp 937, .smp 938, .rd 64216 16, .rd 64232 16, .rd 64248 16, .rd 64264 16, .rd 64280 8,
   .smp 939, .smp 940, .rd 64288 16, .rd 64304 16, .rd 64320 16, .rd 64336 16, .rd 64352 8, .smp 941, .smp 942,
   .rd 64360 16, .rd 64376 16, .rd 64392 16, .rd 64408 16, .rd 64424 16, .rd 64440 16, .cap, .smp 943, .rd 66504 8,
   .smp 944, .smp 945, .smp 946, .smp 947, .smp 948, .smp 949, .smp 950, .smp 951, .smp 952, .smp 953, .smp 954,
   .smp 955, .smp 956, .smp 957, .smp 958, .smp 959, .smp 960, .smp 961, .smp 962, .rd 66512 16, .rd 66528 8,
   .smp 963, .smp 964, .smp 965, .smp 966, .smp 967, .smp 968, .smp 969, .smp 970, .smp 971, .smp 972, .smp 973,
   .smp 974, .smp 975, .smp 976, .smp 977, .smp 978, .smp 979, .smp 980, .smp 981, .smp 982, .opn, .rd 156296 16,
   .rd 156312 16, .rd 156328 16, .rd 156344 16, .rd 156360 8, .smp 983, .smp 984, .rd 156368 16, .rd 156384 16,
   .rd 156400 16, .rd 156416 16, .rd 156432 8, .smp 985, .smp 986, .rd 156440 16, .rd 156456 16, .rd 156472 16,
   .rd 156488 16, .rd 156504 8, .smp 987, .smp 988, .rd 156512 16, .rd 156528 16, .rd 156544 16, .rd 156560 16,
   .rd 156576 8, .smp 989, .smp 990, .rd 156584 16, .rd 156600 16, .rd 156616 16, .rd 156632 16, .cap, .smp 991,
   .rd 157672 8, .smp 992, .smp 993, .smp 994, .smp 995, .smp 996, .smp 997, .smp 998, .smp 999, .smp 1000, .smp 1001,
   .smp 1002, .smp 1003, .smp 1004, .smp 1005, .smp 1006, .rd 157680 16, .rd 157696 8, .smp 1007, .smp 1008,
   .smp 1009, .smp 1010, .smp 1011, .smp 1012, .smp 1013, .smp 1014, .smp 1015, .opn, .rd 189384 16, .rd 189400 16,
   .rd 189416 16, .rd 189432 16, .rd 189448 8, .smp 1016, .smp 1017, .rd 189456 16, .rd 189472 16, .rd 189488 16,
   .rd 189504 16, .rd 189520 8, .smp 1018, .smp 1019, .rd 189528 16, .rd 189544 16, .rd 189560 16, .rd 189576 16,
   .rd 189592 8, .smp 1020, .smp 1021, .rd 189600 16, .rd 189616 16, .rd 189632 16, .rd 189648 16, .rd 189664 8,
   .smp 1022, .smp 1023, .rd 189672 16, .rd 189688 16, .rd 189704 16, .rd 189720 16, .cap, .smp 1024, .rd 190760 8,
   .smp 1025, .smp 1026, .smp 1027, .smp 1028, .smp 1029, .smp 1030, .smp 1031, .smp 1032, .smp 1033, .smp 1034,
   .smp 1035, .rd 190768 16, .rd 190784 8, .smp 1036, .smp 1037, .smp 1038, .smp 1039, .smp 1040, .smp 1041, .opn,
   .rd 210504 16, .rd 210520 16, .rd 210536 16, .rd 210552 16, .rd 210568 8, .smp 1042, .smp 1043, .rd 210576 16,
   .rd 210592 16, .rd 210608 16, .rd 210624 16, .rd 210640 8, .smp 1044, .smp 1045, .rd 210648 16, .rd 210664 16,
   .rd 210680 16, .rd 210696 16, .rd 210712 8, .smp 1046, .smp 1047, .rd 210720 16, .rd 210736 16, .rd 210752 16,
   .rd 210768 16, .rd 210784 8, .smp 1048, .smp 1049, .rd 210792 16, .rd 210808 16, .rd 210824 16, .rd 210840 16,
   .cap, .smp 1050, .rd 211880 8, .smp 1051, .smp 1052, .smp 1053, .smp 1054, .smp 1055, .smp 1056, .smp 1057,
   .rd 211888 16, .rd 211904 8, .smp 1058, .smp 1059, .smp 1060, .smp 1061, .opn, .rd 226024 16, .rd 226040 16,
   .rd 226056 16, .rd 226072 16, .rd 226088 8, .smp 1062, .smp 1063, .rd 226096 16, .rd 226112 16, .rd 226128 16,
   .rd 226144 16, .rd 226160 8, .smp 1064, .smp 1065, .rd 226168 16, .rd 226184 16, .rd 226200 16, .rd 226216 16,
   .rd 226232 8, .smp 1066, .smp 1067, .rd 226240 16, .rd 226256 16, .rd 226272 16, .rd 226288 16, .rd 226304 8,
   .smp 1068, .smp 1069, .rd 226312 16, .rd 226328 16, .rd 226344 16, .rd 226360 16, .rd 226376 16, .rd 226392 16,
   .rd 226408 16, .rd 226424 16, .rd 226440 16, .rd 226456 16, .rd 226472 16, .rd 226488 16, .rd 226504 8, .smp 1070,
   .smp 1071, .smp 1072, .opn, .rd 238032 16, .rd 238048 16, .rd 238064 8, .smp 1073, .rd 238072 16, .rd 238088 16,
   .rd 238104 8, .smp 1074, .rd 238112 16, .rd 238128 16, .rd 238144 8, .smp 1075]

/-- **The copies**, as a literal (`fillTab18_eq`). -/
def fillTabL18 : List (Bool × ℕ × ℕ) :=
  [(true, 16797324, 33554432), (true, 16797325, 33554433), (true, 16797328, 33554434), (true, 16797329, 33554435),
   (true, 16797332, 33554436), (true, 16797333, 33554437), (true, 16797336, 33554438), (true, 16797337, 33554439),
   (true, 16797340, 33554440), (true, 16797341, 33554441), (true, 16797344, 33554442), (true, 16797345, 33554443),
   (true, 16797348, 33554444), (true, 16797349, 33554445), (true, 16797352, 33554446), (true, 16797353, 33554447),
   (true, 16797356, 33554448), (true, 16797357, 33554449), (true, 16797360, 33554450), (true, 16797361, 33554451),
   (true, 16797364, 33554452), (true, 16797365, 33554453), (true, 16797368, 33554454), (true, 16797369, 33554455),
   (true, 16797532, 33554464), (true, 16797533, 33554465), (true, 16797536, 33554466), (true, 16797537, 33554467),
   (true, 16797540, 33554468), (true, 16797541, 33554469), (true, 16797544, 33554470), (true, 16797545, 33554471),
   (true, 16797548, 33554472), (true, 16797549, 33554473), (true, 16797552, 33554474), (true, 16797553, 33554475),
   (true, 16797556, 33554476), (true, 16797557, 33554477), (true, 16797560, 33554478), (true, 16797561, 33554479),
   (true, 16797664, 33554496), (true, 16797665, 33554497), (true, 16797668, 33554498), (true, 16797669, 33554499),
   (true, 16797672, 33554500), (true, 16797673, 33554501), (true, 16797676, 33554502), (true, 16797677, 33554503),
   (true, 16797680, 33554504), (true, 16797681, 33554505), (true, 16797684, 33554506), (true, 16797685, 33554507),
   (true, 16797688, 33554508), (true, 16797689, 33554509), (true, 16797692, 33554510), (true, 16797693, 33554511),
   (true, 16797768, 33554528), (true, 16797769, 33554529), (true, 16797772, 33554530), (true, 16797773, 33554531),
   (true, 16797776, 33554532), (true, 16797777, 33554533), (true, 16797780, 33554534), (true, 16797781, 33554535),
   (true, 16797784, 33554536), (true, 16797785, 33554537), (true, 16797788, 33554538), (true, 16797789, 33554539),
   (true, 16797792, 33554540), (true, 16797793, 33554541), (true, 16797796, 33554542), (true, 16797797, 33554543),
   (true, 16797848, 33554560), (true, 16797849, 33554561), (true, 16797852, 33554562), (true, 16797853, 33554563),
   (true, 16797856, 33554564), (true, 16797857, 33554565), (true, 16797860, 33554566), (true, 16797861, 33554567),
   (true, 16797864, 33554568), (true, 16797865, 33554569), (true, 16797868, 33554570), (true, 16797869, 33554571),
   (true, 16797872, 33554572), (true, 16797873, 33554573), (true, 16797876, 33554574), (true, 16797877, 33554575),
   (false, 8050, 33554688), (false, 8051, 33554689), (false, 8052, 33554690), (false, 8053, 33554691),
   (false, 8054, 33554692), (false, 8055, 33554693), (false, 8056, 33554694), (false, 8057, 33554695),
   (false, 8058, 33554696), (false, 8059, 33554697), (false, 8060, 33554698), (false, 8061, 33554699),
   (false, 19578, 33554704), (false, 19579, 33554705), (false, 19580, 33554706), (false, 19581, 33554707),
   (false, 19582, 33554708), (false, 19583, 33554709), (false, 19584, 33554710), (false, 19585, 33554711),
   (false, 23714, 33554720), (false, 23715, 33554721), (false, 23716, 33554722), (false, 23717, 33554723),
   (false, 23718, 33554724), (false, 23719, 33554725), (false, 23720, 33554726), (false, 23721, 33554727),
   (false, 26354, 33554736), (false, 26355, 33554737), (false, 26356, 33554738), (false, 26357, 33554739),
   (false, 26358, 33554740), (false, 26359, 33554741), (false, 26360, 33554742), (false, 26361, 33554743),
   (false, 28294, 33554944), (false, 28295, 33554945), (false, 28296, 33554946), (false, 28297, 33554947),
   (false, 28298, 33554948), (false, 28299, 33554949), (false, 28300, 33554950), (false, 28301, 33554951),
   (false, 28302, 33554952), (false, 28303, 33554953), (false, 28304, 33554954), (false, 28305, 33554955),
   (false, 28306, 33554956), (false, 28307, 33554957), (false, 28308, 33554958), (false, 28309, 33554959),
   (false, 28310, 33554960), (false, 28311, 33554961), (false, 28312, 33554962), (false, 28313, 33554963),
   (false, 28314, 33554964), (false, 28315, 33554965), (false, 28316, 33554966), (false, 28317, 33554967)]

/-- The replay's facts, one evaluation of `sched6 P18`, `srcs18`, `opsOf P18.levs (sched6 P18)` and the chain's
messages. -/
theorem srcs18_facts : N18 = 5037 ∧ srcs18.drop 5037 = srcsO18 ∧ 0 < ops18.length ∧
    ops18.length ≤ (opsOf P18.levs (sched6 P18)).length ∧ nCh6 P18 = 1076 := by
  decide +kernel

/-- The requests' events lie in the opening. -/
theorem reqs18_ge : reqs18.all (fun r => decide (5037 ≤ r.1)) = true := by
  unfold reqs18; rw [srcs18_facts.1]; decide +kernel

/-- **`fillTab18` is `fillTabL18`**, its lookups read from `srcsO18`. -/
theorem fillTab18_eq : fillTab18 = fillTabL18 := by
  rw [fillTab18, flatMap_getD_drop srcs18 default 5037 cpOf reqs18 reqs18_ge, srcs18_facts.2.1]
  unfold reqs18; rw [srcs18_facts.1]; decide +kernel

/-- A request's check from its source (`reqOK`'s body, the chain's length `n`). -/
def srcOK (n : ℕ) : Src → Bool
  | .smp p => decide (p < n)
  | .rd off w => decide (w = 16) && decide (off % 8 = 0) && decide (off + 16 ≤ pz6)
  | _ => false

theorem reqOK_eq : reqOK = fun r => srcOK (nCh6 P18) (srcs18.getD r.1 default) := by
  funext r; unfold reqOK srcOK; rfl

/-- Strictly increasing (a linear check for `Nodup`). -/
def sortedLt : List ℕ → Bool
  | a :: b :: l => decide (a < b) && sortedLt (b :: l)
  | _ => true

theorem sortedLt_tail {a : ℕ} {l : List ℕ} (h : sortedLt (a :: l) = true) : sortedLt l = true := by
  match l, h with
  | [], _ => rfl
  | b :: l, h =>
    simp only [sortedLt, Bool.and_eq_true] at h
    exact h.2

theorem lt_of_sortedLt : ∀ {a : ℕ} {l : List ℕ}, sortedLt (a :: l) = true → ∀ x ∈ l, a < x
  | _, [], _, _, hx => absurd hx List.not_mem_nil
  | a, b :: l, h, x, hx => by
    have h' := h
    simp only [sortedLt, Bool.and_eq_true, decide_eq_true_eq] at h'
    rcases List.mem_cons.1 hx with rfl | hx
    · exact h'.1
    · exact h'.1.trans (lt_of_sortedLt (sortedLt_tail h) x hx)

theorem nodup_of_sortedLt : ∀ {l : List ℕ}, sortedLt l = true → l.Nodup
  | [], _ => List.nodup_nil
  | a :: _, h => List.nodup_cons.2 ⟨fun ha ↦ lt_irrefl a (lt_of_sortedLt h a ha), nodup_of_sortedLt (sortedLt_tail h)⟩

/-- The literal table's facts: the copies' ranges, increasing destinations, the count. -/
theorem fillTabL18_ok : fillTabL18.all (cpOK 33554432 67108864) = true ∧
    sortedLt (fillTabL18.map fun e ↦ e.2.2) = true ∧ fillTabL18.length = 148 := by
  decide +kernel

/-- **The fill block's static facts** (kernel: `srcs18_facts` and the literals). -/
theorem fill18_ok : fillTab18.all (cpOK 33554432 67108864) = true ∧ (fillTab18.map fun e ↦ e.2.2).Nodup ∧
    reqs18.all reqOK = true ∧ srcs18.length = (opsOf P18.levs (sched6 P18)).length ∧
    0 < ops18.length ∧ ops18.length ≤ (opsOf P18.levs (sched6 P18)).length ∧ fillTab18.length = 148 := by
  have hL : srcs18.length = (opsOf P18.levs (sched6 P18)).length := by
    unfold srcs18; exact length_srcsOp _ _ _ _ _ _ _ _
  have hR : reqs18.all reqOK = true := by
    rw [reqOK_eq, srcs18_facts.2.2.2.2, all_getD_drop srcs18 default 5037 (srcOK 1076) reqs18 reqs18_ge,
      srcs18_facts.2.1]
    unfold reqs18; rw [srcs18_facts.1]; decide +kernel
  rw [fillTab18_eq]
  exact ⟨fillTabL18_ok.1, nodup_of_sortedLt fillTabL18_ok.2.1, hR, hL, srcs18_facts.2.2.1, srcs18_facts.2.2.2.1,
    fillTabL18_ok.2.2⟩

theorem wf_fillIR18 : WF fillIR18 := by unfold fillIR18; generalize fillTab18 = tab; exact wf_cpsIR tab
theorem noLoopT_fillIR18 : NoLoopT fillIR18 := by unfold fillIR18; generalize fillTab18 = tab; exact noLoopT_cpsIR tab
theorem outs_fillIR18 (t : ℕ) : outs fillIR18 t = 0 := by unfold fillIR18; exact outs_cpsIR t fillTab18
theorem hasOut_fillIR18 : hasOut fillIR18 = false := by unfold fillIR18; exact hasOut_cpsIR fillTab18

/-- **The fill block's cost**: at most `3,112` steps. -/
theorem cost_fillIR18 (t : ℕ) : cost fillIR18 t ≤ 3112 := by
  have h := cost_cpsIR t fillTab18
  rw [fill18_ok.2.2.2.2.2.2] at h
  unfold fillIR18
  exact h

/-- **The fill block's size**: at most `3,112` statements. -/
theorem sizeIR_fillIR18 : sizeIR fillIR18 ≤ 3112 := by
  have h := sizeIR_cpsIR fillTab18
  rw [fill18_ok.2.2.2.2.2.2] at h
  unfold fillIR18
  exact h

end Lvm6.X
