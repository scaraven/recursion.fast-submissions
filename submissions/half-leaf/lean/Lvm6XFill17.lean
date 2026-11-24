-- lvm6 X1 (PORT17): the fill block at `P17` (`Lvm6XFill18` at `P17`, KDX's memo pattern): the opening's operations
-- read off the schedule (`ops17`, checked against `opsP17`), the requests (`reqsOf` at `fg17`), the sources of the
-- opening as a 303-entry literal (`srcsO17`, one evaluation of L1's `srcsP17`), the table as a 140-entry literal.
import Lvm6XFillG
import Lvm6XLv18
import Lvm6XFront17
import Lvm6XCostG
import Lvm6P17MemoX

/-!
# The fill block at `P17`

* **`ops17 = openOpsOf rndD tails17 8 2 2`**: the tails `tailOps nh ht 32 ko kq i` with `(nh, ht, ko, kq)` = `(6, 19, 17, 18)`, `(4, 18, 13, 7)`,
  `(4, 17, 9, 3)`, `(4, 16, 5, 2)` (FORMAT6 v2.6 §6.6), 8 final scalars, 2 tail rounds: 303 operations, and
  **`srcs17_facts`**: they are the schedule's last 303 (`(opsOf P17.levs (sched6 P17)).drop 4983 = ops17`); W1's
  `P17` opening follows exactly these: **`opsD_eq_ops17`** (W1's `opsD` at `P17`, `rfl`).
* **`srcs17`** (`= srcsP17`, L1), **`N17 = 4983`**, **`fg17 = ⟨rndD, |tails17 ·|, 8, N17⟩`**, **`F17`** (`FDep`'s cells,
  in `[2^25, 2^26)`), **`reqs17`**, **`fillTab17`**, **`fillIR17 := cpsIR fillTab17`**.
* **`fill17_ok`** (`fill_ok`'s statement at `P17`): the copies' ranges, distinct destinations (`sortedLt`), every
  request's source a chain draw or a 16-byte word-aligned read of π (`srcOKAt 230,424 1,055`), the sources' count,
  the opening inside the history, **140** copies. `cost_fillIR17`, `sizeIR_fillIR17`: at most 2,944.
* **`budget17F`**: `budget17` with the fill's `2,944 + 1` steps.
-/

set_option autoImplicit false

namespace Lvm6.X

open RecursionFast Lvm Lvm.X Lvm6.Whir Lvm6.FD

/-! ## The opening's operations -/

/-- **The tails at `P17`**: `(nh, ht, ko, kq)` per level (the next tree's height, `ko + 1` OOD draws, `kq + 1`
position draws). -/
def tails17 : ℕ → List Op
  | 0 => tailOps 6 19 32 17 18 0
  | 1 => tailOps 4 18 32 13 7 1
  | 2 => tailOps 4 17 32 9 3 2
  | _ => tailOps 4 16 32 5 2 3

/-- **The opening's operations at `P17`.** -/
def ops17 : List Op := openOpsOf rndD tails17 8 2 2

/-- **W1's opening (`Lvm6WhirFollow.opsD`, at `P17`) is `ops17`**: derived independently, equal by `rfl`. -/
theorem opsD_eq_ops17 : opsD = ops17 := rfl

/-! ## The cells and the requests -/

/-- **The sources of the `P17` replay's events**, from π offset `hdrLen` and chain position 1. -/
def srcs17 : List Src :=
  srcsOp (V.capOfL P17.levs) (V.occL P17.levs) tP17 [] (V.widths (sched6 P17)) (hdrLen P17) 1
    (opsOf P17.levs (sched6 P17))

theorem srcs17_eq : srcs17 = srcsP17 := srcsOp_P17

/-- The opening's first event in the history. -/
def N17 : ℕ := (opsOf P17.levs (sched6 P17)).length - ops17.length

/-- **The request geometry at `P17`.** -/
def fg17 : FillGeo := ⟨rndD, fun i ↦ (tails17 i).length, 8, N17⟩

/-- **The cells the front fills at `P17`**: `FDep`'s, in `[2^25, 2^26)`. -/
def F17 : FrontA := ⟨fun i k ↦ 33554432 + 32 * i + 4 * k, fun i ↦ 33554688 + 16 * i, 33554944⟩

/-- **The requests at `P17`.** -/
def reqs17 : List (ℕ × ℕ) := reqsOf fg17 F17.ch F17.hi F17.s

/-- **The copies at `P17`.** -/
def fillTab17 : List (Bool × ℕ × ℕ) := fillTabOf srcs17 fg17 F17.ch F17.hi F17.s

/-- **The fill block at `P17`.** -/
@[irreducible] def fillIR17 : XIR := cpsIR fillTab17

/-! ## The static facts, one evaluation of the sources -/

/-- The opening's sources at `P17`: `srcs17` from event `N17 = 4983` on (`srcs17_facts`). -/
def srcsO17 : List Src :=
  [.rd 63408 16, .rd 63424 16, .rd 63440 16, .rd 63456 16, .rd 63472 8, .smp 916, .smp 917, .rd 63480 16,
   .rd 63496 16, .rd 63512 16, .rd 63528 16, .rd 63544 8, .smp 918, .smp 919, .rd 63552 16, .rd 63568 16,
   .rd 63584 16, .rd 63600 16, .rd 63616 8, .smp 920, .smp 921, .rd 63624 16, .rd 63640 16, .rd 63656 16,
   .rd 63672 16, .rd 63688 8, .smp 922, .smp 923, .rd 63696 16, .rd 63712 16, .rd 63728 16, .rd 63744 16, .rd 63760 8,
   .smp 924, .smp 925, .rd 63768 16, .rd 63784 16, .rd 63800 16, .rd 63816 16, .rd 63832 8, .smp 926, .smp 927,
   .rd 63840 16, .rd 63856 16, .rd 63872 16, .rd 63888 16, .rd 63904 16, .rd 63920 16, .cap, .smp 928, .rd 65984 8,
   .smp 929, .smp 930, .smp 931, .smp 932, .smp 933, .smp 934, .smp 935, .smp 936, .smp 937, .smp 938, .smp 939,
   .smp 940, .smp 941, .smp 942, .smp 943, .smp 944, .smp 945, .smp 946, .rd 65992 16, .rd 66008 8, .smp 947,
   .smp 948, .smp 949, .smp 950, .smp 951, .smp 952, .smp 953, .smp 954, .smp 955, .smp 956, .smp 957, .smp 958,
   .smp 959, .smp 960, .smp 961, .smp 962, .smp 963, .smp 964, .smp 965, .smp 966, .opn, .rd 152256 16, .rd 152272 16,
   .rd 152288 16, .rd 152304 16, .rd 152320 8, .smp 967, .smp 968, .rd 152328 16, .rd 152344 16, .rd 152360 16,
   .rd 152376 16, .rd 152392 8, .smp 969, .smp 970, .rd 152400 16, .rd 152416 16, .rd 152432 16, .rd 152448 16,
   .rd 152464 8, .smp 971, .smp 972, .rd 152472 16, .rd 152488 16, .rd 152504 16, .rd 152520 16, .rd 152536 8,
   .smp 973, .smp 974, .rd 152544 16, .rd 152560 16, .rd 152576 16, .rd 152592 16, .cap, .smp 975, .rd 153632 8,
   .smp 976, .smp 977, .smp 978, .smp 979, .smp 980, .smp 981, .smp 982, .smp 983, .smp 984, .smp 985, .smp 986,
   .smp 987, .smp 988, .smp 989, .rd 153640 16, .rd 153656 8, .smp 990, .smp 991, .smp 992, .smp 993, .smp 994,
   .smp 995, .smp 996, .smp 997, .smp 998, .opn, .rd 183904 16, .rd 183920 16, .rd 183936 16, .rd 183952 16,
   .rd 183968 8, .smp 999, .smp 1000, .rd 183976 16, .rd 183992 16, .rd 184008 16, .rd 184024 16, .rd 184040 8,
   .smp 1001, .smp 1002, .rd 184048 16, .rd 184064 16, .rd 184080 16, .rd 184096 16, .rd 184112 8, .smp 1003,
   .smp 1004, .rd 184120 16, .rd 184136 16, .rd 184152 16, .rd 184168 16, .rd 184184 8, .smp 1005, .smp 1006,
   .rd 184192 16, .rd 184208 16, .rd 184224 16, .rd 184240 16, .cap, .smp 1007, .rd 185280 8, .smp 1008, .smp 1009,
   .smp 1010, .smp 1011, .smp 1012, .smp 1013, .smp 1014, .smp 1015, .smp 1016, .smp 1017, .rd 185288 16,
   .rd 185304 8, .smp 1018, .smp 1019, .smp 1020, .smp 1021, .smp 1022, .opn, .rd 204128 16, .rd 204144 16,
   .rd 204160 16, .rd 204176 16, .rd 204192 8, .smp 1023, .smp 1024, .rd 204200 16, .rd 204216 16, .rd 204232 16,
   .rd 204248 16, .rd 204264 8, .smp 1025, .smp 1026, .rd 204272 16, .rd 204288 16, .rd 204304 16, .rd 204320 16,
   .rd 204336 8, .smp 1027, .smp 1028, .rd 204344 16, .rd 204360 16, .rd 204376 16, .rd 204392 16, .rd 204408 8,
   .smp 1029, .smp 1030, .rd 204416 16, .rd 204432 16, .rd 204448 16, .rd 204464 16, .cap, .smp 1031, .rd 205504 8,
   .smp 1032, .smp 1033, .smp 1034, .smp 1035, .smp 1036, .smp 1037, .rd 205512 16, .rd 205528 8, .smp 1038,
   .smp 1039, .smp 1040, .smp 1041, .opn, .rd 218976 16, .rd 218992 16, .rd 219008 16, .rd 219024 16, .rd 219040 8,
   .smp 1042, .smp 1043, .rd 219048 16, .rd 219064 16, .rd 219080 16, .rd 219096 16, .rd 219112 8, .smp 1044,
   .smp 1045, .rd 219120 16, .rd 219136 16, .rd 219152 16, .rd 219168 16, .rd 219184 8, .smp 1046, .smp 1047,
   .rd 219192 16, .rd 219208 16, .rd 219224 16, .rd 219240 16, .rd 219256 8, .smp 1048, .smp 1049, .rd 219264 16,
   .rd 219280 16, .rd 219296 16, .rd 219312 16, .rd 219328 16, .rd 219344 16, .rd 219360 16, .rd 219376 16,
   .rd 219392 8, .smp 1050, .smp 1051, .smp 1052, .opn, .rd 230344 16, .rd 230360 16, .rd 230376 8, .smp 1053,
   .rd 230384 16, .rd 230400 16, .rd 230416 8, .smp 1054]

/-- **The copies at `P17`**, as a literal (`fillTab17_eq`). -/
def fillTabL17 : List (Bool × ℕ × ℕ) :=
  [(true, 16797264, 33554432), (true, 16797265, 33554433), (true, 16797268, 33554434), (true, 16797269, 33554435),
   (true, 16797272, 33554436), (true, 16797273, 33554437), (true, 16797276, 33554438), (true, 16797277, 33554439),
   (true, 16797280, 33554440), (true, 16797281, 33554441), (true, 16797284, 33554442), (true, 16797285, 33554443),
   (true, 16797288, 33554444), (true, 16797289, 33554445), (true, 16797292, 33554446), (true, 16797293, 33554447),
   (true, 16797296, 33554448), (true, 16797297, 33554449), (true, 16797300, 33554450), (true, 16797301, 33554451),
   (true, 16797304, 33554452), (true, 16797305, 33554453), (true, 16797308, 33554454), (true, 16797309, 33554455),
   (true, 16797468, 33554464), (true, 16797469, 33554465), (true, 16797472, 33554466), (true, 16797473, 33554467),
   (true, 16797476, 33554468), (true, 16797477, 33554469), (true, 16797480, 33554470), (true, 16797481, 33554471),
   (true, 16797484, 33554472), (true, 16797485, 33554473), (true, 16797488, 33554474), (true, 16797489, 33554475),
   (true, 16797492, 33554476), (true, 16797493, 33554477), (true, 16797496, 33554478), (true, 16797497, 33554479),
   (true, 16797596, 33554496), (true, 16797597, 33554497), (true, 16797600, 33554498), (true, 16797601, 33554499),
   (true, 16797604, 33554500), (true, 16797605, 33554501), (true, 16797608, 33554502), (true, 16797609, 33554503),
   (true, 16797612, 33554504), (true, 16797613, 33554505), (true, 16797616, 33554506), (true, 16797617, 33554507),
   (true, 16797620, 33554508), (true, 16797621, 33554509), (true, 16797624, 33554510), (true, 16797625, 33554511),
   (true, 16797692, 33554528), (true, 16797693, 33554529), (true, 16797696, 33554530), (true, 16797697, 33554531),
   (true, 16797700, 33554532), (true, 16797701, 33554533), (true, 16797704, 33554534), (true, 16797705, 33554535),
   (true, 16797708, 33554536), (true, 16797709, 33554537), (true, 16797712, 33554538), (true, 16797713, 33554539),
   (true, 16797716, 33554540), (true, 16797717, 33554541), (true, 16797720, 33554542), (true, 16797721, 33554543),
   (true, 16797768, 33554560), (true, 16797769, 33554561), (true, 16797772, 33554562), (true, 16797773, 33554563),
   (true, 16797776, 33554564), (true, 16797777, 33554565), (true, 16797780, 33554566), (true, 16797781, 33554567),
   (true, 16797784, 33554568), (true, 16797785, 33554569), (true, 16797788, 33554570), (true, 16797789, 33554571),
   (true, 16797792, 33554572), (true, 16797793, 33554573), (true, 16797796, 33554574), (true, 16797797, 33554575),
   (false, 7985, 33554688), (false, 7986, 33554689), (false, 7987, 33554690), (false, 7988, 33554691),
   (false, 7989, 33554692), (false, 7990, 33554693), (false, 7991, 33554694), (false, 7992, 33554695),
   (false, 7993, 33554696), (false, 7994, 33554697), (false, 7995, 33554698), (false, 7996, 33554699),
   (false, 19073, 33554704), (false, 19074, 33554705), (false, 19075, 33554706), (false, 19076, 33554707),
   (false, 19077, 33554708), (false, 19078, 33554709), (false, 19079, 33554710), (false, 19080, 33554711),
   (false, 23029, 33554720), (false, 23030, 33554721), (false, 23031, 33554722), (false, 23032, 33554723),
   (false, 23033, 33554724), (false, 23034, 33554725), (false, 23035, 33554726), (false, 23036, 33554727),
   (false, 25557, 33554736), (false, 25558, 33554737), (false, 25559, 33554738), (false, 25560, 33554739),
   (false, 25561, 33554740), (false, 25562, 33554741), (false, 25563, 33554742), (false, 25564, 33554743),
   (false, 27413, 33554944), (false, 27414, 33554945), (false, 27415, 33554946), (false, 27416, 33554947),
   (false, 27417, 33554948), (false, 27418, 33554949), (false, 27419, 33554950), (false, 27420, 33554951),
   (false, 27421, 33554952), (false, 27422, 33554953), (false, 27423, 33554954), (false, 27424, 33554955),
   (false, 27425, 33554956), (false, 27426, 33554957), (false, 27427, 33554958), (false, 27428, 33554959)]

/-- The replay's facts at `P17`, one evaluation of L1's literals: the opening starts at event 4,983, its sources are
`srcsO17` and its operations are `ops17`. -/
theorem srcs17_facts : N17 = 4983 ∧ srcs17.drop 4983 = srcsO17 ∧
    (opsOf P17.levs (sched6 P17)).drop 4983 = ops17 ∧ 0 < ops17.length ∧
    ops17.length ≤ (opsOf P17.levs (sched6 P17)).length := by
  unfold N17
  rw [srcs17_eq, opsOf_P17]
  decide +kernel

/-- The requests' events lie in the opening. -/
theorem reqs17_ge : reqs17.all (fun r => decide (4983 ≤ r.1)) = true := by
  unfold reqs17 fg17; rw [srcs17_facts.1]; decide +kernel

/-- **`fillTab17` is `fillTabL17`**, its lookups read from `srcsO17`. -/
theorem fillTab17_eq : fillTab17 = fillTabL17 := by
  rw [fillTab17, fillTabOf_drop srcs17 fg17 F17.ch F17.hi F17.s 4983 reqs17_ge, srcs17_facts.2.1]
  unfold fg17; rw [srcs17_facts.1]; decide +kernel

/-- The literal table's facts: the copies' ranges, increasing destinations, the count. -/
theorem fillTabL17_ok : fillTabL17.all (cpOK 33554432 67108864) = true ∧
    sortedLt (fillTabL17.map fun e ↦ e.2.2) = true ∧ fillTabL17.length = 140 := by
  decide +kernel

/-- **The fill block's static facts at `P17`** (`fill_ok`'s statement). -/
theorem fill17_ok : fillTab17.all (cpOK 33554432 67108864) = true ∧ (fillTab17.map fun e ↦ e.2.2).Nodup ∧
    reqs17.all (fun r => srcOKAt xg17.pz (nCh6 P17) (srcs17.getD r.1 default)) = true ∧
    srcs17.length = (opsOf P17.levs (sched6 P17)).length ∧
    0 < ops17.length ∧ ops17.length ≤ (opsOf P17.levs (sched6 P17)).length ∧ fillTab17.length = 140 := by
  have hL : srcs17.length = (opsOf P17.levs (sched6 P17)).length := by
    unfold srcs17; exact length_srcsOp _ _ _ _ _ _ _ _
  have hR : reqs17.all (fun r => srcOKAt xg17.pz (nCh6 P17) (srcs17.getD r.1 default)) = true := by
    rw [nCh6_P17, all_getD_drop srcs17 default 4983 (srcOKAt xg17.pz 1055) reqs17 reqs17_ge, srcs17_facts.2.1]
    unfold reqs17 fg17; rw [srcs17_facts.1]; decide +kernel
  rw [fillTab17_eq]
  exact ⟨fillTabL17_ok.1, nodup_of_sortedLt fillTabL17_ok.2.1, hR, hL, srcs17_facts.2.2.2.1,
    srcs17_facts.2.2.2.2, fillTabL17_ok.2.2⟩

theorem wf_fillIR17 : WF fillIR17 := by unfold fillIR17; generalize fillTab17 = tab; exact wf_cpsIR tab
theorem noLoopT_fillIR17 : NoLoopT fillIR17 := by unfold fillIR17; generalize fillTab17 = tab; exact noLoopT_cpsIR tab
theorem outs_fillIR17 (t : ℕ) : outs fillIR17 t = 0 := by unfold fillIR17; exact outs_cpsIR t fillTab17
theorem hasOut_fillIR17 : hasOut fillIR17 = false := by unfold fillIR17; exact hasOut_cpsIR fillTab17

/-- **The fill block's cost at `P17`**: at most `2,944` steps. -/
theorem cost_fillIR17 (t : ℕ) : cost fillIR17 t ≤ 2944 := by
  have h := cost_cpsIR t fillTab17
  rw [fill17_ok.2.2.2.2.2.2] at h
  unfold fillIR17
  exact h

/-- **The fill block's size at `P17`**: at most `2,944` statements. -/
theorem sizeIR_fillIR17 : sizeIR fillIR17 ≤ 2944 := by
  have h := sizeIR_cpsIR fillTab17
  rw [fill17_ok.2.2.2.2.2.2] at h
  unfold fillIR17
  exact h

/-- **`budget17` with the fill's `2,944 + 1` steps.** -/
theorem budget17F :
    lvBAt ht17 0 6 191 6 + lvBAt ht17 1 4 128 1 + lvBAt ht17 2 4 128 1 + lvBAt ht17 3 4 128 1 +
      lvBAt ht17 4 4 128 1 + finCap + 5 + 2945 ≤ descCostAt ht17 + 2 ^ 43 := by
  simp only [lvBAt, descCostAt, descLvlAt, rds, lns, ht17, lamCost, laneCost, treeC, levelC, parentC, bflyC, fwdC,
    wtabC, trCap, ldCap, finCap]
  norm_num

end Lvm6.X
