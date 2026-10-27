-- Dev-only dump tool (BLUEPRINT §8, A.8): outside the entry, a compiled `main`, no elaboration-time
-- code. `irdump items` prints the item sequence as JSON; `irdump ops L|P|N|M` prints `gen`'s ops of
-- a kind (or the mux) one per line, `opName operands… → dst`, registers numbered; `irdump summary`
-- prints the counts. The phase-final checks are `gen`'s parameter; the dump uses none
-- (`noFinals`), so it pins the skeleton: every query, challenge map and round check.
import FRVIRFinalsSF

open FR RecursionFast

/-- The finals: S-0's four fields and S-F's (`sfFinals`); S-G's `finP`, `finPf` are pending (marked in
the dump; S-G's private copy `logs/fr-build-SG/dump/IRDumpSG.lean` dumps them). -/
def fins : Finals := sfFinals (fun _ => pending) pending

def hex (l : List UInt8) : String :=
  String.join (l.map fun b =>
    let s := String.ofList (Nat.toDigits 16 b.toNat)
    if s.length = 1 then "0" ++ s else s)

def kindName : Kind → String
  | .L32 => "L" | .P30 => "P" | .N30 => "N"

def kinds : List Kind := [.L32, .P30, .N30]

def showVal : Val → String
  | .f x => "F:" ++ hex x.toBytes.toList
  | .k x => "K:" ++ hex x.toBytes.toList
  | .d x => "D:" ++ hex x.toList
  | .b x => "B:" ++ hex x.data.toList
  | .n x => "N:" ++ toString x
  | .bit x => "Bit:" ++ toString x
  | .af xs => "AF:[" ++ ",".intercalate (xs.toList.map fun x => hex x.toBytes.toList) ++ "]"
  | .ak xs => "AK:[" ++ ",".intercalate (xs.toList.map fun x => hex x.toBytes.toList) ++ "]"
  | _ => "arr"

/-- A kind-dependent datum: the kind's value, or all three for the mux. -/
def showKC {α : Type} (sh : α → String) (m : Mode) (c : KC α) : String :=
  match m with
  | .fixed κ => sh (c κ)
  | .mux => "{" ++ ", ".intercalate (kinds.map fun κ => kindName κ ++ ":" ++ sh (c κ)) ++ "}"

def r (i : ℕ) : String := "r" ++ toString i

def outs : Op → ℕ := Op.outs

def showOp (m : Mode) : Op → String
  | .input w => s!"input {w}"
  | .const c => "const " ++ showKC showVal m c
  | .piField f o len => s!"piField {f} {o} {len}"
  | .piElem f o => s!"piElem {f} {o}"
  | .piElemK f o => s!"piElemK {f} {o}"
  | .piDigest f o => s!"piDigest {f} {o}"
  | .piDigestAt f o k => s!"piDigestAt {f} {o} {r k}"
  | .mkAbsorb xs => "mkAbsorb " ++ " ".intercalate (xs.map r)
  | .askSeed h => s!"askSeed {r h}"
  | .askAbsorb st msg len => s!"askAbsorb {r st} {r msg} {len}"
  | .askSqueeze st => s!"askSqueeze {r st}"
  | .askNode i h l rr act => s!"askNode {i} {h} {r l} {r rr} " ++ showKC toString m act
  | .askCol i col => s!"askCol {i} {r col}"
  | .chF a c => s!"chF {r a} {c}"
  | .chK a => s!"chK {r a}"
  | .idx a b i => "idx " ++ showKC r m a ++ " " ++ showKC toString m b ++ " " ++ showKC toString m i
  | .bitOf n h => s!"bitOf {r n} {h}"
  | .shrN n s => s!"shrN {r n} " ++ showKC toString m s
  | .mulF a b => s!"mulF {r a} {r b}"
  | .addF a b => s!"addF {r a} {r b}"
  | .mulK a b => s!"mulK {r a} {r b}"
  | .addK a b => s!"addK {r a} {r b}"
  | .mulKF a b => s!"mulKF {r a} {r b}"
  | .invF a => s!"invF {r a}"
  | .packF xs => "packF " ++ " ".intercalate (xs.map r)
  | .packK xs => "packK " ++ " ".intercalate (xs.map r)
  | .packFK xs => "packFK " ++ showKC (fun l => "[" ++ " ".intercalate (l.map r) ++ "]") m xs
  | .getF a i => s!"getF {r a} {i}"
  | .getK a i => s!"getK {r a} {i}"
  | .eqTable x => s!"eqTable {r x}"
  | .eqTableK x => s!"eqTableK {r x}"
  | .dotKF w c => s!"dotKF {r w} {r c}"
  | .lagrangeS v l pe => s!"lagrangeS {r v} {r l} {r pe}"
  | .targetS x => s!"targetS {r x}"
  | .eqZ x y => s!"eqZ {r x} {r y}"
  | .tensorW j x => s!"tensorW {r j} {r x}"
  | .rsWeight x ps k y =>
    s!"rsWeight {r x} " ++ showKC (fun l => "[" ++ " ".intercalate (l.map r) ++ "]") m ps ++ s!" {r k} {r y}"
  | .phiRS x a => s!"phiRS {r x} {r a}"
  | .walkA x c => s!"walkA {r x} {r c}"
  | .walkB x c => s!"walkB {r x} {r c}"
  | .kindInd x => s!"kindInd {r x}"
  | .maskRows k w => s!"maskRows {r k} {r w}"
  | .evalM t s => s!"evalM {r t} {r s}"
  | .evalL t s => s!"evalL {r t} {r s}"
  | .evalMK t s => s!"evalMK {r t} {r s}"
  | .shiftTarget t h bd => s!"shiftTarget {r t} {r h} {r bd}"
  | .slotW sm t x => s!"slotW {sm} {r t} {r x}"
  | .kindFoldWeight x b y => s!"kindFoldWeight {r x} {r b} {r y}"
  | .eqPt a b => s!"eqPt {r a} {r b}"
  | .rowW l h => s!"rowW {r l} {r h}"
  | .shiftEq t x => s!"shiftEq {r t} {r x}"
  | .linkW t f p => s!"linkW {r t} {f} {r p}"
  | .splitDigest d => s!"splitDigest {r d}"
  | .selectHalf b x y => s!"selectHalf {r b} {r x} {r y}"
  | .keep act n o => "keep " ++ showKC toString m act ++ s!" {r n} {r o}"
  | .hashStmt s => "hashStmt " ++ showKC kindName m (fun κ => κ) ++ s!" {r s}"
  | .kindSel => "kindSel"
  | .assertEq a b act => s!"assertEq {r a} {r b} " ++ showKC toString m act
  | .assertBit a act => s!"assertBit {r a} " ++ showKC toString m act
  | .assertZero a act => s!"assertZero {r a} " ++ showKC toString m act
  | .assertOneHot a b c => s!"assertOneHot {r a} {r b} {r c}"
  | .accept => "accept"

def dumpList (m : Mode) (ops : List Op) (n0 : ℕ) : IO ℕ := do
  let mut n := n0
  for op in ops do
    let k := outs op
    let dst := if k = 0 then "" else " → " ++ " ".intercalate ((List.range k).map (fun i => r (n + i)))
    IO.println (showOp m op ++ dst)
    n := n + k
  return n

/-- The skeleton, then each final field with a header line; pending fields are marked. -/
def dumpOps (m : Mode) : IO Unit := do
  let n ← dumpList m skeleton.1 0
  let outs := skeleton.2.outs
  let rs := fins.finRS ⟨outs, [], #[]⟩ n
  IO.println "-- final finRS (S-F)"
  let mut b ← dumpList m rs.1 n
  let names := ["finZ", "finLc", "finSh", "finLr", "finE (S-F)", "finB' (S-F)"] ++ (List.range nLevels).map (fun i => s!"finP {i} (S-G): PENDING placeholder") ++
    ["finPf (S-G): PENDING placeholder"]
  let mut ex : Array (List Reg) := #[rs.2]
  for (f, nm) in fins.rest.zip names do
    let x := f ⟨outs, rs.2, ex⟩ b
    IO.println s!"-- final {nm}"
    b ← dumpList m x.1 b
    ex := ex.push x.2
  IO.println "accept"

def itemJson : Item → String
  | .seed => "{\"q\":\"seed\",\"qlen\":119}"
  | .absorb len => s!"\{\"q\":\"absorb\",\"len\":{len},\"qlen\":{(Item.absorb len).qlen}}"
  | .squeeze => "{\"q\":\"squeeze\",\"qlen\":40}"
  | .col i => s!"\{\"q\":\"col\",\"level\":{i},\"qlen\":{(Item.col i).qlen}}"
  | .node i h => s!"\{\"q\":\"node\",\"level\":{i},\"depth\":{h},\"qlen\":72}"

def dumpItems : IO Unit := do
  IO.println "["
  let ps := phases
  let mut first := true
  for p in ps do
    for it in p.shape.items do
      let line := "{\"phase\":\"" ++ p.name ++ "\"," ++ ((itemJson it).drop 1).toString
      IO.println ((if first then " " else ",") ++ line)
      first := false
  IO.println "]"

def main (args : List String) : IO UInt32 := do
  match args with
  | ["items"] => dumpItems; return 0
  | ["ops", k] =>
    let m := match k with
      | "L" => Mode.fixed .L32 | "P" => .fixed .P30 | "N" => .fixed .N30 | _ => .mux
    dumpOps m; return 0
  | ["summary"] =>
    let P := gen fins .mux
    let asks := P.ops.filterMap Op.item?
    IO.println s!"ops {P.ops.length}; registers {skeleton.2.next}; asks {asks.length}; items {items.length}; asks = items: {decide (asks = items)}"
    IO.println s!"fieldSizes {fieldSizes}; piSize {piSize}; streamBytes {streamBytes}; chainLen {chainLen}"
    return 0
  | _ => IO.eprintln "usage: irdump items | ops L|P|N|M | summary"; return 1
