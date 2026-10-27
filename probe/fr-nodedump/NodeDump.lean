-- S-E2 node dump (dev-only, outside the entry): the node's M rows (`compileMux (gen fin .mux)` per
-- slot) with the register → cell map, L's rows and bit cells, and `nodeLayout`'s kind intervals.
import FRVIRFinalsSF
import FRNodeLayout

open FR FR.Layout FR.Circ

/-- The finals as the IR dump uses them (S-G's `finP`, `finPf` pending). -/
def fins : Finals := sfFinals (fun _ => pending) pending

def hexF (x : F) : String :=
  String.join ((F.toBytes x).toList.map fun b =>
    let s := String.mk (Nat.toDigits 16 b.toNat); if s.length < 2 then "0" ++ s else s)

def linStr (l : Lin) : String := " ".intercalate (l.map fun t => s!"{t.1}:{hexF t.2}")

def tyStr : Ty → String
  | .f => "F" | .k => "K" | .bit => "Bit" | .d => "D" | .af n => s!"AF{n}" | .ak n => s!"AK{n}"

def dumpRows (h : IO.FS.Handle) (rows : List Row) : IO Unit := do
  let mut i := 0
  for r in rows do
    h.putStrLn s!"{i} | {linStr r.a} | {linStr r.b} | {linStr r.c}"
    i := i + 1

def main (args : List String) : IO UInt32 := do
  let out := args.headD "."
  -- (c) the layout
  IO.FS.withFile s!"{out}/layout.txt" .write fun h => do
    h.putStrLn s!"# kind lo hi (blocks, [lo, hi)); oneCell {oneCell}; Mbase {mBase}; Lbase {lBase}; wmBase {wmBase} (WM {wmSlot} per slot)"
    for iv in nodeLayout do h.putStrLn s!"{repr iv.kind} {iv.lo} {iv.hi}"
  -- (b) L
  IO.FS.withFile s!"{out}/lrows.txt" .write fun h => do
    h.putStrLn s!"# L bit cells: slot 0 from {(lBitCells 0).headD 0}, slot 1 from {(lBitCells 1).headD 0}, {(lBitCells 0).length} each (digits 133, selectors 399, position bits 7552, kind selector 3); rows b·(one − b) = 0"
    dumpRows h lRows
  -- (a) M, per slot
  for σ in [0, 1] do
    let cs := slotCS fins σ
    IO.FS.withFile s!"{out}/mrows-{σ}.txt" .write fun h => do
      h.putStrLn s!"# slot {σ}: base {slotBase σ}, next {cs.next}, rows {cs.rows.length}, sel cells {selCells σ .L32} {selCells σ .P30} {selCells σ .N30}; row | A | B | C (cell:coef hex LE)"
      dumpRows h cs.rowList
    IO.FS.withFile s!"{out}/mregs-{σ}.txt" .write fun h => do
      h.putStrLn s!"# register | import? | type | one linear form per F component (cell:coef)"
      let imps := cs.imp
      let mut i := 0
      for sl in cs.slots.toList do
        match sl with
        | none => h.putStrLn s!"{i} | - | untracked"
        | some (t, ls) =>
          h.putStrLn s!"{i} | {if imps.contains i then "imp" else "-"} | {tyStr t} | {" ; ".intercalate (ls.map linStr)}"
        i := i + 1
    IO.println s!"slot {σ}: {cs.rows.length} rows, {cs.next - slotBase σ} cells, {cs.imp.length} import regs, {cs.fors.length} foreign"
  return 0
