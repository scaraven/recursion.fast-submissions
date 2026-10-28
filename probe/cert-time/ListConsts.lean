/-
  H-cert probe tooling (outside the entry; never on the badge path). Lists the constants that the
  modules matching a prefix declare, split by kind, for the comparator's `theorem_names` and
  `definition_names`:
    lake env lean --run ListConsts.lean ROOT PREFIX OUTDIR
  writes OUTDIR/theorems.txt, OUTDIR/definitions.txt, OUTDIR/other.txt (kind, name) and
  OUTDIR/per-module.tsv (module, theorems, definitions, other). Internal, private and
  non-round-tripping names are skipped: the export's dependency closure brings in what they are
  used by.
-/
import Lean
open Lean

def main (args : List String) : IO Unit := do
  let [root, pre, out] := args | throw <| .userError "usage: ROOT PREFIX OUTDIR"
  initSearchPath (← findSysroot)
  let env ← importModules #[{ module := root.toName }] {} (loadExts := false)
  let mods := env.header.moduleNames
  let mut thms : Array String := #[]
  let mut defs : Array String := #[]
  let mut oth : Array String := #[]
  let mut per : Std.HashMap Name (Nat × Nat × Nat) := {}
  let mut skipped := 0
  for (n, ci) in env.constants.map₁.toList do
    let some idx := env.getModuleIdxFor? n | continue
    let m := mods[idx.toNat]!
    unless (m.toString.startsWith pre) do continue
    let s := n.toString
    if n.isInternal || isPrivateName n || s.toName != n || s.contains '«' then
      skipped := skipped + 1
      continue
    let (a, b, c) := per.getD m (0, 0, 0)
    match ci with
    | .thmInfo _ => thms := thms.push s; per := per.insert m (a + 1, b, c)
    | .defnInfo _ => defs := defs.push s; per := per.insert m (a, b + 1, c)
    | _ =>
      let k := match ci with
        | .axiomInfo _ => "axiom" | .opaqueInfo _ => "opaque" | .inductInfo _ => "inductive"
        | .ctorInfo _ => "ctor" | .recInfo _ => "rec" | .quotInfo _ => "quot" | _ => "?"
      oth := oth.push s!"{k} {s}"; per := per.insert m (a, b, c + 1)
  IO.FS.writeFile (out ++ "/theorems.txt") (String.intercalate "\n" thms.toList ++ "\n")
  IO.FS.writeFile (out ++ "/definitions.txt") (String.intercalate "\n" defs.toList ++ "\n")
  IO.FS.writeFile (out ++ "/other.txt") (String.intercalate "\n" oth.toList ++ "\n")
  let rows := per.toList.map fun (m, a, b, c) => s!"{m}\t{a}\t{b}\t{c}"
  IO.FS.writeFile (out ++ "/per-module.tsv") (String.intercalate "\n" rows ++ "\n")
  IO.println s!"modules {per.size}, theorems {thms.size}, definitions {defs.size}, other {oth.size}, skipped {skipped}"
