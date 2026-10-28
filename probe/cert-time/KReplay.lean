/-
  H-cert probe tooling (outside the entry): the comparator's kernel step with a per-declaration
  clock. It imports ROOT, takes the dependency closure of the names in NAMEDIR/theorems.txt and
  NAMEDIR/definitions.txt (what lean4export exports for the comparator), and replays it into an
  empty kernel environment as `Lean.Kernel.Environment.replay` does (the comparator's
  `runBuiltinKernel`), timing each `addDeclCore`. Writes OUT: one line per declaration sent to the
  kernel, `nanoseconds<TAB>module<TAB>name`, and prints the totals.
    lake env lean --run KReplay.lean ROOT NAMEDIR OUT
-/
import Lean
open Lean

structure St where
  env : Kernel.Environment
  remaining : NameSet := {}
  pending : NameSet := {}
  rows : Array (Nat × Name) := #[]

abbrev M := ReaderT (Std.HashMap Name ConstantInfo) <| StateRefT St IO

def isTodo (n : Name) : M Bool := do
  if (← get).remaining.contains n then
    modify fun s => { s with remaining := s.remaining.erase n, pending := s.pending.insert n }
    return true
  return false

def addD (n : Name) (d : Declaration) : M Unit := do
  let t0 ← IO.monoNanosNow
  match (← get).env.addDeclCore 0 0 d (cancelTk? := none) with
  | .ok env =>
    let t1 ← IO.monoNanosNow
    modify fun s => { s with env, rows := s.rows.push (t1 - t0, n) }
  | .error _ => throw <| .userError s!"kernel rejects {n}"

mutual
partial def replayConstant (name : Name) : M Unit := do
  if ← isTodo name then
    let some ci := (← read)[name]? | throw <| .userError s!"missing {name}"
    replayConstants ci.getUsedConstantsAsSet
    if (← get).pending.contains name then
      match ci with
      | .defnInfo i => addD name (.defnDecl i)
      | .thmInfo i => addD name (.thmDecl i)
      | .axiomInfo i => addD name (.axiomDecl i)
      | .opaqueInfo i => addD name (.opaqueDecl i)
      | .inductInfo i =>
        let all ← i.all.mapM fun n => do pure ((← read)[n]!)
        for o in all do
          modify fun s => { s with remaining := s.remaining.erase o.name, pending := s.pending.erase o.name }
        let ctorInfo ← all.mapM fun ci => do
          pure (ci, ← ci.inductiveVal!.ctors.mapM fun n => do pure ((← read)[n]!))
        for (_, ctors) in ctorInfo do
          for c in ctors do replayConstants c.getUsedConstantsAsSet
        let types : List InductiveType := ctorInfo.map fun ⟨ci, ctors⟩ =>
          { name := ci.name, type := ci.type, ctors := ctors.map fun c => { name := c.name, type := c.type } }
        addD name (.inductDecl i.levelParams i.numParams types false)
      | .ctorInfo _ | .recInfo _ => pure ()
      | .quotInfo _ => replayConstant `Eq; addD name .quotDecl
      modify fun s => { s with pending := s.pending.erase name }

partial def replayConstants (names : NameSet) : M Unit := do
  for n in names do replayConstant n
end

def main (args : List String) : IO Unit := do
  let [root, dir, out] := args | throw <| .userError "usage: ROOT NAMEDIR OUT"
  initSearchPath (← findSysroot)
  let env ← importModules #[{ module := root.toName }] {} (loadExts := false)
  let rd (f : String) : IO (List Name) := do
    return (← IO.FS.lines (dir ++ "/" ++ f)).toList.filter (· ≠ "") |>.map String.toName
  let targets := (← rd "theorems.txt") ++ (← rd "definitions.txt") ++
    [`propext, `Classical.choice, `Quot.sound, `Quot, `Quot.mk, `Quot.lift, `Quot.ind]
  -- the closure, as lean4export collects it (types, values, and an inductive's constructors)
  let t0 ← IO.monoMsNow
  let mut seen : Std.HashMap Name ConstantInfo := {}
  let mut todo := targets.toArray
  while h : todo.size > 0 do
    let n := todo.back
    todo := todo.pop
    if seen.contains n then continue
    let some ci := env.find? n | throw <| .userError s!"not found {n}"
    seen := seen.insert n ci
    for m in ci.getUsedConstantsAsSet do
      unless seen.contains m do todo := todo.push m
    match ci with
    | .inductInfo i => for c in i.ctors ++ i.all do todo := todo.push c
    | .ctorInfo i => todo := todo.push i.induct
    | .recInfo i => for c in i.all do todo := todo.push c
    | _ => pure ()
  let t1 ← IO.monoMsNow
  IO.println s!"closure: {seen.size} constants in {t1 - t0} ms"
  let mut remaining : NameSet := {}
  for (n, ci) in seen.toList do
    if !ci.isUnsafe && !ci.isPartial then remaining := remaining.insert n
  let empty ← mkEmptyEnvironment
  let (_, s) ← (do for n in remaining do replayConstant n : M Unit).run seen |>.run
    { env := empty.toKernelEnv, remaining }
  let t2 ← IO.monoMsNow
  let mods := env.header.moduleNames
  let modOf (n : Name) : String :=
    match env.getModuleIdxFor? n with
    | some i => (mods[i.toNat]!).toString
    | none => "?"
  let total := s.rows.foldl (fun a (t, _) => a + t) 0
  let lines := s.rows.toList.map fun (t, n) => s!"{t}\t{modOf n}\t{n}"
  IO.FS.writeFile out (String.intercalate "\n" lines ++ "\n")
  IO.println s!"replay: {s.rows.size} declarations, wall {t2 - t1} ms, in the kernel {total / 1000000} ms"
