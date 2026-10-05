import Lean

/-! Fails when a module under the default target's source tree is outside the
import closure of that target's roots, since `lake build` never elaborates it.

    lean --run scripts/CheckClosure.lean [repo-dir]
    lean --run scripts/CheckClosure.lean --self-test -/

open Lean System

def trimmed (s : String) : String := s.trimAscii.toString

/-- Roots of the single `@[default_target]` library, read from the lakefile text. -/
def defaultRoots (lakefile : String) : Except String (Array Name) := do
  let parts := lakefile.splitOn "@[default_target]"
  unless parts.length == 2 do
    throw s!"expected one @[default_target], found {parts.length - 1}"
  let decl := (parts[1]!.splitOn "\n\n")[0]!
  let afterRoots := decl.splitOn "roots := #["
  unless afterRoots.length == 2 do
    throw "the default target declares no `roots := #[...]`"
  let list := (afterRoots[1]!.splitOn "]")[0]!
  let names ← (list.splitOn ",").toArray.mapM fun tok => do
    let t := trimmed tok
    unless t.startsWith "`" do throw s!"unparsed root `{t}`"
    let raw := (t.drop 1).toString.replace "«" "" |>.replace "»" ""
    pure raw.toName
  if names.isEmpty then throw "the default target has no roots"
  pure names

def modFile (dir : FilePath) (m : Name) : FilePath :=
  (m.components.foldl (fun p c => p / c.toString) dir).addExtension "lean"

def modOfPath (dir path : FilePath) : Name :=
  let rel := (path.toString.drop (dir.toString.length + 1)).toString
  let noExt := (rel.dropEnd 5).toString
  (noExt.splitOn "/").foldl Name.str Name.anonymous

/-- Modules reachable from `roots` through imports whose source lies under `dir`. -/
partial def closure (dir : FilePath) (roots : Array Name) : IO (Std.HashSet Name) := do
  let mut seen : Std.HashSet Name := {}
  let mut todo := roots.toList
  for r in roots do
    unless ← (modFile dir r).pathExists do
      throw <| IO.userError s!"root {r} has no source at {modFile dir r}"
  while true do
    match todo with
    | [] => break
    | m :: rest =>
      todo := rest
      if seen.contains m then continue
      let f := modFile dir m
      unless ← f.pathExists do continue
      seen := seen.insert m
      let hdr ← parseImports' (← IO.FS.readFile f) f.toString
      todo := todo ++ (hdr.imports.map (·.module)).toList
  pure seen

/-- Source modules under each root's top-level tree that the closure misses. -/
def orphans (dir : FilePath) : IO (Array Name × Nat) := do
  let roots ← match defaultRoots (← IO.FS.readFile (dir / "lakefile.lean")) with
    | .ok r => pure r
    | .error e => throw <| IO.userError s!"lakefile.lean: {e}"
  let reach ← closure dir roots
  let tops := (roots.map (·.getRoot)).toList.eraseDups
  let mut srcs : Array Name := #[]
  for t in tops do
    let top := modFile dir t
    if ← top.pathExists then srcs := srcs.push t
    let sub := dir / t.toString
    if ← sub.isDir then
      for p in ← sub.walkDir do
        if p.extension == some "lean" then srcs := srcs.push (modOfPath dir p)
  if srcs.isEmpty then throw <| IO.userError "no source modules found under the roots"
  let out := srcs.filter (!reach.contains ·)
  pure (out.qsort (·.toString < ·.toString), srcs.size)

def report (dir : FilePath) : IO UInt32 := do
  let (out, total) ← orphans dir
  for m in out do IO.println s!"outside closure: {m}"
  IO.println s!"{total - out.size} of {total} modules in the default import closure, {out.size} outside"
  pure (if out.isEmpty then 0 else 1)

def writeTree (dir : FilePath) (files : List (String × String)) : IO Unit := do
  for (rel, body) in files do
    let p := dir / rel
    if let some parent := p.parent then IO.FS.createDirAll parent
    IO.FS.writeFile p body

def lakeP : String := "@[default_target]\nlean_lib «P» where\n  roots := #[`P]\n"

def base : List (String × String) :=
  [("lakefile.lean", lakeP),
   ("P.lean", "/- import P.Orphan -/\nimport Lean\nimport P.A\n-- import P.Orphan\n"),
   ("P/A.lean", "import P.Sub.B\n"),
   ("P/Sub/B.lean", "def b := 1\n")]

def selfTest : IO UInt32 := do
  let mut failed := 0
  let cases : List (String × List (String × String) × Option (Array Name)) :=
    [("all imported passes", base, some #[]),
     ("planted orphan fails", base ++ [("P/Orphan.lean", "def o := 0\n")], some #[`P.Orphan]),
     ("nested orphan fails", base ++ [("P/Sub/Deep/C.lean", "def c := 0\n")], some #[`P.Sub.Deep.C]),
     ("no default target fails", base ++ [("lakefile.lean", "lean_lib «P» where\n  roots := #[`P]\n")], none),
     ("missing root source fails", base.filter (·.1 != "P.lean"), none)]
  for (label, files, want) in cases do
    let got ← IO.FS.withTempDir fun d => do
      writeTree d files
      try
        let (o, _) ← orphans d
        pure (some o)
      catch _ => pure none
    let ok := got == want
    IO.println s!"{if ok then "ok  " else "FAIL"} {label}: got {repr got}"
    unless ok do failed := failed + 1
  IO.println s!"{cases.length - failed} of {cases.length} controls hold"
  pure (if failed == 0 then 0 else 1)

def main (args : List String) : IO UInt32 := do
  match args with
  | ["--self-test"] => selfTest
  | [] => report "."
  | [d] => report d
  | _ => IO.eprintln "usage: CheckClosure.lean [--self-test | repo-dir]"; pure 2
