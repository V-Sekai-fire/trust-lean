import Lean

/-! Fails unless `scripts/vacuity/Vacuity.lean`, a proof that `VarNameInjective` is false, stops
compiling for the right reason: `decide` refutes every collision it claims and nothing else errors.

    lake build && lake env lean --run scripts/CheckVacuity.lean
    lean --run scripts/CheckVacuity.lean --self-test -/

open Lean System

def controlFile : FilePath := "scripts" / "vacuity" / "Vacuity.lean"

/-- The collisions the control claims, as `decide` prints them. -/
def claims : List String := [
  "varNameToC (VarName.user \"int\") = varNameToC (VarName.user \"tl_int\")",
  "varNameToC (VarName.temp 0) = varNameToC (VarName.user \"t0\")"]

/-- The proposition a `decide` refutation names, or `none` for any other message. -/
def refuted (data : String) : Option String :=
  match data.splitOn "\n" with
  | hd :: rest@(_ :: _) =>
    if hd == "Tactic `decide` proved that the proposition" && rest.getLast? == some "is false" then
      some (" ".intercalate (rest.dropLast.map (·.trimAscii.toString)))
    else none
  | _ => none

structure Compiled where
  exitCode : UInt32
  errors : Array String
  stderr : String

/-- Compiles `file` with the running `lean` and collects the data of its error messages. -/
def compile (file : FilePath) (cwd : Option FilePath := none) : IO Compiled := do
  let out ← IO.Process.output {
    cmd := (← IO.appPath).toString, args := #["--json", file.toString], cwd }
  let errors := (out.stdout.splitOn "\n").toArray.filterMap fun line =>
    match Json.parse line with
    | .ok j =>
      match j.getObjValAs? String "severity", j.getObjValAs? String "data" with
      | .ok "error", .ok d => some d
      | _, _ => none
    | .error _ => none
  pure { exitCode := out.exitCode, errors, stderr := out.stderr }

/-- Every reason the control does not fail as expected; empty when it does. -/
def problems (c : Compiled) (claims : List String) : List String :=
  let props := c.errors.filterMap refuted
  (if c.exitCode == 0 then ["the control compiled"] else []) ++
  (c.errors.filter (refuted · |>.isNone)).toList.map (s!"error other than a decide refutation: {·}") ++
  (claims.filter (!props.contains ·)).map (s!"claim not refuted by decide: {·}") ++
  (props.filter (!claims.contains ·)).toList.map (s!"refuted proposition is not a listed claim: {·}")

def report (c : Compiled) : IO UInt32 := do
  match problems c claims with
  | [] =>
    IO.println s!"ok   {controlFile} fails: decide refutes all {claims.length} collisions it claims"
    pure 0
  | ps =>
    for p in ps do IO.println s!"FAIL {p}"
    unless c.stderr.isEmpty do IO.println c.stderr
    pure 1

def toyClaims : List String := ["f \"a\" = f \"b\"", "f \"c\" = f \"d\""]

def injectiveF : String := "def f (s : String) : String := s\n"

def refutations : String :=
  "theorem t1 : f \"a\" = f \"b\" := by decide\n" ++
  "example : f \"c\" = f \"d\" := by decide\n"

/-- Compiles `src` in a temp dir and returns whether it passes as a control for `toyClaims`. -/
def passes (src : String) : IO Bool :=
  IO.FS.withTempDir fun d => do
    IO.FS.writeFile (d / "P.lean") ("set_option autoImplicit false\n" ++ src)
    return (problems (← compile "P.lean" d) toyClaims).isEmpty

def selfTest : IO UInt32 := do
  let cases : List (String × String × Bool) :=
    [("every claim refuted passes", injectiveF ++ refutations, true),
     ("a collision that compiles fails",
       "def f (s : String) : String := if s == \"b\" then \"a\" else s\n" ++ refutations, false),
     ("an unrelated error fails", injectiveF ++ refutations ++ "example : g = 1 := rfl\n", false),
     ("a claim left unrefuted fails", injectiveF ++ "theorem t1 : f \"a\" = f \"b\" := by decide\n", false),
     ("a refutation outside the claims fails",
       injectiveF ++ refutations ++ "example : f \"e\" = f \"g\" := by decide\n", false),
     ("a missing import fails", "import Absent.Module\n" ++ injectiveF ++ refutations, false),
     ("a file that compiles fails", injectiveF, false)]
  let mut failed := 0
  for (label, src, want) in cases do
    let got ← passes src
    let ok := got == want
    IO.println s!"{if ok then "ok  " else "FAIL"} {label}: passes = {got}"
    unless ok do failed := failed + 1
  IO.println s!"{cases.length - failed} of {cases.length} controls hold"
  pure (if failed == 0 then 0 else 1)

def main (args : List String) : IO UInt32 := do
  match args with
  | ["--self-test"] => selfTest
  | [] => report (← compile controlFile)
  | _ => IO.eprintln "usage: CheckVacuity.lean [--self-test]"; pure 2
