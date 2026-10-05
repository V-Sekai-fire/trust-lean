import TrustLean.MicroC.Int64Eval
import TrustLean.MicroRust.PrettyPrint
import TrustLean.Backend.RustBackend

/-! Fails unless the Rust that `microRustExprToString` and `exprToRust` print for the two casts
compiles under `rustc` and prints what the evaluators say, with the operand both a literal and an
`i64` variable. rustc types an unsuffixed literal by the cast it sits under, so a spelling that
is right for a variable can still fail to compile for a literal.

    lake build && lake env lean --run scripts/CheckRustCasts.lean
    lake env lean --run scripts/CheckRustCasts.lean --self-test -/

open TrustLean System

structure Case where
  label : String
  a : Int
  rustExpr : String
  expected : Option Value

def values : List Int :=
  [-2 ^ 63, -1, 0, 2 ^ 31 - 1, 2 ^ 31, 2 ^ 32 - 1, 2 ^ 32, 2 ^ 63 - 1]

def casts : List (String × MicroCUnaryOp) :=
  [("widen32to64", .widen32to64), ("trunc64to32", .trunc64to32)]

def microRustCase (op : MicroCUnaryOp) (operand : MicroCExpr) (a : Int) (label : String) : Case :=
  { label, a, rustExpr := microRustExprToString (.unaryOp op operand),
    expected := evalMicroCUnaryOp_int64 op (.int a) }

def backendCase (op : MicroCUnaryOp) (operand : LowLevelExpr) (a : Int) (label : String) : Case :=
  let op := microCUnaryOpToCore op
  { label, a, rustExpr := exprToRust (.unaryOp op operand), expected := evalUnaryOp op (.int a) }

def matrix : List Case := Id.run do
  let mut out := []
  for (s, op) in casts do
    for a in values do
      out := microRustCase op (.litInt a) a s!"microRust {s} literal {a}" :: out
      out := microRustCase op (.varRef "a") a s!"microRust {s} variable {a}" :: out
      out := backendCase op (.litInt a) a s!"backend {s} literal {a}" :: out
      out := backendCase op (.varRef (.user "a")) a s!"backend {s} variable {a}" :: out
  return out.reverse

def program (c : Case) : String :=
  s!"fn main() \{\n    let a: i64 = {microRustExprToString (.litInt c.a)};\n" ++
    s!"    let _ = a;\n    println!(\"\{}\", {c.rustExpr});\n}\n"

inductive Verdict | agree | disagree (why : String)

def judge (c : Case) (rustc run : IO.Process.Output) : Verdict :=
  let want := match c.expected with
    | some (.int n) => toString n
    | some (.bool b) => toString b
    | none => "none"
  if rustc.exitCode != 0 then
    let err := (rustc.stderr.splitOn "\n").find? (·.startsWith "error") |>.getD ""
    .disagree s!"model {want}, rustc exit {rustc.exitCode}: {err}"
  else
    let printed := run.stdout.trimAscii.toString
    if run.exitCode == 0 && printed == want then .agree
    else .disagree s!"model {want}, Rust exit {run.exitCode} printed '{printed}'"

/-- Compiles and runs each case in its own program, so one case that fails to compile does not
    hide the others. -/
def run (cases : Array Case) : IO (Array Verdict) :=
  IO.FS.withTempDir fun d => do
    let tasks ← cases.mapIdxM fun i c => IO.asTask do
      let src := d / s!"case{i}.rs"
      let exe := d / s!"case{i}"
      IO.FS.writeFile src (program c)
      let rustc ← IO.Process.output {
        cmd := "rustc", args := #["--edition", "2021", src.toString, "-o", exe.toString] }
      if rustc.exitCode != 0 then return judge c rustc { exitCode := 0, stdout := "", stderr := "" }
      return judge c rustc (← IO.Process.output { cmd := exe.toString })
    tasks.mapM fun t => do IO.ofExcept (← IO.wait t)

def report (cases : Array Case) : IO UInt32 := do
  let vs ← run cases
  let mut bad := 0
  for c in cases, v in vs do
    if let .disagree why := v then
      bad := bad + 1
      IO.println s!"FAIL {c.label} `{c.rustExpr}`: {why}"
  IO.println s!"{cases.size} cases: {cases.size - bad} agree, {bad} disagree"
  pure (if bad == 0 then 0 else 1)

def replaceAll (s pat rep : String) : String := rep.intercalate (s.splitOn pat)

/-- Each control pairs a case with whether it must agree. The failing ones plant the earlier
    spellings: `as u32` alone types a literal operand as u32, and `as i64`/`as i32` sign-extend. -/
def controls : List (String × Case × Bool) :=
  let widenLit := microRustCase .widen32to64 (.litInt (-1)) (-1) "widen literal -1"
  let truncLit := microRustCase .trunc64to32 (.litInt (2 ^ 32)) (2 ^ 32) "trunc literal 2^32"
  let widenVar := backendCase .widen32to64 (.varRef (.user "a")) (-1) "widen variable -1"
  let truncVar := backendCase .trunc64to32 (.varRef (.user "a")) (2 ^ 31) "trunc variable 2^31"
  let respell (c : Case) (cast : String) : Case :=
    let now := if c.label.startsWith "widen" then " as i64 as u32 as i64)" else " as i64 as u32)"
    { c with rustExpr := replaceAll c.rustExpr now (cast ++ ")") }
  [("as i64 as u32 as i64 at literal -1 agrees", widenLit, true),
   ("as i64 as u32 at literal 4294967296 agrees", truncLit, true),
   ("as u32 as i64 at literal -1 disagrees", respell widenLit " as u32 as i64", false),
   ("as u32 at literal 4294967296 disagrees", respell truncLit " as u32", false),
   ("as i64 at variable -1 disagrees", respell widenVar " as i64", false),
   ("as i32 at variable 2147483648 disagrees", respell truncVar " as i32", false)]

def selfTest : IO UInt32 := do
  let vs ← run (controls.map (·.2.1)).toArray
  let mut failed := 0
  for (label, c, want) in controls, v in vs do
    let (agreed, detail) := match v with
      | .agree => (true, "agree")
      | .disagree why => (false, why)
    let ok := agreed == want
    IO.println s!"{if ok then "ok  " else "FAIL"} {label} (`{c.rustExpr}`): {detail}"
    unless ok do failed := failed + 1
  IO.println s!"{controls.length - failed} of {controls.length} controls hold"
  pure (if failed == 0 then 0 else 1)

def main (args : List String) : IO UInt32 := do
  match args with
  | ["--self-test"] => selfTest
  | [] => report matrix.toArray
  | _ => IO.eprintln "usage: CheckRustCasts.lean [--self-test]"; pure 2
