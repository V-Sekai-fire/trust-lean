import TrustLean.Frontend.ImpStmt.Compile
import TrustLean.Backend.CBackend

/-! Exports `acc = 1² + 2² + … + n²` as C to `examples/out/`, builds it with `examples/driver.c`
under `cc -std=c11 -Wall -Werror`, and fails unless the program prints what `ImpStmt.eval` computes.
`--self-test` compares against a wrong value and fails unless that comparison fails.

    lake build && lake env lean --run examples/Export.lean -/

open TrustLean

def names (v : VarId) : String := ["n", "i", "acc"].getD v s!"v{v}"

def sumSquares : ImpStmt :=
  .seq (.assign 1 (.lit 0)) <| .seq (.assign 2 (.lit 0)) <|
    .while (.lt_ (.var 1) (.var 0)) <|
      .seq (.assign 1 (.add (.var 1) (.lit 1))) (.assign 2 (.add (.var 2) (.mul (.var 1) (.var 1))))

def input : Int := 100

def model : Option Int :=
  (sumSquares.eval 1000 fun v => if v = 0 then input else 0).map (· 2)

def cfg : CConfig := { includePowerHelper := false }

def source : String :=
  generateCHeader cfg ++ "\n\n" ++ generateCFunction cfg "sum_squares" [("n", "int64_t")]
    (sumSquares.compile names) (.varRef (.user "acc")) ++ "\n"

def runC : IO String := do
  IO.FS.createDirAll "examples/out"
  IO.FS.writeFile "examples/out/sum_squares.c" source
  let cc ← IO.Process.output { cmd := "cc", args := #["-std=c11", "-Wall", "-Werror",
    "examples/out/sum_squares.c", "examples/driver.c", "-o", "examples/out/sum_squares"] }
  if cc.exitCode != 0 then throw <| IO.userError s!"cc failed:\n{cc.stderr}"
  let run ← IO.Process.output { cmd := "examples/out/sum_squares", args := #[toString input] }
  if run.exitCode != 0 then throw <| IO.userError s!"sum_squares exited {run.exitCode}"
  pure run.stdout.trimAscii.toString

def main (args : List String) : IO UInt32 := do
  let some want := model | throw <| IO.userError "the model ran out of fuel"
  let selfTest := args == ["--self-test"]
  let expected := if selfTest then want + 1 else want
  let printed ← runC
  let ok := (printed == toString expected) != selfTest
  let claim := if !selfTest then s!"the Lean model computes {expected}"
    else s!"the wrong value {expected} {if ok then "fails" else "passes"} the comparison"
  IO.println s!"{if ok then "ok  " else "FAIL"} sum_squares({input}) printed {printed}; {claim}"
  pure (if ok then 0 else 1)
