import TrustLean.MicroC.UnsignedSimulation

/-! Fails unless the C that `microCToString` prints for `uint32_t` statements over an array
computes what `evalS32` says, which `evalMicroC_uint32_eq_evalS32` equates with
`evalMicroC_uint32`. Each case declares its variables `uint32_t` or `bool` with their starting
values and `uint32_t buf[8]`, runs the printed statement, and prints the variables and cells it
names, under `clang -std=c11 -Wall -Werror -fsanitize=undefined -fno-sanitize-recover=undefined`.
A defined model must be what C prints; `none` must make UBSan stop the program.

    lake build && lake env lean --run scripts/CheckS32C.lean
    lake env lean --run scripts/CheckS32C.lean --self-test -/

open TrustLean System

inductive Model | values (lines : List String) | undefined | abrupt
  deriving BEq

structure Case where
  label : String
  vars : List (String × V32)
  cells : List (Nat × UInt32)
  body : MicroCStmt
  shown : List String
  word : String := "uint32_t"
  model : Option Model := none

def Case.store (c : Case) : Store32 := fun x =>
  match c.vars.lookup x with
  | some v => v
  | none =>
    match c.cells.find? (fun p => x == cell32 "buf" (UInt32.ofNat p.1)) with
    | some (_, w) => .w w
    | none => .w 0

def showV32 (n : String) : V32 → String
  | .w x => s!"{n}={x.toNat}"
  | .b b => s!"{n}={if b then 1 else 0}"

def Case.expected (c : Case) : Model :=
  c.model.getD <|
    match evalS32 1000 c.store c.body with
    | some (.normal, ρ) => .values (c.shown.map fun n => showV32 n (ρ n))
    | some _ => .abrupt
    | none => .undefined

def Case.isBool (c : Case) (n : String) : Bool :=
  match c.vars.lookup n with
  | some (.b _) => true
  | _ => false

def Case.cFunction (c : Case) (i : Nat) : String := Id.run do
  let mut src := s!"static void case_{i}(void) \{\n"
  for (x, v) in c.vars do
    src := src ++ match v with
      | .w w => s!"  {c.word} {x} = {w.toNat}u; (void){x};\n"
      | .b b => s!"  bool {x} = {if b then "true" else "false"}; (void){x};\n"
  src := src ++ s!"  {c.word} buf[8] = \{0}; (void)buf;\n"
  for (k, w) in c.cells do
    src := src ++ s!"  buf[{k}] = {w.toNat}u;\n"
  src := src ++ "  " ++ microCToString c.body ++ "\n"
  for n in c.shown do
    src := src ++
      if c.isBool n then s!"  printf(\"{n}=%d\\n\", (int){n});\n"
      else s!"  printf(\"{n}=%lld\\n\", (long long){n});\n"
  src ++ "}\n\n"

def program (cases : Array Case) : String := Id.run do
  let mut src := "#include <stdint.h>\n#include <stdbool.h>\n#include <stdio.h>\n#include <stdlib.h>\n\n"
  for c in cases, i in [0:cases.size] do
    src := src ++ c.cFunction i
  src := src ++ "int main(int argc, char **argv) {\n  if (argc != 2) return 2;\n" ++
    "  switch (atoi(argv[1])) {\n"
  for i in [0:cases.size] do
    src := src ++ s!"  case {i}: case_{i}(); break;\n"
  src ++ "  default: return 2;\n  }\n  return 0;\n}\n"

/-! ## Statements -/

def v (x : String) : MicroCExpr := .varRef x
def lit (n : Int) : MicroCExpr := .litInt n
def bin (op : MicroCBinOp) (l r : MicroCExpr) : MicroCExpr := .binOp op l r

/-- `occ = tail - head; if (0 < occ) { x = buf[head & (cap - 1)]; head = head + 1; ok = true; }
    else { ok = false; }` -/
def popK : MicroCStmt :=
  .seq (.assign "occ" (bin .sub (v "tail") (v "head")))
   (.ite (bin .ltOp (lit 0) (v "occ"))
     (.seq (.load "x" (v "buf") (bin .band (v "head") (bin .sub (v "cap") (lit 1))))
       (.seq (.assign "head" (bin .add (v "head") (lit 1)))
             (.assign "ok" (.litBool true))))
     (.assign "ok" (.litBool false)))

/-- Sums `buf[0..n)` with a wrapping accumulator. -/
def sumK : MicroCStmt :=
  .seq (.assign "i" (lit 0))
   (.seq (.assign "acc" (lit 0))
     (.while_ (bin .ltOp (v "i") (v "n"))
       (.seq (.assign "acc" (bin .add (v "acc") (.arrayAccess (v "buf") (v "i"))))
             (.assign "i" (bin .add (v "i") (lit 1))))))

def ring (head tail : UInt32) : List (String × V32) :=
  [("head", .w head), ("tail", .w tail), ("cap", .w 8), ("v", .w 42), ("occ", .w 0),
   ("x", .w 0), ("ok", .b false)]

def pushWrap : Case :=
  { label := "push across the 2^32 wrap", vars := ring 4294967294 4294967295, cells := [],
    body := pushK, shown := ["tail", "occ", "ok", "buf[7]"] }

def shl (n : UInt32) : Case :=
  { label := s!"x << {n}", vars := [("x", .w 3), ("n", .w n)], cells := [],
    body := .assign "x" (bin .bshl (v "x") (v "n")), shown := ["x"] }

def cases : Array Case := #[
  pushWrap,
  { label := "push into a full ring", vars := ring 5 13, cells := [], body := pushK,
    shown := ["tail", "occ", "ok", "buf[5]"] },
  { label := "push into an empty ring", vars := ring 0 0, cells := [], body := pushK,
    shown := ["tail", "occ", "ok", "buf[0]"] },
  { label := "pop across the 2^32 wrap", vars := ring 4294967295 0, cells := [(7, 99)],
    body := popK, shown := ["head", "occ", "ok", "x"] },
  { label := "pop from an empty ring", vars := ring 7 7, cells := [(7, 99)], body := popK,
    shown := ["head", "occ", "ok", "x"] },
  { label := "wrapping sum over buf", vars := [("i", .w 0), ("n", .w 3), ("acc", .w 0)],
    cells := [(0, 4294967295), (1, 4294967295), (2, 5)], body := sumK, shown := ["acc", "i"] },
  { label := "negate, xor, or, right shift",
    vars := [("x", .w 5), ("y", .w 0), ("z", .w 0)], cells := [],
    body := .seq (.assign "y" (.unaryOp .neg (v "x")))
      (.seq (.assign "z" (bin .bxor (v "y") (bin .bor (v "x") (lit 1073741824))))
        (.assign "x" (bin .bshr (v "y") (lit 28)))),
    shown := ["x", "y", "z"] },
  shl 31,
  shl 40]

/-! ## clang -/

/-- The first `clang` on `PATH` outside the Lean toolchain, whose bundled clang has no libc
    headers or sanitizer runtime. -/
def systemClang : IO FilePath := do
  let leanBin := (← IO.appPath).parent
  let dirs := ((← IO.getEnv "PATH").getD "").splitOn ":" |>.map FilePath.mk
  for d in dirs do
    if some d != leanBin && (← (d / "clang").pathExists) then return d / "clang"
  throw <| IO.userError "no clang on PATH outside the Lean toolchain"

def ubsanReport (stderr : String) : Option String :=
  match stderr.splitOn "runtime error: " with
  | _ :: msg :: _ => (msg.splitOn "\n").head?
  | _ => none

inductive Verdict | agree | disagree (why : String)

def judge (m : Model) (out : IO.Process.Output) : Verdict :=
  let printed := (out.stdout.trimAscii.toString.splitOn "\n").filter (· ≠ "")
  match m with
  | .values want =>
    if out.exitCode == 0 && printed == want then .agree
    else .disagree s!"model {want}, C exit {out.exitCode} printed {printed} {(ubsanReport out.stderr).getD ""}"
  | .undefined =>
    if out.exitCode != 0 && (ubsanReport out.stderr).isSome then .agree
    else .disagree s!"model none, C exit {out.exitCode} printed {printed} without a UBSan report"
  | .abrupt => .disagree "the model ended in break, continue, return or out of fuel"

/-- Compiles one program for `cases`, runs each case, and returns the verdicts in order. -/
def run (cases : Array Case) : IO (Array Verdict) :=
  IO.FS.withTempDir fun d => do
    IO.FS.writeFile (d / "s32.c") (program cases)
    let exe := d / "s32"
    let cc ← IO.Process.output {
      cmd := (← systemClang).toString,
      args := #["-std=c11", "-Wall", "-Werror", "-fsanitize=undefined",
        "-fno-sanitize-recover=undefined", (d / "s32.c").toString, "-o", exe.toString] }
    if cc.exitCode != 0 then
      throw <| IO.userError s!"clang failed with exit {cc.exitCode}:\n{cc.stderr}"
    let tasks ← cases.mapIdxM fun i c => IO.asTask do
      return judge c.expected (← IO.Process.output { cmd := exe.toString, args := #[toString i] })
    tasks.mapM fun t => do IO.ofExcept (← IO.wait t)

def report (cases : Array Case) : IO UInt32 := do
  let vs ← run cases
  let mut bad := 0
  for c in cases, verdict in vs do
    match verdict with
    | .agree => IO.println s!"ok   {c.label}"
    | .disagree why =>
      bad := bad + 1
      IO.println s!"FAIL {c.label}: {why}"
  IO.println s!"{cases.size} cases: {cases.size - bad} agree, {bad} disagree"
  pure (if bad == 0 then 0 else 1)

/-- Each control pairs a case with whether it must agree. The failing ones declare `int64_t`,
    the type `CBackend` prints, take the model from the unbounded `evalMicroC`, or wrap the shift
    that C11 leaves undefined. -/
def controls : List (String × Case × Bool) :=
  let unbounded : Model :=
    match evalMicroC 1000 (V32.lift ∘ pushWrap.store) pushK with
    | some (.normal, env) => .values (pushWrap.shown.map fun n => match env n with
      | .int i => s!"{n}={i}"
      | .bool b => s!"{n}={if b then 1 else 0}")
    | _ => .undefined
  [("the wrap under uint32_t agrees", pushWrap, true),
   ("the wrap under int64_t declarations disagrees", { pushWrap with word := "int64_t" }, false),
   ("the unbounded evalMicroC model of the wrap disagrees", { pushWrap with model := unbounded },
     false),
   ("x << 40 is none and UBSan reports it", shl 40, true),
   ("x << 40 wrapping to 0 disagrees", { shl 40 with model := some (.values ["x=0"]) }, false)]

def selfTest : IO UInt32 := do
  let vs ← run (controls.map (·.2.1)).toArray
  let mut failed := 0
  for (label, _, want) in controls, verdict in vs do
    let (agreed, detail) := match verdict with
      | .agree => (true, "agree")
      | .disagree why => (false, why)
    let ok := agreed == want
    IO.println s!"{if ok then "ok  " else "FAIL"} {label}: {detail}"
    unless ok do failed := failed + 1
  IO.println s!"{controls.length - failed} of {controls.length} controls hold"
  pure (if failed == 0 then 0 else 1)

def main (args : List String) : IO UInt32 := do
  match args with
  | ["--self-test"] => selfTest
  | [] => report cases
  | _ => IO.eprintln "usage: CheckS32C.lean [--self-test]"; pure 2
