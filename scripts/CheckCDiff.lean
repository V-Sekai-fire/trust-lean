import TrustLean.MicroC.Int64Eval
import TrustLean.MicroC.UnsignedEval
import TrustLean.MicroC.PrettyPrint

/-! Fails unless the C that `microCExprToString` prints for the casts and integer operators
computes what the evaluators say. Each case declares `volatile` operands `a` and `b` of the
evaluator's C type, prints one expression over them, and runs under
`clang -std=c11 -fsanitize=undefined -fno-sanitize-recover=undefined`. A defined model value must
be what C prints; `none` must make UBSan stop the program. A right shift of a negative `int64_t`
is implementation-defined (C11 6.5.7p5), so UBSan cannot flag it; those cases are counted apart.

    lake build && lake env lean --run scripts/CheckCDiff.lean
    lake env lean --run scripts/CheckCDiff.lean --self-test -/

open TrustLean System

inductive Ty | i64 | u32 | u64
  deriving BEq, Repr

def Ty.name : Ty → String
  | .i64 => "int64" | .u32 => "uint32" | .u64 => "uint64"

def Ty.cType : Ty → String
  | .i64 => "int64_t" | .u32 => "uint32_t" | .u64 => "uint64_t"

def Ty.holds : Ty → Int → Bool
  | .i64, n => decide (InInt64Range n)
  | .u32, n => 0 ≤ n && n < 2 ^ 32
  | .u64, n => 0 ≤ n && n < 2 ^ 64

def Ty.cLit : Ty → Int → String
  | .i64, n => if n == minInt64 then "(-9223372036854775807LL - 1)" else s!"{n}LL"
  | .u32, n => s!"{n}u"
  | .u64, n => s!"{n}ULL"

def Ty.eval : Ty → MicroCEnv → MicroCExpr → Option Value
  | .i64 => evalMicroCExpr_int64
  | .u32 => evalMicroCExpr_uint32
  | .u64 => evalMicroCExpr_uint64

structure Case where
  label : String
  ty : Ty
  a : Int
  b : Int
  cExpr : String
  expected : Option Value
  implDefined : Bool

def env (a b : Int) : MicroCEnv := fun s => if s == "a" then .int a else if s == "b" then .int b else .int 0

def mkCase (ty : Ty) (e : MicroCExpr) (a b : Int) (label : String) : Case :=
  let expected := ty.eval (env a b) e
  let implDefined := match ty, e with
    | .i64, .binOp .bshr _ _ => expected.isNone && a < 0 && 0 ≤ b && b < 64
    | _, _ => false
  { label, ty, a, b, cExpr := microCExprToString e, expected, implDefined }

def values : List Int :=
  [-2 ^ 63, -1, 0, 2 ^ 31 - 1, 2 ^ 31, 2 ^ 32 - 1, 2 ^ 32, 2 ^ 63 - 1]

def counts : List Int := [-1, 0, 1, 31, 32, 40, 63, 64]

def binOps : List (String × MicroCBinOp) :=
  [("+", .add), ("-", .sub), ("*", .mul), ("&", .band), ("|", .bor), ("^", .bxor),
   ("==", .eqOp), ("<", .ltOp)]

def shiftOps : List (String × MicroCBinOp) := [("<<", .bshl), (">>", .bshr)]

def unaryOps : List (String × MicroCUnaryOp) :=
  [("neg", .neg), ("widen32to64", .widen32to64), ("trunc64to32", .trunc64to32)]

def matrix : List Case := Id.run do
  let mut out := []
  for ty in [Ty.i64, .u32, .u64] do
    let vs := values.filter ty.holds
    for (s, op) in binOps do
      for a in vs do
        for b in vs do
          out := mkCase ty (.binOp op (.varRef "a") (.varRef "b")) a b s!"{ty.name} {a} {s} {b}" :: out
    for (s, op) in shiftOps do
      for a in vs do
        for b in counts.filter ty.holds do
          out := mkCase ty (.binOp op (.varRef "a") (.varRef "b")) a b s!"{ty.name} {a} {s} {b}" :: out
    for (s, op) in unaryOps do
      for a in vs do
        out := mkCase ty (.unaryOp op (.varRef "a")) a 0 s!"{ty.name} {s} {a}" :: out
  return out.reverse

def program (cases : Array Case) : String := Id.run do
  let mut src := "#include <stdint.h>\n#include <stdio.h>\n#include <stdlib.h>\n" ++
    "static void show_i(long long v) { printf(\"%lld\\n\", v); }\n" ++
    "static void show_u(unsigned long long v) { printf(\"%llu\\n\", v); }\n" ++
    "#define SHOW(x) _Generic((x), unsigned int: show_u, unsigned long: show_u, " ++
    "unsigned long long: show_u, default: show_i)(x)\n" ++
    "int main(int argc, char **argv) {\n  if (argc != 2) return 2;\n  switch (atoi(argv[1])) {\n"
  for c in cases, i in [0:cases.size] do
    src := src ++ s!"  case {i}: \{ volatile {c.ty.cType} a = {c.ty.cLit c.a}; " ++
      s!"volatile {c.ty.cType} b = {c.ty.cLit c.b}; (void)b; SHOW({c.cExpr}); break; }\n"
  src ++ "  default: return 2;\n  }\n  return 0;\n}\n"

inductive Verdict | agree | implDefined | disagree (why : String)

/-- The UBSan message, without the source location before it. -/
def ubsanReport (stderr : String) : Option String :=
  match stderr.splitOn "runtime error: " with
  | _ :: msg :: _ => (msg.splitOn "\n").head?
  | _ => none

def judge (c : Case) (out : IO.Process.Output) : Verdict :=
  let printed := out.stdout.trimAscii.toString
  let ubsan := ubsanReport out.stderr
  match c.expected with
  | some v =>
    let want := match v with
      | .int n => toString n
      | .bool b => if b then "1" else "0"
    if out.exitCode == 0 && printed == want then .agree
    else .disagree s!"model {want}, C exit {out.exitCode} printed '{printed}' {ubsan.getD ""}"
  | none =>
    if out.exitCode != 0 && ubsan.isSome then .agree
    else if c.implDefined && out.exitCode == 0 then .implDefined
    else .disagree s!"model none, C exit {out.exitCode} printed '{printed}' without a UBSan report"

/-- The first `clang` on `PATH` outside the Lean toolchain, whose bundled clang has no libc
    headers or sanitizer runtime. -/
def systemClang : IO FilePath := do
  let leanBin := (← IO.appPath).parent
  let dirs := ((← IO.getEnv "PATH").getD "").splitOn ":" |>.map FilePath.mk
  for d in dirs do
    if some d != leanBin && (← (d / "clang").pathExists) then return d / "clang"
  throw <| IO.userError "no clang on PATH outside the Lean toolchain"

/-- Compiles one program for `cases`, runs each case, and returns the verdicts in order. -/
def run (cases : Array Case) : IO (Array Verdict) :=
  IO.FS.withTempDir fun d => do
    IO.FS.writeFile (d / "cdiff.c") (program cases)
    let exe := d / "cdiff"
    let cc ← IO.Process.output {
      cmd := (← systemClang).toString,
      args := #["-std=c11", "-O0", "-w", "-fsanitize=undefined", "-fno-sanitize-recover=undefined",
        (d / "cdiff.c").toString, "-o", exe.toString] }
    if cc.exitCode != 0 then
      throw <| IO.userError s!"clang failed with exit {cc.exitCode}:\n{cc.stderr}"
    let tasks ← cases.mapIdxM fun i c => IO.asTask do
      return judge c (← IO.Process.output { cmd := exe.toString, args := #[toString i] })
    tasks.mapM fun t => do IO.ofExcept (← IO.wait t)

def report (cases : Array Case) : IO UInt32 := do
  let vs ← run cases
  let mut agree := 0
  let mut defined := 0
  let mut impl := 0
  let mut bad := 0
  for c in cases, v in vs do
    match v with
    | .agree =>
      agree := agree + 1
      if c.expected.isSome then defined := defined + 1
    | .implDefined =>
      impl := impl + 1
      IO.println s!"impl {c.label}: model none, implementation-defined, C ran without a UBSan report"
    | .disagree why =>
      bad := bad + 1
      IO.println s!"FAIL {c.label} `{c.cExpr}`: {why}"
  IO.println (s!"{cases.size} cases: {agree} agree ({defined} values, {agree - defined} UBSan reports), " ++
    s!"{impl} implementation-defined right shifts UBSan cannot check, {bad} disagree")
  pure (if bad == 0 && agree + impl == cases.size then 0 else 1)

def replaceAll (s pat rep : String) : String := rep.intercalate (s.splitOn pat)

/-- Each control pairs a case with whether it must agree. The failing ones plant the old cast
    spellings and the old wrapping semantics. -/
def controls : List (String × Case × Bool) :=
  let trunc := mkCase .i64 (.unaryOp .trunc64to32 (.varRef "a")) 3000000000 0 "trunc 3000000000"
  let widen := mkCase .i64 (.unaryOp .widen32to64 (.varRef "a")) (-5) 0 "widen -5"
  let add := mkCase .i64 (.binOp .add (.varRef "a") (.varRef "b")) maxInt64 1 "INT64_MAX + 1"
  let shl := mkCase .u32 (.binOp .bshl (.varRef "a") (.varRef "b")) 1 40 "1u << 40"
  [("(uint32_t) at 3000000000 agrees", trunc, true),
   ("(int64_t)(uint32_t) at -5 agrees", widen, true),
   ("INT64_MAX + 1 is none and UBSan reports it", add, true),
   ("1u << 40 is none and UBSan reports it", shl, true),
   ("(int32_t) at 3000000000 disagrees",
     { trunc with cExpr := replaceAll trunc.cExpr "(uint32_t)" "(int32_t)" }, false),
   ("(int64_t) at -5 disagrees",
     { widen with cExpr := replaceAll widen.cExpr "(int64_t)(uint32_t)" "(int64_t)" }, false),
   ("INT64_MAX + 1 wrapping to INT64_MIN disagrees",
     { add with expected := some (.int (wrapInt64 (maxInt64 + 1))) }, false),
   ("1u << 40 wrapping to 0 disagrees",
     { shl with expected := some (.int (wrapUInt32 (Int.shiftLeft 1 (40 % 64)))) }, false)]

def selfTest : IO UInt32 := do
  let vs ← run (controls.map (·.2.1)).toArray
  let mut failed := 0
  for (label, c, want) in controls, v in vs do
    let agreed := match v with | .agree => true | _ => false
    let ok := agreed == want
    let detail := match v with
      | .disagree why => why
      | .agree => "agree"
      | .implDefined => "implementation-defined"
    IO.println s!"{if ok then "ok  " else "FAIL"} {label} (`{c.cExpr}`): {detail}"
    unless ok do failed := failed + 1
  IO.println s!"{controls.length - failed} of {controls.length} controls hold"
  pure (if failed == 0 then 0 else 1)

def main (args : List String) : IO UInt32 := do
  match args with
  | ["--self-test"] => selfTest
  | [] => report matrix.toArray
  | _ => IO.eprintln "usage: CheckCDiff.lean [--self-test]"; pure 2
