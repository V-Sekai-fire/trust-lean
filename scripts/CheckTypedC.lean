import TrustLean.MicroC.TypedEval
import TrustLean.MicroC.TypedRoundtrip
import TrustLean.Backend.CBackend
import TrustLean.Pipeline
import TrustLean.Frontend.ArithExpr
import TrustLean.Frontend.BoolExpr

/-! Fails unless every C program the backend emits compiles under
`clang -std=c11 -Wall -Werror -fsanitize=undefined`, and every typed program computes what
`evalTyped` says. Each typed program is `printTyped` inside a function that prints every
declared variable afterwards; under `-fno-sanitize-recover=undefined` a defined model must be
what C prints, and `none` must make UBSan stop the program. The corpus is hand-written
programs plus a seeded random set, each of which must be well typed and roundtrip.

    lake build && lake env lean --run scripts/CheckTypedC.lean
    lake env lean --run scripts/CheckTypedC.lean --self-test -/

open TrustLean System

/-! ## Typed programs -/

structure TypedCase where
  label : String
  decls : CDecls
  body : MicroCStmt
  deriving Inhabited

def fuel : Nat := 100000

inductive Model | values (lines : List String) | undefined | outOfFuel | abrupt
  deriving Inhabited

def showValue : Value → String
  | .int n => toString n
  | .bool b => if b then "1" else "0"

def model (c : TypedCase) : Model :=
  match evalTyped fuel c.decls (typedDefault c.decls) c.body with
  | some (.normal, env) => .values (c.decls.map fun (x, _) => s!"{x}={showValue (env x)}")
  | some (.outOfFuel, _) => .outOfFuel
  | some _ => .abrupt
  | none => .undefined

def printfOf : String × CType → String
  | (x, .u32) => s!"printf(\"{x}=%u\\n\", (unsigned){x});\n"
  | (x, .i64) => s!"printf(\"{x}=%lld\\n\", (long long){x});\n"
  | (x, .bool) => s!"printf(\"{x}=%d\\n\", (int){x});\n"
  | (_, .ptrU32) => ""

def TrustLean.MicroCExpr.usesPower : MicroCExpr → Bool
  | .powCall _ _ => true
  | .binOp _ l r => l.usesPower || r.usesPower
  | .unaryOp _ e => e.usesPower
  | _ => false

def TrustLean.MicroCStmt.usesPower : MicroCStmt → Bool
  | .assign _ e => e.usesPower
  | .seq s1 s2 => s1.usesPower || s2.usesPower
  | .ite c t e => c.usesPower || t.usesPower || e.usesPower
  | .while_ c b => c.usesPower || b.usesPower
  | _ => false

/-- One C file: the header, a function per case that runs `print c` and prints every variable,
    and a `main` that runs the case its argument names. -/
def typedProgram (cases : Array TypedCase) (print : TypedCase → String := fun c =>
    printTyped c.decls c.body) (header : Bool → String := fun p =>
    generateCHeader { includePowerHelper := p }) : String := Id.run do
  let mut src := header (cases.any (·.body.usesPower)) ++ "\n#include <stdio.h>\n\n"
  for c in cases, i in [0:cases.size] do
    src := src ++ s!"static void case_{i}(void) \{\n{print c}\n" ++
      String.join (c.decls.map printfOf) ++ "}\n\n"
  src := src ++ "int main(int argc, char **argv) {\n  if (argc != 2) return 2;\n" ++
    "  switch (atoi(argv[1])) {\n"
  for i in [0:cases.size] do
    src := src ++ s!"  case {i}: case_{i}(); break;\n"
  src ++ "  default: return 2;\n  }\n  return 0;\n}\n"

/-! ## clang -/

/-- The first `clang` on `PATH` outside the Lean toolchain, whose bundled clang has no libc
    headers or sanitizer runtime. -/
def systemClang : IO FilePath := do
  let leanBin := (← IO.appPath).parent
  let dirs := ((← IO.getEnv "PATH").getD "").splitOn ":" |>.map FilePath.mk
  for d in dirs do
    if some d != leanBin && (← (d / "clang").pathExists) then return d / "clang"
  throw <| IO.userError "no clang on PATH outside the Lean toolchain"

def flags : Array String :=
  #["-std=c11", "-Wall", "-Werror", "-fsanitize=undefined", "-fno-sanitize-recover=undefined"]

/-- Compiles `src` into `out` (an object file when `obj`); `none` on success, else clang's
    diagnostics. -/
def compile (src : String) (dir : FilePath) (name : String) (obj : Bool) : IO (Option String) := do
  IO.FS.writeFile (dir / s!"{name}.c") src
  let out ← IO.Process.output {
    cmd := (← systemClang).toString,
    args := flags ++ (if obj then #["-c"] else #[]) ++
      #[(dir / s!"{name}.c").toString, "-o", (dir / name).toString] }
  pure (if out.exitCode == 0 then none else some out.stderr)

/-- The first error clang reports: its flag, e.g. `-Wparentheses-equality`, or its message. -/
def firstFlag (diag : String) : String :=
  match diag.splitOn "error: " with
  | _ :: rest :: _ =>
    let msg := (rest.splitOn "\n").head?.getD ""
    match msg.splitOn "[-W" with
    | _ :: flag :: _ => "-W" ++ ((flag.splitOn "]").head?.getD "")
    | _ => msg
  | _ => diag

inductive Verdict | agree | disagree (why : String)

def Verdict.ok : Verdict → Bool
  | .agree => true
  | .disagree _ => false

def ubsanReport (stderr : String) : Option String :=
  match stderr.splitOn "runtime error: " with
  | _ :: msg :: _ => (msg.splitOn "\n").head?
  | _ => none

def judge (m : Model) (out : IO.Process.Output) : Verdict :=
  let printed := (out.stdout.trimAscii.toString.splitOn "\n").filter (· ≠ "")
  match m with
  | .values want =>
    if out.exitCode == 0 && printed == want then .agree
    else .disagree s!"model {want}, C exit {out.exitCode} printed {printed} {(ubsanReport out.stderr).getD ""}"
  | .undefined =>
    if out.exitCode != 0 && (ubsanReport out.stderr).isSome then .agree
    else .disagree s!"model none, C exit {out.exitCode} printed {printed} without a UBSan report"
  | .outOfFuel => .disagree "the model ran out of fuel"
  | .abrupt => .disagree "the model ended in break, continue or return"

/-- Compiles one program for `cases` and runs each against the model `models`. -/
def runTyped (cases : Array TypedCase) (models : Array Model) (src : String) :
    IO (Except String (Array Verdict)) :=
  IO.FS.withTempDir fun d => do
    if let some diag := ← compile src d "typed" false then
      return .error diag
    let exe := d / "typed"
    let tasks ← cases.mapIdxM fun i _ => IO.asTask do
      match models[i]! with
      | .outOfFuel => return Verdict.disagree "the model ran out of fuel"
      | m => return judge m (← IO.Process.output { cmd := exe.toString, args := #[toString i] })
    return .ok (← tasks.mapM fun t => do IO.ofExcept (← IO.wait t))

/-! ## Corpus -/

def u (n : Nat) : MicroCExpr := .litU32 (UInt32.ofNat n)
def v (x : String) : MicroCExpr := .varRef x
def bin (op : MicroCBinOp) (l r : MicroCExpr) : MicroCExpr := .binOp op l r

/-- Right-nested sequence, as the parser rebuilds it. -/
def seqs : List MicroCStmt → MicroCStmt
  | [] => .skip
  | [s] => s
  | s :: rest => .seq s (seqs rest)

def ringDecls : CDecls :=
  [("tail", .u32), ("cur", .u32), ("b", .u32), ("pending", .u32), ("next", .u32), ("mask", .u32),
   ("slot", .u32), ("x", .u32), ("a", .u32), ("aligned", .u32)]

/-- The ring kernels' index arithmetic: pending, catch-up and slot across the 2^32 wrap, and
    rounding up to a power of two. -/
def ringCase (tail cur b x a : Nat) : TypedCase :=
  { label := s!"ring tail={tail} cur={cur} b={b} x={x} a={a}", decls := ringDecls,
    body := seqs [
      .assign "tail" (u tail), .assign "cur" (u cur), .assign "b" (u b), .assign "x" (u x),
      .assign "a" (u a), .assign "mask" (u 15),
      .assign "pending" (bin .sub (v "tail") (v "cur")),
      .ite (bin .ltOp (v "b") (v "pending"))
        (.assign "next" (bin .sub (v "tail") (v "b"))) (.assign "next" (v "cur")),
      .assign "slot" (bin .band (v "tail") (v "mask")),
      .assign "aligned" (bin .band (bin .add (v "x") (bin .sub (v "a") (u 1))) (bin .sub (u 0) (v "a")))] }

def loopDecls : CDecls := [("i", .u32), ("s", .u32), ("n", .i64), ("found", .bool)]

/-- Counted loops with `break` and `continue`. -/
def loopCase (limit : Nat) : TypedCase :=
  { label := s!"loop limit={limit}", decls := loopDecls,
    body := seqs [
      .while_ (bin .ltOp (v "i") (u limit))
        (seqs [.assign "i" (bin .add (v "i") (u 1)),
          .ite (bin .eqOp (bin .band (v "i") (u 1)) (u 0)) .continue_ .skip,
          .assign "s" (bin .add (v "s") (bin .mul (v "i") (v "i"))),
          .assign "n" (bin .add (v "n") (.unaryOp .widen32to64 (v "i"))),
          .ite (bin .ltOp (u 1000) (v "s")) (seqs [.assign "found" (.litBool true), .break_]) .skip])] }

def mixDecls : CDecls := [("x", .u32), ("y", .i64), ("z", .i64), ("ok", .bool)]

/-- Casts both ways, `int64_t` arithmetic around the `uint32_t` wrap, and `power`. -/
def mixCase (y0 : Int) (e : Nat) : TypedCase :=
  { label := s!"mix y={y0} e={e}", decls := mixDecls,
    body := seqs [
      .assign "y" (.litInt y0),
      .assign "x" (.unaryOp .trunc64to32 (v "y")),
      .assign "z" (bin .sub (.unaryOp .widen32to64 (v "x")) (v "y")),
      .assign "ok" (bin .land (bin .ltOp (v "z") (.litInt 1)) (.unaryOp .lnot (bin .eqOp (v "x") (u 7)))),
      .assign "z" (bin .add (.powCall (v "z") e) (.litInt 0)),
      .assign "y" (bin .bshr (bin .band (v "y") (.litInt 9223372036854775807)) (.litInt 3))] }

/-- Undefined behaviour the typed semantics stops at. -/
def ubCases : List TypedCase :=
  [{ label := "INT64_MAX + 1", decls := [("y", .i64)],
     body := seqs [.assign "y" (.litInt 9223372036854775807), .assign "y" (bin .add (v "y") (.litInt 1))] },
   { label := "uint32_t shift by a count of 40", decls := [("x", .u32), ("c", .u32)],
     body := seqs [.assign "x" (u 1), .assign "c" (u 40), .assign "x" (bin .bshl (v "x") (v "c"))] },
   { label := "left shift of a negative int64_t", decls := [("y", .i64)],
     body := seqs [.assign "y" (.litInt (-1)), .assign "y" (bin .bshl (v "y") (.litInt 1))] },
   { label := "power(2, 63)", decls := [("y", .i64)],
     body := seqs [.assign "y" (.litInt 2), .assign "y" (bin .add (.powCall (v "y") 63) (.litInt 0))] },
   { label := "-INT64_MIN", decls := [("y", .i64)],
     body := seqs [.assign "y" (.litInt (-9223372036854775807)), .assign "y" (bin .sub (v "y") (.litInt 1)),
       .assign "y" (.unaryOp .neg (v "y"))] }]

def handCases : List TypedCase :=
  [ringCase 4294967295 4294967290 3 4294967280 16, ringCase 5 4294967293 100 17 8,
   ringCase 0 0 0 0 1, ringCase 2147483648 2147483647 1 4294967295 4096,
   loopCase 0, loopCase 7, loopCase 100,
   mixCase (-5) 2, mixCase 3000000000 3, mixCase 4294967296 1, mixCase (-9223372036854775807) 0,
   mixCase 12345678901 62] ++ ubCases

/-! ### Random programs -/

structure Rng where
  state : Nat

def Rng.next (g : Rng) (n : Nat) : Nat × Rng :=
  let s := (g.state * 6364136223846793005 + 1442695040888963407) % 2 ^ 64
  ((s / 2 ^ 33) % n, ⟨s⟩)

def pick {α : Type} [Inhabited α] (g : Rng) (xs : List α) : α × Rng :=
  let (i, g) := g.next xs.length
  (xs[i]!, g)

def randDecls : CDecls :=
  [("a", .u32), ("b", .u32), ("c", .u32), ("p", .i64), ("q", .i64), ("f", .bool), ("g", .bool)]

def u32Values : List Nat :=
  [0, 1, 2, 3, 7, 16, 31, 32, 255, 65535, 65536, 2147483647, 2147483648, 4294967294, 4294967295]

def i64Values : List Int :=
  [0, 1, -1, 2, 7, -7, 2147483648, 4294967296, -4294967296, 4611686018427387904,
   -4611686018427387904, 9223372036854775807, -9223372036854775807]

/-- `e`, or a variable of type `t` when `e` is a constant expression. -/
def readsVar (t : CType) : MicroCExpr × Rng → MicroCExpr × Rng
  | (e, g) =>
    match exprTy randDecls e with
    | some (_, true) => (e, g)
    | _ => pick g (randDecls.filter (·.2 == t) |>.map (v ·.1))

/-- A random expression of type `t`. `int64_t` right shifts are left out: a negative operand
    is implementation-defined (C11 6.5.7p5), so UBSan cannot confirm the model's `none`.
    Both sides of a comparison read a variable: clang's `-Wtautological-bitwise-compare` and
    `-Wtautological-overlap-compare` reject comparisons their constants decide. -/
partial def randExpr : Nat → CType → Rng → MicroCExpr × Rng
  | 0, .u32, g =>
    let (k, g) := g.next 2
    if k == 0 then let (x, g) := pick g ["a", "b", "c"]; (v x, g)
    else let (n, g) := pick g u32Values; (u n, g)
  | 0, .i64, g =>
    let (k, g) := g.next 2
    if k == 0 then let (x, g) := pick g ["p", "q"]; (v x, g)
    else let (n, g) := pick g i64Values; (.litInt n, g)
  | 0, .bool, g =>
    let (k, g) := g.next 3
    if k == 0 then let (b, g) := pick g [true, false]; (.litBool b, g)
    else let (x, g) := pick g ["f", "g"]; (v x, g)
  | d + 1, .u32, g =>
    let (k, g) := g.next 6
    match k with
    | 0 => randExpr 0 .u32 g
    | 1 => let (e, g) := randExpr d .i64 g; (.unaryOp .trunc64to32 e, g)
    | 2 => let (e, g) := randExpr d .u32 g; (.unaryOp .neg e, g)
    | 3 =>
      let (op, g) := pick g [MicroCBinOp.bshl, .bshr]
      let (l, g) := randExpr d .u32 g
      let (c, g) := pick g [0, 1, 5, 16, 31]
      (bin op l (u c), g)
    | _ =>
      let (op, g) := pick g [MicroCBinOp.add, .sub, .mul, .band, .bor, .bxor]
      let (l, g) := randExpr d .u32 g
      let (r, g) := randExpr d .u32 g
      (bin op l r, g)
  | d + 1, .i64, g =>
    let (k, g) := g.next 6
    match k with
    | 0 => randExpr 0 .i64 g
    | 1 => let (e, g) := randExpr d .u32 g; (.unaryOp .widen32to64 e, g)
    | 2 => let (x, g) := pick g ["p", "q"]; (.unaryOp .neg (v x), g)
    | 3 =>
      let (x, g) := pick g ["p", "q"]
      let (c, g) := pick g [0, 1, 7, 31, 32, 62, 63]
      (bin .bshl (v x) (.litInt c), g)
    | _ =>
      let (op, g) := pick g [MicroCBinOp.add, .sub, .mul, .band, .bor, .bxor]
      let (x, g) := pick g ["p", "q"]
      let (r, g) := randExpr d .i64 g
      let (side, g) := g.next 2
      (if side == 0 then bin op (v x) r else bin op r (v x), g)
  | d + 1, .bool, g =>
    let (k, g) := g.next 5
    match k with
    | 0 => randExpr 0 .bool g
    | 1 => let (e, g) := randExpr d .bool g; (.unaryOp .lnot e, g)
    | 2 =>
      let (op, g) := pick g [MicroCBinOp.land, .lor]
      let (l, g) := randExpr d .bool g
      let (r, g) := randExpr d .bool g
      (bin op l r, g)
    | 3 =>
      let (op, g) := pick g [MicroCBinOp.eqOp, .ltOp]
      let (l, g) := readsVar .i64 (randExpr d .i64 g)
      let (r, g) := readsVar .i64 (randExpr d .i64 g)
      (bin op l r, g)
    | _ =>
      let (op, g) := pick g [MicroCBinOp.eqOp, .ltOp]
      let (l, g) := readsVar .u32 (randExpr d .u32 g)
      let (r, g) := readsVar .u32 (randExpr d .u32 g)
      (bin op l r, g)
  | _, .ptrU32, g => (u 0, g)

def randAssign (g : Rng) : MicroCStmt × Rng :=
  let ((x, t), g) := pick g randDecls
  let (e, g) := randExpr 2 t g
  (.assign x e, g)

/-- Literal starting values for every variable, then assignments, some under an `if`. -/
def randCase (seed : Nat) : TypedCase := Id.run do
  let mut g : Rng := ⟨seed⟩
  let mut stmts : List MicroCStmt := []
  for (x, t) in randDecls do
    let (e, g') := randExpr 0 t g
    g := g'
    stmts := stmts ++ [.assign x (match t, e with | _, .varRef _ => t.zero | _, e => e)]
  let (n, g') := g.next 5
  g := g'
  for _ in [0:n + 2] do
    let (k, g') := g.next 4
    g := g'
    if k == 0 then
      let (c, g') := randExpr 2 .bool g
      let (s1, g'') := randAssign g'
      let (s2, g''') := randAssign g''
      g := g'''
      stmts := stmts ++ [.ite c s1 s2]
    else
      let (s, g') := randAssign g
      g := g'
      stmts := stmts ++ [s]
  return { label := s!"random seed {seed}", decls := randDecls, body := seqs stmts }

def randomCount : Nat := 400

/-- Random programs that are well typed; the others are counted, not run. -/
def randomCases : List TypedCase × Nat :=
  let all := (List.range (randomCount * 3)).map randCase
  let typed := all.filter fun c => decide (WellTyped c.decls c.body)
  (typed.take randomCount, all.length - typed.length)

/-! ## Emitted functions -/

def deepArith : ArithExpr :=
  List.foldl (fun acc _ => .add acc (.lit 1)) (.lit 0) (List.replicate 10 ())

def ux (s : String) : LowLevelExpr := .varRef (.user s)

/-- A loop with a branch and `power`, through the Core IR. -/
def loopStmt : Stmt :=
  .seq (.assign (.user "acc") (.litInt 0))
    (.for_ (.assign (.user "i") (.litInt 0)) (.binOp .ltOp (ux "i") (ux "n"))
      (.assign (.user "i") (.binOp .add (ux "i") (.litInt 1)))
      (.ite (.binOp .eqOp (.binOp .band (ux "i") (.litInt 1)) (.litInt 0))
        (.assign (.user "acc") (.binOp .add (ux "acc") (.powCall (ux "i") 2)))
        (.assign (.user "flag") (.binOp .ltOp (ux "acc") (ux "n")))))

def program (cfg : CConfig) (fn : String) : String := generateCHeader cfg ++ "\n\n" ++ fn

def checkExpr : BoolExpr := .or_ (.and_ (.var 0) (.var 1)) (.not_ (.var 0))

/-- A local written a `bool` and then an `int64_t`, through the Core IR. -/
def narrowStmt : Stmt :=
  .seq (.assign (.user "t") (ux "a")) (.assign (.user "t") (.binOp .add (ux "x") (.litInt 1)))

def narrowFn : String :=
  generateCFunction { includePowerHelper := false } "p1" [("a", "bool"), ("x", "int64_t")]
    narrowStmt (ux "t")

/-- What `evalStmt` leaves in `t` from `a = true, x = 41`. -/
def narrowModel : String :=
  let env := (LowLevelEnv.default.update (.user "a") (.bool true)).update (.user "x") (.int 41)
  match evalStmt 10 env narrowStmt with
  | some (.normal, env') => showValue (env' (.user "t"))
  | _ => "none"

/-- `fn` with a `main` that prints `p1(true, 41)`. -/
def narrowMain (fn : String) : String :=
  program { includePowerHelper := false } fn ++
    "\n#include <stdio.h>\nint main(void) {\n  printf(\"%lld\\n\", (long long)p1(true, 41));\n  return 0;\n}\n"

/-- Programs the C backend emits, header and function, as the test modules emit them. -/
def emittedPrograms : List (String × String) :=
  [("compute", Pipeline.emit (ArithExpr.mul (.add (.var 0) (.lit 3)) (.add (.var 1) (.lit 2)))
      (default : CConfig) "compute" [("v0", "int64_t"), ("v1", "int64_t")]),
   ("check", Pipeline.emit checkExpr (default : CConfig) "check" [("b0", "bool"), ("b1", "bool")]),
   ("check with int64_t parameters", Pipeline.emit checkExpr (default : CConfig) "check"
      [("b0", "int64_t"), ("b1", "int64_t")]),
   ("constant", Pipeline.emit (ArithExpr.lit 42) (default : CConfig) "constant" []),
   ("deep", Pipeline.emit deepArith (default : CConfig) "deep" [("x", "int64_t")]),
   ("long long", Pipeline.emit (ArithExpr.lit 42) ({ useInt64 := false } : CConfig) "test_ll"
      [("x", "long long")]),
   ("no power helper", Pipeline.emit deepArith ({ includePowerHelper := false } : CConfig) "deep"
      [("x", "int64_t")]),
   ("keyword parameters", program default
      (generateCFunction default "compute" [("int", "int64_t"), ("for", "int64_t"),
        ("while", "int64_t")] .skip (.litInt 0))),
   ("reserved and macro parameter names", program default (generateCFunction default "names"
      (cReservedIdentifiers.map (·, "int64_t")) .skip (.litInt 0))),
   ("empty", program default (generateCFunction default "empty" [] .skip (.litInt 0))),
   ("loop", program default (generateCFunction default "loop" [("n", "int64_t")] loopStmt (ux "acc"))),
   ("a local written a bool and then an int64_t", program { includePowerHelper := false } narrowFn)]

def checkEmitted (progs : List (String × String)) : IO Nat :=
  IO.FS.withTempDir fun d => do
    let mut bad := 0
    for (label, src) in progs, i in [0:progs.length] do
      match ← compile src d s!"emitted{i}" true with
      | none => IO.println s!"ok   emitted {label} compiles"
      | some diag =>
        bad := bad + 1
        IO.println s!"FAIL emitted {label}: {firstFlag diag}\n{diag}"
    pure bad

/-! ## Report -/

def checkTyped (cases : Array TypedCase) : IO Nat := do
  let mut bad := 0
  for c in cases do
    unless decide (WellTyped c.decls c.body) do
      bad := bad + 1; IO.println s!"FAIL {c.label}: not well typed"
    unless parseTyped (printTyped c.decls c.body) == some (c.decls, c.body) do
      bad := bad + 1; IO.println s!"FAIL {c.label}: does not roundtrip"
  let models := cases.map model
  match ← runTyped cases models (typedProgram cases) with
  | .error diag =>
    IO.println s!"FAIL the typed programs do not compile: {firstFlag diag}\n{diag}"
    pure (bad + cases.size)
  | .ok vs =>
    let mut values := 0
    let mut reports := 0
    for c in cases, m in models, verdict in vs do
      match verdict with
      | .agree => match m with
        | .values _ => values := values + 1
        | _ => reports := reports + 1
      | .disagree why =>
        bad := bad + 1
        IO.println s!"FAIL {c.label}: {why}\n{printTyped c.decls c.body}"
    IO.println s!"{cases.size} typed programs: {values + reports} agree ({values} values, {reports} UBSan reports), {cases.size - values - reports} disagree"
    pure bad

/-- The object-like macros `clang -dM -E` output defines, other than the implementation's `_`
    names, and those of them `cReservedIdentifiers` leaves out. A parameter or local with one of
    the latter names expands. An output without `CHAR_BIT` is an error, not an empty list. -/
def macroNames (dump : String) : Except String (Nat × List String) :=
  let names := (dump.splitOn "\n").filterMap fun l => match l.splitOn " " with
    | "#define" :: n :: _ => if n.contains '(' || n.startsWith "_" then none else some n
    | _ => none
  if names.contains "CHAR_BIT" then .ok (names.length, names.filter (!cReservedIdentifiers.contains ·))
  else .error "no #define CHAR_BIT in the output"

def unreservedMacros : IO (Except String (Nat × List String)) :=
  IO.FS.withTempDir fun d => do
    IO.FS.writeFile (d / "header.c") (generateCHeader default)
    let out ← IO.Process.output {
      cmd := (← systemClang).toString, args := #["-std=c11", "-dM", "-E", (d / "header.c").toString] }
    if out.exitCode != 0 then return .error out.stderr
    return macroNames out.stdout

def report : IO UInt32 := do
  let (random, rejected) := randomCases
  IO.println s!"{random.length} random programs kept, {rejected} generated ill typed and not run"
  let cases := (handCases ++ random).toArray
  let typedBad ← checkTyped cases
  let emittedBad ← checkEmitted emittedPrograms
  IO.println s!"{emittedPrograms.length} emitted programs: {emittedPrograms.length - emittedBad} compile, {emittedBad} fail"
  let macrosBad ← match ← unreservedMacros with
    | .error diag => do IO.println s!"FAIL clang -dM -E of the header: {diag}"; pure 1
    | .ok (seen, ms) => do
      IO.println s!"{ms.length} of {seen} object-like macros the header defines here are not reserved, so a parameter named one expands: {ms.take 8}"
      pure 0
  pure (if typedBad == 0 && emittedBad == 0 && macrosBad == 0 && random.length == randomCount then 0 else 1)

/-! ## Controls -/

def replaceAll (s pat rep : String) : String := rep.intercalate (s.splitOn pat)

/-- The C function body the backend printed before it declared locals and used the proved
    printer. -/
def stmtToCFunction (cfg : CConfig) (name : String) (params : List (String × String))
    (body : Stmt) (result : LowLevelExpr) : String :=
  cfg.intType ++ " " ++ name ++ "(" ++
    ", ".intercalate (params.map fun (n, t) => t ++ " " ++ varNameToC (.user n)) ++ ") {\n" ++
    joinCode (stmtToC 1 body) ("  return " ++ exprToC result ++ ";") ++ "\n}"

def oldPowerHeader (cfg : CConfig) : String :=
  replaceAll (generateCHeader cfg) "    exp /= 2;\n    if (exp > 0) base *= base;\n"
    "    base *= base;\n    exp /= 2;\n"

def eqCase : TypedCase :=
  { label := "if (x == 5u)", decls := [("x", .u32), ("b", .bool)],
    body := seqs [.assign "x" (u 5), .ite (bin .eqOp (v "x") (u 5)) (.assign "b" (.litBool true)) .skip] }

/-- tlprobe case C: `(x + 4294967295) < 1u` is `long` arithmetic in C, but `uint32_t` in the
    model, and the typing rejects it. -/
def unsuffixedCase : TypedCase :=
  { label := "x + 4294967295 with an unsuffixed literal", decls := [("x", .u32), ("b", .bool)],
    body := seqs [.assign "x" (u 1),
      .assign "b" (bin .ltOp (bin .add (v "x") (.litInt 4294967295)) (u 1))] }

/-- C skips `(p + 1) < q` because the left operand of `&&` is false; `evalTyped` evaluates it
    and overflows, and the typing rejects it. -/
def skippedCase : TypedCase :=
  { label := "false && ((p + 1) < q) at p = INT64_MAX", decls := [("p", .i64), ("q", .i64), ("f", .bool)],
    body := seqs [.assign "p" (.litInt 9223372036854775807),
      .assign "f" (bin .land (.litBool false) (bin .ltOp (bin .add (v "p") (.litInt 1)) (v "q")))] }

/-- Compiles and runs `src`; `none` when it prints `want`. -/
def runPrints (src want : String) : IO (Option String) :=
  IO.FS.withTempDir fun d => do
    if let some diag := ← compile src d "main" false then return some (firstFlag diag)
    let out ← IO.Process.output { cmd := (d / "main").toString }
    let got := out.stdout.trimAscii.toString
    pure (if out.exitCode == 0 && got == want then none
      else some s!"C exit {out.exitCode} printed {got}, evalStmt gives {want}")

def macroParam : String :=
  program default (generateCFunction default "f" [("CHAR_BIT", "int64_t")] .skip (ux "CHAR_BIT"))

def powerCase : TypedCase :=
  { label := "power(4294967296, 1)", decls := [("y", .i64)],
    body := seqs [.assign "y" (.litInt 4294967296), .assign "y" (bin .add (.powCall (v "y") 1) (.litInt 0))] }

/-- Each control compiles or runs one program and says whether that must succeed. The failing
    ones plant undeclared locals, `stmtToC`, doubled condition parentheses, an unused helper, an
    unsuffixed `uint32_t` operand, a helper that squares past the last bit, a local typed by its
    first write, parameters the body does not name, a macro as a parameter name, an undefined
    right operand of `&&`, and a macro dump without `CHAR_BIT`. -/
def controls : List (String × Bool × IO (Option String)) :=
  let compileOnly (src : String) : IO (Option String) :=
    IO.FS.withTempDir fun d => do
      pure ((← compile src d "control" true).map firstFlag)
  let runOne (c : TypedCase) (src : String) : IO (Option String) := do
    match ← runTyped #[c] #[model c] src with
    | .error diag => pure (some (firstFlag diag))
    | .ok vs => pure (match (vs[0]? : Option Verdict) with
      | some .agree => none
      | some (.disagree why) => some why
      | none => some "no verdict")
  [("a typed program compiles and agrees", true, runOne (ringCase 4294967295 4294967290 3 4294967280 16)
      (typedProgram #[ringCase 4294967295 4294967290 3 4294967280 16])),
   ("INT64_MAX + 1 is none and UBSan reports it", true, runOne ubCases[0]! (typedProgram #[ubCases[0]!])),
   ("power(4294967296, 1) agrees with the helper", true, runOne powerCase (typedProgram #[powerCase])),
   ("the emitted loop compiles", true,
      compileOnly (program default (generateCFunction default "loop" [("n", "int64_t")] loopStmt (ux "acc")))),
   ("a typed body without its declarations does not compile", false,
      compileOnly ("#include <stdbool.h>\nvoid f(void) {\n{ " ++ microCToString eqCase.body ++ " }\n}\n")),
   ("the stmtToC export of deep does not compile", false,
      compileOnly (generateCHeader default ++ "\n\n" ++
        stmtToCFunction default "deep" [("x", "int64_t")] (Pipeline.lower deepArith).stmt
          (Pipeline.lower deepArith).resultVar)),
   ("if ((x == 5u)) fails -Werror", false,
      compileOnly (replaceAll (typedProgram #[eqCase]) "if (x == 5u)" "if ((x == 5u))")),
   ("an unused power helper fails -Werror", false,
      compileOnly (replaceAll (program default (generateCFunction default "deep" [("x", "int64_t")]
        (Pipeline.lower deepArith).stmt (Pipeline.lower deepArith).resultVar)) "(void)power;\n" "")),
   ("an unsuffixed literal on a uint32_t operand disagrees", false,
      runOne unsuffixedCase (typedProgram #[unsuffixedCase])),
   ("the helper that squares past the last bit disagrees at power(4294967296, 1)", false,
      runOne powerCase (typedProgram #[powerCase] (header := fun p => oldPowerHeader { includePowerHelper := p }))),
   ("a local written a bool and then an int64_t returns what evalStmt gives", true,
      runPrints (narrowMain narrowFn) narrowModel),
   ("the same local declared bool, its first write's type, returns 1", false,
      runPrints (narrowMain (replaceAll narrowFn "int64_t t = 0;" "bool t = false;")) narrowModel),
   ("check with int64_t parameters b0 and b1 compiles", true,
      compileOnly (Pipeline.emit checkExpr (default : CConfig) "check" [("b0", "int64_t"), ("b1", "int64_t")])),
   ("check with parameters a and b, which the body does not read, does not compile", false,
      compileOnly (Pipeline.emit checkExpr (default : CConfig) "check" [("a", "int64_t"), ("b", "int64_t")])),
   ("a parameter named CHAR_BIT compiles", true, compileOnly macroParam),
   ("the same parameter printed as CHAR_BIT does not compile", false,
      compileOnly (replaceAll macroParam (varNameToC (.user "CHAR_BIT")) "CHAR_BIT")),
   ("a right operand of && that overflows where C skips it disagrees", false,
      runOne skippedCase (typedProgram #[skippedCase])),
   ("macro names parse from #define lines", true,
      pure (match macroNames "#define CHAR_BIT 8\n#define ARG_MAX 1\n#define _X 1\n#define F(x) x\n" with
        | .ok (2, ["ARG_MAX"]) => none
        | .ok (n, ms) => some s!"{n} names, unreserved {ms}"
        | .error e => some e)),
   ("an empty macro dump is an error", false,
      pure (match macroNames "" with
        | .error e => some e
        | .ok (n, _) => if n == 0 then none else some s!"{n} names"))]

def selfTest : IO UInt32 := do
  let mut failed := 0
  for (label, want, act) in controls do
    let got ← act
    let ok := got.isNone == want
    IO.println s!"{if ok then "ok  " else "FAIL"} {label}: {got.getD "succeeds"}"
    unless ok do failed := failed + 1
  for c in [unsuffixedCase, skippedCase] do
    if decide (WellTyped c.decls c.body) then
      failed := failed + 1
      IO.println s!"FAIL the control {c.label} is well typed"
  IO.println s!"{controls.length - failed} of {controls.length} controls hold"
  pure (if failed == 0 then 0 else 1)

def main (args : List String) : IO UInt32 := do
  match args with
  | ["--self-test"] => selfTest
  | [] => report
  | _ => IO.eprintln "usage: CheckTypedC.lean [--self-test]"; pure 2
