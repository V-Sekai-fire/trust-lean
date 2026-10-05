import TrustLean.MicroC.FuncEval

/-! Exports `ring_push`, `ring_pop` and `ring_mask` with `emitFile` to `examples/out/ring.h` and
`examples/out/ring.c`, builds them with a generated driver under `clang -std=c11 -Wall -Werror
-fsanitize=address,undefined`, and fails unless each call prints the return value and buffer
cells `evalFunc_u32` computes, or stops with a sanitizer report where `evalFunc_u32` is `none`.
The calls are seeded walks of push and pop across 2^31 and 2^32, which fill and empty the ring,
seeded single calls at boundary counters, and `ring_mask` at every count up to 40.

    lake build && lake env lean --run examples/Ring.lean
    lake env lean --run examples/Ring.lean --self-test -/

open TrustLean System

def funcs : List MicroCFunc := [ringPush, ringPop, ringMask]

def fuel : Nat := 1000

structure Call where
  f : MicroCFunc
  args : List Arg32

def w (n : UInt32) : Arg32 := .val (.w n)

def Call.input (c : Call) : String :=
  " ".intercalate (c.f.name :: c.args.map fun
    | .val (.w n) => toString n.toNat
    | .val (.b b) => if b then "1" else "0"
    | .buf cs => " ".intercalate (toString cs.length :: cs.map (toString ·.toNat)))

def showValue : Value → String
  | .int n => toString n
  | .bool b => if b then "1" else "0"

/-- What the driver prints for a call: the return value, then ` |` and the cells of each buffer. -/
def showResult (r : Value × List (List Value)) : String :=
  showValue r.1 ++ String.join (r.2.map fun cs => " |" ++ String.join (cs.map (" " ++ showValue ·)))

/-- The line the driver must print, or `none` where it must stop with a sanitizer report. -/
abbrev Model := Call → Option String

def bounded : Model := fun c => (evalFunc_u32 fuel c.f c.args).map showResult

/-- `evalMicroC_uint32` on the same arguments, without the bounds check. -/
def unbounded : Model := fun c =>
  match bindArgs c.f.params c.args with
  | some (ρ, B) =>
    match evalMicroC_uint32 fuel (V32.lift ∘ declareLocals ρ c.f.locals) c.f.body with
    | some (.return_ (some v), env) => some (showResult (v, readBufs env c.f.params B))
    | _ => none
  | none => none

/-! ## Calls -/

structure Rng where
  s : UInt64

def Rng.next (g : Rng) (n : Nat) : Nat × Rng :=
  let s := g.s * 6364136223846793005 + 1442695040888963407
  ((s >>> 33).toNat % n, ⟨s⟩)

def Rng.word (g : Rng) : UInt32 × Rng :=
  let (a, g) := g.next 65536
  let (b, g) := g.next 65536
  (UInt32.ofNat (a * 65536 + b), g)

def boundaries : List UInt32 := [0, 1, 2147483646, 2147483647, 2147483648, 4294967294, 4294967295]

def Rng.counter (g : Rng) : UInt32 × Rng :=
  let (k, g) := g.next 3
  if k == 0 then g.word
  else
    let (i, g) := g.next boundaries.length
    let (d, g) := g.next 5
    (boundaries[i]! + UInt32.ofNat d - 2, g)

def Rng.cells (g : Rng) (n : Nat) : List UInt32 × Rng :=
  (List.range n).foldl (fun (acc, g) _ => let (x, g) := g.word; (acc ++ [x], g)) ([], g)

/-- Push and pop from `start`, each call on the state the model's previous result leaves.
    Pushes take 4 of 5 calls for 40 calls, then pops do, so the ring fills and empties. -/
def walk (seed : Nat) (start mask : UInt32) (steps : Nat) : List Call := Id.run do
  let mut g : Rng := ⟨UInt64.ofNat seed⟩
  let mut head := start
  let mut tail := start
  let (cs, g') := g.cells (mask.toNat + 1)
  g := g'
  let mut buf := cs
  let mut out : List Call := []
  for k in [0:steps] do
    let (r, g') := g.next 5
    g := g'
    let pushing := if (k / 40) % 2 == 0 then r != 0 else r == 0
    if pushing then
      let (x, g') := g.word
      g := g'
      let c : Call := ⟨ringPush, [w head, w tail, w mask, .buf buf, w x]⟩
      out := out ++ [c]
      if let some (.int t, [b]) := evalFunc_u32 fuel ringPush c.args then
        tail := UInt32.ofNat t.toNat
        buf := b.map fun | .int n => UInt32.ofNat n.toNat | _ => 0
    else
      let c : Call := ⟨ringPop, [w head, w tail, w mask, .buf buf, .buf [0]]⟩
      out := out ++ [c]
      if let some (.int h, _) := evalFunc_u32 fuel ringPop c.args then
        head := UInt32.ofNat h.toNat
  out

/-- Single calls on counters at and around 2^31 and 2^32 and on random ones. -/
def singles (seed : Nat) (count : Nat) : List Call := Id.run do
  let mut g : Rng := ⟨UInt64.ofNat seed⟩
  let mut out : List Call := []
  for _ in [0:count] do
    let (head, g1) := g.counter
    let (tail, g2) := g1.counter
    let (m, g3) := g2.next 5
    let mask := UInt32.ofNat (2 ^ m - 1)
    let (buf, g4) := g3.cells (mask.toNat + 1)
    let (x, g5) := g4.word
    let (k, g6) := g5.next 2
    g := g6
    out := out ++ [if k == 0 then ⟨ringPush, [w head, w tail, w mask, .buf buf, w x]⟩
      else ⟨ringPop, [w head, w tail, w mask, .buf buf, .buf [7]]⟩]
  out

/-- The push `evalMicroC_uint32_pushK` runs: `tail` wraps to 0 and `buf[7]` takes 42. -/
def pushWrap : Call := ⟨ringPush, [w 4294967294, w 4294967295, w 7, .buf (List.replicate 8 0), w 42]⟩

def pushFull : Call := ⟨ringPush, [w 5, w 13, w 7, .buf (List.range 8 |>.map UInt32.ofNat), w 42]⟩

/-- A buffer one cell short of `mask + 1`, so the push stores past its end. -/
def pushShort : Call := ⟨ringPush, [w 0, w 7, w 7, .buf (List.replicate 7 0), w 42]⟩

def calls : List Call :=
  [pushWrap, pushFull] ++ walk 1 2147483642 3 400 ++ walk 2 4294967290 7 400 ++ singles 3 600 ++
    (List.range 41).map fun b => ⟨ringMask, [w (UInt32.ofNat b)]⟩

def Call.word (c : Call) (i : Nat) : Option Nat :=
  match c.args[i]? with
  | some (.val (.w n)) => some n.toNat
  | _ => none

/-- `tail - head` modulo 2^32, from the first two arguments. -/
def Call.occupancy (c : Call) : Option Nat :=
  match c.word 0, c.word 1 with
  | some h, some t => some ((t + 2 ^ 32 - h) % 2 ^ 32)
  | _, _ => none

def Call.returns (c : Call) : Option Int :=
  match evalFunc_u32 fuel c.f c.args with
  | some (.int r, _) => some r
  | _ => none

/-- The cases the calls must reach, each with how many calls reach it. -/
def coverage (cs : List Call) : List (String × Nat) :=
  let count (p : Call → Bool) := (cs.filter p).length
  let push (c : Call) := c.f.name == ringPush.name
  let pop (c : Call) := c.f.name == ringPop.name
  [("push at tail = 2^32-1 that wraps to 0", count fun c =>
      push c && c.word 1 == some 4294967295 && c.returns == some 0),
   ("push across 2^31", count fun c => push c && c.word 1 == some 2147483647 &&
      c.returns == some 2147483648),
   ("push into a full ring, which returns tail", count fun c =>
      push c && (c.returns.map Int.toNat) == c.word 1 && c.occupancy == (c.word 2).map (· + 1)),
   ("pop at head = 2^32-1 that wraps to 0", count fun c =>
      pop c && c.word 0 == some 4294967295 && c.returns == some 0),
   ("pop from an empty ring", count fun c => pop c && (c.returns.map Int.toNat) == c.word 0),
   ("call the model leaves undefined", count fun c => (evalFunc_u32 fuel c.f c.args).isNone)]

/-! ## The C side -/

def driver (base : String) (fs : List MicroCFunc) : String := Id.run do
  let mut src := "#include <stdio.h>\n#include <stdlib.h>\n#include <string.h>\n#include \"" ++
    base ++ ".h\"\n\nstatic FILE *in;\n\n" ++
    "static uint32_t num(void) {\n  unsigned long v;\n  if (fscanf(in, \"%lu\", &v) != 1) exit(3);\n" ++
    "  return (uint32_t)v;\n}\n\n" ++
    "static uint32_t *cells(uint32_t *n) {\n  *n = num();\n" ++
    "  uint32_t *p = malloc(*n ? *n * sizeof(uint32_t) : 1);\n  if (p == NULL) exit(4);\n" ++
    "  for (uint32_t i = 0; i < *n; i++) p[i] = num();\n  return p;\n}\n\n" ++
    "static void show(const uint32_t *p, uint32_t n) {\n  printf(\" |\");\n" ++
    "  for (uint32_t i = 0; i < n; i++) printf(\" %u\", (unsigned)p[i]);\n}\n\n" ++
    "int main(int argc, char **argv) {\n  char fn[64];\n  (void)cells; (void)show;\n" ++
    "  if (argc != 2 || (in = fopen(argv[1], \"r\")) == NULL) return 2;\n" ++
    "  while (fscanf(in, \"%63s\", fn) == 1) {\n"
  for f in fs do
    src := src ++ s!"    if (strcmp(fn, \"{f.name}\") == 0) \{\n"
    let mut args : List String := []
    let mut bufs : List String := []
    for (p, i) in f.params.zipIdx do
      let a := s!"a{i}"
      args := args ++ [a]
      src := src ++ match p.2 with
        | .bool => s!"      bool {a} = num() != 0;\n"
        | .ptrU32 => s!"      uint32_t n{i}; uint32_t *{a} = cells(&n{i});\n"
        | _ => s!"      uint32_t {a} = num();\n"
      if p.2 == .ptrU32 then bufs := bufs ++ [s!"{i}"]
    src := src ++ s!"      {f.ret.name} r = {f.name}({", ".intercalate args});\n" ++
      (if f.ret == .bool then "      printf(\"%d\", (int)r);\n"
       else "      printf(\"%u\", (unsigned)r);\n")
    for i in bufs do
      src := src ++ s!"      show(a{i}, n{i});\n      free(a{i});\n"
    src := src ++ "      printf(\"\\n\");\n      fflush(stdout);\n      continue;\n    }\n"
  src ++ "    return 5;\n  }\n  fclose(in);\n  return 0;\n}\n"

/-- The first `clang` on `PATH` outside the Lean toolchain, whose bundled clang has no libc
    headers or sanitizer runtime. -/
def systemClang : IO FilePath := do
  let leanBin := (← IO.appPath).parent
  let dirs := ((← IO.getEnv "PATH").getD "").splitOn ":" |>.map FilePath.mk
  for d in dirs do
    if some d != leanBin && (← (d / "clang").pathExists) then return d / "clang"
  throw <| IO.userError "no clang on PATH outside the Lean toolchain"

def generatorSha : IO String := do
  try
    let out ← IO.Process.output { cmd := "git", args := #["rev-parse", "HEAD"] }
    pure (if out.exitCode == 0 then out.stdout.trimAscii.toString else "unknown")
  catch _ => pure "unknown"

/-- Writes the header, source and driver to `dir` after `edit`, and builds them. -/
def build (dir : FilePath) (edit : String → String := id) : IO FilePath := do
  let (h, c) := emitFile "ring" (← generatorSha) funcs
  IO.FS.createDirAll dir
  IO.FS.writeFile (dir / "ring.h") (edit h)
  IO.FS.writeFile (dir / "ring.c") (edit c)
  IO.FS.writeFile (dir / "ring_driver.c") (driver "ring" funcs)
  let exe := dir / "ring"
  let cc ← IO.Process.output {
    cmd := (← systemClang).toString,
    args := #["-std=c11", "-Wall", "-Werror", "-g", "-fno-omit-frame-pointer",
      "-fsanitize=address,undefined", "-fno-sanitize-recover=undefined", "-I", dir.toString,
      (dir / "ring.c").toString, (dir / "ring_driver.c").toString, "-o", exe.toString] }
  if cc.exitCode != 0 then
    throw <| IO.userError s!"clang failed with exit {cc.exitCode}:\n{cc.stderr}"
  pure exe

def sanitizerReport (stderr : String) : Option String :=
  match stderr.splitOn "runtime error: ", stderr.splitOn "ERROR: AddressSanitizer: " with
  | _ :: msg :: _, _ | _, _ :: msg :: _ => (msg.splitOn "\n").head?
  | _, _ => none

def runCalls (exe dir : FilePath) (name : String) (cs : List Call) : IO IO.Process.Output := do
  IO.FS.writeFile (dir / name) ("\n".intercalate (cs.map Call.input) ++ "\n")
  IO.Process.output {
    cmd := exe.toString, args := #[(dir / name).toString],
    env := #[("ASAN_OPTIONS", some "detect_leaks=0")] }

/-- Runs every call with a defined model in one process and each other call alone, and returns
    a description of each disagreement. -/
def judge (exe dir : FilePath) (model : Model) (cs : List Call) : IO (Array String) := do
  let defined := cs.filter (model · |>.isSome)
  let undefined := cs.filter (model · |>.isNone)
  let out ← runCalls exe dir "calls.txt" defined
  let lines := (out.stdout.splitOn "\n").toArray
  let mut bad := #[]
  for c in defined, i in [0:defined.length] do
    let want := (model c).getD ""
    let got := lines[i]?.getD ""
    if got != want then
      let report := (sanitizerReport out.stderr).getD "no sanitizer report"
      bad := bad.push s!"{c.input}: model {want}, C printed {got} (exit {out.exitCode}, {report})"
  for c in undefined do
    let o ← runCalls exe dir "undefined.txt" [c]
    if o.exitCode == 0 || (sanitizerReport o.stderr).isNone then
      bad := bad.push s!"{c.input}: model none, C exit {o.exitCode} printed {o.stdout.trimAscii} without a sanitizer report"
  pure bad

def summary (model : Model) (cs : List Call) (bad : Array String) : String :=
  let n := (cs.filter (model · |>.isNone)).length
  s!"{cs.length} calls ({n} undefined): {cs.length - bad.size} agree, {bad.size} disagree"

/-! ## Controls -/

/-- Every `uint32_t` printed as `int32_t`, the buffer type excepted. -/
def asInt32 (s : String) : String :=
  ((s.replace "uint32_t *restrict" "BUF").replace "uint32_t" "int32_t").replace "BUF" "uint32_t *restrict"

/-- Every `u` suffix dropped from a decimal literal. -/
def unsuffixed (s : String) : String := Id.run do
  let mut out : List Char := []
  let mut inNumber := false
  let mut prev := ' '
  for c in s.toList do
    unless c == 'u' && inNumber do out := out ++ [c]
    inNumber := c.isDigit && (inNumber || !(prev.isAlpha || prev.isDigit || prev == '_'))
    prev := c
  String.ofList out

def selfTest : IO UInt32 := do
  IO.FS.withTempDir fun d => do
    let exe ← build (d / "plain")
    let controls : List (String × IO (Array String) × Bool) := [
      ("the push across 2^32 agrees", judge exe d bounded [pushWrap], true),
      ("the push into a full ring agrees", judge exe d bounded [pushFull], true),
      ("the store past a short buffer is none and the sanitizer reports it",
        judge exe d bounded [pushShort], true),
      ("the same store under evalMicroC_uint32, which has no bound, disagrees",
        judge exe d unbounded [pushShort], false),
      ("the calls with every uint32_t printed as int32_t disagree", do
        let exe ← build (d / "int32") asInt32
        judge exe (d / "int32") bounded calls, false),
      ("the calls with unsuffixed literals disagree", do
        let exe ← build (d / "unsuffixed") unsuffixed
        judge exe (d / "unsuffixed") bounded calls, false),
      ("no calls reach none of the required cases",
        pure ((coverage []).filter (·.2 == 0) |>.map (·.1) |>.toArray), false)]
    let mut failed := 0
    for (label, run, want) in controls do
      let bad ← run
      let ok := bad.isEmpty == want
      let first := match bad[0]? with
        | some b => "; first: " ++ b
        | none => ""
      IO.println s!"{if ok then "ok  " else "FAIL"} {label}: {bad.size} disagree{first}"
      unless ok do failed := failed + 1
    IO.println s!"{controls.length - failed} of {controls.length} controls hold"
    pure (if failed == 0 then 0 else 1)

def main (args : List String) : IO UInt32 := do
  unless decide (WFFile funcs) do
    IO.eprintln "the ring functions are not well formed"; return 1
  match args with
  | ["--self-test"] => selfTest
  | [] =>
    let dir : FilePath := "examples/out"
    let exe ← build dir
    let bad ← judge exe dir bounded calls
    for b in bad.toList.take 10 do IO.println s!"FAIL {b}"
    let cov := coverage calls
    for (label, n) in cov do
      IO.println s!"{if n == 0 then "FAIL" else "ok  "} {n} calls: {label}"
    IO.println (summary bounded calls bad)
    pure (if bad.isEmpty && cov.all (·.2 > 0) then 0 else 1)
  | _ => IO.eprintln "usage: Ring.lean [--self-test]"; pure 2
