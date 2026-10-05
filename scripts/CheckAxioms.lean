import Lean

/-! Fails unless every gate theorem of the built `TrustLean` library depends only on
`propext`, `Classical.choice` and `Quot.sound`. A gate theorem is one listed in
`required`, or any public theorem under `TrustLean` whose name ends in `_correct`,
contains `_correct_`, or starts with `master_`.

    lake build && lake env lean --run scripts/CheckAxioms.lean
    lean --run scripts/CheckAxioms.lean --self-test -/

open Lean System

def standard : Array Name := #[``propext, ``Classical.choice, ``Quot.sound]

def required : Array Name := #[
  `TrustLean.master_roundtrip, `TrustLean.master_expr_roundtrip,
  `TrustLean.master_roundtrip_rust, `TrustLean.master_expr_roundtrip_rust,
  `TrustLean.parseMicroC_roundtrip, `TrustLean.parseMicroCExpr_roundtrip,
  `TrustLean.parseMicroRust_roundtrip, `TrustLean.parseMicroRustExpr_roundtrip,
  `TrustLean.stmtToMicroC_correct, `TrustLean.stmtToMicroC_correct_withCalls,
  `TrustLean.stmtToMicroRust_correct, `TrustLean.stmtToMicroRust_correct_withCalls,
  `TrustLean.Bridge.expandedSigmaToStmt_correct, `TrustLean.Pipeline.sound,
  `TrustLean.varNameToC_injective, `TrustLean.varNameToRust_injective,
  `TrustLean.microCExprToString_trunc_3000000000, `TrustLean.microCExprToString_widen_neg5,
  `TrustLean.microRustExprToString_trunc_3000000000, `TrustLean.microRustExprToString_widen_neg5,
  `TrustLean.evalMicroCBinOp_int64_inRange, `TrustLean.evalMicroCUnaryOp_int64_inRange,
  `TrustLean.evalMicroCBinOp_int64_refines, `TrustLean.evalMicroCUnaryOp_int64_refines,
  `TrustLean.evalMicroCBinOp_int64_add_eq_some, `TrustLean.evalMicroCBinOp_int64_add_maxInt64_one,
  `TrustLean.evalMicroCBinOp_uint32_shl_1_40,
  `TrustLean.master_typed_roundtrip, `TrustLean.evalTyped_eq_evalMicroC_uint32,
  `TrustLean.evalTyped_preserves_types, `TrustLean.evalTypedExpr_definedOn,
  `TrustLean.evalMicroC_uint32_eq_evalS32, `TrustLean.evalTyped_eq_evalS32,
  `TrustLean.evalMicroC_uint32_pushK, `TrustLean.evalMicroC_ne_evalS32]

def isGateName (n : Name) : Bool :=
  match n with
  | .str _ s => s.endsWith "_correct" || (s.splitOn "_correct_").length > 1 || s.startsWith "master_"
  | _ => false

/-- `native_decide`, `bv_decide` and `decide +native` each add an axiom `<thm>._native.<tactic>.ax_*`. -/
def kind (a : Name) : String :=
  let cs := a.components.map (·.toString)
  match cs.dropWhile (· != "_native") with
  | _ :: tac :: _ => tac
  | _ => if a == ``sorryAx then "sorry" else a.toString

def gateNames (env : Environment) (pfx : Name) : Array Name := Id.run do
  let mut out := #[]
  for mod in env.header.moduleNames, data in env.header.moduleData do
    unless pfx.isPrefixOf mod do continue
    for n in data.constNames do
      if n.isInternal || !isGateName n then continue
      if let some (.thmInfo _) := env.find? n then out := out.push n
  out

structure Report where
  checked : Array (Name × Array Name)
  missing : Array Name

/-- The failing gate theorems, or `none` when a required theorem is missing or none was found. -/
def verdict (r : Report) : Option (Array Name) :=
  if !r.missing.isEmpty || r.checked.isEmpty then none
  else some ((r.checked.filter fun (_, axs) => axs.any (!standard.contains ·)).map (·.1))

def gate (env : Environment) (pfx : Name) (req : Array Name) : IO Report := do
  let found := gateNames env pfx
  let names := found ++ req.filter (fun n => !found.contains n && env.contains n)
  let ctx : Core.Context := { fileName := "<axiom gate>", fileMap := default }
  let checked ← names.mapM fun n => do
    let axs ← (collectAxioms n : CoreM _).toIO' ctx { env }
    pure (n, axs)
  pure { checked, missing := req.filter (!env.contains ·) }

def loadEnv (mod : Name) (extra : System.SearchPath := ∅) : IO Environment := do
  initSearchPath (← findSysroot (← IO.appPath).toString) extra
  importModules #[{ module := mod }] {}

def report (r : Report) : IO UInt32 := do
  for (n, axs) in r.checked do
    let off := axs.filter (!standard.contains ·)
    if off.isEmpty then IO.println s!"ok   {n} {axs.toList}"
    else
      let kinds := (off.map kind).toList.eraseDups
      IO.println s!"FAIL {n}: {off.size} axioms outside the standard three ({kinds})"
  for n in r.missing do IO.println s!"FAIL required gate theorem {n} does not exist"
  let bad := (verdict r).map (·.size)
  IO.println s!"{r.checked.size} gate theorems checked, {bad.getD 0} rest on other axioms, {r.missing.size} required missing"
  pure (if bad == some 0 then 0 else 1)

def plantedHeader : String := "import Std.Tactic.BVDecide\n"

def okThm : String :=
  "theorem good_correct (p : Prop) : p ∨ ¬p := Classical.em p\n" ++
  "theorem master_good (a b : Nat) (h : a = b) : b = a := by simp [h]\n"

/-- Compiles `src` as module `P` in a temp dir and returns the gate's verdict on it. -/
def runPlanted (src : String) (req : Array Name) : IO (Option (Array Name)) :=
  IO.FS.withTempDir fun d => do
    IO.FS.writeFile (d / "P.lean") (plantedHeader ++ src)
    let out ← IO.Process.output {
      cmd := (← IO.appPath).toString, cwd := d,
      args := #["-o", (d / "P.olean").toString, (d / "P.lean").toString] }
    if out.exitCode != 0 then
      throw <| IO.userError s!"planted module did not compile:\n{out.stdout}{out.stderr}"
    return verdict (← gate (← loadEnv `P [d]) `P req)

def selfTest : IO UInt32 := do
  let mut failed := 0
  let cases : List (String × String × Array Name × Option (Array Name)) :=
    [("standard axioms pass", okThm, #[], some #[]),
     ("native_decide fails", okThm ++ "theorem nd_correct : 2 ^ 10 = 1024 := by native_decide\n",
       #[], some #[`nd_correct]),
     ("bv_decide fails", okThm ++ "theorem bv_correct (x y : BitVec 8) : x * y = y * x := by bv_decide\n",
       #[], some #[`bv_correct]),
     ("decide +native fails", okThm ++ "theorem master_dn : 2 ^ 10 = 1024 := by decide +native\n",
       #[], some #[`master_dn]),
     ("sorry fails", okThm ++ "theorem s_correct_withX : 1 = 2 := sorry\n", #[], some #[`s_correct_withX]),
     ("declared axiom fails", okThm ++ "axiom bad : 1 = 2\ntheorem ax_correct : 1 = 2 := bad\n",
       #[], some #[`ax_correct]),
     ("native_decide through a lemma fails",
       okThm ++ "theorem leaf : 2 ^ 10 = 1024 := by native_decide\ntheorem dep_correct : 2 ^ 10 = 1024 := leaf\n",
       #[], some #[`dep_correct]),
     ("required name outside the pattern is checked",
       okThm ++ "theorem sound : 2 ^ 10 = 1024 := by native_decide\n", #[`sound], some #[`sound]),
     ("missing required name stops the gate", okThm, #[`absent_correct], none),
     ("no gate theorem stops the gate", "theorem other : True := trivial\n", #[], none)]
  for (label, src, req, want) in cases do
    let got ← runPlanted src req
    let ok := got == want
    IO.println s!"{if ok then "ok  " else "FAIL"} {label}: got {repr got}"
    unless ok do failed := failed + 1
  IO.println s!"{cases.length - failed} of {cases.length} controls hold"
  pure (if failed == 0 then 0 else 1)

def main (args : List String) : IO UInt32 := do
  match args with
  | ["--self-test"] => selfTest
  | [] => report (← gate (← loadEnv `TrustLean) `TrustLean required)
  | _ => IO.eprintln "usage: CheckAxioms.lean [--self-test]"; pure 2
