import TrustLean.Pipeline
import TrustLean.Frontend.ArithExpr
import TrustLean.Backend.CBackend

/-! `lake env lean --run examples/Export.lean export.c` writes `3 + v0 * 5` as C. -/

open TrustLean

def expr : ArithExpr := .add (.lit 3) (.mul (.var 0) (.lit 5))

def main (args : List String) : IO Unit := do
  let path := args.headD "export.c"
  let expected := ArithExpr.eval (fun _ => 7) expr
  IO.FS.writeFile path <| Pipeline.emit expr ({} : CConfig) "f" [("v0", "int64_t")] ++
    s!"\n\n#ifndef EXPECTED\n#define EXPECTED {expected}\n#endif\n\n" ++
    "int main(void) { return f(7) == EXPECTED ? 0 : 1; }\n"
  IO.println s!"wrote {path}: f(7) should be {expected}"
