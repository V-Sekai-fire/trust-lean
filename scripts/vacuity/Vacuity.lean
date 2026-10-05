import TrustLean.MicroC.Simulation

/-! Expected to fail. `varNameToC` is injective, so `decide` refutes both collisions below and
the proof that `VarNameInjective` is false no longer compiles. `scripts/CheckVacuity.lean`
asserts that it fails for exactly that reason. -/

open TrustLean

/-- The simulation theorem's injectivity hypothesis is false: two user names collide. -/
theorem varNameInjective_false : ¬ VarNameInjective := by
  intro h
  have : varNameToC (.user "int") = varNameToC (.user "tl_int") := by decide
  exact absurd (h this) (by decide)

/-- A temp and a user name also collide. -/
example : varNameToC (.temp 0) = varNameToC (.user "t0") := by decide

/-- Hence stmtToMicroC_correct would prove anything about any statement. -/
example : ∀ (stmt : Stmt) (mcEnv : MicroCEnv) (fuel : Nat),
    VarNameInjective → evalMicroC fuel mcEnv (stmtToMicroC stmt) = none := by
  intro _ _ _ h; exact absurd h varNameInjective_false
