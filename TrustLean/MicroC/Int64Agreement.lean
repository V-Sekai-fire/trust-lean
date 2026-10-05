/-
  Trust-Lean — Verified Code Generation Framework
  MicroC/Int64Agreement.lean: Int64-Unbounded Agreement Theorems (v3.0.0)

  N14.3: Proves that when arithmetic results are in Int64 range,
  the int64 evaluator agrees with the unbounded evaluator.

  Key theorems:
  - evalMicroCBinOp_int64_refines / evalMicroCUnaryOp_int64_refines: a value the int64
    evaluator returns is the value the unbounded evaluator returns
  - evalMicroCBinOp_int64_agree: general BinOp agreement (shifts: per-op theorems)
  - evalMicroCUnaryOp_int64_agree: general UnaryOp agreement
  - Per-operator convenience theorems for add/sub/mul
  - Non-vacuity example: concrete overflow-free program agreement
-/

import TrustLean.MicroC.Int64Eval

set_option autoImplicit false

namespace TrustLean

/-! ## Per-Operator BinOp Agreement -/

/-- Addition agrees when result is in Int64 range. -/
theorem evalMicroCBinOp_int64_agree_add (a b : Int) (h : InInt64Range (a + b)) :
    evalMicroCBinOp_int64 .add (.int a) (.int b) =
    evalMicroCBinOp .add (.int a) (.int b) := by
  simp only [evalMicroCBinOp_int64_add, evalMicroCBinOp, microCBinOpToCore, evalBinOp_add,
             checkedInt64_of_inRange h, Option.map_some]

/-- Subtraction agrees when result is in Int64 range. -/
theorem evalMicroCBinOp_int64_agree_sub (a b : Int) (h : InInt64Range (a - b)) :
    evalMicroCBinOp_int64 .sub (.int a) (.int b) =
    evalMicroCBinOp .sub (.int a) (.int b) := by
  simp only [evalMicroCBinOp_int64_sub, evalMicroCBinOp, microCBinOpToCore, evalBinOp_sub,
             checkedInt64_of_inRange h, Option.map_some]

/-- Multiplication agrees when result is in Int64 range. -/
theorem evalMicroCBinOp_int64_agree_mul (a b : Int) (h : InInt64Range (a * b)) :
    evalMicroCBinOp_int64 .mul (.int a) (.int b) =
    evalMicroCBinOp .mul (.int a) (.int b) := by
  simp only [evalMicroCBinOp_int64_mul, evalMicroCBinOp, microCBinOpToCore, evalBinOp_mul,
             checkedInt64_of_inRange h, Option.map_some]

/-! ## Non-Arithmetic BinOp Agreement (Unconditional) -/

/-- Equality comparison always agrees (produces Bool, no wrapping). -/
theorem evalMicroCBinOp_int64_agree_eqOp (a b : Int) :
    evalMicroCBinOp_int64 .eqOp (.int a) (.int b) =
    evalMicroCBinOp .eqOp (.int a) (.int b) := by
  simp [evalMicroCBinOp_int64, evalMicroCBinOp, evalBinOp, microCBinOpToCore]

/-- Less-than comparison always agrees (produces Bool, no wrapping). -/
theorem evalMicroCBinOp_int64_agree_ltOp (a b : Int) :
    evalMicroCBinOp_int64 .ltOp (.int a) (.int b) =
    evalMicroCBinOp .ltOp (.int a) (.int b) := by
  simp [evalMicroCBinOp_int64, evalMicroCBinOp, evalBinOp, microCBinOpToCore]

/-- Logical AND always agrees (operates on Bool). -/
theorem evalMicroCBinOp_int64_agree_land (a b : Bool) :
    evalMicroCBinOp_int64 .land (.bool a) (.bool b) =
    evalMicroCBinOp .land (.bool a) (.bool b) := by
  simp [evalMicroCBinOp_int64, evalMicroCBinOp, evalBinOp, microCBinOpToCore]

/-- Logical OR always agrees (operates on Bool). -/
theorem evalMicroCBinOp_int64_agree_lor (a b : Bool) :
    evalMicroCBinOp_int64 .lor (.bool a) (.bool b) =
    evalMicroCBinOp .lor (.bool a) (.bool b) := by
  simp [evalMicroCBinOp_int64, evalMicroCBinOp, evalBinOp, microCBinOpToCore]

/-! ### Bitwise: CONDITIONAL on InInt64Range(result) -/

/-- Bitwise AND agrees when result is in Int64 range. -/
theorem evalMicroCBinOp_int64_agree_band (a b : Int) (h : InInt64Range (Int.land a b)) :
    evalMicroCBinOp_int64 .band (.int a) (.int b) =
    evalMicroCBinOp .band (.int a) (.int b) := by
  simp only [evalMicroCBinOp_int64_band, evalMicroCBinOp, microCBinOpToCore, evalBinOp_band,
             checkedInt64_of_inRange h, Option.map_some]

/-- Bitwise OR agrees when result is in Int64 range. -/
theorem evalMicroCBinOp_int64_agree_bor (a b : Int) (h : InInt64Range (Int.lor a b)) :
    evalMicroCBinOp_int64 .bor (.int a) (.int b) =
    evalMicroCBinOp .bor (.int a) (.int b) := by
  simp only [evalMicroCBinOp_int64_bor, evalMicroCBinOp, microCBinOpToCore, evalBinOp_bor,
             checkedInt64_of_inRange h, Option.map_some]

/-- Bitwise XOR agrees when result is in Int64 range. -/
theorem evalMicroCBinOp_int64_agree_bxor (a b : Int) (h : InInt64Range (Int.xor a b)) :
    evalMicroCBinOp_int64 .bxor (.int a) (.int b) =
    evalMicroCBinOp .bxor (.int a) (.int b) := by
  simp only [evalMicroCBinOp_int64_bxor, evalMicroCBinOp, microCBinOpToCore, evalBinOp_bxor,
             checkedInt64_of_inRange h, Option.map_some]

/-- Left shift agrees when the count is in `[0, 64)`, the shifted value is non-negative and
    the result is in Int64 range. -/
theorem evalMicroCBinOp_int64_agree_bshl (a b : Int) (hb : 0 ≤ b ∧ b < 64) (ha : 0 ≤ a)
    (h : InInt64Range (Int.shiftLeft a (b.toNat % 64))) :
    evalMicroCBinOp_int64 .bshl (.int a) (.int b) =
    evalMicroCBinOp .bshl (.int a) (.int b) := by
  have hm : b.toNat % 64 = b.toNat := Nat.mod_eq_of_lt (by omega)
  have hc : 0 ≤ b ∧ b < 64 ∧ 0 ≤ a := ⟨hb.1, hb.2, ha⟩
  rw [hm] at h
  simp only [evalMicroCBinOp_int64_bshl, evalMicroCBinOp, microCBinOpToCore, evalBinOp_bshl,
             shlInt64, if_pos hc, checkedInt64_of_inRange h, Option.map_some, hm]

/-- Right shift agrees when the count is in `[0, 64)`, the shifted value is non-negative and
    the result is in Int64 range. -/
theorem evalMicroCBinOp_int64_agree_bshr (a b : Int) (hb : 0 ≤ b ∧ b < 64) (ha : 0 ≤ a)
    (h : InInt64Range (Int.shiftRight a (b.toNat % 64))) :
    evalMicroCBinOp_int64 .bshr (.int a) (.int b) =
    evalMicroCBinOp .bshr (.int a) (.int b) := by
  have hm : b.toNat % 64 = b.toNat := Nat.mod_eq_of_lt (by omega)
  have hc : 0 ≤ b ∧ b < 64 ∧ 0 ≤ a := ⟨hb.1, hb.2, ha⟩
  rw [hm] at h
  simp only [evalMicroCBinOp_int64_bshr, evalMicroCBinOp, microCBinOpToCore, evalBinOp_bshr,
             shrInt64, if_pos hc, checkedInt64_of_inRange h, Option.map_some, hm]

/-! ## General BinOp Agreement -/

/-- General BinOp agreement for every operator but the shifts: if every Int result of the
    unbounded evaluator is in Int64 range, the int64 evaluator agrees.
    For comparison/logical ops, the hypothesis is vacuously satisfied
    (they produce Bool, not Int). -/
theorem evalMicroCBinOp_int64_agree (op : MicroCBinOp) (v1 v2 : Value)
    (hop : op ≠ .bshl ∧ op ≠ .bshr)
    (h : ∀ n, evalMicroCBinOp op v1 v2 = some (.int n) → InInt64Range n) :
    evalMicroCBinOp_int64 op v1 v2 = evalMicroCBinOp op v1 v2 := by
  cases op <;> cases v1 <;> cases v2 <;>
    simp_all [evalMicroCBinOp_int64, evalMicroCBinOp, evalBinOp, microCBinOpToCore,
              checkedInt64_of_inRange]

/-- A value the int64 binary evaluator returns is the value the unbounded evaluator returns. -/
theorem evalMicroCBinOp_int64_refines (op : MicroCBinOp) (v1 v2 v : Value)
    (h : evalMicroCBinOp_int64 op v1 v2 = some v) : evalMicroCBinOp op v1 v2 = some v := by
  cases op <;> cases v1 <;> cases v2 <;>
    simp only [evalMicroCBinOp_int64, Option.map_eq_some_iff] at h <;>
    simp only [evalMicroCBinOp, microCBinOpToCore, evalBinOp] <;>
    first
    | exact h
    | (obtain ⟨m, hm, rfl⟩ := h; rw [(checkedInt64_eq_some.mp hm).2])
    | (obtain ⟨m, hm, rfl⟩ := h
       obtain ⟨⟨hb0, hb1, -⟩, hc⟩ := shlInt64_eq_some.mp hm
       rw [(checkedInt64_eq_some.mp hc).2, Nat.mod_eq_of_lt (by omega)])
    | (obtain ⟨m, hm, rfl⟩ := h
       obtain ⟨⟨hb0, hb1, -⟩, hc⟩ := shrInt64_eq_some.mp hm
       rw [(checkedInt64_eq_some.mp hc).2, Nat.mod_eq_of_lt (by omega)])

/-! ## UnaryOp Agreement -/

/-- Negation agrees when result is in Int64 range. -/
theorem evalMicroCUnaryOp_int64_agree_neg (n : Int) (h : InInt64Range (-n)) :
    evalMicroCUnaryOp_int64 .neg (.int n) =
    evalMicroCUnaryOp .neg (.int n) := by
  simp only [evalMicroCUnaryOp_int64_neg, evalMicroCUnaryOp, evalUnaryOp, microCUnaryOpToCore,
             checkedInt64_of_inRange h, Option.map_some]

/-- Logical not always agrees (operates on Bool). -/
theorem evalMicroCUnaryOp_int64_agree_lnot (b : Bool) :
    evalMicroCUnaryOp_int64 .lnot (.bool b) =
    evalMicroCUnaryOp .lnot (.bool b) := by
  simp [evalMicroCUnaryOp_int64, evalMicroCUnaryOp, evalUnaryOp, microCUnaryOpToCore]

/-- General UnaryOp agreement. -/
theorem evalMicroCUnaryOp_int64_agree (op : MicroCUnaryOp) (v : Value)
    (h : ∀ n, evalMicroCUnaryOp op v = some (.int n) → InInt64Range n) :
    evalMicroCUnaryOp_int64 op v = evalMicroCUnaryOp op v := by
  cases op <;> cases v <;>
    simp_all [evalMicroCUnaryOp_int64, evalMicroCUnaryOp, evalUnaryOp, microCUnaryOpToCore,
              checkedInt64_of_inRange]

/-- A value the int64 unary evaluator returns is the value the unbounded evaluator returns. -/
theorem evalMicroCUnaryOp_int64_refines (op : MicroCUnaryOp) (v w : Value)
    (h : evalMicroCUnaryOp_int64 op v = some w) : evalMicroCUnaryOp op v = some w := by
  cases op <;> cases v <;>
    simp only [evalMicroCUnaryOp_int64, Option.map_eq_some_iff] at h <;>
    simp only [evalMicroCUnaryOp, microCUnaryOpToCore, evalUnaryOp] <;>
    first
    | exact h
    | (obtain ⟨m, hm, rfl⟩ := h; rw [(checkedInt64_eq_some.mp hm).2])

/-! ## Non-Vacuity: Overflow-Free Program Agreement -/

/-- Non-vacuity: simple assignment x = 3 + 4 produces x = 7 under both evaluators.
    This demonstrates that the BinOp agreement hypotheses are jointly satisfiable. -/
example :
    let stmt := MicroCStmt.assign "x" (.binOp .add (.litInt 3) (.litInt 4))
    let env := MicroCEnv.default
    -- Int64 evaluator produces x = 7
    (do let (_, e) ← evalMicroC_int64 10 env stmt; pure (e "x")) =
    some (.int 7) ∧
    -- Unbounded evaluator produces x = 7
    (do let (_, e) ← evalMicroC 10 env stmt; pure (e "x")) =
    some (.int 7) := by
  constructor <;> native_decide

/-- Non-vacuity: multi-step program x = 3 + 4; y = x * 2; z = y - 5.
    All intermediate results (7, 14, 9) are in Int64 range.
    Both evaluators produce z = 9. -/
example :
    let prog := MicroCStmt.seq
      (MicroCStmt.assign "x" (.binOp .add (.litInt 3) (.litInt 4)))
      (MicroCStmt.seq
        (MicroCStmt.assign "y" (.binOp .mul (.varRef "x") (.litInt 2)))
        (MicroCStmt.assign "z" (.binOp .sub (.varRef "y") (.litInt 5))))
    let env := MicroCEnv.default
    -- Both evaluators produce z = 9
    (do let (_, e) ← evalMicroC_int64 10 env prog; pure (e "z")) =
    some (.int 9) ∧
    (do let (_, e) ← evalMicroC 10 env prog; pure (e "z")) =
    some (.int 9) := by
  constructor <;> native_decide

/-- Non-vacuity: while loop agreement.
    sum = 0; i = 0; while (i < 3) { sum = sum + 10; i = i + 1 }
    Both evaluators produce sum = 30, verifying overflow-free agreement
    across multiple loop iterations. -/
example :
    let body := MicroCStmt.seq
      (MicroCStmt.assign "sum" (.binOp .add (.varRef "sum") (.litInt 10)))
      (MicroCStmt.assign "i" (.binOp .add (.varRef "i") (.litInt 1)))
    let loop := MicroCStmt.while_ (.binOp .ltOp (.varRef "i") (.litInt 3)) body
    let init := MicroCStmt.seq
      (MicroCStmt.assign "sum" (.litInt 0))
      (MicroCStmt.seq (MicroCStmt.assign "i" (.litInt 0)) loop)
    let env := MicroCEnv.default
    -- Both evaluators produce sum = 30
    (do let (_, e) ← evalMicroC_int64 10 env init; pure (e "sum")) =
    some (.int 30) ∧
    (do let (_, e) ← evalMicroC 10 env init; pure (e "sum")) =
    some (.int 30) := by
  constructor <;> native_decide

end TrustLean
