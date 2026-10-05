/-
  Trust-Lean — Verified Code Generation Framework
  MicroC/Bridge.lean: Bridge predicate linking LowLevelEnv and MicroCEnv

  N11.2 (v2.0.0): CRITICO — defines the microCBridge predicate and proves
  key properties:
  - Bridge preservation under env updates
  - Expression evaluation bridge (evalExpr = evalMicroCExpr ∘ exprToMicroC)

  The bridge connects VarName-keyed environments (Core IR) to
  String-keyed environments (MicroC) via varNameToC, which is injective
  (varNameToC_injective).
-/

import TrustLean.MicroC.Translation
import TrustLean.MicroC.EvalWith

set_option autoImplicit false

namespace TrustLean

/-! ## Bridge Predicate -/

/-- The bridge predicate: links a Core IR environment (VarName → Value)
    to a MicroC environment (String → Value) via varNameToC.
    For every variable v, both environments agree on its value. -/
def microCBridge (env : LowLevelEnv) (mcEnv : MicroCEnv) : Prop :=
  ∀ v : VarName, env v = mcEnv (varNameToC v)

/-! ## Bridge Preservation -/

/-- Bridge holds for default environments. -/
theorem microCBridge_default :
    microCBridge LowLevelEnv.default MicroCEnv.default := by
  intro v; rfl

/-- Bridge is preserved by updating the same variable. -/
theorem microCBridge_update {env : LowLevelEnv} {mcEnv : MicroCEnv}
    (hb : microCBridge env mcEnv) (name : VarName) (v : Value) :
    microCBridge (env.update name v) (mcEnv.update (varNameToC name) v) := by
  intro w
  unfold microCBridge at hb
  simp only [LowLevelEnv.update, MicroCEnv.update]
  by_cases hw : w = name
  · subst hw; simp
  · have hne : varNameToC w ≠ varNameToC name := fun h => hw (varNameToC_injective h)
    simp [hw, hne, hb w]

/-! ## Operator Bridge Lemmas -/

/-- Core lemma: operator evaluation is preserved across the translation.
    evalMicroCBinOp (binOpToMicroC op) = evalBinOp op -/
@[simp] theorem evalMicroCBinOp_eq_evalBinOp (op : BinOp) (v1 v2 : Value) :
    evalMicroCBinOp (binOpToMicroC op) v1 v2 = evalBinOp op v1 v2 := by
  simp [evalMicroCBinOp]

/-- Core lemma: unary operator evaluation is preserved across the translation. -/
@[simp] theorem evalMicroCUnaryOp_eq_evalUnaryOp (op : UnaryOp) (v : Value) :
    evalMicroCUnaryOp (unaryOpToMicroC op) v = evalUnaryOp op v := by
  simp [evalMicroCUnaryOp]

/-! ## Expression Bridge -/

/-- Expression bridge for every operator semantics: evaluating a Core expression in env with
    `S.core` equals evaluating the translated MicroC expression in the bridged mcEnv with `S`.
    No fuel needed — both evaluators are structural. -/
theorem exprToMicroC_bridge_with (S : MicroCOps) (env : LowLevelEnv) (mcEnv : MicroCEnv)
    (e : LowLevelExpr) (hb : microCBridge env mcEnv) :
    evalExprWith S.core env e = evalMicroCExprWith S mcEnv (exprToMicroC e) := by
  induction e with
  | litInt n => rfl
  | litBool b => rfl
  | varRef v =>
    simp only [evalExprWith, exprToMicroC_varRef, evalMicroCExprWith]
    exact congrArg some (hb v)
  | binOp op e1 e2 ih1 ih2 =>
    simp only [evalExprWith, exprToMicroC_binOp, evalMicroCExprWith, ih1, ih2]; rfl
  | unaryOp op e ih =>
    simp only [evalExprWith, exprToMicroC_unaryOp, evalMicroCExprWith, ih]; rfl
  | powCall base n ih =>
    simp only [evalExprWith, exprToMicroC_powCall, evalMicroCExprWith, ih]; rfl
  | addrOf v =>
    simp only [evalExprWith, exprToMicroC_addrOf, evalMicroCExprWith]
    exact congrArg some (hb v)

/-- Expression bridge: evaluating a Core expression in env equals
    evaluating the translated MicroC expression in the bridged mcEnv.

    This is the key semantic preservation theorem for expressions. -/
theorem exprToMicroC_bridge (env : LowLevelEnv) (mcEnv : MicroCEnv)
    (e : LowLevelExpr) (hb : microCBridge env mcEnv) :
    evalExpr env e = evalMicroCExpr mcEnv (exprToMicroC e) := by
  rw [evalExpr_eq_with, evalMicroCExpr_eq_with, ← MicroCOps.int_core]
  exact exprToMicroC_bridge_with .int env mcEnv e hb

/-! ## Array Name Bridge -/

/-- Specialized: for user variable array bases (the common case),
    the MicroC array name is the C identifier of the Core name. -/
theorem getArrayName_user_bridge (name : String) :
    getMicroCArrayName (exprToMicroC (.varRef (.user name))) =
      some (varNameToC (.user name)) := by
  simp [exprToMicroC, getMicroCArrayName]

/-- getArrayName correspondence: if Core's getArrayName extracts a name
    from base, then getMicroCArrayName extracts a corresponding name
    from the translated expression. -/
theorem getArrayName_bridge (base : LowLevelExpr)
    (name : String) (h : getArrayName base = some name) :
    ∃ mcName, getMicroCArrayName (exprToMicroC base) = some mcName := by
  cases base with
  | varRef v =>
    cases v with
    | user s => exact ⟨_, getArrayName_user_bridge s⟩
    | array s idx =>
      simp only [exprToMicroC, getMicroCArrayName, varNameToC]
      exact ⟨_, rfl⟩
    | temp _ => simp [getArrayName] at h
  | _ => simp [getArrayName] at h

end TrustLean
