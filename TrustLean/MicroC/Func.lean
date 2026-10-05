/-
  Trust-Lean — Verified Code Generation Framework
  MicroC/Func.lean: functions with `uint32_t *restrict` buffer parameters

  A function has a return type, typed parameters, typed locals and a body. A parameter may be a
  `uint32_t *restrict` buffer, which the body reads with `x = p[i];` and writes with `p[i] = e;`.
  `master_func_roundtrip` parses a well-formed function's printed text back to the function,
  through `master_roundtrip` for its body.
-/

import TrustLean.MicroC.TypedRoundtrip

set_option autoImplicit false

namespace TrustLean

/-! ## Functions -/

structure MicroCFunc where
  name : String
  ret : CType
  params : CDecls
  locals : CDecls
  body : MicroCStmt
  deriving Repr, DecidableEq, Inhabited

/-- The expressions a statement evaluates. -/
def MicroCStmt.exprs : MicroCStmt → List MicroCExpr
  | .assign _ e | .return_ (some e) => [e]
  | .store b i v => [b, i, v]
  | .load _ b i => [b, i]
  | .call _ _ args => args
  | .seq s1 s2 => s1.exprs ++ s2.exprs
  | .ite c t e => c :: (t.exprs ++ e.exprs)
  | .while_ c b => c :: b.exprs
  | .skip | .break_ | .continue_ | .return_ none => []

/-- Every path through `s` ends in `return e;`; a loop counts as not returning. -/
def MicroCStmt.returns : MicroCStmt → Bool
  | .return_ (some _) => true
  | .seq s1 s2 => s1.returns || s2.returns
  | .ite _ t e => t.returns && e.returns
  | _ => false

/-! ## Typing -/

def isU32 (Γ : CDecls) (e : MicroCExpr) : Bool := (exprTy Γ e).map (·.1) == some .u32

def isBuf (Γ : CDecls) : MicroCExpr → Bool
  | .varRef p => Γ.lookup p == some .ptrU32
  | _ => false

/-- A function body under its parameters and locals `Γ`: the statements of `stmtTy`, `x = p[i];`
    and `p[i] = e;` on a buffer parameter `p` with a `uint32_t` index and value, and `return e;`
    with `e` of type `ret`. A pointer is never assigned. -/
def bodyTy (Γ : CDecls) (ret : CType) (inLoop : Bool) : MicroCStmt → Bool
  | .skip => true
  | .break_ => inLoop
  | .continue_ => inLoop
  | .assign x e =>
    match Γ.lookup x, exprTy Γ e with
    | some t, some (t', _) => t == t' && t != .ptrU32 && !sameVar (.varRef x) e && !e.isPowCall
    | _, _ => false
  | .store b i v => isBuf Γ b && isU32 Γ i && isU32 Γ v
  | .load x b i => isBuf Γ b && Γ.lookup x == some .u32 && isU32 Γ i
  | .return_ (some e) => (exprTy Γ e).map (·.1) == some ret
  | .seq s1 s2 => !s1.isSeq && bodyTy Γ ret inLoop s1 && bodyTy Γ ret inLoop s2
  | .ite c t e => condTy Γ c && bodyTy Γ ret inLoop t && bodyTy Γ ret inLoop e
  | .while_ c b => condTy Γ c && bodyTy Γ ret true b
  | _ => false

def CType.isScalar32 : CType → Bool
  | .u32 | .bool => true
  | _ => false

/-- `f` prints as a C function that `parseMicroCFunc` reads back: declared names, distinct across
    parameters and locals; `uint32_t` or `bool` values and `uint32_t *restrict` parameters; a body
    of the `uint32_t` subset that returns on every path, where the right operand of every `&&` and
    `||` is defined. -/
def WFFunc (f : MicroCFunc) : Prop :=
  declNameOk f.name = true ∧ f.ret.isScalar32 = true ∧
  (f.params ++ f.locals).all (fun p => declNameOk p.1) = true ∧
  ((f.params ++ f.locals).map (·.1)).Nodup ∧
  f.params.all (fun p => p.2.isScalar32 || p.2 == .ptrU32) = true ∧
  f.locals.all (fun p => p.2.isScalar32) = true ∧
  bodyTy (f.params ++ f.locals) f.ret false f.body = true ∧ f.body.returns = true ∧
  f.body.exprs.all (fun e => e.inU32Subset && e.shortCircuitOk (f.params ++ f.locals)) = true

instance : DecidablePred WFFunc := fun f => by unfold WFFunc; infer_instance

/-! ## Printing -/

def paramToString (p : String × CType) : String := p.2.name ++ " " ++ p.1

def paramsTail : CDecls → String
  | [] => ""
  | p :: ps => ", " ++ paramToString p ++ paramsTail ps

def paramsToString : CDecls → String
  | [] => "void"
  | p :: ps => paramToString p ++ paramsTail ps

/-- `uint32_t ring_push(uint32_t head, uint32_t tail, uint32_t *restrict buf)` -/
def microCFuncSig (f : MicroCFunc) : String :=
  paramToString (f.name, f.ret) ++ "(" ++ paramsToString f.params ++ ")"

/-- The signature, then the locals and body as `printTyped` prints them. -/
def microCFuncToString (f : MicroCFunc) : String :=
  microCFuncSig f ++ " {\n" ++ printTyped f.locals f.body ++ "\n}"

/-! ## Parser -/

/-- A type name and the space after it; `uint32_t *restrict` is tried before `uint32_t`. -/
def pTypeName (cs : List Char) : Option (CType × List Char) :=
  [CType.ptrU32, .u32, .i64, .bool].findSome? fun t =>
    (pKeyword (t.name ++ " ").toList cs).map (t, ·)

def pTyped (cs : List Char) : Option ((String × CType) × List Char) :=
  match pTypeName cs with
  | some (t, r) => (pIdent r).map fun (x, r') => ((x, t), r')
  | none => none

/-- The parameters after the first, each after `, `, through the closing `)`. -/
def pParamsRest : Nat → List Char → Option (CDecls × List Char)
  | 0, _ => none
  | _ + 1, ')' :: r => some ([], r)
  | n + 1, ',' :: ' ' :: r =>
    match pTyped r with
    | some (p, r') => (pParamsRest n r').map fun (ps, r'') => (p :: ps, r'')
    | none => none
  | _ + 1, _ => none

def pParams (cs : List Char) : Option (CDecls × List Char) :=
  match pKeyword "void)".toList cs with
  | some r => some ([], r)
  | none =>
    match pTyped cs with
    | some (p, r) => (pParamsRest r.length r).map fun (ps, r') => (p :: ps, r')
    | none => none

/-- Reads back what `microCFuncToString` prints. -/
def parseMicroCFunc (src : String) : Option MicroCFunc :=
  match pTyped src.toList with
  | some ((name, ret), '(' :: r1) =>
    match pParams r1 with
    | some (params, r2) =>
      match pKeyword " {\n".toList r2 with
      | some r3 =>
        if r3.drop (r3.length - 2) = ['\n', '}'] then
          (parseTyped (String.ofList (r3.take (r3.length - 2)))).map fun (locals, body) =>
            { name, ret, params, locals, body }
        else none
      | none => none
    | none => none
  | _ => none

/-! ## Well-Formed Bodies -/

theorem isU32_wf (Γ : CDecls) (hΓ : ∀ p ∈ Γ, declNameOk p.1 = true) (e : MicroCExpr)
    (h : isU32 Γ e = true) : WFExpr e ∧ NegLitDisam e := by
  unfold isU32 at h
  cases he : exprTy Γ e with
  | none => simp [he] at h
  | some p => exact exprTy_wf Γ hΓ e p he

theorem isBuf_name (Γ : CDecls) (hΓ : ∀ p ∈ Γ, declNameOk p.1 = true) (b : MicroCExpr)
    (h : isBuf Γ b = true) : ∃ p, b = .varRef p ∧ declNameOk p = true := by
  cases b with
  | varRef p =>
    simp only [isBuf, beq_iff_eq] at h
    exact ⟨p, rfl, hΓ _ (lookup_mem h)⟩
  | _ => simp [isBuf] at h

theorem bodyTy_wf (Γ : CDecls) (ret : CType) (hΓ : ∀ p ∈ Γ, declNameOk p.1 = true) :
    ∀ (b : Bool) (s : MicroCStmt), bodyTy Γ ret b s = true → WFStmt s ∧ NegLitDisamS s
  | _, .skip, _ => ⟨.skip, trivial⟩
  | _, .break_, _ => ⟨.break_, trivial⟩
  | _, .continue_, _ => ⟨.continue_, trivial⟩
  | _, .assign x e, h => by
    simp only [bodyTy] at h
    split at h
    · rename_i t p hx he
      simp only [Bool.and_eq_true, Bool.not_eq_true'] at h
      have hn := hΓ _ (lookup_mem hx)
      obtain ⟨c, cs, hcs, hα, hall⟩ := declNameOk_chars hn
      have hne : x ≠ "" := by intro h0; subst h0; simp at hcs
      have ⟨hw, hd⟩ := exprTy_wf Γ hΓ e _ he
      refine ⟨.assign x e hne (by simp only [hcs, List.head_cons]; exact Or.inl hα) hall hw,
        hd, declNameOk_safe hn, ?_⟩
      cases e with
      | arrayAccess => simp [exprTy] at he
      | powCall => simp [MicroCExpr.isPowCall] at h
      | _ => simp [AssignRhsSafe]
    · exact absurd h (by simp)
  | _, .store base i v, h => by
    simp only [bodyTy, Bool.and_eq_true] at h
    obtain ⟨⟨hb, hi⟩, hv⟩ := h
    obtain ⟨p, rfl, hp⟩ := isBuf_name Γ hΓ base hb
    have ⟨hwi, hdi⟩ := isU32_wf Γ hΓ i hi
    have ⟨hwv, hdv⟩ := isU32_wf Γ hΓ v hv
    refine ⟨.store _ i v (declNameOk_wf hp) hwi hwv ⟨p, rfl⟩, trivial, hdi, hdv, ?_⟩
    intro n hn; cases hn; exact declNameOk_safe hp
  | _, .load x base i, h => by
    simp only [bodyTy, Bool.and_eq_true, beq_iff_eq] at h
    obtain ⟨⟨hb, hx⟩, hi⟩ := h
    obtain ⟨p, rfl, hp⟩ := isBuf_name Γ hΓ base hb
    have hn := hΓ _ (lookup_mem hx)
    obtain ⟨c, cs, hcs, hα, hall⟩ := declNameOk_chars hn
    have hne : x ≠ "" := by intro h0; subst h0; simp at hcs
    have ⟨hwi, hdi⟩ := isU32_wf Γ hΓ i hi
    exact ⟨.load x _ i hne (by simp only [hcs, List.head_cons]; exact Or.inl hα) hall
      (declNameOk_wf hp) hwi ⟨p, rfl⟩, trivial, hdi, declNameOk_safe hn⟩
  | _, .return_ (some e), h => by
    simp only [bodyTy] at h
    cases he : exprTy Γ e with
    | none => simp [he] at h
    | some p =>
      have ⟨hw, hd⟩ := exprTy_wf Γ hΓ e p he
      exact ⟨.return_some e hw, hd⟩
  | b, .seq s1 s2, h => by
    simp only [bodyTy, Bool.and_eq_true, Bool.not_eq_true'] at h
    obtain ⟨⟨hns, h1⟩, h2⟩ := h
    have ⟨hw1, hd1⟩ := bodyTy_wf Γ ret hΓ b s1 h1
    have ⟨hw2, hd2⟩ := bodyTy_wf Γ ret hΓ b s2 h2
    refine ⟨.seq s1 s2 hw1 hw2, hd1, hd2, ?_⟩
    intro a c hs; subst hs; simp [MicroCStmt.isSeq] at hns
  | b, .ite c t e, h => by
    simp only [bodyTy, Bool.and_eq_true] at h
    obtain ⟨⟨hc, ht⟩, he⟩ := h
    have ⟨hwc, hdc⟩ := condTy_wf Γ hΓ c hc
    have ⟨hwt, hdt⟩ := bodyTy_wf Γ ret hΓ b t ht
    have ⟨hwe, hde⟩ := bodyTy_wf Γ ret hΓ b e he
    exact ⟨.ite c t e hwc hwt hwe, hdc, hdt, hde⟩
  | _, .while_ c body, h => by
    simp only [bodyTy, Bool.and_eq_true] at h
    obtain ⟨hc, hb⟩ := h
    have ⟨hwc, hdc⟩ := condTy_wf Γ hΓ c hc
    have ⟨hwb, hdb⟩ := bodyTy_wf Γ ret hΓ true body hb
    exact ⟨.while_ c body hwc hwb, hdc, hdb⟩
  | _, .return_ none, h => by simp [bodyTy] at h
  | _, .call _ _ _, h => by simp [bodyTy] at h

/-! ## Signature Roundtrip -/

private theorem u32_toList : CType.u32.name.toList = ['u', 'i', 'n', 't', '3', '2', '_', 't'] := by
  decide

private theorem i64_toList : CType.i64.name.toList = ['i', 'n', 't', '6', '4', '_', 't'] := by
  decide

private theorem bool_toList : CType.bool.name.toList = ['b', 'o', 'o', 'l'] := by decide

private theorem ptr_toList : CType.ptrU32.name.toList =
    ['u', 'i', 'n', 't', '3', '2', '_', 't', ' ', '*', 'r', 'e', 's', 't', 'r', 'i', 'c', 't'] := by
  decide

theorem pTypeName_name (t : CType) (c : Char) (cs : List Char) (hc : c ≠ '*') :
    pTypeName ((t.name ++ " ").toList ++ c :: cs) = some (t, c :: cs) := by
  cases t <;> simp [pTypeName, String.toList_append, u32_toList, i64_toList, bool_toList,
    ptr_toList, List.findSome?, pKeyword, Ne.symm hc]

private theorem lower_ne_star {x : String} (hx : declNameOk x = true) :
    ∃ c cs, x.toList = c :: cs ∧ c ≠ '*' := by
  obtain ⟨⟨c, cs, hcs, hl, -⟩, -⟩ := declNameOk_spec hx
  refine ⟨c, cs, hcs, ?_⟩
  rintro rfl; exact absurd hl (by decide)

theorem pTyped_roundtrip (x : String) (t : CType) (hx : declNameOk x = true) (rest : List Char)
    (hrest : NoLeadingIdent rest) :
    pTyped ((paramToString (x, t)).toList ++ rest) = some ((x, t), rest) := by
  obtain ⟨c, cs, hcs, hc⟩ := lower_ne_star hx
  obtain ⟨_, _, hcs', hα, hall⟩ := declNameOk_chars hx
  have hne : x ≠ "" := by intro h0; subst h0; simp at hcs
  have hsplit : (paramToString (x, t)).toList ++ rest = (t.name ++ " ").toList ++ c :: (cs ++ rest) := by
    simp [paramToString, String.toList_append, hcs]
  rw [hsplit, pTyped, pTypeName_name t c (cs ++ rest) hc]
  simp only []
  rw [← List.cons_append, ← hcs, pIdent_exact x rest hne
    (by simp only [hcs', List.head_cons]; exact Or.inl hα) hall hrest]
  rfl

private theorem noLeadingIdent_sep (c : Char) (rest : List Char) (ha : c.isAlpha = false)
    (hd : c.isDigit = false) (hu : c ≠ '_') : NoLeadingIdent (c :: rest) :=
  Or.inr ⟨c, rest, rfl, ha, hd, hu⟩

theorem paramsTail_length (ps : CDecls) : ps.length ≤ (paramsTail ps).toList.length := by
  induction ps with
  | nil => simp
  | cons p ps ih =>
    simp only [paramsTail, String.toList_append, List.length_append, List.length_cons]
    have : (", " : String).toList.length = 2 := by decide
    omega

theorem pParamsRest_roundtrip (ps : CDecls) (hps : ∀ p ∈ ps, declNameOk p.1 = true)
    (rest : List Char) : ∀ n, ps.length < n →
      pParamsRest n ((paramsTail ps).toList ++ ')' :: rest) = some (ps, rest) := by
  induction ps with
  | nil =>
    intro n hn
    obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by simp at hn; omega⟩
    rfl
  | cons p ps ih =>
    intro n hn
    obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by simp at hn; omega⟩
    have hsplit : (paramsTail (p :: ps)).toList ++ ')' :: rest =
        ',' :: ' ' :: ((paramToString p).toList ++ ((paramsTail ps).toList ++ ')' :: rest)) := by
      simp [paramsTail, String.toList_append]
    rw [hsplit, pParamsRest]
    have hnl : NoLeadingIdent ((paramsTail ps).toList ++ ')' :: rest) := by
      cases ps with
      | nil => exact noLeadingIdent_sep ')' rest (by decide) (by decide) (by decide)
      | cons q qs =>
        simp only [paramsTail, String.toList_append, List.append_assoc]
        exact noLeadingIdent_sep ',' _ (by decide) (by decide) (by decide)
    rw [pTyped_roundtrip p.1 p.2 (hps p (List.mem_cons_self ..)) _ hnl]
    simp only []
    rw [ih (fun q hq => hps q (List.mem_cons_of_mem _ hq)) k (by simp at hn; omega)]
    rfl

private theorem name_head_ne_v (t : CType) : ∃ c cs, (t.name ++ " ").toList = c :: cs ∧ c ≠ 'v' := by
  cases t <;> simp [String.toList_append, u32_toList, i64_toList, bool_toList, ptr_toList]

theorem pParams_roundtrip (ps : CDecls) (hps : ∀ p ∈ ps, declNameOk p.1 = true)
    (rest : List Char) :
    pParams ((paramsToString ps).toList ++ ')' :: rest) = some (ps, rest) := by
  cases ps with
  | nil =>
    have : (paramsToString []).toList ++ ')' :: rest = "void)".toList ++ rest := by
      simp [paramsToString]
    rw [this, pParams, pKeyword_append]
  | cons p ps =>
    have hsplit : (paramsToString (p :: ps)).toList ++ ')' :: rest =
        (paramToString p).toList ++ ((paramsTail ps).toList ++ ')' :: rest) := by
      simp [paramsToString, String.toList_append]
    have hvoid : pKeyword "void)".toList ((paramToString p).toList ++
        ((paramsTail ps).toList ++ ')' :: rest)) = none := by
      obtain ⟨c, cs, hcs, hc⟩ := name_head_ne_v p.2
      have : (paramToString p).toList = c :: (cs ++ p.1.toList) := by
        simp only [paramToString]; rw [String.toList_append, hcs]; rfl
      rw [this, show ("void)" : String).toList = ['v', 'o', 'i', 'd', ')'] by decide]
      simp [pKeyword, Ne.symm hc]
    have hnl : NoLeadingIdent ((paramsTail ps).toList ++ ')' :: rest) := by
      cases ps with
      | nil => exact noLeadingIdent_sep ')' rest (by decide) (by decide) (by decide)
      | cons q qs =>
        simp only [paramsTail, String.toList_append, List.append_assoc]
        exact noLeadingIdent_sep ',' _ (by decide) (by decide) (by decide)
    rw [hsplit, pParams, hvoid]
    simp only []
    rw [pTyped_roundtrip p.1 p.2 (hps p (List.mem_cons_self ..)) _ hnl]
    simp only []
    rw [pParamsRest_roundtrip ps (fun q hq => hps q (List.mem_cons_of_mem _ hq)) rest _
      (by have := paramsTail_length ps; simp only [List.length_append, List.length_cons]; omega)]
    rfl

/-! ## Function Roundtrip -/

/-- **Function roundtrip**: a well-formed function's printed text parses back to it. -/
theorem master_func_roundtrip (f : MicroCFunc) (h : WFFunc f) :
    parseMicroCFunc (microCFuncToString f) = some f := by
  obtain ⟨hname, -, hnames, -, -, hlocals, hbody, -, -⟩ := h
  have hΓ : ∀ p ∈ f.params ++ f.locals, declNameOk p.1 = true := List.all_eq_true.mp hnames
  have ⟨hwf, hd⟩ := bodyTy_wf _ f.ret hΓ false f.body hbody
  have hloc : ∀ p ∈ f.locals, declNameOk p.1 = true ∧ p.2 ≠ .ptrU32 := by
    intro p hp
    refine ⟨hΓ p (List.mem_append_right _ hp), ?_⟩
    have := List.all_eq_true.mp hlocals p hp
    intro hpt; rw [hpt] at this; exact absurd this (by decide)
  have hcs : (microCFuncToString f).toList =
      (paramToString (f.name, f.ret)).toList ++ '(' :: ((paramsToString f.params).toList ++
        ')' :: (" {\n".toList ++ ((printTyped f.locals f.body).toList ++ ['\n', '}']))) := by
    simp [microCFuncToString, microCFuncSig, String.toList_append]
  unfold parseMicroCFunc
  rw [hcs, pTyped_roundtrip f.name f.ret hname _
    (noLeadingIdent_sep '(' _ (by decide) (by decide) (by decide))]
  simp only []
  rw [pParams_roundtrip f.params (fun p hp => hΓ p (List.mem_append_left _ hp))]
  simp only []
  rw [pKeyword_append]
  simp only [List.length_append, List.length_cons, List.length_nil, Nat.add_sub_cancel,
    List.drop_left', List.take_left', String.ofList_toList, if_true]
  rw [parseTyped_printTyped f.locals f.body hloc hwf hd]
  rfl

/-! ## Files -/

/-- Well-formed functions with distinct names. -/
def WFFile (fs : List MicroCFunc) : Prop := (∀ f ∈ fs, WFFunc f) ∧ (fs.map (·.name)).Nodup

instance : DecidablePred WFFile := fun fs => by unfold WFFile; infer_instance

/-- The header `base.h` and source `base.c` for `fs`, each opening with a line that names the
    generator revision `sha`. The header declares each function; the source includes it, asserts
    what printed `uint32_t` code relies on, and defines each function as `microCFuncToString`
    prints it. -/
def emitFile (base sha : String) (fs : List MicroCFunc) : String × String :=
  let stamp := "/* Generated by trust-lean " ++ sha ++ ". Do not edit. */\n"
  let guard := base.map Char.toUpper ++ "_H"
  (stamp ++ "#ifndef " ++ guard ++ "\n#define " ++ guard ++
      "\n\n#include <stdbool.h>\n#include <stdint.h>\n\n" ++
      String.join (fs.map fun f => microCFuncSig f ++ ";\n") ++ "\n#endif\n",
    stamp ++ "#include \"" ++ base ++ ".h\"\n\n#include <limits.h>\n\n" ++ uint32Asserts ++ "\n" ++
      String.join (fs.map fun f => "\n" ++ microCFuncToString f ++ "\n"))

end TrustLean
