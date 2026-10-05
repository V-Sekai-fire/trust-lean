/-
  Trust-Lean — Verified Code Generation Framework
  MicroC/TypedRoundtrip.lean: parsing a typed program back

  `parseTyped (printTyped Γ s) = some (Γ, s)` for every well-typed `s`. A well-typed body is
  well-formed and disambiguated, so the body's half is `master_roundtrip`.
-/

import TrustLean.MicroC.Typed
import TrustLean.MicroC.RoundtripMaster

set_option autoImplicit false

namespace TrustLean

/-! ## Parser -/

/-- Strips the prefix `ks`, or fails. -/
def pKeyword : List Char → List Char → Option (List Char)
  | [], cs => some cs
  | k :: ks, c :: cs => if k = c then pKeyword ks cs else none
  | _ :: _, [] => none

def pDecl (cs : List Char) : Option ((String × CType) × List Char) :=
  match pIdent cs with
  | some (tn, ' ' :: r1) =>
    match CType.ofName tn with
    | some t =>
      match pIdent r1 with
      | some (x, r2) => (pKeyword (declTail x t).toList r2).map fun r3 => ((x, t), r3)
      | none => none
    | none => none
  | _ => none

def pDecls : Nat → List Char → CDecls × List Char
  | 0, cs => ([], cs)
  | n + 1, cs =>
    match pDecl cs with
    | some (d, rest) => ((d :: (pDecls n rest).1), (pDecls n rest).2)
    | none => ([], cs)

/-- Reads back what `printTyped` prints. -/
def parseTyped (src : String) : Option (CDecls × MicroCStmt) :=
  let cs := src.toList
  let r := pDecls cs.length cs
  match pKeyword ['{', ' '] r.2 with
  | some body =>
    if body.drop (body.length - 2) = [' ', '}'] then
      (parseMicroC (String.ofList (body.take (body.length - 2)))).map fun s => (r.1, s)
    else none
  | none => none

/-! ## Names -/

theorem declsOk_names {Γ : CDecls} (h : declsOk Γ = true) : ∀ p ∈ Γ, declNameOk p.1 = true := by
  simp only [declsOk, Bool.and_eq_true, List.all_eq_true] at h
  exact h.1

theorem declNameOk_spec {x : String} (h : declNameOk x = true) :
    (∃ c cs, x.toList = c :: cs ∧ c.isLower = true ∧ cs.all isValidCIdentChar = true) ∧
    cReservedIdentifiers.contains x = false ∧ x.toList.take 6 ≠ "return".toList := by
  unfold declNameOk at h
  split at h
  · exact absurd h (by decide)
  · rename_i c cs hx
    simp only [Bool.and_eq_true, Bool.not_eq_true', bne_iff_ne, ne_eq] at h
    exact ⟨⟨c, cs, hx, h.1.1.1.1, h.1.1.1.2⟩, h.1.1.2, h.2⟩

private theorem isLower_isAlpha (c : Char) (h : c.isLower = true) : c.isAlpha = true := by
  simp [Char.isAlpha, h]

theorem declNameOk_chars {x : String} (h : declNameOk x = true) :
    ∃ c cs, x.toList = c :: cs ∧ c.isAlpha = true ∧
      ∀ ch ∈ x.toList, ch.isAlpha = true ∨ ch.isDigit = true ∨ ch = '_' := by
  obtain ⟨⟨c, cs, hx, hl, hall⟩, -, -⟩ := declNameOk_spec h
  refine ⟨c, cs, hx, isLower_isAlpha c hl, ?_⟩
  intro ch hch
  rw [hx] at hch
  rcases List.mem_cons.mp hch with rfl | hmem
  · exact Or.inl (isLower_isAlpha ch hl)
  · have := List.all_eq_true.mp hall ch hmem
    simp only [isValidCIdentChar, Bool.or_eq_true, beq_iff_eq] at this
    rcases this with (h1 | h1) | h1
    · exact Or.inl h1
    · exact Or.inr (Or.inl h1)
    · exact Or.inr (Or.inr h1)

theorem declNameOk_ne {x : String} (h : declNameOk x = true) (y : String)
    (hy : cReservedIdentifiers.contains y = true) : x ≠ y := by
  intro hxy; subst hxy; rw [(declNameOk_spec h).2.1] at hy; exact absurd hy (by decide)

theorem declNameOk_wf {x : String} (h : declNameOk x = true) : WFExpr (.varRef x) := by
  obtain ⟨c, cs, hx, hα, hall⟩ := declNameOk_chars h
  have hne : x ≠ "" := by intro h0; subst h0; simp at hx
  exact .varRef x hne (by simp only [hx, List.head_cons]; exact Or.inl hα) hall
    ⟨declNameOk_ne h "true" (by decide), declNameOk_ne h "false" (by decide)⟩

theorem declNameOk_safe {x : String} (h : declNameOk x = true) : VarNameSafe x := by
  refine ⟨?_, declNameOk_ne h "if" (by decide), declNameOk_ne h "while" (by decide)⟩
  intro cs hcs
  apply (declNameOk_spec h).2.2
  rw [hcs, show ("return" : String).toList = ['r', 'e', 't', 'u', 'r', 'n'] by decide]; rfl

/-! ## Well-Typed Bodies Are Well-Formed -/

theorem exprTy_wf (Γ : CDecls) (hΓ : declsOk Γ = true) :
    ∀ (e : MicroCExpr) (p : CType × Bool), exprTy Γ e = some p → WFExpr e ∧ NegLitDisam e
  | .litInt n, _, _ => ⟨.litInt n, trivial⟩
  | .litU32 n, _, _ => ⟨.litU32 n, trivial⟩
  | .litBool b, _, _ => ⟨.litBool b, trivial⟩
  | .varRef x, _, h => by
    simp only [exprTy, Option.map_eq_some_iff] at h
    obtain ⟨t, ht, -⟩ := h
    exact ⟨declNameOk_wf (declsOk_names hΓ _ (lookup_mem ht)), trivial⟩
  | .binOp op l r, _, h => by
    simp only [exprTy] at h
    split at h
    · rename_i pl pr hl hr
      have ⟨hwl, hdl⟩ := exprTy_wf Γ hΓ l _ hl
      have ⟨hwr, hdr⟩ := exprTy_wf Γ hΓ r _ hr
      exact ⟨.binOp op l r hwl hwr, hdl, hdr⟩
    · exact absurd h (by simp)
  | .unaryOp op e, _, h => by
    simp only [exprTy] at h
    split at h
    · rename_i p he
      have ⟨hw, hd⟩ := exprTy_wf Γ hΓ e _ he
      split at h
      · exact absurd h (by simp)
      · rename_i hn
        refine ⟨.unaryOp op e hw, ?_⟩
        cases op with
        | neg =>
          refine ⟨?_, ?_, hd⟩
          · intro n hn0 hen; subst hen; simp [negOfLit, hn0] at hn
          · intro n hen; subst hen; simp [negOfLit] at hn
        | lnot | widen32to64 | trunc64to32 => exact hd
    · exact absurd h (by simp)
  | .powCall b n, _, h => by
    simp only [exprTy] at h
    split at h
    · rename_i hb
      have ⟨hw, hd⟩ := exprTy_wf Γ hΓ b _ hb
      exact ⟨.powCall b n hw, hd⟩
    · exact absurd h (by simp)
  | .arrayAccess _ _, _, h => by simp [exprTy] at h

theorem condTy_wf (Γ : CDecls) (hΓ : declsOk Γ = true) (c : MicroCExpr)
    (h : condTy Γ c = true) : WFExpr c ∧ NegLitDisam c := by
  unfold condTy at h
  split at h
  · rename_i v hc; exact exprTy_wf Γ hΓ c _ hc
  · exact absurd h (by simp)

theorem stmtTy_wf (Γ : CDecls) (hΓ : declsOk Γ = true) :
    ∀ (b : Bool) (s : MicroCStmt), stmtTy Γ b s = true → WFStmt s ∧ NegLitDisamS s
  | _, .skip, _ => ⟨.skip, trivial⟩
  | _, .break_, _ => ⟨.break_, trivial⟩
  | _, .continue_, _ => ⟨.continue_, trivial⟩
  | _, .assign x e, h => by
    simp only [stmtTy] at h
    split at h
    · rename_i t p hx he
      simp only [Bool.and_eq_true, Bool.not_eq_true'] at h
      have hn := declsOk_names hΓ _ (lookup_mem hx)
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
  | b, .seq s1 s2, h => by
    simp only [stmtTy, Bool.and_eq_true, Bool.not_eq_true'] at h
    obtain ⟨⟨hns, h1⟩, h2⟩ := h
    have ⟨hw1, hd1⟩ := stmtTy_wf Γ hΓ b s1 h1
    have ⟨hw2, hd2⟩ := stmtTy_wf Γ hΓ b s2 h2
    refine ⟨.seq s1 s2 hw1 hw2, hd1, hd2, ?_⟩
    intro a c hs; subst hs; simp [MicroCStmt.isSeq] at hns
  | b, .ite c t e, h => by
    simp only [stmtTy, Bool.and_eq_true] at h
    obtain ⟨⟨hc, ht⟩, he⟩ := h
    have ⟨hwc, hdc⟩ := condTy_wf Γ hΓ c hc
    have ⟨hwt, hdt⟩ := stmtTy_wf Γ hΓ b t ht
    have ⟨hwe, hde⟩ := stmtTy_wf Γ hΓ b e he
    exact ⟨.ite c t e hwc hwt hwe, hdc, hdt, hde⟩
  | _, .while_ c body, h => by
    simp only [stmtTy, Bool.and_eq_true] at h
    obtain ⟨hc, hb⟩ := h
    have ⟨hwc, hdc⟩ := condTy_wf Γ hΓ c hc
    have ⟨hwb, hdb⟩ := stmtTy_wf Γ hΓ true body hb
    exact ⟨.while_ c body hwc hwb, hdc, hdb⟩
  | _, .return_ _, h => by simp [stmtTy] at h
  | _, .store _ _ _, h => by simp [stmtTy] at h
  | _, .load _ _ _, h => by simp [stmtTy] at h
  | _, .call _ _ _, h => by simp [stmtTy] at h

/-! ## Declarations Roundtrip -/

theorem pKeyword_append (ks rest : List Char) : pKeyword ks (ks ++ rest) = some rest := by
  induction ks with
  | nil => rfl
  | cons k ks ih => simp [pKeyword, ih]

private theorem pIdent_typeName (t : CType) (rest : List Char) :
    pIdent (t.name.toList ++ ' ' :: rest) = some (t.name, ' ' :: rest) := by
  have hsp : NoLeadingIdent (' ' :: rest) := Or.inr ⟨' ', rest, rfl, by decide, by decide, by decide⟩
  cases t with
  | u32 =>
    have h : ("uint32_t" : String).toList = ['u', 'i', 'n', 't', '3', '2', '_', 't'] := by decide
    exact pIdent_exact "uint32_t" _ (by decide) (by simp [h]) (by rw [h]; decide) hsp
  | i64 =>
    have h : ("int64_t" : String).toList = ['i', 'n', 't', '6', '4', '_', 't'] := by decide
    exact pIdent_exact "int64_t" _ (by decide) (by simp [h]) (by rw [h]; decide) hsp
  | bool =>
    have h : ("bool" : String).toList = ['b', 'o', 'o', 'l'] := by decide
    exact pIdent_exact "bool" _ (by decide) (by simp [h]) (by rw [h]; decide) hsp

private theorem ofName_name (t : CType) : CType.ofName t.name = some t := by
  cases t <;> rfl

private theorem declTail_toList (x : String) (t : CType) :
    (declTail x t).toList = ' ' :: ('=' :: ' ' :: ((microCExprToString t.zero).toList ++
      ("; (void)" ++ x ++ ";\n").toList)) := by
  simp [declTail, String.toList_append]

theorem pDecl_roundtrip (x : String) (t : CType) (hx : declNameOk x = true) (rest : List Char) :
    pDecl ((declToString (x, t)).toList ++ rest) = some ((x, t), rest) := by
  obtain ⟨c, cs, hcs, hα, hall⟩ := declNameOk_chars hx
  have hne : x ≠ "" := by intro h0; subst h0; simp at hcs
  have hsplit : (declToString (x, t)).toList ++ rest =
      t.name.toList ++ ' ' :: (x.toList ++ ((declTail x t).toList ++ rest)) := by
    simp [declToString, String.toList_append]
  rw [hsplit]
  unfold pDecl
  rw [pIdent_typeName]
  simp only [ofName_name]
  have hnl : NoLeadingIdent ((declTail x t).toList ++ rest) := by
    rw [declTail_toList]; exact Or.inr ⟨' ', _, rfl, by decide, by decide, by decide⟩
  rw [pIdent_exact x _ hne (by simp only [hcs, List.head_cons]; exact Or.inl hα) hall hnl]
  simp [pKeyword_append]

private theorem pIdent_lbrace (rest : List Char) : pIdent ('{' :: rest) = none := by
  unfold pIdent; simp

theorem pDecls_roundtrip (Γ : CDecls) (hΓ : ∀ p ∈ Γ, declNameOk p.1 = true) (rest : List Char) :
    ∀ n, Γ.length ≤ n →
      pDecls n ((declsToString Γ).toList ++ '{' :: rest) = (Γ, '{' :: rest) := by
  induction Γ with
  | nil =>
    intro n _
    cases n with
    | zero => rfl
    | succ k => simp [declsToString, pDecls, pDecl, pIdent_lbrace]
  | cons d ds ih =>
    intro n hn
    obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by simp at hn; omega⟩
    simp only [declsToString, String.toList_append, List.append_assoc]
    rw [pDecls, pDecl_roundtrip d.1 d.2 (hΓ d (List.mem_cons_self ..))]
    simp only []
    rw [ih (fun p hp => hΓ p (List.mem_cons_of_mem _ hp)) k (by simp at hn; omega)]

theorem declsToString_length (Γ : CDecls) : Γ.length ≤ (declsToString Γ).toList.length := by
  induction Γ with
  | nil => simp
  | cons d ds ih =>
    simp only [declsToString, declToString, String.toList_append, List.length_append,
      List.length_cons]
    have : (" " : String).toList.length = 1 := by decide
    omega

/-! ## Typed Roundtrip -/

/-- **Typed roundtrip**: the declarations and body of a well-typed program parse back. -/
theorem master_typed_roundtrip (Γ : CDecls) (s : MicroCStmt) (h : WellTyped Γ s) :
    parseTyped (printTyped Γ s) = some (Γ, s) := by
  have ⟨hwf, hd⟩ := stmtTy_wf Γ h.1 false s h.2
  have hnames := declsOk_names h.1
  have hcs : (printTyped Γ s).toList =
      (declsToString Γ).toList ++ '{' :: ' ' :: ((microCToString s).toList ++ [' ', '}']) := by
    simp [printTyped, String.toList_append]
  have hlen : Γ.length ≤ (printTyped Γ s).toList.length := by
    have := declsToString_length Γ
    rw [hcs, List.length_append]; omega
  unfold parseTyped
  simp only []
  rw [hcs] at hlen ⊢
  rw [pDecls_roundtrip Γ hnames _ _ hlen]
  simp only []
  rw [show ('{' :: ' ' :: ((microCToString s).toList ++ [' ', '}'])) =
    ['{', ' '] ++ ((microCToString s).toList ++ [' ', '}']) from rfl, pKeyword_append]
  simp only [List.length_append, List.length_cons, List.length_nil, Nat.add_sub_cancel,
    List.drop_left', List.take_left', String.ofList_toList, if_true]
  rw [master_roundtrip s hwf hd]
  rfl

/-! ## Non-Vacuity -/

private def exDecls : CDecls := [("x", .u32), ("b", .bool), ("y", .i64)]

private def exBody : MicroCStmt :=
  .seq (.assign "x" (.litU32 4294967295))
    (.seq (.ite (.binOp .eqOp (.varRef "x") (.litU32 5)) (.assign "b" (.litBool true))
        (.assign "b" (.litBool false)))
      (.while_ (.varRef "b")
        (.seq (.assign "b" (.unaryOp .lnot (.varRef "b")))
          (.assign "y" (.binOp .add (.varRef "y") (.unaryOp .widen32to64 (.varRef "x")))))))

example : WellTyped exDecls exBody := by decide

example : parseTyped (printTyped exDecls exBody) = some (exDecls, exBody) :=
  master_typed_roundtrip exDecls exBody (by decide)

/-- A `uint32_t` variable takes a `u`-suffixed literal at any value below 2^32. -/
example : WellTyped [("x", .u32)] (.assign "x" (.litU32 4294967295)) := by decide

/-- An unsuffixed literal is `int64_t`, so assigning one to a `uint32_t` variable is an implicit
    conversion and is rejected at every value. -/
example : ¬ WellTyped [("x", .u32)] (.assign "x" (.litInt 5)) := by decide

/-- `x + 4294967295` with an unsuffixed literal is `long` arithmetic in C, not `uint32_t`. -/
example : ¬ WellTyped [("x", .u32), ("b", .bool)]
    (.assign "b" (.binOp .ltOp (.binOp .add (.varRef "x") (.litInt 4294967295)) (.litU32 1))) := by
  decide

/-- Two unsuffixed literals multiply as `int`, which overflows at 65536 * 65536. -/
example : ¬ WellTyped [("y", .i64)] (.assign "y" (.binOp .mul (.litInt 65536) (.litInt 65536))) := by
  decide

/-- A constant shift count must be below the width. -/
example : ¬ WellTyped [("x", .u32)] (.assign "x" (.binOp .bshl (.varRef "x") (.litU32 40))) := by
  decide

/-- `break` outside a loop is a C constraint violation (6.8.6.3). -/
example : ¬ WellTyped [] .break_ := by decide

/-- `power` takes an `int64_t` base only. -/
example : ¬ WellTyped [("x", .u32)]
    (.assign "x" (.binOp .add (.varRef "x") (.powCall (.varRef "x") 2))) := by decide

end TrustLean
