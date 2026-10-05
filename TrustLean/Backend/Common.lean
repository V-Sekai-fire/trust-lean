/-
  Trust-Lean — Verified Code Generation Framework
  Backend/Common.lean: Shared emission helpers for backends

  N4.1: PAR — shared utilities used by both C and Rust backends.
  N9.1 (v1.2.0): Added c99Keywords, cReservedIdentifiers, sanitizeIdentifier,
  isValidCIdent, filterCIdentChars, formatArrayAccess with correctness theorems.
  N21.1 (v3.2.0): Added countChar shared infrastructure, rustKeywords (Rust 2021 edition,
  Rust Reference S2.1), rustReservedIdentifiers, sanitizeIdentifierRust with theorems.
-/

import TrustLean.Core.Value
import Std.Data.String.ToInt

set_option autoImplicit false

namespace TrustLean

/-! ## Indentation -/

/-- Generate indentation string (2 spaces per level). -/
def indentStr (level : Nat) : String :=
  String.join (List.replicate level "  ")

@[simp] theorem indentStr_zero : indentStr 0 = "" := rfl

/-! ## Variable Name Conversion -/

/-- Convert a VarName to a string suitable for emission.
    User variables pass through; temps become t0, t1, etc.;
    array elements become base[idx]. -/
def varNameToStr : VarName → String
  | .user s => s
  | .temp k => s!"t{k}"
  | .array base idx => s!"{base}[{idx}]"

@[simp] theorem varNameToStr_user (s : String) :
    varNameToStr (.user s) = s := rfl
@[simp] theorem varNameToStr_temp (k : Nat) :
    varNameToStr (.temp k) = s!"t{k}" := rfl

/-! ## Code Joining -/

/-- Join two code fragments with a newline, skipping empty fragments. -/
def joinCode (c1 c2 : String) : String :=
  if c1.isEmpty then c2
  else if c2.isEmpty then c1
  else c1 ++ "\n" ++ c2

/-! ## C99 Keyword Sanitization (N9.1, v1.2.0) -/

/-- C99 reserved words (37 keywords per ISO/IEC 9899:1999 §6.4.1). -/
def c99Keywords : List String :=
  ["auto", "break", "case", "char", "const", "continue", "default", "do",
   "double", "else", "enum", "extern", "float", "for", "goto", "if",
   "inline", "int", "long", "register", "restrict", "return", "short",
   "signed", "sizeof", "static", "struct", "switch", "typedef", "union",
   "unsigned", "void", "volatile", "while",
   "_Bool", "_Complex", "_Imaginary"]

/-- Additional reserved identifiers: C11 keywords (ISO/IEC 9899:2011 §6.4.1),
    stdint.h types, and common stdlib names.
    C11 additions included for robustness; explicitly listed rather than excluded. -/
def cReservedExtra : List String :=
  ["_Alignas", "_Atomic", "_Generic", "_Noreturn", "_Static_assert", "_Thread_local",
   "int8_t", "int16_t", "int32_t", "int64_t",
   "uint8_t", "uint16_t", "uint32_t", "uint64_t",
   "size_t", "ptrdiff_t", "bool", "true", "false",
   "NULL", "main", "printf", "malloc", "free", "exit", "abort"]

/-- The macros C11 defines in the headers `generateCHeader` includes, other than `bool`, `true`,
    `false` and `NULL` in `cReservedExtra`: limits.h (5.2.4.2.1), stdint.h (7.20.2-7.20.4),
    stdbool.h (7.18) and stdlib.h (7.22). A parameter or local with one of these names would
    expand. -/
def cHeaderMacros : List String :=
  ["CHAR_BIT", "SCHAR_MIN", "SCHAR_MAX", "UCHAR_MAX", "CHAR_MIN", "CHAR_MAX", "MB_LEN_MAX",
   "SHRT_MIN", "SHRT_MAX", "USHRT_MAX", "INT_MIN", "INT_MAX", "UINT_MAX",
   "LONG_MIN", "LONG_MAX", "ULONG_MAX", "LLONG_MIN", "LLONG_MAX", "ULLONG_MAX",
   "INT8_MIN", "INT16_MIN", "INT32_MIN", "INT64_MIN", "INT8_MAX", "INT16_MAX", "INT32_MAX",
   "INT64_MAX", "UINT8_MAX", "UINT16_MAX", "UINT32_MAX", "UINT64_MAX",
   "INT_LEAST8_MIN", "INT_LEAST16_MIN", "INT_LEAST32_MIN", "INT_LEAST64_MIN",
   "INT_LEAST8_MAX", "INT_LEAST16_MAX", "INT_LEAST32_MAX", "INT_LEAST64_MAX",
   "UINT_LEAST8_MAX", "UINT_LEAST16_MAX", "UINT_LEAST32_MAX", "UINT_LEAST64_MAX",
   "INT_FAST8_MIN", "INT_FAST16_MIN", "INT_FAST32_MIN", "INT_FAST64_MIN",
   "INT_FAST8_MAX", "INT_FAST16_MAX", "INT_FAST32_MAX", "INT_FAST64_MAX",
   "UINT_FAST8_MAX", "UINT_FAST16_MAX", "UINT_FAST32_MAX", "UINT_FAST64_MAX",
   "INTPTR_MIN", "INTPTR_MAX", "UINTPTR_MAX", "INTMAX_MIN", "INTMAX_MAX", "UINTMAX_MAX",
   "PTRDIFF_MIN", "PTRDIFF_MAX", "SIG_ATOMIC_MIN", "SIG_ATOMIC_MAX", "SIZE_MAX",
   "WCHAR_MIN", "WCHAR_MAX", "WINT_MIN", "WINT_MAX",
   "INT8_C", "INT16_C", "INT32_C", "INT64_C", "UINT8_C", "UINT16_C", "UINT32_C", "UINT64_C",
   "INTMAX_C", "UINTMAX_C", "__bool_true_false_are_defined",
   "EXIT_FAILURE", "EXIT_SUCCESS", "RAND_MAX", "MB_CUR_MAX"]

/-- All C reserved identifiers (C99 keywords + C11 + stdint.h + stdlib + the headers' macros). -/
def cReservedIdentifiers : List String := c99Keywords ++ (cReservedExtra ++ cHeaderMacros)

/-- Check if a character is valid in a C identifier (letter, digit, or underscore). -/
def isValidCIdentChar (c : Char) : Bool :=
  c.isAlpha || c.isDigit || c == '_'

/-- Check if a string is a valid C identifier:
    non-empty, starts with letter or underscore, all characters valid. -/
def isValidCIdent (s : String) : Bool :=
  match s.toList with
  | [] => false
  | c :: cs => (c.isAlpha || c == '_') && (c :: cs).all isValidCIdentChar

/-- Remove characters that are not valid in C identifiers. -/
def filterCIdentChars (s : String) : String :=
  String.ofList (s.toList.filter isValidCIdentChar)

/-- Sanitize a string to produce a valid, non-reserved C identifier.
    Removes invalid characters, then prefixes with "tl_" if needed. -/
def sanitizeIdentifier (s : String) : String :=
  match s.toList.filter isValidCIdentChar with
  | [] => "tl_empty"
  | c :: cs =>
    if c.isDigit then "tl_" ++ String.ofList (c :: cs)
    else if cReservedIdentifiers.contains (String.ofList (c :: cs))
      then "tl_" ++ String.ofList (c :: cs)
    else String.ofList (c :: cs)

/-! ## Sanitization Properties (N9.1) -/

/-- No C99 keyword's character list starts with "tl_". -/
private theorem c99_no_tl_prefix :
    ∀ k ∈ c99Keywords, k.toList.take 3 ≠ ['t', 'l', '_'] := by decide

set_option maxRecDepth 2048 in
/-- No reserved identifier's character list starts with "tl_". -/
private theorem reserved_no_tl_prefix :
    ∀ k ∈ cReservedIdentifiers, k.toList.take 3 ≠ ['t', 'l', '_'] := by decide

/-- "tl_empty" is not a C99 keyword. -/
private theorem tl_empty_not_c99 : "tl_empty" ∉ c99Keywords := by decide

/-- "tl_".toList equals ['t', 'l', '_']. -/
private theorem tl_toList : "tl_".toList = ['t', 'l', '_'] := by decide

/-- The toList of "tl_" ++ s starts with ['t', 'l', '_']. -/
private theorem tl_append_toList_take (s : String) :
    ("tl_" ++ s).toList.take 3 = ['t', 'l', '_'] := by
  rw [String.toList_append, tl_toList]
  show List.take 3 ('t' :: 'l' :: '_' :: s.toList) = ['t', 'l', '_']
  rfl

/-- No string prefixed with "tl_" is a C99 keyword (P0). -/
theorem tl_prefix_not_c99 (s : String) : ("tl_" ++ s) ∉ c99Keywords := by
  intro hmem
  exact c99_no_tl_prefix ("tl_" ++ s) hmem (tl_append_toList_take s)

/-- Helper: every element of a filtered list satisfies the predicate. -/
private theorem all_filter_pred {α : Type} (l : List α) (p : α → Bool) :
    (l.filter p).all p = true :=
  List.all_eq_true.mpr (fun _ hx => (List.mem_filter.mp hx).2)

/-- sanitizeIdentifier never produces a C99 keyword (P0). -/
theorem sanitizeIdentifier_not_keyword (s : String) :
    sanitizeIdentifier s ∉ c99Keywords := by
  unfold sanitizeIdentifier
  split
  · exact tl_empty_not_c99
  · rename_i c cs hfilter
    split
    · exact tl_prefix_not_c99 _
    · split
      · exact tl_prefix_not_c99 _
      · rename_i hnotdigit hnotreserved
        intro hmem
        have hres : String.ofList (c :: cs) ∈ cReservedIdentifiers :=
          List.mem_append_left _ hmem
        rw [List.contains_iff_mem] at hnotreserved
        exact hnotreserved hres

/-- sanitizeIdentifier always produces a non-empty string (P0). -/
theorem sanitizeIdentifier_nonempty (s : String) :
    (sanitizeIdentifier s).toList ≠ [] := by
  unfold sanitizeIdentifier
  split
  · -- "tl_empty"
    decide
  · rename_i c cs _hfilter
    split
    · -- "tl_" ++ ...
      rw [String.toList_append, tl_toList]
      exact List.cons_ne_nil _ _
    · split
      · -- "tl_" ++ ...
        rw [String.toList_append, tl_toList]
        exact List.cons_ne_nil _ _
      · -- String.ofList (c :: cs)
        rw [String.toList_ofList]
        exact List.cons_ne_nil _ _

/-- Helper: isValidCIdent holds for "tl_" ++ String.ofList chars
    when chars come from a filter on isValidCIdentChar. -/
private theorem isValidCIdent_tl_prefix (chars : List Char)
    (hall : chars.all isValidCIdentChar = true) :
    isValidCIdent ("tl_" ++ String.ofList chars) = true := by
  unfold isValidCIdent
  rw [String.toList_append, tl_toList, String.toList_ofList]
  show (('t'.isAlpha || 't' == '_') && ('t' :: 'l' :: '_' :: chars).all isValidCIdentChar) = true
  simp only [Bool.and_eq_true]
  constructor
  · decide
  · simp only [List.all_cons, Bool.and_eq_true]
    exact ⟨by decide, by decide, by decide, hall⟩

/-- sanitizeIdentifier output is a valid C identifier (P0). -/
theorem sanitizeIdentifier_valid (s : String) :
    isValidCIdent (sanitizeIdentifier s) = true := by
  unfold sanitizeIdentifier
  split
  · -- "tl_empty"
    unfold isValidCIdent; decide
  · rename_i c cs hfilter
    have hall : (c :: cs).all isValidCIdentChar = true :=
      hfilter ▸ all_filter_pred s.toList isValidCIdentChar
    split
    · -- "tl_" ++ ... where c is digit
      exact isValidCIdent_tl_prefix (c :: cs) hall
    · split
      · -- "tl_" ++ ... where cleaned is reserved
        exact isValidCIdent_tl_prefix (c :: cs) hall
      · -- String.ofList (c :: cs) passes through
        rename_i hnotdigit _hnotreserved
        unfold isValidCIdent
        rw [String.toList_ofList]
        simp only [Bool.and_eq_true]
        constructor
        · -- First char c is alpha or underscore
          have hvalid : isValidCIdentChar c = true :=
            List.all_eq_true.mp hall c List.mem_cons_self
          unfold isValidCIdentChar at hvalid
          have hd : c.isDigit = false := Bool.eq_false_iff.mpr hnotdigit
          rw [hd] at hvalid
          simp only [Bool.or_false] at hvalid
          exact hvalid
        · exact hall

/-! ## Injective Identifier Mapping

    A user name prints unchanged when it is a valid identifier, not reserved, and does
    not start with `tl_`. Temps print `tl_t<k>`, every other user name prints `tl_u`
    followed by its escape, and array elements print `base[idx]`. The three shapes
    cannot collide, so the mapping is injective (`varNameIdent_injective`). -/

/-- Inverse of `Nat.digitChar` on hex digits. -/
def hexVal (c : Char) : Nat := if c.isDigit then c.toNat - 48 else c.toNat - 87

private theorem hexVal_digitChar (n : Nat) (h : n < 16) : hexVal (Nat.digitChar n) = n :=
  (by decide : ∀ i : Fin 16, hexVal (Nat.digitChar i) = i) ⟨n, h⟩

private theorem isValidCIdentChar_digitChar (n : Nat) (h : n < 16) :
    isValidCIdentChar (Nat.digitChar n) = true :=
  (by decide : ∀ i : Fin 16, isValidCIdentChar (Nat.digitChar i) = true) ⟨n, h⟩

/-- `n` as six lowercase hex digits, most significant first. -/
def hex6 (n : Nat) : List Char :=
  [1048576, 65536, 4096, 256, 16, 1].map fun d => Nat.digitChar (n / d % 16)

private theorem hex6_injective {n m : Nat} (hn : n < 16777216) (hm : m < 16777216)
    (h : hex6 n = hex6 m) : n = m := by
  have hd : ∀ d, Nat.digitChar (n / d % 16) = Nat.digitChar (m / d % 16) →
      n / d % 16 = m / d % 16 := fun d e => by
    rw [← hexVal_digitChar _ (Nat.mod_lt _ (by decide)), e,
      hexVal_digitChar _ (Nat.mod_lt _ (by decide))]
  simp only [hex6, List.map_cons, List.map_nil, List.cons.injEq] at h
  obtain ⟨h5, h4, h3, h2, h1, h0, -⟩ := h
  have := hd _ h5; have := hd _ h4; have := hd _ h3
  have := hd _ h2; have := hd _ h1; have := hd _ h0
  omega

private theorem toNat_lt_hex6 (c : Char) : c.toNat < 16777216 := by
  have := c.valid
  simp only [UInt32.isValidChar, Nat.isValidChar] at this
  show c.val.toNat < _
  omega

/-- ASCII letters and digits stand for themselves; every other character becomes `_`
    and six hex digits of its code point. -/
def escapeChar (c : Char) : List Char :=
  if c.isAlphanum then [c] else '_' :: hex6 c.toNat

private theorem escapeChar_append_inj {c d : Char} {l r : List Char}
    (h : escapeChar c ++ l = escapeChar d ++ r) : c = d ∧ l = r := by
  unfold escapeChar at h
  by_cases hc : c.isAlphanum <;> by_cases hd : d.isAlphanum <;>
    simp only [hc, hd, if_true, if_false, Bool.false_eq_true, List.cons_append,
      List.nil_append, List.cons.injEq] at h
  · exact h
  · exact absurd (h.1 ▸ hc) (by decide)
  · exact absurd (h.1 ▸ hd) (by decide)
  · obtain ⟨hh, hl⟩ := List.append_inj h.2 (by simp [hex6])
    exact ⟨Char.toNat_inj.mp (hex6_injective (toNat_lt_hex6 c) (toNat_lt_hex6 d) hh), hl⟩

private theorem escapeChar_ne_nil (c : Char) : escapeChar c ≠ [] := by
  unfold escapeChar; split <;> simp

private theorem flatMap_escapeChar_injective {l r : List Char}
    (h : l.flatMap escapeChar = r.flatMap escapeChar) : l = r := by
  induction l generalizing r with
  | nil =>
    cases r with
    | nil => rfl
    | cons d r =>
      simp only [List.flatMap_nil, List.flatMap_cons] at h
      exact absurd (List.append_eq_nil_iff.mp h.symm).1 (escapeChar_ne_nil d)
  | cons c l ih =>
    cases r with
    | nil =>
      simp only [List.flatMap_nil, List.flatMap_cons] at h
      exact absurd (List.append_eq_nil_iff.mp h).1 (escapeChar_ne_nil c)
    | cons d r =>
      simp only [List.flatMap_cons] at h
      obtain ⟨rfl, ht⟩ := escapeChar_append_inj h
      rw [ih ht]

private theorem escapeChar_valid (c : Char) :
    ∀ x ∈ escapeChar c, isValidCIdentChar x = true := by
  intro x hx
  unfold escapeChar at hx
  split at hx
  · rename_i h
    simp only [List.mem_singleton] at hx; subst hx
    simp only [isValidCIdentChar, Bool.or_eq_true]
    exact Or.inl (by simpa [Char.isAlphanum] using h)
  · simp only [List.mem_cons, hex6, List.map_cons, List.map_nil, List.not_mem_nil,
      or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · decide
    all_goals exact isValidCIdentChar_digitChar _ (Nat.mod_lt _ (by decide))

/-- Injective escape of an arbitrary string into identifier characters. -/
def escapeIdent (s : String) : String := String.ofList (s.toList.flatMap escapeChar)

/-- A user name prints unchanged when it is a valid identifier, not in `reserved`,
    and does not start with `tl_`. -/
def keepsIdent (reserved : List String) (s : String) : Bool :=
  isValidCIdent s && !reserved.contains s && s.toList.take 3 != ['t', 'l', '_']

/-- Identifier for a user variable. -/
def userIdent (reserved : List String) (s : String) : String :=
  if keepsIdent reserved s then s else "tl_u" ++ escapeIdent s

/-- Identifier for a temp. -/
def tempIdent (k : Nat) : String := "tl_t" ++ toString k

private theorem not_mem_split {c : Char} :
    ∀ {a₁ a₂ b₁ b₂ : List Char}, c ∉ a₁ → c ∉ a₂ →
      a₁ ++ c :: b₁ = a₂ ++ c :: b₂ → a₁ = a₂ ∧ b₁ = b₂
  | [], [], _, _, _, _, h => ⟨rfl, (List.cons.inj h).2⟩
  | [], _ :: _, _, _, _, h₂, h =>
    absurd (List.cons.inj h).1 (fun e => h₂ (e ▸ List.mem_cons_self))
  | _ :: _, [], _, _, h₁, _, h =>
    absurd (List.cons.inj h).1.symm (fun e => h₁ (e ▸ List.mem_cons_self))
  | x :: a₁, y :: a₂, b₁, b₂, h₁, h₂, h => by
    simp only [List.cons_append, List.cons.injEq] at h
    obtain ⟨rfl, h⟩ := h
    obtain ⟨rfl, rfl⟩ := not_mem_split (fun m => h₁ (List.mem_cons_of_mem _ m))
      (fun m => h₂ (List.mem_cons_of_mem _ m)) h
    exact ⟨rfl, rfl⟩

private theorem not_mem_split_right {c : Char} {a₁ a₂ b₁ b₂ : List Char}
    (h₁ : c ∉ b₁) (h₂ : c ∉ b₂) (h : a₁ ++ c :: b₁ = a₂ ++ c :: b₂) :
    a₁ = a₂ ∧ b₁ = b₂ := by
  have hr := congrArg List.reverse h
  simp only [List.reverse_append, List.reverse_cons, List.append_assoc,
    List.singleton_append] at hr
  obtain ⟨hb, ha⟩ := not_mem_split (by simpa using h₁) (by simpa using h₂) hr
  exact ⟨List.reverse_inj.mp ha, List.reverse_inj.mp hb⟩

private theorem isDigit_of_mem_repr {n : Nat} {c : Char} (h : c ∈ (Nat.repr n).toList) :
    c.isDigit = true := by
  rw [Nat.toList_repr] at h
  exact Nat.isDigit_of_mem_toDigits (by decide) (by decide) h

private theorem bracket_not_mem_int (i : Int) : '[' ∉ (toString i).toList := by
  intro h
  cases i with
  | ofNat m => exact absurd (isDigit_of_mem_repr (n := m) h) (by decide)
  | negSucc m =>
    change '[' ∈ ("-" ++ Nat.repr (m + 1)).toList at h
    rw [String.toList_append] at h
    rcases List.mem_append.mp h with h | h
    · exact absurd h (by decide)
    · exact absurd (isDigit_of_mem_repr h) (by decide)

private theorem bracket_not_mem_of_valid {l : List Char}
    (h : ∀ x ∈ l, isValidCIdentChar x = true) : '[' ∉ l :=
  fun m => absurd (h _ m) (by decide)

private theorem userIdent_valid (reserved : List String) (s : String) :
    ∀ x ∈ (userIdent reserved s).toList, isValidCIdentChar x = true := by
  unfold userIdent
  split
  · rename_i hk
    unfold keepsIdent isValidCIdent at hk
    intro x hx
    cases hs : s.toList with
    | nil => rw [hs] at hk; simp at hk
    | cons c cs =>
      rw [hs] at hk hx
      simp only [Bool.and_eq_true] at hk
      exact List.all_eq_true.mp hk.1.1.2 x hx
  · intro x hx
    simp only [escapeIdent, String.toList_append, String.toList_ofList, List.mem_append,
      List.mem_flatMap] at hx
    rcases hx with hx | ⟨c, -, hx⟩
    · revert x; decide
    · exact escapeChar_valid c x hx

private theorem tempIdent_valid (k : Nat) :
    ∀ x ∈ (tempIdent k).toList, isValidCIdentChar x = true := by
  intro x hx
  simp only [tempIdent, String.toList_append, List.mem_append] at hx
  rcases hx with hx | hx
  · revert x; decide
  · have := isDigit_of_mem_repr (n := k) hx
    simp [isValidCIdentChar, this]

private theorem tlu_toList (s : String) :
    ("tl_u" ++ s).toList = 't' :: 'l' :: '_' :: 'u' :: s.toList := by
  rw [String.toList_append]; rfl

private theorem tlt_toList (s : String) :
    ("tl_t" ++ s).toList = 't' :: 'l' :: '_' :: 't' :: s.toList := by
  rw [String.toList_append]; rfl

private theorem userIdent_cases (reserved : List String) (s : String) :
    (userIdent reserved s = s ∧ s.toList.take 3 ≠ ['t', 'l', '_']) ∨
      userIdent reserved s = "tl_u" ++ escapeIdent s := by
  unfold userIdent
  split
  · rename_i hk
    unfold keepsIdent at hk
    simp only [Bool.and_eq_true, bne_iff_ne, ne_eq] at hk
    exact Or.inl ⟨rfl, hk.2⟩
  · exact Or.inr rfl

private theorem array_toList (b : String) (i : Int) :
    (b ++ "[" ++ toString i ++ "]").toList =
      b.toList ++ '[' :: ((toString i).toList ++ [']']) := by
  simp [String.toList_append]

private theorem bracket_mem_array (b : String) (i : Int) :
    '[' ∈ (b ++ "[" ++ toString i ++ "]").toList := by
  rw [array_toList]; simp

theorem userIdent_injective (reserved : List String) :
    Function.Injective (userIdent reserved) := by
  intro s₁ s₂ h
  rcases userIdent_cases reserved s₁ with ⟨h₁, k₁⟩ | h₁ <;>
    rcases userIdent_cases reserved s₂ with ⟨h₂, k₂⟩ | h₂ <;> rw [h₁, h₂] at h
  · exact h
  · exact absurd (by rw [h, tlu_toList]; rfl) k₁
  · exact absurd (by rw [← h, tlu_toList]; rfl) k₂
  · have := congrArg String.toList h
    simp only [tlu_toList, List.cons.injEq, true_and, escapeIdent, String.toList_ofList] at this
    exact String.toList_inj.mp (flatMap_escapeChar_injective this)

/-- Any VarName printer built from `userIdent`, `tempIdent` and `base[idx]` is injective. -/
theorem varNameIdent_injective (reserved : List String) (f : VarName → String)
    (hu : ∀ s, f (.user s) = userIdent reserved s) (ht : ∀ k, f (.temp k) = tempIdent k)
    (ha : ∀ b i, f (.array b i) = b ++ "[" ++ toString i ++ "]") :
    Function.Injective f := by
  have user_temp : ∀ s k, userIdent reserved s ≠ tempIdent k := fun s k h => by
    rcases userIdent_cases reserved s with ⟨h₁, k₁⟩ | h₁ <;> rw [h₁] at h
    · exact k₁ (by rw [h, tempIdent, tlt_toList]; rfl)
    · have := congrArg String.toList h
      simp [tempIdent] at this
  have user_array : ∀ s b i, userIdent reserved s ≠ b ++ "[" ++ toString i ++ "]" :=
    fun s b i h => bracket_not_mem_of_valid (userIdent_valid reserved s) (h ▸ bracket_mem_array b i)
  have temp_array : ∀ k b i, tempIdent k ≠ b ++ "[" ++ toString i ++ "]" :=
    fun k b i h => bracket_not_mem_of_valid (tempIdent_valid k) (h ▸ bracket_mem_array b i)
  intro v w h
  cases v <;> cases w <;> simp only [hu, ht, ha] at h
  · rw [userIdent_injective reserved h]
  · exact absurd h (user_temp _ _)
  · exact absurd h (user_array _ _ _)
  · exact absurd h.symm (user_temp _ _)
  · have := congrArg String.toList h
    simp only [tempIdent, tlt_toList, List.cons.injEq, true_and] at this
    exact congrArg VarName.temp (Nat.repr_injective (String.toList_inj.mp this))
  · exact absurd h (temp_array _ _ _)
  · exact absurd h.symm (user_array _ _ _)
  · exact absurd h.symm (temp_array _ _ _)
  · have := congrArg String.toList h
    rw [array_toList, array_toList] at this
    obtain ⟨hb, hi⟩ := not_mem_split_right
      (by simpa using bracket_not_mem_int _) (by simpa using bracket_not_mem_int _) this
    have hi := List.append_inj_left' hi rfl
    rw [String.toList_inj.mp hb, Int.repr_injective (String.toList_inj.mp hi)]

/-! ## Array Access Helper (N9.1) -/

/-- Format an array access expression. For generated code,
    the base expression is assumed to already be parenthesized by exprToC. -/
def formatArrayAccess (base : String) (idx : String) : String :=
  base ++ "[" ++ idx ++ "]"

@[simp] theorem formatArrayAccess_def (base idx : String) :
    formatArrayAccess base idx = base ++ "[" ++ idx ++ "]" := rfl

/-! ## Character Counting Infrastructure (shared C + Rust) (N21.1) -/

/-- Count occurrences of a character in a string. -/
def countChar (c : Char) (s : String) : Nat :=
  s.toList.countP (· == c)

@[simp] theorem countChar_empty (c : Char) : countChar c "" = 0 := by
  unfold countChar; rfl

theorem countChar_append (c : Char) (s1 s2 : String) :
    countChar c (s1 ++ s2) = countChar c s1 + countChar c s2 := by
  unfold countChar
  rw [String.toList_append, List.countP_append]

/-- countChar is additive over joinCode for non-newline characters. -/
private theorem isEmpty_eq_empty {s : String} (h : s.isEmpty = true) : s = "" := by
  simp [String.isEmpty] at h; exact h

theorem countChar_joinCode (c : Char) (s1 s2 : String) (hc : c ≠ '\n') :
    countChar c (joinCode s1 s2) = countChar c s1 + countChar c s2 := by
  unfold joinCode
  split
  · -- s1 empty
    rename_i h; rw [isEmpty_eq_empty h]; simp [countChar_empty]
  · split
    · -- s2 empty
      rename_i _ h; rw [isEmpty_eq_empty h]; simp [countChar_empty]
    · -- both non-empty: s1 ++ "\n" ++ s2
      rw [countChar_append, countChar_append]
      have : countChar c "\n" = 0 := by
        unfold countChar
        have htl : "\n".toList = ['\n'] := by native_decide
        rw [htl, List.countP_cons, List.countP_nil]
        simp [beq_iff_eq, Ne.symm hc]
      omega

/-! ## Rust Keyword Infrastructure (N21.1)
    Source: Rust 2021 edition, The Rust Reference §2.1 (Keywords) -/

/-- Rust strict keywords (39): cannot be used as identifiers. -/
def rustStrictKeywords : List String :=
  ["as", "async", "await", "break", "const", "continue", "crate", "dyn",
   "else", "enum", "extern", "false", "fn", "for", "if", "impl", "in",
   "let", "loop", "match", "mod", "move", "mut", "pub", "ref", "return",
   "self", "Self", "static", "struct", "super", "trait", "true", "type",
   "unsafe", "use", "where", "while"]

/-- Rust reserved keywords (14): reserved for future use. -/
def rustReservedKeywords : List String :=
  ["abstract", "become", "box", "do", "final", "gen", "macro", "override",
   "priv", "try", "typeof", "unsized", "virtual", "yield"]

/-- All Rust keywords (53 = 39 strict + 14 reserved). -/
def rustKeywords : List String :=
  rustStrictKeywords ++ rustReservedKeywords

/-- Rust standard library prelude names to avoid. -/
def rustStdlibNames : List String :=
  ["std", "alloc", "core", "usize", "isize",
   "i8", "i16", "i32", "i64", "i128",
   "u8", "u16", "u32", "u64", "u128",
   "f32", "f64", "bool", "str", "char",
   "Vec", "String", "Box", "Result", "Option",
   "Some", "None", "Ok", "Err",
   "panic", "println", "print", "assert", "main"]

/-- All Rust reserved identifiers (keywords + stdlib prelude). -/
def rustReservedIdentifiers : List String :=
  rustKeywords ++ rustStdlibNames

/-- Sanitize a string to produce a valid, non-reserved Rust identifier.
    Same strategy as C sanitization: removes invalid chars, prefixes "tl_" if needed. -/
def sanitizeIdentifierRust (s : String) : String :=
  match s.toList.filter isValidCIdentChar with
  | [] => "tl_empty"
  | c :: cs =>
    if c.isDigit then "tl_" ++ String.ofList (c :: cs)
    else if rustReservedIdentifiers.contains (String.ofList (c :: cs))
      then "tl_" ++ String.ofList (c :: cs)
    else String.ofList (c :: cs)

/-- Rust identifier validity uses the same ASCII rules as C
    (Trust-Lean only generates ASCII identifiers from its AST). -/
abbrev isValidRustIdent := isValidCIdent

/-! ## Rust Sanitization Properties (N21.2) -/

/-- No Rust keyword starts with "tl_". -/
private theorem rustKeywords_no_tl_prefix :
    ∀ k ∈ rustKeywords, k.toList.take 3 ≠ ['t', 'l', '_'] := by decide

/-- No Rust reserved identifier starts with "tl_". -/
private theorem rustReserved_no_tl_prefix :
    ∀ k ∈ rustReservedIdentifiers, k.toList.take 3 ≠ ['t', 'l', '_'] := by decide

/-- "tl_empty" is not a Rust keyword. -/
private theorem tl_empty_not_rustKeyword : "tl_empty" ∉ rustKeywords := by decide

/-- No string prefixed with "tl_" is a Rust keyword. -/
theorem tl_prefix_not_rustKeyword (s : String) : ("tl_" ++ s) ∉ rustKeywords := by
  intro hmem
  exact rustKeywords_no_tl_prefix ("tl_" ++ s) hmem (tl_append_toList_take s)

/-- sanitizeIdentifierRust never produces a Rust keyword (P0). -/
theorem sanitizeIdentifierRust_not_keyword (s : String) :
    sanitizeIdentifierRust s ∉ rustKeywords := by
  unfold sanitizeIdentifierRust
  split
  · exact tl_empty_not_rustKeyword
  · rename_i c cs hfilter
    split
    · exact tl_prefix_not_rustKeyword _
    · split
      · exact tl_prefix_not_rustKeyword _
      · rename_i _hnotdigit hnotreserved
        intro hmem
        have hres : String.ofList (c :: cs) ∈ rustReservedIdentifiers :=
          List.mem_append_left _ hmem
        rw [List.contains_iff_mem] at hnotreserved
        exact hnotreserved hres

/-- sanitizeIdentifierRust always produces a non-empty string (P0). -/
theorem sanitizeIdentifierRust_nonempty (s : String) :
    (sanitizeIdentifierRust s).toList ≠ [] := by
  unfold sanitizeIdentifierRust
  split
  · decide
  · rename_i c cs _hfilter
    split
    · rw [String.toList_append, tl_toList]; exact List.cons_ne_nil _ _
    · split
      · rw [String.toList_append, tl_toList]; exact List.cons_ne_nil _ _
      · rw [String.toList_ofList]; exact List.cons_ne_nil _ _

/-- sanitizeIdentifierRust output is a valid identifier (P0). -/
theorem sanitizeIdentifierRust_valid (s : String) :
    isValidRustIdent (sanitizeIdentifierRust s) = true := by
  unfold sanitizeIdentifierRust
  split
  · unfold isValidRustIdent isValidCIdent; decide
  · rename_i c cs hfilter
    have hall : (c :: cs).all isValidCIdentChar = true :=
      hfilter ▸ all_filter_pred s.toList isValidCIdentChar
    split
    · exact isValidCIdent_tl_prefix (c :: cs) hall
    · split
      · exact isValidCIdent_tl_prefix (c :: cs) hall
      · rename_i hnotdigit _hnotreserved
        unfold isValidRustIdent isValidCIdent
        rw [String.toList_ofList]
        simp only [Bool.and_eq_true]
        constructor
        · have hvalid : isValidCIdentChar c = true :=
            List.all_eq_true.mp hall c List.mem_cons_self
          unfold isValidCIdentChar at hvalid
          have hd : c.isDigit = false := Bool.eq_false_iff.mpr hnotdigit
          rw [hd] at hvalid
          simp only [Bool.or_false] at hvalid
          exact hvalid
        · exact hall

/-- No string prefixed with "tl_" is in rustReservedIdentifiers. -/
theorem tl_prefix_not_rustReserved (s : String) :
    ("tl_" ++ s) ∉ rustReservedIdentifiers := by
  intro hmem
  exact rustReserved_no_tl_prefix ("tl_" ++ s) hmem (tl_append_toList_take s)

/-- "tl_empty" is not in rustReservedIdentifiers. -/
private theorem tl_empty_not_rustReserved : "tl_empty" ∉ rustReservedIdentifiers := by decide

/-- Helper: if all chars are valid, filter is identity. -/
private theorem filter_valid_id (l : List Char) (h : l.all isValidCIdentChar = true) :
    l.filter isValidCIdentChar = l :=
  List.filter_eq_self.mpr (List.all_eq_true.mp h)

/-- Helper: output of sanitizeIdentifierRust has all valid ident chars. -/
private theorem sanitizeIdentifierRust_allValid (s : String) :
    (sanitizeIdentifierRust s).toList.all isValidCIdentChar = true := by
  have h := sanitizeIdentifierRust_valid s
  unfold isValidRustIdent isValidCIdent at h
  cases hlist : (sanitizeIdentifierRust s).toList with
  | nil => simp
  | cons c cs =>
    rw [hlist] at h; simp only [Bool.and_eq_true] at h; exact h.2

/-- Helper: output of sanitizeIdentifierRust starts with non-digit. -/
private theorem sanitizeIdentifierRust_notDigitStart (s : String) :
    ∀ c cs, (sanitizeIdentifierRust s).toList = c :: cs → c.isDigit = false := by
  unfold sanitizeIdentifierRust
  split
  · -- "tl_empty": first char 't'
    intro c cs h
    have heq : "tl_empty".toList = ['t', 'l', '_', 'e', 'm', 'p', 't', 'y'] := by native_decide
    rw [heq] at h; rw [(List.cons.inj h.symm).1]; decide
  · rename_i c' cs' _
    split
    · -- "tl_" ++ ...: first char 't'
      intro c cs h; rw [String.toList_append, tl_toList] at h
      have : c = 't' := by simp at h; exact h.1.symm
      rw [this]; decide
    · split
      · -- "tl_" ++ ...: first char 't'
        intro c cs h; rw [String.toList_append, tl_toList] at h
        have : c = 't' := by simp at h; exact h.1.symm
        rw [this]; decide
      · -- pass-through: c'.isDigit is false
        rename_i hnotdigit _
        intro c cs h; rw [String.toList_ofList] at h
        have : c = c' := (List.cons.inj h).1.symm
        rw [this]; exact Bool.eq_false_iff.mpr hnotdigit

/-- Helper: output of sanitizeIdentifierRust is not in rustReservedIdentifiers. -/
private theorem sanitizeIdentifierRust_notReserved (s : String) :
    sanitizeIdentifierRust s ∉ rustReservedIdentifiers := by
  unfold sanitizeIdentifierRust
  split
  · exact tl_empty_not_rustReserved
  · rename_i c cs _hfilter
    split
    · exact tl_prefix_not_rustReserved _
    · split
      · exact tl_prefix_not_rustReserved _
      · rename_i _ hnotres
        intro hmem
        exact absurd (List.contains_iff_mem.mpr hmem) hnotres

/-- sanitizeIdentifierRust is idempotent: applying it twice = once (P0).
    Relies on three properties of the output: all chars valid, non-digit start,
    not in rustReservedIdentifiers. -/
theorem sanitizeIdentifierRust_idempotent (s : String) :
    sanitizeIdentifierRust (sanitizeIdentifierRust s) = sanitizeIdentifierRust s := by
  set r := sanitizeIdentifierRust s
  have hallValid := sanitizeIdentifierRust_allValid s
  have hnotempty := sanitizeIdentifierRust_nonempty s
  have hnotres := sanitizeIdentifierRust_notReserved s
  -- r.toList.filter isValidCIdentChar = r.toList (all chars are valid)
  have hfilterId := filter_valid_id r.toList hallValid
  -- Unfold the second application
  show sanitizeIdentifierRust r = r
  unfold sanitizeIdentifierRust
  rw [hfilterId]
  cases hlist : r.toList with
  | nil => exact absurd hlist hnotempty
  | cons c cs =>
    have hnotdigit := sanitizeIdentifierRust_notDigitStart s c cs hlist
    -- r.toList = c :: cs, so String.ofList (c :: cs) = r
    have heq_r : String.ofList (c :: cs) = r := by
      rw [← hlist, String.ofList_toList]
    -- Not reserved as Bool (needed for if-then-else reduction)
    have hnotresOL : rustReservedIdentifiers.contains (String.ofList (c :: cs)) = false := by
      apply Bool.eq_false_iff.mpr; intro h
      have hmem := List.contains_iff_mem.mp h
      rw [heq_r] at hmem; exact hnotres hmem
    simp only [hnotdigit, hnotresOL]
    exact heq_r

/-! ## C-Safe Variable Names (N9.2) -/

/-- Convert VarName to a C identifier string. Valid user names that are not C-reserved
    and do not start with `tl_` print unchanged; temps print `tl_t<k>`; every other
    user name prints `tl_u` and its escape; array elements print `base[idx]`. -/
def varNameToC : VarName → String
  | .user s => userIdent cReservedIdentifiers s
  | .temp k => tempIdent k
  | .array base idx => base ++ "[" ++ toString idx ++ "]"

/-- Distinct variables print to distinct C identifiers. -/
theorem varNameToC_injective : Function.Injective varNameToC :=
  varNameIdent_injective cReservedIdentifiers varNameToC
    (fun _ => rfl) (fun _ => rfl) (fun _ _ => rfl)

end TrustLean
