{-
This module provides  utilities designed for printing messages and errors in the context of macros.

Key functionalities include:

- **Error Message Composition:**
  - Custom composable error parts using the `_∷ₑ_`, `_++ₑ_`, `_∷nl_`, and `_++nl_` operators.
  - Instances for converting various types (`String`, `Char`, `ℕ`, `Bool`, `R.Term`, `R.Name`, `R.ErrorPart`) to `R.ErrorPart`.

- **String Manipulation:**
  - Indentation and offsetting functions (`indent'`, `indent`, `indentₑ`, `offsetStr`, `offsetStrR`).
  - String formatting and line handling (`lines`).

- **Error Rendering:**
  - Functions for rendering terms and arguments (`renderTerm`, `renderArg`).
  - Concatenating runs of consecutive strErr in List of ErrorParts  (`<>StrErr`).

- **Result Wrappers:**
  - Wrapping results and errors in the `ResultIs` type using `wrapResult` and `wrapError`.

- **Testing Helpers:**
  - `assertNoErr` function to facilitate writing tests that check for the presence or absence of errors.
  - `TestResult` data type which includes `✓-pass` and `⊘-fail` constructors.

- **Macros:**
  - `showCtx` macro for printing the current context in the form of a type error.
  - `showTeles` function to generate a list of error parts from a telescope.

-}

{-# OPTIONS --safe  #-}

module Cubical.Tactics.Reflection.Error where


import Agda.Builtin.Reflection as R
open import Agda.Builtin.String
open import Agda.Builtin.Char

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function

open import Cubical.Reflection.Base
open import Cubical.Reflection.Sugar

open import Cubical.Data.List
open import Cubical.Data.Nat
open import Cubical.Data.Bool
open import Cubical.Data.Sigma

open import Cubical.Tactics.Reflection.Variables
open import Cubical.Tactics.Reflection.Utilities

record ToErrorPart {ℓ} (A : Type ℓ) : Type ℓ where
 field
   toErrorPart : A → R.ErrorPart

open ToErrorPart

infixr 5 _∷ₑ_ _∷nl_ _++ₑ_ _++nl_



_∷ₑ_ :  ∀ {ℓ} {A : Type ℓ} → {{ToErrorPart A}} → A → List R.ErrorPart → List R.ErrorPart
_∷ₑ_  ⦃ tep ⦄ x = (toErrorPart tep x) ∷_

_++ₑ_ :  ∀ {ℓ} {A : Type ℓ} → {{ToErrorPart A}} → List A → List R.ErrorPart → List R.ErrorPart
_++ₑ_  ⦃ tep ⦄ x = (map (toErrorPart tep) x) ++_

[_]ₑ :  ∀ {ℓ} {A : Type ℓ} → {{ToErrorPart A}} → A → List R.ErrorPart
[_]ₑ = _∷ₑ []

instance
 ToErrorPartString : ToErrorPart String
 toErrorPart ToErrorPartString = R.strErr

 ToErrorPartChar : ToErrorPart Char
 toErrorPart ToErrorPartChar = R.strErr ∘S primStringFromList ∘S [_]


 ToErrorPartℕ : ToErrorPart ℕ
 toErrorPart ToErrorPartℕ = R.strErr ∘ primShowNat

 ToErrorPartBool : ToErrorPart Bool
 toErrorPart ToErrorPartBool = R.strErr ∘ (if_then "𝟙" else "𝟘")


 ToErrorPartTerm : ToErrorPart R.Term
 toErrorPart ToErrorPartTerm = R.termErr

 ToErrorPartName : ToErrorPart R.Name
 toErrorPart ToErrorPartName = R.nameErr

 ToErrorPartErrorPart : ToErrorPart R.ErrorPart
 toErrorPart ToErrorPartErrorPart x = x


_∷nl_ :  ∀ {ℓ} {A : Type ℓ} → {{ToErrorPart A}} → A → List R.ErrorPart → List R.ErrorPart
_∷nl_  x y = x ∷ₑ "\n" ∷ₑ y

_++nl_ :  ∀ {ℓ} {A : Type ℓ} → {{ToErrorPart A}} → List A → List R.ErrorPart → List R.ErrorPart
_++nl_  x y = x ++ₑ "\n" ∷ₑ y


<>StrErr :  List R.ErrorPart → List R.ErrorPart
<>StrErr [] = []
<>StrErr (x ∷ xs) = h x xs
 where
 h : R.ErrorPart → List R.ErrorPart → List R.ErrorPart
 h x [] = [ x ]
 h (R.strErr x) (R.strErr y ∷ xs) = h (R.strErr (x <> y)) xs
 h x (y ∷ xs) = x ∷ h y xs

niceAtomList : List (R.Term) → List R.ErrorPart
niceAtomList = h 0
 where
  h : _ → _
  h _  [] = []
  h k (x ∷ xs) = (mkNiceVar k  <> " = ") ∷ₑ x ∷ₑ  "\n"  ∷ₑ h (suc k) xs



unArgs : List (R.Arg (R.Term)) → List R.ErrorPart
unArgs [] = []
unArgs (R.arg i x ∷ x₁) = x ∷ₑ unArgs x₁

renderTerm : R.Term → R.TC String
renderTerm = R.formatErrorParts ∘ [_]ₑ

renderArg : R.Arg R.Term → R.TC String
renderArg (R.arg i x) = renderTerm x


stringLength : String → ℕ
stringLength = length ∘S primStringToList


indent' : Bool → Char → ℕ → String → String
indent' _ _ zero x = x
indent' b ch k =
  primStringFromList ∘S
   (if b then ((ch ∷_) ∘S (ind ++_)) else (idfun _)) ∘S h ∘S primStringToList

  where
  ind = repeat k ' '

  h : List Char → List Char
  h [] = []
  h (x ∷ xs) with primCharEquality x '\n'
  ... | false = x ∷ h xs
  ... | true =  '\n' ∷ ch ∷ ind ++ h xs


indent = indent' true

indentₑ : ℕ → List R.ErrorPart → List R.ErrorPart
indentₑ k = map (λ { (R.strErr x) → R.strErr (indent ' ' k x) ; x → x }) ∘S <>StrErr

offsetStr : ℕ → String → String
offsetStr k =   primStringFromList ∘S offset ' ' k ∘S primStringToList

offsetStrR : ℕ → String → String
offsetStrR k =   primStringFromList ∘S offsetR ' ' k ∘S primStringToList

data ResultIs {ℓ} {A : Type ℓ} : A → Type ℓ where
 resultIs : ∀ s → ResultIs s


wrapResult : ∀ {ℓ} {A : Type ℓ} → R.Term → A → R.TC Unit
wrapResult hole x = do
   x' ← R.quoteTC x
   R.unify (R.con (quote resultIs) v[ x' ]) hole


lines : String → List String
lines = map primStringFromList ∘S h [] ∘S primStringToList
 where
 h : List (List Char) → List Char →  List (List Char)
 h xxs [] = xxs
 h xxs ('\n' ∷ xs) = xxs ++ h [] xs
 h [] (x ∷ xs) = h [ [ x ] ] xs

 h xxs (x ∷ xs) =  h ((init xxs) ++ map (_∷ʳ x) (drop (predℕ (length xxs)) xxs))  xs



wrapError : R.Term → List (R.ErrorPart) → R.TC Unit
wrapError hole x = do
   x' ← ((map (offsetStrR 45) ∘S lines) <$> R.formatErrorParts x) >>= R.quoteTC
   R.unify (R.con (quote resultIs) v[ x' ]) hole


data TestResult : Type where
 ✓-pass ⊘-fail : TestResult

assertNoErr : ∀ {ℓ} {A : Type ℓ} → R.Term → R.TC A → R.TC Unit
assertNoErr h x = do
  (x >> wrapResult h ✓-pass) <|> wrapResult h ⊘-fail


visibillityWrap : R.Visibility → String → String
visibillityWrap R.visible x = " " <> x <> " "
visibillityWrap R.hidden x = "{" <> x <> "}"
visibillityWrap R.instance′ x = "⦃" <> x <> "⦄"

showTeles : R.Telescope → R.TC (List R.ErrorPart)
showTeles = concatMapM h ∘S liftedTele
 where
 h : String × R.Arg R.Type → R.TC (List R.ErrorPart)
 h (s , R.arg (R.arg-info v m) ty) = do
   pure $ s ∷ₑ " : " ∷ₑ ty ∷nl []

macro
 showCtx : R.Term → R.TC Unit
 showCtx _ = R.getContext >>= (showTeles >=> R.typeError)

