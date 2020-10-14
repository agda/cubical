{-# OPTIONS --cubical --no-import-sorts --allow-unsolved-metas #-}

module SyntheticReals.Number.Operations where

open import Cubical.Foundations.Everything renaming (_⁻¹ to _⁻¹ᵖ; assoc to ∙-assoc)
open import Cubical.Relation.Nullary.Base -- ¬_
open import Cubical.Data.Unit.Base -- Unit
open import Cubical.Data.Sigma.Base renaming (_×_ to infixr 4 _×_)
open import Cubical.Data.Empty renaming (elim to ⊥-elim) -- `⊥` and `elim`
open import Function.Base using (_$_)

open import SyntheticReals.Number.Postulates
open import SyntheticReals.Number.Base
open import SyntheticReals.Number.Coercions

open import SyntheticReals.Number.Operations.Specification
open import SyntheticReals.Number.Operations.Details
open import SyntheticReals.Number.Operations.Details using (_⁻¹; -_) public

open ℕⁿ
open ℤᶻ
open ℚᶠ
open ℝʳ
open ℂᶜ

-- infixl 6 _-_
infixl 7 _·_
infixl 6 _+_
infixl 4 _#_
infixl 4 _<_
infixl 4 _≤_

-- homogeneous operations

private
  _+ʰ_ : ∀{l p q} → Number (l , p) → Number (l , q) → Number (l , +-Positivityʰ l p q)
  _+ʰ_ {isNat    } x y = (num x +ⁿ num y) ,, (x +ʰⁿ y)
  _+ʰ_ {isInt    } x y = (num x +ᶻ num y) ,, (x +ʰᶻ y)
  _+ʰ_ {isRat    } x y = (num x +ᶠ num y) ,, (x +ʰᶠ y)
  _+ʰ_ {isReal   } x y = (num x +ʳ num y) ,, (x +ʰʳ y)
  _+ʰ_ {isComplex} x y = (num x +ᶜ num y) ,, (x +ʰᶜ y)

  _·ʰ_ : ∀{l p q} → Number (l , p) → Number (l , q) → Number (l , ·-Positivityʰ l p q)
  _·ʰ_ {isNat    } x y = (num x ·ⁿ num y) ,, (x ·ʰⁿ y)
  _·ʰ_ {isInt    } x y = (num x ·ᶻ num y) ,, (x ·ʰᶻ y)
  _·ʰ_ {isRat    } x y = (num x ·ᶠ num y) ,, (x ·ʰᶠ y)
  _·ʰ_ {isReal   } x y = (num x ·ʳ num y) ,, (x ·ʰʳ y)
  _·ʰ_ {isComplex} x y = (num x ·ᶜ num y) ,, (x ·ʰᶜ y)

  _<ʰ_ : ∀{L} → (x y : NumberKindInterpretation L) → Type (NumberKindProplevel L)
  _<ʰ_ {isNat}     x y = x <ⁿ y
  _<ʰ_ {isInt}     x y = x <ᶻ y
  _<ʰ_ {isRat}     x y = x <ᶠ y
  _<ʰ_ {isReal}    x y = x <ʳ y
  -- NOTE: this is some realization of a partial function, because `_<_` is defined on all numbers
  --       one might already anticipate that this breaks something in the future ...
  _<ʰ_ {isComplex} x y = {{p : ⊥}} → Lift ⊥

  _≤ʰ_ : ∀{L} → (x y : NumberKindInterpretation L) → Type (NumberKindProplevel L)
  _≤ʰ_ {isNat}     x y = x ≤ⁿ y
  _≤ʰ_ {isInt}     x y = x ≤ᶻ y
  _≤ʰ_ {isRat}     x y = x ≤ᶠ y
  _≤ʰ_ {isReal}    x y = x ≤ʳ y
  -- NOTE: this is some realization of a partial function, because `_≤_` is defined on all numbers
  --       one might already anticipate that this breaks something in the future ...
  _≤ʰ_ {isComplex} x y = {{p : ⊥}} → Lift ⊥

  _#ʰ_ : ∀{L} → (x y : NumberKindInterpretation L) → Type (NumberKindProplevel L)
  _#ʰ_ {isNat}     x y = x #ⁿ y
  _#ʰ_ {isInt}     x y = x #ᶻ y
  _#ʰ_ {isRat}     x y = x #ᶠ y
  _#ʰ_ {isReal}    x y = x #ʳ y
  _#ʰ_ {isComplex} x y = x #ᶜ y


{- NOTE: this creates a weird Number.L in the Have/Goal display

module _ {Lx Ly Px Py} (x : Number (Lx , Px)) (y : Number (Ly , Py)) where
  private L = maxₙₗ' Lx Ly
  _+_ : Number (L , +-Positivityʰ L (coerce-PositivityKind Lx L Px) (coerce-PositivityKind Ly L Py))
  _+_ =
    let (Lx≤L , Ly≤L) = max-implies-≤ₙₗ₂' Lx Ly
    in coerce Lx L Lx≤L x +ʰ coerce Ly L Ly≤L y
-}

-- inhomogeneous operations

_+_ : ∀{Lx Ly Px Py} → (x : Number (Lx , Px)) (y : Number (Ly , Py))
    → let L = maxₙₗ Lx Ly
      in Number (L , +-Positivityʰ L (coerce-PositivityKind Lx L Px) (coerce-PositivityKind Ly L Py))
_+_ {Lx} {Ly} {Px} {Py} x y =
  let L = maxₙₗ Lx Ly
      (Lx≤L , Ly≤L) = max-implies-≤ₙₗ₂ Lx Ly
  in coerce Lx L Lx≤L x +ʰ coerce Ly L Ly≤L y

_·_ : ∀{Lx Ly Px Py} → (x : Number (Lx , Px)) (y : Number (Ly , Py))
    → let L = maxₙₗ Lx Ly
      in Number (L , ·-Positivityʰ L (coerce-PositivityKind Lx L Px) (coerce-PositivityKind Ly L Py))
_·_ {Lx} {Ly} {Px} {Py} x y =
  let L = maxₙₗ Lx Ly
      (Lx≤L , Ly≤L) = max-implies-≤ₙₗ₂ Lx Ly
  in coerce Lx L Lx≤L x ·ʰ coerce Ly L Ly≤L y


_<_ : ∀{Lx Ly Px Py} → (x : Number (Lx , Px)) (y : Number (Ly , Py)) → Type (NumberKindProplevel (maxₙₗ Lx Ly))
_<_ {Lx} {Ly} {Px} {Py} x y =
  let L = maxₙₗ Lx Ly
      (Lx≤L , Ly≤L) = max-implies-≤ₙₗ₂ Lx Ly
  in num (coerce Lx L Lx≤L x) <ʰ num (coerce Ly L Ly≤L y)


_≤_ : ∀{Lx Ly Px Py} → (x : Number (Lx , Px)) (y : Number (Ly , Py)) → Type (NumberKindProplevel (maxₙₗ Lx Ly))
_≤_ {Lx} {Ly} {Px} {Py} x y =
  let L = maxₙₗ Lx Ly
      (Lx≤L , Ly≤L) = max-implies-≤ₙₗ₂ Lx Ly
  in num (coerce Lx L Lx≤L x) ≤ʰ num (coerce Ly L Ly≤L y)

_#_ : ∀{Lx Ly Px Py} → (x : Number (Lx , Px)) (y : Number (Ly , Py)) → Type (NumberKindProplevel (maxₙₗ Lx Ly))
_#_ {Lx} {Ly} {Px} {Py} x y =
  let L = maxₙₗ Lx Ly
      (Lx≤L , Ly≤L) = max-implies-≤ₙₗ₂ Lx Ly
  in num (coerce Lx L Lx≤L x) #ʰ num (coerce Ly L Ly≤L y)
