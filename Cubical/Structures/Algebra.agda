{-# OPTIONS --cubical --safe #-}

module Cubical.Structures.Algebra where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Equiv.HalfAdjoint
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.SIP renaming (SNS-PathP to SNS)

open import Cubical.Data.Sigma

open import Cubical.Structures.Macro
open import Cubical.Structures.Module    renaming (⟨_⟩ to ⟨_⟩m)
open import Cubical.Structures.Ring      renaming (⟨_⟩ to ⟨_⟩r)
open import Cubical.Structures.AbGroup   hiding (⟨_⟩)
open import Cubical.Structures.Group     hiding (⟨_⟩)
open import Cubical.Structures.Monoid    using (Monoid)

open Iso

private
  variable
    ℓ : Level


record IsAlgebra (R : Ring {ℓ}) {A : Type ℓ}
                 (0a 1a : A) (_+_ _·_ : A → A → A) (-_ : A → A)
                 (_⋆_ : ⟨ R ⟩r → A → A) : Type ℓ where

  constructor isalgebra

  open Ring R using (1r) renaming (_+_ to _+r_; _·_ to _·r_)

  field
    isRing       : IsRing 0a 1a _+_ _·_ -_
    isLeftModule : IsLeftModule R 0a _+_ -_ _⋆_
    ⋆-lassoc     : (r : ⟨ R ⟩r) (x y : A) → (r ⋆ x) · y ≡ r ⋆ (x · y)
    ⋆-rassoc     : (r : ⟨ R ⟩r) (x y : A) → r ⋆ (x · y) ≡ x · (r ⋆ y)

  open IsLeftModule isLeftModule public

record Algebra (R : Ring {ℓ}) : Type (ℓ-suc ℓ) where

  constructor algebra

  field
    Carrier        : Type ℓ
    0a             : Carrier
    1a             : Carrier
    _+_            : Carrier → Carrier → Carrier
    _·_            : Carrier → Carrier → Carrier
    -_             : Carrier → Carrier
    _⋆_            : ⟨ R ⟩r → Carrier → Carrier
    isAlgebra      : IsAlgebra R 0a 1a _+_ _·_ -_ _⋆_

  open IsAlgebra isAlgebra public


module _ {R : Ring {ℓ}} where
  ⟨_⟩ : Algebra R → Type ℓ
  ⟨_⟩ = Algebra.Carrier

  Algebra→Module : (A : Algebra R) → LeftModule R
  Algebra→Module (algebra A _ _ _ _ _ _ (isalgebra _ isLeftModule _ _)) =
    leftmodule A _ _ _ _ isLeftModule

  Algebra→Ring : (A : Algebra R) → Ring {ℓ}
  Algebra→Ring (algebra A _ _ _ _ _ _ (isalgebra isRing _ _ _)) =
    ring A _ _ _ _ _ isRing

  Algebra→AbGroup : (A : Algebra R) → AbGroup {ℓ}
  Algebra→AbGroup A = Ring→AbGroup (Algebra→Ring A)

  Algebra→Monoid : (A : Algebra R) → Monoid {ℓ}
  Algebra→Monoid A = Ring→Monoid (Algebra→Ring A)

  isSetAlgebra : (A : Algebra R) → isSet ⟨ A ⟩
  isSetAlgebra A = isSetAbGroup (Algebra→AbGroup A)

record AlgebraIso {R : Ring {ℓ}} (A B : Algebra R) : Type ℓ where

  constructor moduleiso

  instance
    _ : Algebra R
    _ = A
    _ : Algebra R
    _ = B

  open Algebra {{...}}

  field
    e      : ⟨ A ⟩ ≃ ⟨ B ⟩
    isHom+ : (x y : ⟨ A ⟩) → equivFun e (x + y) ≡ equivFun e x + equivFun e y
    isHom· : (x y : ⟨ A ⟩) → equivFun e (x · y) ≡ equivFun e x · equivFun e y
    pres1  : equivFun e 1a ≡ 1a
    comm⋆  : (r : ⟨ R ⟩r) (x : ⟨ A ⟩) → equivFun e (r ⋆ x) ≡ r ⋆ equivFun e x

module AlgebraΣ-theory (R : Ring {ℓ}) where

  open Macro ℓ (recvar (recvar var) , recvar (recvar var) , var ,
                param ⟨ R ⟩r (recvar var)) public renaming
    ( structure to raw-algebra-structure
    ; iso       to raw-algebra-iso
    ; isSNS     to raw-algebra-is-SNS )

  open Ring R using (1r) renaming (_+_ to _+r_; _·_ to _·r_)
  open RingΣ-theory
  open LeftModuleΣ-theory R

  algebra-axioms : (A : Type ℓ) (str : raw-algebra-structure A) → Type ℓ
  algebra-axioms A (_+_ , _·_ , 1a , _⋆_) =
               ring-axioms A (_+_ , 1a , _·_)
               × leftModule-axioms A (_+_ , _⋆_)
               × ((r : ⟨ R ⟩r) (x y : A) → (r ⋆ x) · y ≡ r ⋆ (x · y))
               × ((r : ⟨ R ⟩r) (x y : A) → r ⋆ (x · y) ≡ x · (r ⋆ y))

  algebra-structure : Type ℓ → Type ℓ
  algebra-structure = add-to-structure raw-algebra-structure algebra-axioms

  AlgebraΣ : Type (ℓ-suc ℓ)
  AlgebraΣ = TypeWithStr ℓ algebra-structure

  algebra-iso : StrIso algebra-structure ℓ
  algebra-iso = add-to-iso raw-algebra-iso algebra-axioms

  isSetAlgebraΣ : (A : AlgebraΣ) → isSet _
  isSetAlgebraΣ (A , _ , (_ , isLeftModule , _) ) = isSetLeftModuleΣ (A , _ , isLeftModule)

  isProp-algebra-axioms : (A : Type ℓ) (s : raw-algebra-structure A)
                             → isProp (algebra-axioms A s)
  isProp-algebra-axioms A (_+_ , _·_ , 1a , _⋆_) =
     isProp× (isProp-ring-axioms A (_+_ , 1a , _·_ ))
    (isPropΣ (isProp-leftModule-axioms A (_+_ , _⋆_))
      (λ isLeftModule →
     isProp× (isPropΠ3 (λ _ _ _ → (isSetLeftModuleΣ (A , _ , isLeftModule)) _ _))
             (isPropΠ3 (λ _ _ _ → (isSetLeftModuleΣ (A , _ , isLeftModule)) _ _))))

  Algebra→AlgebraΣ : Algebra R → AlgebraΣ
  Algebra→AlgebraΣ (algebra A 0a 1a _+_ _·_ -_ _⋆_
                            (isalgebra isRing isLeftModule ⋆-lassoc ⋆-rassoc)) =
    A , (_+_ , _·_ , 1a , _⋆_) ,
    Ring→RingΣ (ring A 0a 1a _+_ _·_ -_ isRing) .snd .snd ,
    (LeftModule→LeftModuleΣ (leftmodule A _ _ _ _ isLeftModule) .snd .snd) ,
    ⋆-lassoc ,
    ⋆-rassoc

{-
  AlgebraΣ→Algebra : AlgebraΣ → Algebra R
  AlgebraΣ→Algebra (A , (_+_ , _·_ , 1a , _⋆_) , isRing , isLeftModule , lassoc , rassoc) =
    let
        isRing : IsRing _ 1a _+_ _·_ _
        isRing = RingΣ→Ring (A , (_+_ , 1a , _·_) , isRing) .Ring.isRing
        open Ring (ring _ _ _ _ _ _ isRing) using (-_)
        0a : A
        0a = {!!}
        open LeftModule (LeftModuleΣ→LeftModule (_ , _ , isLeftModule))
          using () renaming (isLeftModule to isLeftModule′)
        isLeftModule″ : IsLeftModule R _ _+_ _ _⋆_
        isLeftModule″ = isLeftModule′
    in algebra A 0a 1a _+_ _·_ -_ _⋆_ (isalgebra isRing {!isLeftModule′!} lassoc rassoc)
-}
