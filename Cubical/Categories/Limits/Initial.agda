{-# OPTIONS --safe #-}
module Cubical.Categories.Limits.Initial where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism renaming (Iso to _≅_)
open import Cubical.HITs.PropositionalTruncation.Base

open import Cubical.Data.Sigma

open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.Adjoint

private
  variable
    ℓ ℓ' : Level
    ℓC ℓC' ℓD ℓD' : Level

module _ (C : Category ℓ ℓ') where
  open Category C

  isInitial : (x : ob) → Type (ℓ-max ℓ ℓ')
  isInitial x = ∀ (y : ob) → isContr (C [ x , y ])

  Initial : Type (ℓ-max ℓ ℓ')
  Initial = Σ[ x ∈ ob ] isInitial x

  initialOb : Initial → ob
  initialOb = fst

  initialArrow : (T : Initial) (y : ob) → C [ initialOb T , y ]
  initialArrow T y = T .snd y .fst

  initialArrowUnique : {T : Initial} {y : ob} (f : C [ initialOb T , y ])
                      → initialArrow T y ≡ f
  initialArrowUnique {T} {y} f = T .snd y .snd f

  initialEndoIsId : (T : Initial) (f : C [ initialOb T , initialOb T ])
                   → f ≡ id
  initialEndoIsId T f = isContr→isProp (T .snd (initialOb T)) f id

  hasInitial : Type (ℓ-max ℓ ℓ')
  hasInitial = ∥ Initial ∥₁

  -- Initiality of an object is a proposition.
  isPropIsInitial : (x : ob) → isProp (isInitial x)
  isPropIsInitial _ = isPropΠ λ _ → isPropIsContr

  open isIso

  -- Objects that are initial are isomorphic.
  initialToIso : (x y : Initial) → CatIso C (initialOb x) (initialOb y)
  initialToIso x y .fst = initialArrow x (initialOb y)
  initialToIso x y .snd .inv = initialArrow y (initialOb x)
  initialToIso x y .snd .sec = initialEndoIsId y _
  initialToIso x y .snd .ret = initialEndoIsId x _

  open isUnivalent

  -- The type of initial objects of a univalent category is a proposition,
  -- i.e. all initial objects are equal.
  isPropInitial : (hC : isUnivalent C) → isProp Initial
  isPropInitial hC x y =
    Σ≡Prop isPropIsInitial (CatIsoToPath hC (initialToIso x y))

module _ {C : Category ℓC ℓC'} {D : Category ℓD ℓD'} (F : Functor C D) where
  open Category
  open Functor
  open NaturalBijection
  open _⊣_
  open _≅_

  preservesInitial : Type (ℓ-max (ℓ-max ℓC ℓC') (ℓ-max ℓD ℓD'))
  preservesInitial = ∀ (x : ob C) → isInitial C x → isInitial D (F-ob F x)

  isLeftAdjoint→preservesInitial : isLeftAdjoint F → preservesInitial
  fst (isLeftAdjoint→preservesInitial (G , F⊣G) x initX y) = _♯ F⊣G (fst (initX (F-ob G y)))
  snd (isLeftAdjoint→preservesInitial (G , F⊣G) x initX y) ψ =
    _♯ F⊣G (fst (initX (F-ob G y)))
      ≡⟨ cong (F⊣G ♯) (snd (initX (F-ob G y)) (_♭ F⊣G ψ)) ⟩
    _♯ F⊣G (_♭ F⊣G ψ)
      ≡⟨ leftInv (adjIso F⊣G) ψ ⟩
    ψ ∎
