{-# OPTIONS --safe #-}
module Cubical.Categories.Limits.Terminal where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.HITs.PropositionalTruncation.Base
open import Cubical.Data.Sigma

open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.Isomorphism

private
  variable
    ℓ ℓ' ℓc ℓc' ℓd ℓd' : Level

module _ (C : Category ℓ ℓ') where
  open Category C

  isTerminal : (x : ob) → Type (ℓ-max ℓ ℓ')
  isTerminal x = ∀ (y : ob) → isContr (C [ y , x ])

  Terminal : Type (ℓ-max ℓ ℓ')
  Terminal = Σ[ x ∈ ob ] isTerminal x

  terminalOb : Terminal → ob
  terminalOb = fst

  terminalArrow : (T : Terminal) (y : ob) → C [ y , terminalOb T ]
  terminalArrow T y = T .snd y .fst

  terminalArrowUnique : {T : Terminal} {y : ob} (f : C [ y , terminalOb T ])
                      → terminalArrow T y ≡ f
  terminalArrowUnique {T} {y} f = T .snd y .snd f

  terminalEndoIsId : (T : Terminal) (f : C [ terminalOb T , terminalOb T ])
                   → f ≡ id
  terminalEndoIsId T f = isContr→isProp (T .snd (terminalOb T)) f id

  hasTerminal : Type (ℓ-max ℓ ℓ')
  hasTerminal = ∥ Terminal ∥₁

  -- Terminality of an object is a proposition.
  isPropIsTerminal : (x : ob) → isProp (isTerminal x)
  isPropIsTerminal _ = isPropΠ λ _ → isPropIsContr

  open isIso

  -- Objects that are initial are isomorphic.
  terminalToIso : (x y : Terminal) → CatIso C (terminalOb x) (terminalOb y)
  terminalToIso x y .fst = terminalArrow y (terminalOb x)
  terminalToIso x y .snd .inv = terminalArrow x (terminalOb y)
  terminalToIso x y .snd .sec = terminalEndoIsId y _
  terminalToIso x y .snd .ret = terminalEndoIsId x _

  isoToTerminal : ∀ (x : Terminal) y → CatIso C (terminalOb x) y → isTerminal y
  isoToTerminal x y x≅y y' .fst = x≅y .fst ∘⟨ C ⟩ terminalArrow x y'
  isoToTerminal x y x≅y y' .snd f =
    sym (⋆InvRMove
          (invIso x≅y)
          (sym (terminalArrowUnique {T = x} (invIso x≅y .fst ∘⟨ C ⟩ f))))

  open isUnivalent

  -- The type of terminal objects of a univalent category is a proposition,
  -- i.e. all terminal objects are equal.
  isPropTerminal : (hC : isUnivalent C) → isProp Terminal
  isPropTerminal hC x y =
    Σ≡Prop isPropIsTerminal (CatIsoToPath hC (terminalToIso x y))

preservesTerminal : ∀ (C : Category ℓc ℓc')(D : Category ℓd ℓd')
                  → Functor C D
                  → Type (ℓ-max (ℓ-max (ℓ-max ℓc ℓc') ℓd) ℓd')
preservesTerminal C D F = ∀ (One : Terminal C) → isTerminal D (F ⟅ One .fst ⟆)

preserveOnePreservesAll : ∀ (C : Category ℓc ℓc')(D : Category ℓd ℓd')
                        → (F : Functor C D)
                        → (One : Terminal C) → isTerminal D (F ⟅ One .fst ⟆)
                        → preservesTerminal C D F
preserveOnePreservesAll C D F One D-preserves-One One' =
  isoToTerminal D
                ((F ⟅ One .fst ⟆) , D-preserves-One) (F ⟅ One' .fst ⟆)
                (F-Iso {F = F} (terminalToIso C One One'))
