{-# OPTIONS --safe #-}
module Cubical.Categories.Limits.Terminal where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.HITs.PropositionalTruncation.Base

open import Cubical.Data.Sigma

open import Cubical.Categories.Category

private
  variable
    ℓ ℓ' : Level

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

  open isUnivalent

  -- The type of terminal objects of a univalent category is a proposition,
  -- i.e. all terminal objects are equal.
  isPropTerminal : (hC : isUnivalent C) → isProp Terminal
  isPropTerminal hC x y =
    Σ≡Prop isPropIsTerminal (CatIsoToPath hC (terminalToIso x y))
