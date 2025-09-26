{-# OPTIONS --safe #-}

module Cubical.Categories.Instances.Propositions where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Function

open import Cubical.Categories.Category
open Category
open import Cubical.Categories.Thin

private
  variable
    ℓ : Level

PROP : ∀ (ℓ : Level) → Category (ℓ-suc ℓ) ℓ
ob (PROP ℓ) = hProp ℓ
Hom[_,_] (PROP ℓ) (P , _) (Q , _) = P → Q
id (PROP ℓ) = idfun _
_⋆_ (PROP ℓ) f g x = g (f x)
⋆IdL (PROP ℓ) {P , _} {Q , propQ} f = isProp→ propQ _ _
⋆IdR (PROP ℓ) {P , _} {Q , propQ} f = isProp→ propQ _ _
⋆Assoc (PROP ℓ) {P , _} {Q , _} {R , _} {S , propS} f g h = isPropΠ (λ _ → propS) _ _
isSetHom (PROP ℓ) {P , _} {Q , propQ} = isProp→isSet (isProp→ propQ)

isThinPROP : isThin (PROP ℓ)
isThinPROP (P , propP) (Q , propQ) = isProp→ propQ
