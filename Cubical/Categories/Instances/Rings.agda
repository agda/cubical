{-# OPTIONS --safe #-}
module Cubical.Categories.Instances.Rings where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function

open import Cubical.Algebra.Ring

open import Cubical.Categories.Category

open Precategory
open RingHoms

RingsPrecategory : ∀ {ℓ} → Precategory (ℓ-suc ℓ) ℓ
ob RingsPrecategory       = Ring _
Hom[_,_] RingsPrecategory = RingHom
id RingsPrecategory       = idRingHom
_⋆_ RingsPrecategory      = compRingHom
⋆IdL RingsPrecategory     = compIdRingHom
⋆IdR RingsPrecategory     = idCompRingHom
⋆Assoc RingsPrecategory   = compAssocRingHom
