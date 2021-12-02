{-# OPTIONS --safe #-}
module Cubical.Categories.Instances.Rings where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function

open import Cubical.Algebra.Ring

open import Cubical.Categories.Category

open Category
open RingHoms

RingsCategory : ∀ {ℓ} → Category (ℓ-suc ℓ) ℓ
ob RingsCategory       = Ring _
Hom[_,_] RingsCategory = RingHom
id RingsCategory {R}   = idRingHom R
_⋆_ RingsCategory      = compRingHom
⋆IdL RingsCategory     = compIdRingHom
⋆IdR RingsCategory     = idCompRingHom
⋆Assoc RingsCategory   = compAssocRingHom
isSetHom RingsCategory = isSetRingHom _ _
