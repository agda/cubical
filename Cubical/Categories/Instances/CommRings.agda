{-# OPTIONS --safe #-}
module Cubical.Categories.Instances.CommRings where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function

open import Cubical.Algebra.Ring
open import Cubical.Algebra.CommRing

open import Cubical.Categories.Category

open Category
open CommRingHoms

CommRingsCategory : ∀ {ℓ} → Category (ℓ-suc ℓ) ℓ
ob CommRingsCategory                     = CommRing _
Hom[_,_] CommRingsCategory               = CommRingHom
id CommRingsCategory {R}                 = idCommRingHom R
_⋆_ CommRingsCategory {R} {S} {T}        = compCommRingHom R S T
⋆IdL CommRingsCategory {R} {S}           = compIdCommRingHom {R = R} {S}
⋆IdR CommRingsCategory {R} {S}           = idCompCommRingHom {R = R} {S}
⋆Assoc CommRingsCategory {R} {S} {T} {U} = compAssocCommRingHom {R = R} {S} {T} {U}
isSetHom CommRingsCategory               = isSetRingHom _ _
