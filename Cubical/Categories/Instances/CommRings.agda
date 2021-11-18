{-# OPTIONS --safe #-}
module Cubical.Categories.Instances.CommRings where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function

open import Cubical.Algebra.CommRing

open import Cubical.Categories.Category

open Precategory
open CommRingHoms

CommRingsPrecategory : ∀ {ℓ} → Precategory (ℓ-suc ℓ) ℓ
ob CommRingsPrecategory                     = CommRing _
Hom[_,_] CommRingsPrecategory               = CommRingHom
id CommRingsPrecategory                     = idCommRingHom
_⋆_ CommRingsPrecategory {R} {S} {T}        = compCommRingHom R S T
⋆IdL CommRingsPrecategory {R} {S}           = compIdCommRingHom {R = R} {S}
⋆IdR CommRingsPrecategory {R} {S}           = idCompCommRingHom {R = R} {S}
⋆Assoc CommRingsPrecategory {R} {S} {T} {U} = compAssocCommRingHom {R = R} {S} {T} {U}
