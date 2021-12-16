{-# OPTIONS --safe #-}
module Cubical.Categories.Instances.CommRings where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function

open import Cubical.Data.Unit

open import Cubical.Algebra.Ring
open import Cubical.Algebra.CommRing

open import Cubical.Categories.Category
open import Cubical.Categories.Limits.Terminal

open Category
open CommRingHoms

private
  variable
    ℓ : Level

CommRingsCategory : Category (ℓ-suc ℓ) ℓ
ob CommRingsCategory                     = CommRing _
Hom[_,_] CommRingsCategory               = CommRingHom
id CommRingsCategory {R}                 = idCommRingHom R
_⋆_ CommRingsCategory {R} {S} {T}        = compCommRingHom R S T
⋆IdL CommRingsCategory {R} {S}           = compIdCommRingHom {R = R} {S}
⋆IdR CommRingsCategory {R} {S}           = idCompCommRingHom {R = R} {S}
⋆Assoc CommRingsCategory {R} {S} {T} {U} = compAssocCommRingHom {R = R} {S} {T} {U}
isSetHom CommRingsCategory               = isSetRingHom _ _

trivialRing : CommRing ℓ-zero
fst trivialRing = Unit
CommRingStr.0r (snd trivialRing) = tt
CommRingStr.1r (snd trivialRing) = tt
CommRingStr._+_ (snd trivialRing) = λ _ _ → tt
CommRingStr._·_ (snd trivialRing) = λ _ _ → tt
CommRingStr.- snd trivialRing = λ _ → tt
CommRingStr.isCommRing (snd trivialRing) = makeIsCommRing isSetUnit (λ _ _ _ → refl) (λ { tt → refl }) (λ _ → refl) (λ _ _ → refl) (λ _ _ _ → refl) (λ { tt → refl }) (λ _ _ _ → refl) (λ _ _ → refl)

TerminalCommRing : Terminal {ℓ-suc ℓ-zero} CommRingsCategory
fst TerminalCommRing = trivialRing
snd TerminalCommRing y = ((λ _ → tt) , (makeIsRingHom refl (λ _ _ → refl) (λ _ _ → refl))) , (λ f → RingHom≡ (funExt (λ _ → refl)))
