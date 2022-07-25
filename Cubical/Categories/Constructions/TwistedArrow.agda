
{-# OPTIONS --safe #-}

module Cubical.Categories.Constructions.TwistedArrow where

open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function

open import Cubical.Data.Sigma

open import Cubical.Categories.Category.Base
open import Cubical.Categories.Functor.Base
open import Cubical.Categories.Constructions.BinProduct renaming (_×_ to _×C_)

open Category hiding (_∘_)
open Functor

private
  variable
    ℓ ℓ' : Level

TwistedArrowCategory : (C : Category ℓ ℓ') → Category (ℓ-max ℓ ℓ') ℓ'
ob (TwistedArrowCategory C) = Σ[ x ∈ ob C ] Σ[ y ∈ ob C ] C [ x , y ]
Hom[_,_] (TwistedArrowCategory C) (x , y , φ) (x' , y' , φ') = (C [ x' , x ]) × (C [ y , y' ])
id (TwistedArrowCategory C) {x , y , φ} = id C , id C
_⋆_ (TwistedArrowCategory C) (ξ , υ) (ξ' , υ') = (ξ' ⋆⟨ C ⟩ ξ) , υ ⋆⟨ C ⟩ υ'
⋆IdL (TwistedArrowCategory C) (ξ , υ) = cong₂ _,_ (⋆IdR C ξ) (⋆IdL C υ)
⋆IdR (TwistedArrowCategory C) (ξ , υ) = cong₂ _,_ (⋆IdL C ξ) (⋆IdR C υ)
⋆Assoc (TwistedArrowCategory C) (ξ , υ) (ξ' , υ') (ξ'' , υ'') =
  cong₂ _,_ (sym (⋆Assoc C ξ'' ξ' ξ)) (⋆Assoc C υ υ' υ'')
isSetHom (TwistedArrowCategory C) = isSet× (isSetHom C) (isSetHom C)

TwistedDom : (C : Category ℓ ℓ') → Functor (TwistedArrowCategory (C ^op)) C
F-ob (TwistedDom C) = fst
F-hom (TwistedDom C) = fst
F-id (TwistedDom C) = refl
F-seq (TwistedDom C) (ξ , υ) (ξ' , υ') = refl

TwistedCod : (C : Category ℓ ℓ') → Functor (TwistedArrowCategory C) C
F-ob (TwistedCod C) = fst ∘ snd
F-hom (TwistedCod C) = snd
F-id (TwistedCod C) = refl
F-seq (TwistedCod C) (ξ , υ) (ξ' , υ') = refl

TwistedEnds : (C : Category ℓ ℓ') → Functor (TwistedArrowCategory C) (C ^op ×C C)
TwistedEnds C = {!!}
