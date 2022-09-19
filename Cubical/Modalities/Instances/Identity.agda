{-# OPTIONS --safe #-}
module Cubical.Modalities.Instances.Identity where

open import Cubical.Modalities.Modality

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function

open import Cubical.Data.Unit


open Modality

identityModality : {ℓ : Level} → Modality ℓ
isModal identityModality = const Unit*
isPropIsModal identityModality = isPropUnit*
◯ identityModality A = A
◯-isModal identityModality = tt*
η identityModality = idfun _
◯-elim identityModality _ f = f
◯-elim-β identityModality _ _ _ = refl
◯-=-isModal identityModality _ _  = tt*
