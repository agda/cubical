{-# OPTIONS --safe #-}
module Cubical.Modalities.Instances.Identity where

open import Cubical.Modalities.Modality

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function

open import Cubical.Data.Unit


identityModality : {ℓ : Level} → Modality ℓ
Modality.isModal identityModality = const Unit*
Modality.isPropIsModal identityModality = isPropUnit*
Modality.◯ identityModality A = A
Modality.◯-isModal identityModality = tt*
Modality.η identityModality = idfun _
Modality.◯-elim identityModality _ f = f
Modality.◯-elim-β identityModality _ _ _ = refl
Modality.◯-=-isModal identityModality _ _  = tt*
