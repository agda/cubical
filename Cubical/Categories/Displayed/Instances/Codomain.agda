{-# OPTIONS --safe #-}

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels

open import Cubical.Data.Sigma

open import Cubical.Categories.Category
open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Displayed.Cartesian

module Cubical.Categories.Displayed.Instances.Codomain
  {ℓC ℓ'C : Level}
  (C : Category ℓC ℓ'C)
  where

private
  module C = Category C

module _ where
  open Categoryᴰ

  codomainᴰ : Categoryᴰ C (ℓ-max ℓC ℓ'C) ℓ'C
  codomainᴰ .ob[_] c = Σ[ d ∈ C.ob ] C.Hom[ d , c ]
  codomainᴰ .Hom[_][_,_] f (d , g) (e , h) = Σ[ fᴰ ∈ C.Hom[ d , e ] ] fᴰ C.⋆ h ≡ g C.⋆ f
  codomainᴰ .idᴰ = (C.id , C.⋆IdL _ ∙ sym (C.⋆IdR _))
  codomainᴰ ._⋆ᴰ_ (fᴰ , fᴰ-comm) (gᴰ , gᴰ-comm) =
      fᴰ C.⋆ gᴰ
    , C.⋆Assoc _ _ _
    ∙ cong (fᴰ C.⋆_) gᴰ-comm
    ∙ sym (C.⋆Assoc _ _ _)
    ∙ cong (C._⋆ _) fᴰ-comm
    ∙ C.⋆Assoc _ _ _
  codomainᴰ .⋆IdLᴰ (fᴰ , _) = ΣPathPProp (λ _ → C.isSetHom _ _) (C.⋆IdL fᴰ)
  codomainᴰ .⋆IdRᴰ (fᴰ , _) = ΣPathPProp (λ _ → C.isSetHom _ _) (C.⋆IdR fᴰ)
  codomainᴰ .⋆Assocᴰ (fᴰ , _) (gᴰ , _) (hᴰ , _) =
    ΣPathPProp (λ _ → C.isSetHom _ _) (C.⋆Assoc fᴰ gᴰ hᴰ)
  codomainᴰ .isSetHomᴰ = isSetΣSndProp C.isSetHom (λ _ → C.isSetHom _ _)

  open Covariant

  codomainOpcleavage : Opcleavage codomainᴰ
  codomainOpcleavage f (dᴰ , dᴰ→d) .fst = dᴰ , dᴰ→d C.⋆ f
  codomainOpcleavage _ _ .snd .fst = C.id , C.⋆IdL _
  codomainOpcleavage _ _ .snd .snd _ .equiv-proof (gᴰ , gᴰ-commutes) .fst =
      (gᴰ , gᴰ-commutes ∙ sym (C.⋆Assoc _ _ _))
    , Σ≡Prop (λ _ → C.isSetHom _ _) (C.⋆IdL _)
  codomainOpcleavage _ _ .snd .snd _ .equiv-proof _ .snd (_ , infib) =
    Σ≡Prop (λ _ → isSetΣSndProp C.isSetHom (λ _ → C.isSetHom _ _) _ _) $
      Σ≡Prop (λ _ → C.isSetHom _ _) $
        sym (cong fst infib) ∙ C.⋆IdL _
