module Cubical.Categories.Displayed.Instances.TotalCategory where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels

open import Cubical.Data.Sigma
import      Cubical.Data.Equality as Eq

open import Cubical.Categories.Category.Base
open import Cubical.Categories.Functor
open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Displayed.Functor
open import Cubical.Categories.Displayed.HLevels
open import Cubical.Categories.Displayed.Section.Base
open import Cubical.Categories.Displayed.Instances.Terminal hiding (introF)
open import Cubical.Categories.Instances.TotalCategory as TC hiding (intro)

private
  variable
    ℓC ℓC' ℓD ℓD' ℓE ℓE' ℓCᴰ ℓCᴰ' ℓDᴰ ℓDᴰ' ℓEᴰ ℓEᴰ' : Level

-- Displayed total category, i.e. Σ for displayed categories
--
-- The ordinary total category (∫C Cᴰ) has as objects
-- pairs (x, xᴰ) where x is an object of C and xᴰ is an object of Cᴰ over x.
--
-- Whereas if we had a category Dᴰ displayed over (∫C Cᴰ),
-- and a category Cᴰ displayed over C, then the
-- displayed total category (∫Cᴰ Cᴰ Dᴰ) likewise has pairs
-- as displayed objects.
--
-- In the displayed total category, we have objects (xᴰ, yᴰ) displayed
-- over x, where x is an object of C, xᴰ an object in Cᴰ displayed over x,
-- and yᴰ is an object of Dᴰ over (x, xᴰ).
module _ {C : Category ℓC ℓC'}
  (Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ')
  (Dᴰ : Categoryᴰ (∫C Cᴰ) ℓDᴰ ℓDᴰ')
  where

  open Categoryᴰ
  private
    module Cᴰ = Categoryᴰ Cᴰ
    module Dᴰ = Categoryᴰ Dᴰ

  ∫Cᴰ : Categoryᴰ C (ℓ-max ℓCᴰ ℓDᴰ) (ℓ-max ℓCᴰ' ℓDᴰ')
  ∫Cᴰ .ob[_] x = Σ[ xᴰ ∈ Cᴰ.ob[ x ] ] Dᴰ.ob[ x , xᴰ ]
  ∫Cᴰ .Hom[_][_,_] f (_ , zᴰ) (_ , wᴰ) =
    Σ[ fᴰ ∈ Cᴰ.Hom[ f ][ _ , _ ] ] Dᴰ.Hom[ f , fᴰ ][ zᴰ , wᴰ ]
  ∫Cᴰ .idᴰ = Cᴰ.idᴰ , Dᴰ.idᴰ
  ∫Cᴰ ._⋆ᴰ_ (_ , hᴰ) (_ , kᴰ) = _ , hᴰ Dᴰ.⋆ᴰ kᴰ
  ∫Cᴰ .⋆IdLᴰ _ = ΣPathP (_ , Dᴰ.⋆IdLᴰ _)
  ∫Cᴰ .⋆IdRᴰ _ = ΣPathP (_ , Dᴰ.⋆IdRᴰ _)
  ∫Cᴰ .⋆Assocᴰ _ _ _ = ΣPathP (_ , Dᴰ.⋆Assocᴰ _ _ _)
  ∫Cᴰ .isSetHomᴰ = isSetΣ Cᴰ.isSetHomᴰ (λ _ → Dᴰ.isSetHomᴰ)

-- Projection out of the displayed total category
module _ {C : Category ℓC ℓC'}
  {Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ'}
  (Dᴰ : Categoryᴰ (∫C Cᴰ) ℓDᴰ ℓDᴰ')
  where

  hasPropHoms∫Cᴰ : hasPropHoms Cᴰ → hasPropHoms Dᴰ → hasPropHoms (∫Cᴰ Cᴰ Dᴰ)
  hasPropHoms∫Cᴰ ph-Cᴰ ph-Dᴰ f cᴰ cᴰ' = isPropΣ
    (ph-Cᴰ f (cᴰ .fst) (cᴰ' .fst))
    (λ fᴰ → ph-Dᴰ (f , fᴰ) (cᴰ .snd) (cᴰ' .snd))

  private
    module Cᴰ = Categoryᴰ Cᴰ
    module Dᴰ = Categoryᴰ Dᴰ
    ∫∫Cᴰ = ∫C {C = C} (∫Cᴰ Cᴰ Dᴰ)
  open Functor
  open Functorᴰ

  Assocᴰ : Functor ∫∫Cᴰ (∫C Dᴰ)
  Assocᴰ .F-ob  x   = (x .fst , x .snd .fst) , x .snd .snd
  Assocᴰ .F-hom f   = (f .fst , f .snd .fst) , f .snd .snd
  Assocᴰ .F-id      = refl
  Assocᴰ .F-seq _ _ = refl

  Assocᴰ⁻ : Functor (∫C Dᴰ) ∫∫Cᴰ
  Assocᴰ⁻ .F-ob  x   = x .fst .fst , x .fst .snd , x .snd
  Assocᴰ⁻ .F-hom f   = f .fst .fst , f .fst .snd , f .snd
  Assocᴰ⁻ .F-id      = refl
  Assocᴰ⁻ .F-seq _ _ = refl

  Fstᴰ : Functorᴰ Id (∫Cᴰ Cᴰ Dᴰ) Cᴰ
  Fstᴰ .F-obᴰ = fst
  Fstᴰ .F-homᴰ = fst
  Fstᴰ .F-idᴰ = refl
  Fstᴰ .F-seqᴰ _ _ = refl

  open Section
  module _ {Eᴰ : Categoryᴰ ∫∫Cᴰ ℓEᴰ ℓEᴰ'} where
    elimGlobal : Section Assocᴰ⁻ Eᴰ → GlobalSection Eᴰ
    elimGlobal s .F-obᴰ d = s .F-obᴰ ((d .fst , d .snd .fst) , d .snd .snd)
    elimGlobal s .F-homᴰ f =  s .F-homᴰ ((f .fst , f .snd .fst) , f .snd .snd)
    elimGlobal s .F-idᴰ = s .F-idᴰ
    elimGlobal s .F-seqᴰ _ _ = s .F-seqᴰ _ _

  module _ {E : Category ℓE ℓE'} (F : Functor E C)
           (Fᴰ : Section F Cᴰ)
           (Gᴰ : Section (TC.intro F Fᴰ) Dᴰ)
           where
    introS : Section F (∫Cᴰ Cᴰ Dᴰ)
    introS .F-obᴰ  d   = Fᴰ .F-obᴰ d , Gᴰ .F-obᴰ d
    introS .F-homᴰ f   = Fᴰ .F-homᴰ f , Gᴰ .F-homᴰ f
    introS .F-idᴰ      = ΣPathP (Fᴰ .F-idᴰ , Gᴰ .F-idᴰ)
    introS .F-seqᴰ f g = ΣPathP (Fᴰ .F-seqᴰ f g , Gᴰ .F-seqᴰ f g)

  module _ {E : Category ℓE ℓE'} {Eᴰ : Categoryᴰ E ℓEᴰ ℓEᴰ'} (F : Functor E C)
           (Fᴰ : Functorᴰ F Eᴰ Cᴰ)
           (Gᴰ : Section (∫F Fᴰ) Dᴰ)
           where
    introF : Functorᴰ F Eᴰ (∫Cᴰ Cᴰ Dᴰ)
    introF = TC.recᴰ _ _ (introS _ (elim Fᴰ)
      (reindS' (Eq.refl , Eq.refl) Gᴰ))
