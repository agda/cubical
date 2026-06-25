module Cubical.Categories.Instances.TotalCategory.Base where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism

open import Cubical.Data.Sigma
open import Cubical.Reflection.StrictEquiv

open import Cubical.Categories.Category.Base
open import Cubical.Categories.Functor.Base
open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Displayed.Functor

private
  variable
    ℓC ℓC' ℓD ℓD' ℓE ℓE' ℓCᴰ ℓCᴰ' ℓDᴰ ℓDᴰ' ℓEᴰ ℓEᴰ' : Level

-- Total category of a displayed category
module _ {C : Category ℓC ℓC'} (Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ') where

  open Category
  open Categoryᴰ Cᴰ
  private
    module C = Category C

  ∫C : Category (ℓ-max ℓC ℓCᴰ) (ℓ-max ℓC' ℓCᴰ')
  ∫C .ob = Σ _ ob[_]
  ∫C .Hom[_,_] (_ , xᴰ) (_ , yᴰ) = Σ _ Hom[_][ xᴰ , yᴰ ]
  ∫C .id = _ , idᴰ
  ∫C ._⋆_ (_ , fᴰ) (_ , gᴰ) = _ , fᴰ ⋆ᴰ gᴰ
  ∫C .⋆IdL _ = ΣPathP (_ , ⋆IdLᴰ _)
  ∫C .⋆IdR _ = ΣPathP (_ , ⋆IdRᴰ _)
  ∫C .⋆Assoc _ _ _ = ΣPathP (_ , ⋆Assocᴰ _ _ _)
  ∫C .isSetHom = isSetΣ C.isSetHom (λ _ → isSetHomᴰ)


  ∫CatIso : ∀ {x y}{xᴰ yᴰ}
    (f : CatIso C x y) (fᴰ : CatIsoᴰ Cᴰ f xᴰ yᴰ)
    → CatIso ∫C (x , xᴰ) (y , yᴰ)
  ∫CatIso f fᴰ .fst = f .fst , fᴰ .fst
  ∫CatIso f fᴰ .snd .isIso.inv = f .snd .isIso.inv , fᴰ .snd .isIsoᴰ.invᴰ
  ∫CatIso f fᴰ .snd .isIso.sec = ΣPathP (f .snd .isIso.sec , fᴰ .snd .isIsoᴰ.secᴰ)
  ∫CatIso f fᴰ .snd .isIso.ret = ΣPathP (f .snd .isIso.ret , fᴰ .snd .isIsoᴰ.retᴰ)

  ∫CatIso⁻ : ∀ {x y}{xᴰ yᴰ}
    → CatIso ∫C (x , xᴰ) (y , yᴰ)
    → Σ[ f ∈ CatIso C x y ] CatIsoᴰ Cᴰ f xᴰ yᴰ
  ∫CatIso⁻ ∫f .fst .fst = ∫f .fst .fst
  ∫CatIso⁻ ∫f .fst .snd .isIso.inv = ∫f .snd .isIso.inv .fst
  ∫CatIso⁻ ∫f .fst .snd .isIso.sec = PathPΣ (∫f .snd .isIso.sec) .fst
  ∫CatIso⁻ ∫f .fst .snd .isIso.ret = PathPΣ (∫f .snd .isIso.ret) .fst
  ∫CatIso⁻ ∫f .snd .fst = ∫f .fst .snd
  ∫CatIso⁻ ∫f .snd .snd .isIsoᴰ.invᴰ = ∫f .snd .isIso.inv .snd
  ∫CatIso⁻ ∫f .snd .snd .isIsoᴰ.secᴰ = PathPΣ (∫f .snd .isIso.sec) .snd
  ∫CatIso⁻ ∫f .snd .snd .isIsoᴰ.retᴰ = PathPΣ (∫f .snd .isIso.ret) .snd

  ∫CatIso-Iso : ∀ {x y}{xᴰ yᴰ}
    → Iso (Σ[ f ∈ CatIso C x y ] CatIsoᴰ Cᴰ f xᴰ yᴰ)
          (CatIso ∫C (x , xᴰ) (y , yᴰ))
  ∫CatIso-Iso .Iso.fun = uncurry ∫CatIso
  ∫CatIso-Iso .Iso.inv = ∫CatIso⁻
  ∫CatIso-Iso .Iso.sec = λ _ → refl
  ∫CatIso-Iso .Iso.ret = λ _ → refl

  module _ {x y}{xᴰ}{yᴰ} where
    unquoteDecl ∫CatIso-Equiv = declStrictIsoToEquiv ∫CatIso-Equiv (∫CatIso-Iso {x = x}{y = y}{xᴰ = xᴰ}{yᴰ = yᴰ})

  isUnivalent∫C : isUnivalent C → isUnivalentᴰ Cᴰ → isUnivalent ∫C
  isUnivalent∫C univC univCᴰ .isUnivalent.univ (x , xᴰ) (y , yᴰ) =
    subst isEquiv fix-up (equiv∫ .snd) where
    equivΣ : (Σ[ p ∈ x ≡ y ] (PathP (λ i → ob[ p i ]) xᴰ yᴰ))
           ≃ (Σ[ f ∈ CatIso C x y ] (CatIsoᴰ Cᴰ f xᴰ yᴰ))
    equivΣ = Σ-cong-equiv
      (pathToIso , univC .isUnivalent.univ x y)
      (λ p → pathToIsoᴰ Cᴰ p , univCᴰ x y xᴰ yᴰ p)

    equiv∫ : ((x , xᴰ) ≡ (y , yᴰ)) ≃ CatIso ∫C (x , xᴰ) (y , yᴰ)
    equiv∫ = compEquiv (invEquiv ΣPath≃PathΣ)
      (compEquiv equivΣ ∫CatIso-Equiv)

    -- Is it possible to define equiv∫ compositionally in a way
    -- that makes this refl on proofs?
    fix-up : equiv∫ .fst ≡ pathToIso
    fix-up = funExt (λ xxᴰ≡yyᴰ →
      CatIso≡ (equiv∫ .fst xxᴰ≡yyᴰ) (pathToIso xxᴰ≡yyᴰ) refl)

-- Total functor of a displayed functor
module _ {C : Category ℓC ℓC'} {D : Category ℓD ℓD'}
  {F : Functor C D} {Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ'} {Dᴰ : Categoryᴰ D ℓDᴰ ℓDᴰ'}
  (Fᴰ : Functorᴰ F Cᴰ Dᴰ)
  where

  open Functor
  private
    module Fᴰ = Functorᴰ Fᴰ

  ∫F : Functor (∫C Cᴰ) (∫C Dᴰ)
  ∫F .F-ob (x , xᴰ) = _ , Fᴰ.F-obᴰ xᴰ
  ∫F .F-hom (_ , fᴰ) = _ , Fᴰ.F-homᴰ fᴰ
  ∫F .F-id = ΣPathP (_ , Fᴰ.F-idᴰ)
  ∫F .F-seq _ _ = ΣPathP (_ , (Fᴰ.F-seqᴰ _ _))
