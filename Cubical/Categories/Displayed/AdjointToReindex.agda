{-# OPTIONS --safe #-}
--
module Cubical.Categories.Displayed.AdjointToReindex where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Path
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Data.Sigma

open import Cubical.Categories.Category.Base
open import Cubical.Categories.Category.Properties
open import Cubical.Categories.Instances.Terminal
open import Cubical.Categories.Constructions.BinProduct
  renaming (Fst to FstBP ; Snd to SndBP)
open import Cubical.Categories.Functor

open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Displayed.Properties
open import Cubical.Categories.Displayed.Functor
open import Cubical.Categories.Displayed.Instances.Terminal

private
  variable
    ℓC ℓC' ℓCᴰ ℓCᴰ' ℓD ℓD' ℓDᴰ ℓDᴰ' ℓE ℓE' ℓEᴰ ℓEᴰ' : Level

open Categoryᴰ

module _
  {C : Category ℓC ℓC'} {D : Category ℓD ℓD'}
  (Cᴰ : Categoryᴰ C ℓDᴰ ℓDᴰ') (F : Functor C D)
  where

  open Category
  open Functor F
  private
    module Cᴰ = Categoryᴰ Cᴰ
    open Iso

    hom-path : ∀ {A B A' B'} (p : A ≡ A') (q : B ≡ B') →
      (D [ A , B ]) ≡ (D [ A' , B' ])
    hom-path p q = cong₂ (λ a b → D [ a , b ]) p q

    hom-pathP : ∀ {A B A' B'} (p : A ≡ A') (q : B ≡ B') →
                (f : D [ A , B ]) → (f' : D [ A' , B' ]) →
                Type ℓD'
    hom-pathP p q f f' = PathP (λ i → hom-path p q i) f f'

    isPropHomP : ∀ {A B A' B'} (p : A ≡ A') (q : B ≡ B') →
                (f : D [ A , B ]) → (f' : D [ A' , B' ]) →
                isProp (hom-pathP p q f f')
    isPropHomP pdom pcod f f'' x y =
      isoFunInjective (PathPIsoPath _ _ _) x y fromPathPeq
      where
      fromPathPeq : fromPathP x ≡ fromPathP y
      fromPathPeq = D .isSetHom _ _ (fromPathP x) (fromPathP y)

  ∃F : Categoryᴰ D (ℓ-max (ℓ-max ℓC ℓD) ℓDᴰ) (ℓ-max (ℓ-max ℓC' ℓD') ℓDᴰ')
  ∃F .ob[_] d = Σ[ c ∈ C .ob ] (F-ob c ≡ d) × Cᴰ.ob[ c ]
  ∃F .Hom[_][_,_] f (c , p , x) (c' , p' , x') =
    Σ[ g ∈ C [ c , c' ] ] hom-pathP p p' (F-hom g) f × Cᴰ.Hom[ g ][ x , x' ]
  ∃F .idᴰ {d} {c , p , x} =
    (C .id) ,
    (F-id ◁ (cong (λ v → D .id {v}) p)) ,
    Cᴰ .idᴰ
  ∃F ._⋆ᴰ_ (g , p , gᴰ) (h , q , hᴰ) =
      g ⋆⟨ C ⟩ h ,
      F-seq g h ◁ (λ i → p i ⋆⟨ D ⟩ q i) ,
      (Cᴰ._⋆ᴰ_ gᴰ hᴰ)
  ⋆IdLᴰ ∃F {d}{d'}{g}{c , pc , xc}{c' , pc' , xc'} (f , p , x) =
    λ i →
      C .⋆IdL f i ,
      isProp→PathP
        (λ i → isPropHomP pc pc' (F-hom (C .⋆IdL f i)) (D .⋆IdL g i))
        ((F-seq (C .id {c}) f ◁
          (λ i₁ → seq' D ((F-id {c} ◁ (λ i₂ → D .id {pc i₂})) i₁) (p i₁))))
        p i ,
      Cᴰ .⋆IdLᴰ x i
  ⋆IdRᴰ ∃F {d}{d'}{g}{c , pc , xc}{c' , pc' , xc'} (f , p , x) =
    λ i →
      C .⋆IdR f i ,
      isProp→PathP
        (λ i → isPropHomP pc pc' (F-hom (C .⋆IdR f i)) (D .⋆IdR g i))
        (F-seq f (C .id {c'}) ◁
          (λ i₁ → seq' D (p i₁) ((F-id {c' }◁ (λ i₂ → D .id {pc' i₂})) i₁)))
        p i ,
      Cᴰ .⋆IdRᴰ x i
  ⋆Assocᴰ ∃F {xᴰ = xᴰ}{yᴰ = yᴰ}{zᴰ = zᴰ}{wᴰ = wᴰ}
    (f , pf , fᴰ)
    (g , pg , gᴰ)
    (h , ph , hᴰ) =
    λ i →
      C .⋆Assoc f g h i ,
      isProp→PathP
        (λ j → isPropHomP
          (xᴰ .snd .fst) (wᴰ .snd .fst)
          (F-hom (C .⋆Assoc f g h j)) (D .⋆Assoc _ _ _ j))
        (F-seq (seq' C f g) h ◁
          (λ i₁ → seq' D
            ((F-seq f g ◁ (λ i₂ → seq' D (pf i₂) (pg i₂))) i₁) (ph i₁)))
        (F-seq f (seq' C g h) ◁
          (λ i₁ → seq' D
          (pf i₁) ((F-seq g h ◁ (λ i₂ → seq' D (pg i₂) (ph i₂))) i₁)))
        i ,
      Cᴰ .⋆Assocᴰ fᴰ gᴰ hᴰ i
  isSetHomᴰ ∃F {d}{d'}{f}{u}{v} =
    isSetΣ (C .isSetHom)
      λ g → isSet×
        (isProp→isSet (isPropHomP _ _ _ _))
        (Cᴰ .isSetHomᴰ)

-- Examples of ∃F instantiated
private
  module _ where
    module ∃FDisplayOverProjections
      {C : Category ℓC ℓC'} {D : Category ℓD ℓD'}
      (Cᴰ : Categoryᴰ (C ×C D) ℓCᴰ ℓCᴰ')
      where

      open Category
      open Categoryᴰ

      ∫Cᴰsr' : Categoryᴰ C (ℓ-max (ℓ-max (ℓ-max ℓC ℓD) ℓC) ℓCᴰ)
                        (ℓ-max (ℓ-max (ℓ-max ℓC' ℓD') ℓC') ℓCᴰ')
      ∫Cᴰsr' = ∃F Cᴰ (FstBP C D)

      ∫Cᴰsl' : Categoryᴰ D (ℓ-max (ℓ-max (ℓ-max ℓC ℓD) ℓD) ℓCᴰ)
                        (ℓ-max (ℓ-max (ℓ-max ℓC' ℓD') ℓD') ℓCᴰ')
      ∫Cᴰsl' = ∃F Cᴰ (SndBP C D)

      private
        module Cᴰ = Categoryᴰ Cᴰ
        module ∫Cᴰsr' = Categoryᴰ ∫Cᴰsr'

      -- This is equivalent to the definition of objects
      -- ∫Cᴰsr given previously
      obj :
        (c : C .ob) →
        (d : D .ob) →
        (xᴰ : Cᴰ.ob[ c , d ]) →
        ∫Cᴰsr'.ob[ c ]
      obj c d xᴰ = (c , d) , refl , xᴰ

    -- Can equivalently define the displayed total category
    -- via ∃F
    module ∃FDisplayedTotalCategory
      {C : Category ℓC ℓC'}
      {ℓ : Level}
      (F : Functor C (TerminalCategory {ℓ}))
      (Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ')
      (Dᴰ : Categoryᴰ (∫C Cᴰ) ℓDᴰ ℓDᴰ')
      where
      ∫Cᴰ' : Categoryᴰ C
        (ℓ-max (ℓ-max (ℓ-max ℓC ℓCᴰ) ℓC) ℓDᴰ)
        (ℓ-max (ℓ-max (ℓ-max ℓC' ℓCᴰ') ℓC') ℓDᴰ')
      ∫Cᴰ' = ∃F Dᴰ (Fst {C = C} {Cᴰ = Cᴰ})

      open Category
      private
        module Cᴰ = Categoryᴰ Cᴰ
        module Dᴰ = Categoryᴰ Dᴰ
        module ∫Cᴰ' = Categoryᴰ ∫Cᴰ'

      -- Same crieria as used to build an object in ∫Cᴰ
      -- Note that the refl path here is trivial
      -- becaue it is a proof that
      -- (c , xᴰ) has a fst projection equal to c
      obj :
        (c : C .ob) →
        (xᴰ : Cᴰ.ob[ c ]) →
        (yᴰ : Dᴰ.ob[ c , xᴰ ]) →
        ∫Cᴰ'.ob[ c ]
      obj c xᴰ yᴰ = (c , xᴰ) , refl , yᴰ
