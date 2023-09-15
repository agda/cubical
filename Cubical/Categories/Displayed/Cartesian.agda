{-# OPTIONS --safe #-}

open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Prelude

open import Cubical.Data.Sigma

open import Cubical.HITs.PropositionalTruncation as PT

open import Cubical.Categories.Category
open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Displayed.Properties
import      Cubical.Categories.Displayed.Reasoning as HomᴰReasoning
open import Cubical.Categories.Functor
open import Cubical.Categories.Instances.Sets
open import Cubical.Categories.NaturalTransformation

module Cubical.Categories.Displayed.Cartesian where

module Covariant
  {ℓB ℓ'B ℓC ℓ'C : Level}
  {B : Category ℓB ℓ'B}
  (Cᴰ : Categoryᴰ B ℓC ℓ'C)
  where

  private
    module B = Category B
    module Cᴰ = Categoryᴰ Cᴰ
    module R = HomᴰReasoning Cᴰ

  open Cᴰ

  isOpcartesian :
      {a b : B.ob} {f : B [ a , b ]}
      {aᴰ : ob[ a ]} {bᴰ : ob[ b ]}
      (fᴰ : Hom[ f ][ aᴰ , bᴰ ])
    → Type (ℓ-max (ℓ-max ℓB ℓ'B) (ℓ-max ℓC ℓ'C))
  isOpcartesian {b = b} {bᴰ = bᴰ} fᴰ =
    {c : B.ob} {cᴰ : ob[ c ]}
    (g : B [ b , c ]) → isEquiv (λ (gᴰ : Hom[ g ][ bᴰ , cᴰ ]) → fᴰ ⋆ᴰ gᴰ)

  isPropIsOpcartesian :
      {a b : B.ob} {f : B [ a , b ]}
      {aᴰ : ob[ a ]} {bᴰ : ob[ b ]}
      (fᴰ : Hom[ f ][ aᴰ , bᴰ ])
    → isProp (isOpcartesian fᴰ)
  isPropIsOpcartesian fᴰ = isPropImplicitΠ2 λ _ _ → isPropΠ λ _ → isPropIsEquiv _

  Opcleavage : Type (ℓ-max (ℓ-max ℓB ℓ'B) (ℓ-max ℓC ℓ'C))
  Opcleavage =
      {a b : B.ob} (f : B [ a , b ]) (aᴰ : ob[ a ])
    → Σ[ bᴰ ∈ ob[ b ] ]
      Σ[ fᴰ ∈ Hom[ f ][ aᴰ , bᴰ ] ]
      isOpcartesian fᴰ

  isOpfibration : Type (ℓ-max (ℓ-max ℓB ℓ'B) (ℓ-max ℓC ℓ'C))
  isOpfibration = PT.∥ Opcleavage ∥₁

  record isDiscreteOpfibration : Type (ℓ-max (ℓ-max ℓB ℓ'B) (ℓ-max ℓC ℓ'C)) where
    field
      isSet-fibers : (a : B.ob) → isSet ob[ a ]
      unique-lift : ({a b : B.ob} (f : B [ a , b ]) (aᴰ : ob[ a ])
                  → ∃![ bᴰ ∈ ob[ b ] ]
                    Hom[ f ][ aᴰ , bᴰ ])

  -- Discrete opfibrations
  module _ (isDiscOpfib : isDiscreteOpfibration) where
    open isDiscreteOpfibration isDiscOpfib

    -- Equality of displayed morphisms is trivial in a discrete opfibration.
    -- Rectify using isSet-fibers the dependent path on morphisms we get from
    -- unique-lift.
    Homᴰ≡-DiscreteOpfibration :
        {a b : B.ob} {f : B [ a , b ]}
        {aᴰ : ob[ a ]} {bᴰ : ob[ b ]}
      → isProp Hom[ f ][ aᴰ , bᴰ ]
    Homᴰ≡-DiscreteOpfibration {f = f} {aᴰ = aᴰ} {bᴰ = bᴰ} fᴰ f'ᴰ =
      subst (λ p → PathP (λ i → Hom[ f ][ aᴰ , p i ]) fᴰ f'ᴰ) (isSet-fibers _ bᴰ bᴰ _ refl) $
        snd (PathPΣ (isContr→isProp (unique-lift f aᴰ) (bᴰ , fᴰ) (bᴰ , f'ᴰ)))

    -- Any displayed arrow is opcartesian.
    isOpcartesianDiscreteOpfibration :
        {a b : B.ob} {f : B [ a , b ]}
        {aᴰ : ob[ a ]} {bᴰ : ob[ b ]}
        (fᴰ : Hom[ f ][ aᴰ , bᴰ ])
      → isOpcartesian fᴰ
    isOpcartesianDiscreteOpfibration
      {f = f} {aᴰ = aᴰ} {bᴰ = bᴰ} fᴰ {c = c} {cᴰ = cᴰ} g .equiv-proof compᴰ =
             -- Rectify lift-g to have the same codomain as compᴰ
             (subst Hom[ g ][ bᴰ ,_]
                    (PathPΣ eq-over-comp .fst)
                    (lift-g .snd)
             -- It trivially composes to the expected morphism.
           , Homᴰ≡-DiscreteOpfibration _ _)
             -- And it's trivially equal to any other choice.
         , λ _ → Σ≡Prop (λ _ → isSetHomᴰ _ _) (Homᴰ≡-DiscreteOpfibration _ _)
         where
           lift-g : Σ[ cᴰ ∈ ob[ c ] ] Hom[ g ][ bᴰ , cᴰ ]
           lift-g = unique-lift g bᴰ .fst

           eq-over-comp : (map-snd (fᴰ ⋆ᴰ_) lift-g) ≡ (cᴰ , compᴰ)
           eq-over-comp = isContr→isProp (unique-lift (f B.⋆ g) aᴰ)
                                         (map-snd (fᴰ ⋆ᴰ_) lift-g)
                                         (cᴰ , compᴰ)

    isDiscreteOpfibration→Opcleavage : Opcleavage
    isDiscreteOpfibration→Opcleavage {a = a} {b = b} f aᴰ =
      -- Extend the second argument with a proof of opcartesianness.
      map-snd (λ fᴰ → fᴰ , isOpcartesianDiscreteOpfibration fᴰ)
              (unique-lift f aᴰ .fst)

    isDiscreteOpfibration→isOpfibration : isOpfibration
    isDiscreteOpfibration→isOpfibration = ∣ isDiscreteOpfibration→Opcleavage ∣₁

    uniqueOpcleavageDiscreteOpfibration : isContr Opcleavage
    uniqueOpcleavageDiscreteOpfibration .fst = isDiscreteOpfibration→Opcleavage
    uniqueOpcleavageDiscreteOpfibration .snd opcleavage =
      implicitFunExt $ implicitFunExt $ funExt λ f → funExt λ aᴰ →
      ΣPathP $
      map-snd (ΣPathPProp isPropIsOpcartesian) $
      PathPΣ $
      unique-lift f aᴰ .snd (map-snd fst (opcleavage f aᴰ))

    open Functor
    discreteOpfibrationToCopresheaf : Functor B (SET ℓC)
    discreteOpfibrationToCopresheaf .F-ob b = ob[ b ] , isSet-fibers b
    discreteOpfibrationToCopresheaf .F-hom f a = unique-lift f a .fst .fst
    discreteOpfibrationToCopresheaf .F-id = funExt λ a →
      cong fst $ unique-lift B.id a .snd (a , idᴰ)
    discreteOpfibrationToCopresheaf .F-seq f g = funExt λ a →
      let
        step1 = unique-lift f a .fst
        step2 = unique-lift g (step1 .fst) .fst
      in cong fst $
        unique-lift (f B.⋆ g) a .snd (step2 .fst , step1 .snd ⋆ᴰ step2 .snd)


  -- Characterization of opcartesian morphisms over an isomorphism (they're
  -- exactly displayed isomorphisms).
  module _
    {a b : B.ob} {f : B [ a , b ]} {f-isIso : isIso B f}
    {aᴰ : Cᴰ.ob[ a ]} {bᴰ : Cᴰ.ob[ b ]} {fᴰ : Cᴰ.Hom[ f ][ aᴰ , bᴰ ]}
    where

    open isIso f-isIso

    module _ (fᴰ-isIsoᴰ : isIsoᴰ Cᴰ f-isIso fᴰ) where
      open isIsoᴰ fᴰ-isIsoᴰ

      private basepath : {c : B.ob} (g : B [ b , c ]) → inv B.⋆ f B.⋆ g ≡ g
      basepath g =
          sym (B.⋆Assoc _ _ _)
        ∙ cong (B._⋆ g) sec
        ∙ B.⋆IdL _
      {-# INLINE basepath #-}

      isIsoᴰ→isOpcartesian : isOpcartesian fᴰ
      isIsoᴰ→isOpcartesian g .equiv-proof fgᴰ .fst .fst =
        R.reind
          (basepath g)
          (invᴰ ⋆ᴰ fgᴰ)
      isIsoᴰ→isOpcartesian g .equiv-proof fgᴰ .fst .snd =
        R.≡[]-rectify $
          (refl R.[ refl ]⋆[ sym (basepath g) ] symP (R.reind-filler (basepath g) _))
            R.[ _ ]∙[ _ ]
          symP (Cᴰ.⋆Assocᴰ fᴰ invᴰ fgᴰ)
            R.[ sym $ B.⋆Assoc f inv (f B.⋆ g) ]∙[ _ ]
          (retᴰ R.[ ret ]⋆[ refl ] refl)
            R.[ _ ]∙[ _ ]
          Cᴰ.⋆IdLᴰ fgᴰ
      isIsoᴰ→isOpcartesian g .equiv-proof fgᴰ .snd (gᴰ , gᴰ-infib) =
        Σ≡Prop (λ _ → isOfHLevelPathP' 1 Cᴰ.isSetHomᴰ _ _) $
          R.≡[]-rectify $
            symP (R.reind-filler (basepath g) _)
              R.[ sym (basepath g) ]∙[ _ ]
            (refl R.[ refl ]⋆[ refl ] symP gᴰ-infib)
              R.[ _ ]∙[ _ ]
            symP (Cᴰ.⋆Assocᴰ invᴰ fᴰ gᴰ)
              R.[ sym (B.⋆Assoc inv f g) ]∙[ _ ]
            (secᴰ R.[ sec ]⋆[ refl ] refl)
              R.[ _ ]∙[ _ ]
            Cᴰ.⋆IdLᴰ gᴰ

    module _ (opcart : isOpcartesian fᴰ) where
      open isIsoᴰ

      isOpcartesian→isIsoᴰ : isIsoᴰ Cᴰ f-isIso fᴰ
      isOpcartesian→isIsoᴰ .invᴰ =
        opcart inv .equiv-proof (R.reind (sym ret) idᴰ) .fst .fst
      isOpcartesian→isIsoᴰ .retᴰ = R.≡[]-rectify $
        opcart inv .equiv-proof (R.reind (sym ret) idᴰ) .fst .snd
          R.[ _ ]∙[ ret ]
        R.reind-filler-sym ret idᴰ
      isOpcartesian→isIsoᴰ .secᴰ =
        let
          ≡-any-two-in-fib = isContr→isProp $
            opcart (inv B.⋆ f) .equiv-proof
              (fᴰ ⋆ᴰ (isOpcartesian→isIsoᴰ .invᴰ) ⋆ᴰ fᴰ)
          -- Reindexed idᴰ is a valid lift for the composition.
          idᴰ-in-fib = R.≡[]-rectify $
            (refl {x = fᴰ} R.[ refl ]⋆[ _ ] R.reind-filler-sym sec idᴰ)
              R.[ _ ]∙[ _ ]
            ⋆IdRᴰ fᴰ
              R.[ B.⋆IdR f ]∙[ _ ]
            symP (⋆IdLᴰ fᴰ)
              R.[ sym (B.⋆IdL f) ]∙[ _ ]
            (symP (isOpcartesian→isIsoᴰ .retᴰ) R.[ sym ret ]⋆[ refl ] refl {x = fᴰ})
              R.[ _ ]∙[ _ ]
            ⋆Assocᴰ fᴰ (isOpcartesian→isIsoᴰ .invᴰ) fᴰ
        in R.≡[]-rectify $
        (cong fst $ ≡-any-two-in-fib
          ((isOpcartesian→isIsoᴰ .invᴰ) ⋆ᴰ fᴰ , refl)
          (R.reind (sym sec) idᴰ , idᴰ-in-fib))

          R.[ _ ]∙[ _ ]
        R.reind-filler-sym sec idᴰ

  -- Construction of the substitution functor for a general opfibration.
  module _
    (cleavage : Opcleavage)
    {a b : B.ob}
    (σ : B [ a , b ])
    where

    open Functor
    open Category

    -- Nice universal characterization of candidates for arrow substitution.
    substituteArrow : {x y : VerticalCategory Cᴰ a .ob}
      → (f : VerticalCategory Cᴰ a [ x , y ])
      → ∃![ g ∈ VerticalCategory Cᴰ b [ cleavage σ x .fst , cleavage σ y .fst ] ]
          (cleavage σ x .snd .fst ⋆ᴰ g
             ≡[ B.⋆IdR σ ∙ sym (B.⋆IdL σ) ]
           f ⋆ᴰ cleavage σ y .snd .fst)
    substituteArrow f =
        map-snd
          (λ p → R.≡[]-rectify $
            p
              R.[ _ ]∙[ sym (B.⋆IdL _ ∙ sym (B.⋆IdR _)) ]
            symP (R.reind-filler _ _))
          (cart .fst)
      , λ g' →
          Σ≡Prop
            (λ _ → isOfHLevelPathP' 1 isSetHomᴰ _ _)
            (cong fst $ cart .snd $
              map-snd
                (λ p → R.≡[]-rectify $ p R.[ _ ]∙[ _ ] R.reind-filler _ _)
                g')
      where
        cart : isContr (Σ _ _)
        cart =
          cleavage σ _ .snd .snd _ .equiv-proof $
            R.reind (B.⋆IdL _ ∙ sym (B.⋆IdR _)) (f ⋆ᴰ cleavage σ _ .snd .fst)

    substitutionFunctor : Functor (VerticalCategory Cᴰ a) (VerticalCategory Cᴰ b)
    substitutionFunctor .F-ob c = cleavage σ c .fst
    substitutionFunctor .F-hom f = substituteArrow f .fst .fst
    substitutionFunctor .F-id {x} = cong fst $
      substituteArrow (VerticalCategory Cᴰ a .Category.id) .snd $
        VerticalCategory Cᴰ b .Category.id
      , R.≡[]-rectify
          ((refl R.[ refl ]⋆[ refl ] symP (R.reind-filler refl idᴰ))
             R.[ cong₂ B._⋆_ refl refl ]∙[ _ ]
           ⋆IdRᴰ (cleavage σ x .snd .fst)
             R.[ B.⋆IdR σ ]∙[ _ ]
           symP (⋆IdLᴰ (cleavage σ x .snd .fst))
             R.[ sym (B.⋆IdL σ) ]∙[ _ ]
           (R.reind-filler refl idᴰ R.[ refl ]⋆[ refl ] refl))
    substitutionFunctor .F-seq {x} {y} {z} f g = cong fst $
      substituteArrow (VerticalCategory Cᴰ a .Category._⋆_ f g) .snd $
        VerticalCategory Cᴰ b .Category._⋆_ (stepf .fst) (stepg .fst)
      , R.≡[]-rectify
          ((refl
              R.[ refl ]⋆[ sym (B.⋆IdL B.id) ]
            R.reind-filler-sym (sym $ B.⋆IdL B.id) (stepf .fst ⋆ᴰ stepg .fst))
             R.[ cong₂ B._⋆_ refl (sym $ B.⋆IdL B.id) ]∙[ _ ]
           symP (⋆Assocᴰ (cleavage σ x .snd .fst) (stepf .fst) (stepg .fst))
             R.[ sym (B.⋆Assoc σ B.id B.id) ]∙[ _ ]
           (stepf .snd R.[ (B.⋆IdR σ ∙ sym (B.⋆IdL σ)) ]⋆[ refl ] refl)
             R.[ cong₂ B._⋆_ (B.⋆IdR σ ∙ sym (B.⋆IdL σ)) refl ]∙[ _ ]
           ⋆Assocᴰ f (cleavage σ y .snd .fst) (stepg .fst)
             R.[ B.⋆Assoc B.id σ B.id ]∙[ _ ]
           (refl R.[ refl ]⋆[ (B.⋆IdR σ ∙ sym (B.⋆IdL σ)) ] stepg .snd)
             R.[ cong₂ B._⋆_ refl (B.⋆IdR σ ∙ sym (B.⋆IdL σ)) ]∙[ _ ]
           symP (⋆Assocᴰ f g (cleavage σ z .snd .fst))
             R.[ sym (B.⋆Assoc B.id B.id σ) ]∙[ cong₂ B._⋆_ (B.⋆IdL B.id) refl ]
           (R.reind-filler (B.⋆IdL B.id) (f ⋆ᴰ g) R.[ B.⋆IdL B.id ]⋆[ refl ] refl))
      where
        stepf = substituteArrow f .fst
        stepg = substituteArrow g .fst
