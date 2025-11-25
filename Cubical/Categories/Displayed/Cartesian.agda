
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Prelude

open import Cubical.Data.Sigma

open import Cubical.HITs.PropositionalTruncation as PT

open import Cubical.Categories.Category
open import Cubical.Categories.Displayed.Base
import      Cubical.Categories.Displayed.Reasoning as HomᴰReasoning
open import Cubical.Categories.Functor
open import Cubical.Categories.Instances.Sets
open import Cubical.Categories.NaturalTransformation
open import Cubical.Categories.Constructions.Vertical

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

      isIsoᴰ→isOpcartesian : isOpcartesian fᴰ
      isIsoᴰ→isOpcartesian g .equiv-proof fgᴰ .fst .fst =
        R.reind
          ( sym (B.⋆Assoc _ _ _)
          ∙ B.⟨ sec ⟩⋆⟨ refl ⟩
          ∙ B.⋆IdL _)
          (invᴰ ⋆ᴰ fgᴰ)
      isIsoᴰ→isOpcartesian g .equiv-proof fgᴰ .fst .snd =
        R.rectify $ R.≡out $
            R.⟨ refl ⟩⋆⟨ sym $ R.reind-filler _ _ ⟩
          ∙ sym (R.⋆Assoc _ _ _)
          ∙ R.⟨ R.≡in retᴰ ⟩⋆⟨ refl ⟩
          ∙ R.⋆IdL _
      isIsoᴰ→isOpcartesian g .equiv-proof fgᴰ .snd (gᴰ , gᴰ-infib) =
        Σ≡Prop (λ _ → isOfHLevelPathP' 1 Cᴰ.isSetHomᴰ _ _) $
          R.rectify $ R.≡out $
              sym (R.reind-filler _ _)
            ∙ R.⟨ refl ⟩⋆⟨ sym $ R.≡in gᴰ-infib ⟩
            ∙ sym (R.⋆Assoc _ _ _)
            ∙ R.⟨ R.≡in secᴰ ⟩⋆⟨ refl ⟩
            ∙ R.⋆IdL _

    module _ (opcart : isOpcartesian fᴰ) where
      open isIsoᴰ

      isOpcartesian→isIsoᴰ : isIsoᴰ Cᴰ f-isIso fᴰ
      isOpcartesian→isIsoᴰ .invᴰ =
        opcart inv .equiv-proof (R.reind (sym ret) idᴰ) .fst .fst
      isOpcartesian→isIsoᴰ .retᴰ = R.rectify $ R.≡out $
          R.≡in (opcart inv .equiv-proof (R.reind (sym ret) idᴰ) .fst .snd)
        ∙ sym (R.reind-filler _ _)
      isOpcartesian→isIsoᴰ .secᴰ =
        let
          ≡-any-two-in-fib = isContr→isProp $
            opcart (inv B.⋆ f) .equiv-proof
              (fᴰ ⋆ᴰ (isOpcartesian→isIsoᴰ .invᴰ) ⋆ᴰ fᴰ)
          -- Reindexed idᴰ is a valid lift for the composition.
          idᴰ-in-fib = R.rectify $ R.≡out $
              R.⟨ refl ⟩⋆⟨ sym $ R.reind-filler _ _ ⟩
            ∙ R.⋆IdR _
            ∙ sym (R.⋆IdL _)
            ∙ R.⟨ sym $ R.≡in $ isOpcartesian→isIsoᴰ .retᴰ ⟩⋆⟨ refl ⟩
            ∙ R.⋆Assoc _ _ _
        in R.rectify $ R.≡out $
            R.≡in (cong fst $ ≡-any-two-in-fib
              ((isOpcartesian→isIsoᴰ .invᴰ) ⋆ᴰ fᴰ , refl)
              (R.reind (sym sec) idᴰ , idᴰ-in-fib))
          ∙ sym (R.reind-filler _ _)

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
          (λ p → R.rectify $ R.≡out $
              R.≡in p
            ∙ sym (R.reind-filler _ _))
          (cart .fst)
      , λ g' →
          Σ≡Prop
            (λ _ → isOfHLevelPathP' 1 isSetHomᴰ _ _)
            (cong fst $ cart .snd $
              map-snd
                (λ p → R.rectify $ R.≡out $ R.≡in p ∙ R.reind-filler _ _)
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
      , (R.rectify $ R.≡out $
            R.⟨ refl ⟩⋆⟨ sym $ R.reind-filler _ _ ⟩
          ∙ R.⋆IdR _
          ∙ sym (R.⋆IdL _)
          ∙ R.⟨ R.reind-filler _ _ ⟩⋆⟨ refl ⟩)
    substitutionFunctor .F-seq {x} {y} {z} f g = cong fst $
      substituteArrow (VerticalCategory Cᴰ a .Category._⋆_ f g) .snd $
        VerticalCategory Cᴰ b .Category._⋆_ (stepf .fst) (stepg .fst)
      , (R.rectify $ R.≡out $
            R.⟨ refl ⟩⋆⟨ sym $ R.reind-filler _ _ ⟩
          ∙ sym (R.⋆Assoc _ _ _)
          ∙ R.⟨ R.≡in $ stepf .snd ⟩⋆⟨ refl ⟩
          ∙ R.⋆Assoc _ _ _
          ∙ R.⟨ refl ⟩⋆⟨ R.≡in $ stepg .snd ⟩
          ∙ sym (R.⋆Assoc _ _ _)
          ∙ R.⟨ R.reind-filler _ _ ⟩⋆⟨ refl ⟩)
      where
        stepf = substituteArrow f .fst
        stepg = substituteArrow g .fst
