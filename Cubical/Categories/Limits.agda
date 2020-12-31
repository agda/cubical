{-# OPTIONS --cubical --no-import-sorts --safe #-}

module Cubical.Categories.Limits where

open import Cubical.Foundations.Prelude
open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.NaturalTransformation

private
  variable
    ℓJ ℓJ' ℓC ℓC' : Level

module _ (J : Precategory ℓJ ℓJ')
         (C : Precategory ℓC ℓC') where
  open Precategory
  open Functor
  open NatTrans

  -- functor which sends all objects to c and all
  -- morphisms to the identity
  constF : (c : C .ob) → Functor J C
  constF c .F-ob _ = c
  constF c .F-hom _ = C .id c
  constF c .F-id = refl
  constF c .F-seq _ _ = sym (C .⋆IdL _)

  module _ (K : Functor J C) where

    -- precomposes a cone with a morphism
    _●_ : ∀ {d c : C .ob}
        → (f : C [ d , c ])
        → NatTrans (constF c) K
        → NatTrans (constF d) K
    (f ● μ) .N-ob x = f ⋆⟨ C ⟩ μ ⟦ x ⟧
    (f ● μ) .N-hom {x = x} {y} k
      = C .id _ ⋆⟨ C ⟩ (f ⋆⟨ C ⟩ μ ⟦ y ⟧)
      ≡⟨ C .⋆IdL _ ⟩
        f ⋆⟨ C ⟩ μ ⟦ y ⟧
      ≡⟨ cong (λ v → f ⋆⟨ C ⟩ v) (sym (C .⋆IdL _)) ⟩
        f ⋆⟨ C ⟩ (C .id _ ⋆⟨ C ⟩ μ ⟦ y ⟧)
      ≡⟨ cong (λ v → f ⋆⟨ C ⟩ v) (μ .N-hom k) ⟩
        f ⋆⟨ C ⟩ (μ ⟦ x ⟧ ⋆⟨ C ⟩ K ⟪ k ⟫)
      ≡⟨ sym (C .⋆Assoc _ _ _) ⟩
        f ⋆⟨ C ⟩ μ ⟦ x ⟧ ⋆⟨ C ⟩ K ⟪ k ⟫
      ∎

    -- a cone is a head with a natural transformation between that head and the diagram
    record Cone : Type (ℓ-max (ℓ-max ℓJ ℓJ') (ℓ-max ℓC ℓC'))  where
      field
        {head} : C .ob
        legs : NatTrans (constF head) K

    open Cone

    -- μ factors ν if there's a morphism such that the natural transformation
    -- from precomposing it with ν gives you back μ
    _factors_ : (μ ν : Cone) → Type (ℓ-max (ℓ-max ℓJ ℓJ') (ℓ-max ℓC ℓC'))
    μ factors ν = Σ[ mor ∈ C [ ν .head , μ .head ] ] ν .legs ≡ (mor ● μ .legs)

    -- μ uniquely factors ν if the factor from above is contractible
    _uniquelyFactors_ : (μ ν : Cone) → Type (ℓ-max (ℓ-max ℓJ ℓJ') (ℓ-max ℓC ℓC'))
    μ uniquelyFactors ν = isContr (μ factors ν)

    -- a Limit is a cone such that all cones are uniquely factored by it
    record Limit : Type (ℓ-max (ℓ-max ℓJ ℓJ') (ℓ-max ℓC ℓC'))  where
      field
        cone : Cone
        up   : ∀ (ν : Cone) → cone uniquelyFactors ν
