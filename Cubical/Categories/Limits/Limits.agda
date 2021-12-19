{-# OPTIONS --safe #-}

module Cubical.Categories.Limits.Limits where

open import Cubical.Foundations.Prelude
open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.NaturalTransformation

private
  variable
    ℓJ ℓJ' ℓC ℓC' : Level
    ℓ ℓ' ℓ'' : Level

module _ {J : Category ℓJ ℓJ'}
         {C : Category ℓC ℓC'} where
  open Category
  open Functor
  open NatTrans

  -- functor which sends all objects to c and all
  -- morphisms to the identity
  constF : (c : C .ob) → Functor J C
  constF c .F-ob _ = c
  constF c .F-hom _ = C .id
  constF c .F-id = refl
  constF c .F-seq _ _ = sym (C .⋆IdL _)


  -- a cone is a natural transformation from the constant functor at x to K
  Cone : (K : Functor J C) → C .ob → Type _
  Cone K x = NatTrans (constF x) K


  module _ {K : Functor J C} where

    -- precomposes a cone with a morphism
    _◼_ : ∀ {d c : C .ob}
        → (f : C [ d , c ])
        → Cone K c
        → Cone K d
    (f ◼ μ) .N-ob x = f ⋆⟨ C ⟩ μ ⟦ x ⟧
    (f ◼ μ) .N-hom {x = x} {y} k
      = C .id ⋆⟨ C ⟩ (f ⋆⟨ C ⟩ μ ⟦ y ⟧)
      ≡⟨ C .⋆IdL _ ⟩
        f ⋆⟨ C ⟩ μ ⟦ y ⟧
      ≡⟨ cong (λ v → f ⋆⟨ C ⟩ v) (sym (C .⋆IdL _)) ⟩
        f ⋆⟨ C ⟩ (C .id ⋆⟨ C ⟩ μ ⟦ y ⟧)
      ≡⟨ cong (λ v → f ⋆⟨ C ⟩ v) (μ .N-hom k) ⟩
        f ⋆⟨ C ⟩ (μ ⟦ x ⟧ ⋆⟨ C ⟩ K ⟪ k ⟫)
      ≡⟨ sym (C .⋆Assoc _ _ _) ⟩
        f ⋆⟨ C ⟩ μ ⟦ x ⟧ ⋆⟨ C ⟩ K ⟪ k ⟫
      ∎

    -- μ factors ν if there's a morphism such that the natural transformation
    -- from precomposing it with ν gives you back μ
    _factors_ : {u v : C .ob} (μ : Cone K u) (ν : Cone K v) → Type _
    _factors_ {u} {v} μ ν = Σ[ mor ∈ C [ v , u ] ] ν ≡ (mor ◼ μ)

    -- μ uniquely factors ν if the factor from above is contractible
    _uniquelyFactors_ : {u v : C .ob} (μ : Cone K u) (ν : Cone K v) → Type _
    _uniquelyFactors_ {u} {v} μ ν = isContr (μ factors ν)

  module _ (K : Functor J C) where

    -- a Limit is a cone such that all cones are uniquely factored by it
    record isLimit (head : C .ob) : Type (ℓ-max (ℓ-max ℓJ ℓJ') (ℓ-max ℓC ℓC'))  where
      constructor islimit
      field
        cone : Cone K head
        -- TODO: change this to terminal object in category of Cones?
        up   : ∀ {v} (ν : Cone K v) → cone uniquelyFactors ν

    record Limit : Type (ℓ-max (ℓ-max ℓJ ℓJ') (ℓ-max ℓC ℓC'))  where
      field
        head : C .ob
        islim : isLimit head

-- a Category is complete if it has all limits
complete' : {ℓJ ℓJ' : Level} (C : Category ℓC ℓC') → Type _
complete' {ℓJ = ℓJ} {ℓJ'} C = (J : Category ℓJ ℓJ') (K : Functor J C) → Limit K

complete : (C : Category ℓC ℓC') → Typeω
complete C = ∀ {ℓJ ℓJ'} → complete' {ℓJ = ℓJ} {ℓJ'} C
