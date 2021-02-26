{-# OPTIONS --cubical --no-import-sorts --safe #-}

module Cubical.Categories.Limits.Base where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Data.Unit
open import Cubical.Data.Sigma using (ΣPathP)
open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.NaturalTransformation
open import Cubical.Categories.Instances.Sets

private
  variable
    ℓJ ℓJ' ℓC ℓC' : Level
    ℓ ℓ' ℓ'' : Level

module _ {J : Precategory ℓJ ℓJ'}
         {C : Precategory ℓC ℓC'} where
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
      field
        cone : Cone K head
        -- TODO: change this to terminal object in category of Cones?
        up   : ∀ {v} (ν : Cone K v) → cone uniquelyFactors ν

    record Limit : Type (ℓ-max (ℓ-max ℓJ ℓJ') (ℓ-max ℓC ℓC'))  where
      field
        head : C .ob
        islim : isLimit head

-- a Category is complete if it has all limits
complete' : {ℓJ ℓJ' : Level} (C : Precategory ℓC ℓC') → Type _
complete' {ℓJ = ℓJ} {ℓJ'} C = (J : Precategory ℓJ ℓJ') (K : Functor J C) → Limit K

complete : (C : Precategory ℓC ℓC') → Typeω
complete C = ∀ {ℓJ ℓJ'} → complete' {ℓJ = ℓJ} {ℓJ'} C

open Limit
open NatTrans
open Precategory



-- TODO:

-- 1. every diagram has limits isomorphic to the limit of an equalizer of products

-- 2. every equalizer can be made into a pullback

-- 3. every product can be made into an equalizer

-- 4. a category with all pullbacks and a terminal object has all limits


-- SET is complete

-- notes:
-- didn't need to restrict to *finite* diagrams , why is that required in Set theoretic?
-- didn't use coinduction here because Agda didn't like me referencing 'cone' frome 'up' (termination check)

isCompleteSET : ∀ {ℓJ ℓJ'} → complete' {ℓJ = ℓJ} {ℓJ'} (SET (ℓ-max ℓJ ℓJ'))
isCompleteSET J K = record
                  { head = head'
                  ; islim = record { cone = cone' ; up = up' } }
  where
    -- the limit is defined as the Set of all cones with head Unit
    head' = Cone K (Unit* , isOfHLevelLift 2 isSetUnit) , isSetNat

    -- the legs are defined by taking a cone to its component at j
    cone' : Cone K head'
    cone' .N-ob j μ = (μ ⟦ j ⟧) tt*
    -- Naturality follows from naturality of the Unit cone
    cone' .N-hom {x = i} {j} f
      = funExt λ μ → (μ ⟦ j ⟧) tt*
        ≡[ i ]⟨ (μ .N-hom f i) tt* ⟩
          (K ⟪ f ⟫) ((μ ⟦ i ⟧) tt*)
        ∎

    -- Given another cone α, we want a unique function f from α → cone' which factors it
    -- factorization property enforces that (cone' ⟦ j ⟧ ● f) ≡ α ⟦ j ⟧
    -- but cone' ⟦ j ⟧ simply takes the jth component the output Cone K Unit from f
    -- so this enforces that for all x ∈ A, (f x) ⟦ j ⟧ ≡ α ⟦ j ⟧ x
    -- this determines the *only* possible factoring morphism
    up' : ∀ {A} (α : Cone K A) → cone' uniquelyFactors α
    up' {A} α = (f , fact) , unique
      where
        f : fst A → Cone K (Unit* , isOfHLevelLift 2 isSetUnit)
        f x = natTrans (λ j _ → α .N-ob j x)
                       (λ {m} {n} f → funExt λ μ i → α .N-hom f i x)

        fact : α ≡ (f ◼ cone')
        fact = makeNatTransPath refl -- I LOVE DEFINITIONAL EQUALITY

        unique : (τ : cone' factors α) → (f , fact) ≡ τ
        unique (f' , fact') = ΣPathP (f≡f' , fact≡fact')
          where
            f≡f' : f ≡ f'
            f≡f' = funExt λ x → makeNatTransPath (funExt λ _ → sym eq2)
              where
                -- the factorization property enforces that f' must have the same behavior as f
                eq1 : ∀ {x j} → ((cone' ⟦ j ⟧) (f' x)) ≡ (α ⟦ j ⟧) x
                eq1 {x} {j} i = ((fact' (~ i)) ⟦ j ⟧) x

                eq2 : ∀ {x j} → (f' x) ⟦ j ⟧ ≡ λ _ → (α ⟦ j ⟧) x -- = (f x) ⟦ j ⟧
                eq2 {x} {j} = funExt λ _ → eq1

            -- follows from Set having homsets
            fact≡fact' : PathP (λ i → α ≡ ((f≡f' i) ◼ cone')) fact fact'
            fact≡fact' = isOfHLevel→isOfHLevelDep 1 (λ β → isSetNat α β) fact fact' λ i → (f≡f' i) ◼ cone'
