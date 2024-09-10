-- The category of small categories
{-# OPTIONS --safe #-}

module Cubical.Categories.Instances.Cat where


open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Equiv.Properties
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Function
open import Cubical.Foundations.Univalence
open import Cubical.Data.Unit
open import Cubical.Data.Sigma
open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.NaturalTransformation
open import Cubical.Categories.Equivalence.WeakEquivalence
open import Cubical.Categories.Category.Path
open import Cubical.Relation.Binary.Properties

open import Cubical.Categories.Limits

open Category hiding (_∘_)
open Functor

module _ (ℓ ℓ' : Level) where
  Cat : Category (ℓ-max (ℓ-suc ℓ) (ℓ-suc ℓ')) (ℓ-max ℓ ℓ')
  ob Cat = Σ (Category ℓ ℓ') isSmall
  Hom[_,_] Cat X Y = Functor (fst X) (fst Y)
  id Cat = 𝟙⟨ _ ⟩
  _⋆_ Cat G H = H ∘F G
  ⋆IdL Cat _ = F-lUnit
  ⋆IdR Cat _ = F-rUnit
  ⋆Assoc Cat _ _ _ = F-assoc
  isSetHom Cat {y = _ , isSetObY} = isSetFunctor isSetObY
