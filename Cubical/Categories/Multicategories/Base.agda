open import Cubical.Foundations.Prelude

open import Cubical.WildCat.Functor
open import Cubical.WildCat.Monad
open import Cubical.WildCat.Instances.Types

module Cubical.Categories.Multicategories.Base ℓ (T : WildMonad (TypeCat ℓ)) where

open WildFunctor (T .fst) renaming (F-ob to T-ob; F-hom to T-hom; F-id to T-id; F-seq to T-seq)
open IsMonad (T .snd)
open WildNatTrans η renaming (N-ob to η-ob; N-hom to η-hom)
open WildNatTrans μ renaming (N-ob to μ-ob; N-hom to μ-hom)

record Multicategory ℓ' : Type (ℓ-suc (ℓ-max ℓ ℓ')) where
  no-eta-equality
  field
    Ob : Type ℓ
    Hom : T-ob Ob → Ob → Type ℓ'
    id : ∀ {x} → Hom (η-ob _ x) x
