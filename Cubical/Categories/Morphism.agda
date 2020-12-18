{-# OPTIONS --cubical --no-import-sorts --safe #-}

module Cubical.Categories.Morphism where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Sigma
open import Cubical.Categories.Category

private
  variable
    ℓ ℓ' : Level

module MorphTypes (C : Precategory ℓ ℓ') where
  open Precategory C
  private
    variable
      x y z w : ob

  IsMonic : (Hom[ x , y ]) → Type (ℓ-max ℓ ℓ')
  IsMonic {x} {y} f = ∀ {z : ob} {a a' : Hom[ z , x ]}
    → (f ∘ a ≡ f ∘ a') → (a ≡ a')

  IsEpic : (Hom[ x , y ]) → Type (ℓ-max ℓ ℓ')
  IsEpic {x} {y} g = ∀ {z : ob} {b b' : Hom[ y , z ]}
    → (b ∘ g ≡ b' ∘ g) → (b ≡ b')

  -- A morphism is split monic if it has a *retraction*
  IsSplitMon : (Hom[ x , y ]) → Type ℓ'
  IsSplitMon {x} {y} f = ∃[ r ∈ Hom[ y , x ] ] r ∘ f ≡ id x

  -- A morphism is split epic if it has a *section*
  IsSplitEpi : (Hom[ x , y ]) → Type ℓ'
  IsSplitEpi {x} {y} g = ∃[ s ∈ Hom[ y , x ] ] g ∘ s ≡ id y

  AreInv : (f : Hom[ x , y ]) → (g : Hom[ y , x ]) → Type ℓ'
  AreInv {x} {y} f g = (g ∘ f ≡ id x) × (f ∘ g ≡ id y)

  IsIso : (f : Hom[ x , y ]) → Type ℓ'
  IsIso {x} {y} f = ∃[ g ∈ Hom[ y , x ] ] AreInv f g

  AreIso : ob → ob → Type ℓ'
  AreIso x y = ∃[ f ∈ Hom[ x , y ] ] IsIso f
