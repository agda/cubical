{-# OPTIONS --cubical --no-import-sorts --safe #-}

module Cubical.Categories.Limits.Pullback where

open import Cubical.Foundations.Prelude
open import Cubical.Categories.Limits.Base
open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.Instances.Cospan public


private
  variable
    ℓ ℓ' : Level

module _ {C : Precategory ℓ ℓ'} where

  open Precategory C
  open Functor

  record Cospan : Type (ℓ-max ℓ ℓ') where
    constructor cospan
    field
      l m r : ob
      s₁ : C [ l , m ]
      s₂ : C [ r , m ]

  record PullbackCone (cspn : Cospan) (c : ob) : Type (ℓ-max ℓ ℓ') where
    constructor cone
    open Cospan cspn
    field
      p₁ : C [ c , l ]
      p₂ : C [ c , r ]
      sq : p₁ ⋆⟨ C ⟩ s₁ ≡ p₂ ⋆⟨ C ⟩ s₂

  Cospan→Func : Cospan → Functor CospanCat C
  Cospan→Func (cospan l m r f g) .F-ob ⓪ = l
  Cospan→Func (cospan l m r f g) .F-ob ① = m
  Cospan→Func (cospan l m r f g) .F-ob ② = r
  Cospan→Func (cospan l m r f g) .F-hom {⓪} {①} k = f
  Cospan→Func (cospan l m r f g) .F-hom {②} {①} k = g
  Cospan→Func (cospan l m r f g) .F-hom {⓪} {⓪} k = id l
  Cospan→Func (cospan l m r f g) .F-hom {①} {①} k = id m
  Cospan→Func (cospan l m r f g) .F-hom {②} {②} k = id r
  Cospan→Func (cospan l m r f g) .F-id {⓪} = refl
  Cospan→Func (cospan l m r f g) .F-id {①} = refl
  Cospan→Func (cospan l m r f g) .F-id {②} = refl
  Cospan→Func (cospan l m r f g) .F-seq {⓪} {⓪} {⓪} φ ψ = sym (⋆IdL _)
  Cospan→Func (cospan l m r f g) .F-seq {⓪} {⓪} {①} φ ψ = sym (⋆IdL _)
  Cospan→Func (cospan l m r f g) .F-seq {⓪} {①} {①} φ ψ = sym (⋆IdR _)
  Cospan→Func (cospan l m r f g) .F-seq {①} {①} {①} φ ψ = sym (⋆IdL _)
  Cospan→Func (cospan l m r f g) .F-seq {②} {②} {②} φ ψ = sym (⋆IdL _)
  Cospan→Func (cospan l m r f g) .F-seq {②} {②} {①} φ ψ = sym (⋆IdL _)
  Cospan→Func (cospan l m r f g) .F-seq {②} {①} {①} φ ψ = sym (⋆IdR _)
