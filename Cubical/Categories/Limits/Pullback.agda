{-# OPTIONS --safe #-}
module Cubical.Categories.Limits.Pullback where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.HITs.PropositionalTruncation.Base

open import Cubical.Data.Sigma

open import Cubical.Categories.Limits.Base
open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.Instances.Cospan

private
  variable
    ℓ ℓ' : Level

module _ {C : Category ℓ ℓ'} where

  open Category C
  open Functor

  record Cospan : Type (ℓ-max ℓ ℓ') where
    constructor cospan
    field
      l m r : ob
      s₁ : C [ l , m ]
      s₂ : C [ r , m ]

  open Cospan

  isPullback : (cspn : Cospan) → {c : ob} (p₁ : C [ c , cspn .l ]) (p₂ : C [ c , cspn .r ])
               (H : p₁ ⋆ cspn .s₁ ≡ p₂ ⋆ cspn .s₂) → Type (ℓ-max ℓ ℓ')
  isPullback cspn {c} p₁ p₂ H =
    ∀ {d} (h : C [ d , cspn .l ]) (k : C [ d , cspn .r ]) (H' : h ⋆ cspn .s₁ ≡ k ⋆ cspn .s₂)
    → ∃![ hk ∈ C [ d , c ] ] (h ≡ hk ⋆ p₁) × (k ≡ hk ⋆ p₂)

  isPropIsPullback : (cspn : Cospan) → {c : ob} (p₁ : C [ c , cspn .l ]) (p₂ : C [ c , cspn .r ])
    (H : p₁ ⋆ cspn .s₁ ≡ p₂ ⋆ cspn .s₂) → isProp (isPullback cspn p₁ p₂ H)
  isPropIsPullback cspn p₁ p₂ H = isPropImplicitΠ (λ x → isPropΠ3 λ h k H' → isPropIsContr)

  record Pullback (cspn : Cospan) : Type (ℓ-max ℓ ℓ') where
    field
      pbOb  : ob
      pbPr1 : C [ pbOb , cspn .l ]
      pbPr2 : C [ pbOb , cspn .r ]
      pbCommutes : pbPr1 ⋆ cspn .s₁ ≡ pbPr2 ⋆ cspn .s₂
      isPb : isPullback cspn pbPr1 pbPr2 pbCommutes

  -- TODO: define accessor functions for the pullback arrow and its properties

Pullbacks : (C : Category ℓ ℓ') → Type (ℓ-max ℓ ℓ')
Pullbacks C = (cspn : Cospan) → Pullback {C = C} cspn

hasPullbacks : (C : Category ℓ ℓ') → Type (ℓ-max ℓ ℓ')
hasPullbacks C = ∥ Pullbacks C ∥


-- TODO: finish the following show that this definition of Pullback is equivalent to the Cospan limit
module _ {C : Category ℓ ℓ'} where
  open Category C
  open Functor

  Cospan→Func : Cospan {C = C} → Functor CospanCat C
  Cospan→Func (cospan l m r f g) .F-ob ⓪ = l
  Cospan→Func (cospan l m r f g) .F-ob ① = m
  Cospan→Func (cospan l m r f g) .F-ob ② = r
  Cospan→Func (cospan l m r f g) .F-hom {⓪} {①} k = f
  Cospan→Func (cospan l m r f g) .F-hom {②} {①} k = g
  Cospan→Func (cospan l m r f g) .F-hom {⓪} {⓪} k = id
  Cospan→Func (cospan l m r f g) .F-hom {①} {①} k = id
  Cospan→Func (cospan l m r f g) .F-hom {②} {②} k = id
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


