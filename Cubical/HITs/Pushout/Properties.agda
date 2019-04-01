{-# OPTIONS --cubical --safe #-}

module Cubical.HITs.Pushout.Properties where

open import Cubical.Core.Primitives
open import Cubical.Core.Prelude
open import Cubical.Core.Glue

open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.GroupoidLaws

open import Cubical.Data.Prod.Base
open import Cubical.Data.Unit

open import Cubical.HITs.Pushout.Base

-- 3×3 lemma for pushouts

{-
 
A00 ←—f01—— A02 ——f03—→ A04
 ↑           ↑           ↑
f10   H11   f12   H13   f14
 |           |           |
A20 ←—f21—— A22 ——f23—→ A24
 |           |           |
f30   H31   f32   H33   f34
 ↓           ↓           ↓
A40 ←—f41—— A42 ——f43—→ A44

-}

module 3x3 (A00 A02 A04 A20 A22 A24 A40 A42 A44 : Set)
           (f10 : A20 → A00)
           (f12 : A22 → A02)
           (f14 : A24 → A04)

           (f30 : A20 → A40)
           (f32 : A22 → A42)
           (f34 : A24 → A44)

           (f01 : A02 → A00)
           (f21 : A22 → A20)
           (f41 : A42 → A40)

           (f03 : A02 → A04)
           (f23 : A22 → A24)
           (f43 : A42 → A44)

           (H11 : ∀ x → f01 (f12 x) ≡ f10 (f21 x))
           (H13 : ∀ x → f03 (f12 x) ≡ f14 (f23 x))
           (H31 : ∀ x → f41 (f32 x) ≡ f30 (f21 x))
           (H33 : ∀ x → f43 (f32 x) ≡ f34 (f23 x))
  where

  A⋅0 : Set
  A⋅0 = Pushout f10 f30

  A⋅2 : Set
  A⋅2 = Pushout f12 f32

  A⋅4 : Set
  A⋅4 = Pushout f14 f34

  f⋅1 : A⋅2 → A⋅0
  f⋅1 (inl x) = inl (f01 x)
  f⋅1 (inr x) = inr (f41 x)
  f⋅1 (push a j) = ((λ i → inl (H11 a i))
                   ∙∙ push (f21 a)
                   ∙∙ (λ i → inr (H31 a (~ i)))) j
                   
  f⋅3 : A⋅2 → A⋅4
  f⋅3 (inl x) = inl (f03 x)
  f⋅3 (inr x) = inr (f43 x)
  f⋅3 (push a j) = ((λ i → inl (H13 a i))
                   ∙∙ push (f23 a)
                   ∙∙ (λ i → inr (H33 a (~ i)))) j
  
  A⋅× : Set
  A⋅× = Pushout f⋅1 f⋅3

  A0⋅ : Set
  A0⋅ = Pushout f01 f03

  A2⋅ : Set
  A2⋅ = Pushout f21 f23

  A4⋅ : Set
  A4⋅ = Pushout f41 f43

  f1⋅ : A2⋅ → A0⋅
  f1⋅ (inl x) = inl (f10 x)
  f1⋅ (inr x) = inr (f14 x)
  f1⋅ (push a j) = ((λ i → inl (H11 a (~ i)))
                   ∙∙ push (f12 a)
                   ∙∙ (λ i → inr (H13 a i))) j

  f3⋅ : A2⋅ → A4⋅
  f3⋅ (inl x) = inl (f30 x)
  f3⋅ (inr x) = inr (f34 x)
  f3⋅ (push a j) = ((λ i → inl (H31 a (~ i)))
                   ∙∙ push (f32 a)
                   ∙∙ (λ i → inr (H33 a i))) j

  A×⋅ : Set
  A×⋅ = Pushout f1⋅ f3⋅

  3x3 : A⋅× ≡ A×⋅
  3x3 = {!!}
