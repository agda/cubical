{-

This file is included only temporarly to test some features of this module,

I plan to remove it before final pull request (or maybe move it to the experiments folder?)

-}

{-# OPTIONS --cubical --no-import-sorts --safe #-}

module Cubical.Data.Sigma.Nested.Example where

open import Cubical.Data.Nat

open import Cubical.Data.Bool
open import Cubical.Data.Sigma

open import Cubical.Foundations.Everything

open import Cubical.Data.Sigma.Nested.Base
open import Cubical.Data.Sigma.Nested.Nested
open import Cubical.Data.Sigma.Nested.Currying



Σ-par-assoc-7 : ∀ A A₁ A₂ A₃ A₄ A₅ A₆
            → (A₇ : (x : A)
                    (x₁ : A₁ x)
                    (x₂ : A₂ x x₁)
                    (x₃ : A₃ x x₁ x₂)
                    (x₄ : A₄ x x₁ x₂ x₃)
                    (x₅ : A₅ x x₁ x₂ x₃ x₄)
                    (x₆ : A₆ x x₁ x₂ x₃ x₄ x₅) → Type)
                   →
                                 Σ (Σ (Σ (Σ (Σ (Σ (Σ
                                                     A
                                              (λ x → A₁ x))
                                       (λ (x , x₁) → A₂ x x₁))
                                (λ ((x , x₁) , x₂) → A₃ x x₁ x₂))
                         (λ (((x , x₁) , x₂) , x₃) → A₄ x x₁ x₂ x₃))
                  (λ ((((x , x₁) , x₂) , x₃) , x₄) → A₅ x x₁ x₂ x₃ x₄))
           (λ (((((x , x₁) , x₂) , x₃) , x₄) , x₅) → A₆ x x₁ x₂ x₃ x₄ x₅))
    (λ ((((((x , x₁) , x₂) , x₃) , x₄) , x₅) , x₆) → A₇ x x₁ x₂ x₃ x₄ x₅ x₆)
       ≃
               Σ  A
         λ x → Σ (A₁ x)
        λ x₁ → Σ (A₂ x x₁ )
        λ x₂ → Σ (A₃ x x₁ x₂)
        λ x₃ → Σ (A₄ x x₁ x₂ x₃)
        λ x₄ → Σ (A₅ x x₁ x₂ x₃ x₄)
        λ x₅ → Σ (A₆ x x₁ x₂ x₃ x₄ x₅)
        λ x₆ →    A₇ x x₁ x₂ x₃ x₄ x₅ x₆

Σ-par-assoc-7 = Σ-par-assoc-n {ℓ-zero} (leftMost 7)


-- type above is only provided as ilustration, proper type can be infered from definition
Σ-par-assoc-7-noHint : _
Σ-par-assoc-7-noHint = Σ-par-assoc-n {ℓ-zero} (leftMost 7)



-- random example of record, with some dependencies betwen fields

record IsPrecategory' (ob : Type₀) (hom : ob → ob → Type₀) : Type₀ where
  no-eta-equality
  constructor isPrec
  field
    idn : ∀ x → hom x x
    seq : ∀ {x y z} (f : hom x y) (g : hom y z) → hom x z
    seq-λ : ∀ {x y : ob} (f : hom x y) → seq (idn x) f ≡ f
    seq-ρ : ∀ {x y} (f : hom x y) → seq f (idn y) ≡ f
    seq-α : ∀ {u v w x} (f : hom u v) (g : hom v w) (h : hom w x) → seq (seq f g) h ≡ seq f (seq g h)


-- if we provide the length of record
-- it is not necessary to describe type of fields to uncurry constructor
 
isPrec' : {ob : Type ℓ-zero}
        {hom : ob → ob → Type ℓ-zero} →
        (x : _) → IsPrecategory' ob hom
     --      ↑ - Agda do _not_ complain here
     --          (it is not any suprising feature of this implementation,
     --            but my earlier faulty attempt was not able to do this
     --            so I decided to include this test here)
isPrec' {ob} {hom} = n-uncurryᵣ {n = 5} _ (isPrec {ob} {hom}) 


-- Types of holes in nestedΣ are not ugly, they do not mention suc, or fst
-- holes evaluates slighly beter for NestedΣ in default (rightMost) shape



test-isPrec' : IsPrecategory' {!!} {!!}
test-isPrec' = isPrec' ({!!} , {!!} , {!!} , {!!} , {!!})


-- here (C-u C-u C-c C-,) must be used to evaluate types of the holes
-- but after this all mentions of snd, fst , curry and uncurry disapears

test-isPrec'-leftMost : IsPrecategory' {!!} {!!}
test-isPrec'-leftMost = isPrec'
   (Iso.fun (NestedΣ-NestedΣᵣ-Iso (leftMost 4) _)
      ((((({!!}) , {!!}) , {!!}) , {!!}) , {!!}))
