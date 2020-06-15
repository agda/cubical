{-

This file is included only temporarly to test some features of this module,

I plan to remove it before final pull request (or maybe move it to the experiments folder?)

-}

{-# OPTIONS --cubical --no-import-sorts --safe #-}

module Cubical.Data.Sigma.Nested.Example where

open import Cubical.Data.Nat

open import Cubical.Data.Bool
open import Cubical.Data.Sigma
open import Cubical.Data.Vec
open import Cubical.Data.List

open import Cubical.Foundations.Everything

open import Cubical.Data.Sigma.Nested.Base
open import Cubical.Data.Sigma.Nested.Nested
open import Cubical.Data.Sigma.Nested.Currying
open import Cubical.Data.Sigma.Nested.Path


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
        λ x  → Σ (A₁ x)
        λ x₁ → Σ (A₂ x x₁ )
        λ x₂ → Σ (A₃ x x₁ x₂)
        λ x₃ → Σ (A₄ x x₁ x₂ x₃)
        λ x₄ → Σ (A₅ x x₁ x₂ x₃ x₄)
        λ x₅ → Σ (A₆ x x₁ x₂ x₃ x₄ x₅)
        λ x₆ →    A₇ x x₁ x₂ x₃ x₄ x₅ x₆

Σ-par-assoc-7 = Σ-par-assoc-n {ℓ-zero} (leftMost 7)


-- verision of above function, where type families have implicit arguments can be also
-- generated

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
     --          (it is not suprising feature,
     --            but my earlier faulty attempt was not able to do this
     --            so I decided to include this test here)
isPrec' = n-uncurryᵣ {n = 5} _ isPrec


-- Types of holes in nestedΣ are not ugly, they do not mention snd, or fst
-- holes evaluates slighly beter for NestedΣ in default (rightMost) shape


{-
test-isPrec' : IsPrecategory' {!!} {!!}
test-isPrec' = isPrec' ({!!} , {!!} , {!!} , {!!} , {!!})
-}

-- here , for the leftMost shape of NestedΣ (C-u C-u C-c C-,)
-- must be used to evaluate types of the holes
-- but after this all mentions of snd, fst , curry and uncurry disapears

{-
test-isPrec'-leftMost : IsPrecategory' {!!} {!!}
test-isPrec'-leftMost = isPrec'
   (Iso.fun (NestedΣ-NestedΣᵣ-Iso (leftMost 4) _)
      ((((({!!}) , {!!}) , {!!}) , {!!}) , {!!}))
-}


-- test of equivalence of function spaces of different explicity
-- both Sig, and uncurried description of the "Target" can be infered
-- (only if description of arguments is correct)

n-exp-imp-≃-test : ((z : ℕ) → (n k : ℕ) → (v₁ v₂ : Vec (Vec ℕ n × Vec ℕ k) z) → v₁ ≡ v₂)
                   ≃
                   ({z n k : ℕ} → (v₁ v₂ : Vec (Vec ℕ n × Vec ℕ k) z) → v₁ ≡ v₂)
n-exp-imp-≃-test = n-exp-imp-≃ (repeat false) (impex (0 ∷ 3 ∷ 2 ∷ [])) _



-- --- examples related to Paths.agda :

Pathⁿ-Pathⁿ'-2 : ∀ {ℓ} → {A : Type ℓ} → {bd : Boundaryⁿ 2 A}
            → Pathⁿ 2 A (getVal {n = 8} bd 2) (getVal {n = 8} bd 5)
                        (getVal {n = 8} bd 6) (getVal {n = 8} bd 7)

            → Pathⁿ' 2 A (getVal {n = 8} bd 2) (getVal {n = 8} bd 5)
                         (getVal {n = 8} bd 6) (getVal {n = 8} bd 7)
Pathⁿ-Pathⁿ'-2 x i j = x j i


-- this takes long time to typecheck (~6s), all the implicit arguments of Pathⁿ have to be
-- infered from value {bd : Boundaryⁿ 3 A},

-- Pathⁿ-3-Cube : ∀ {ℓ} → {A : Type ℓ} → {bd : Boundaryⁿ 3 A}
--             → Pathⁿ 3 A (getVal {n = 26} bd 8) (getVal {n = 26} bd 17)
--                         (getVal {n = 26} bd 20) (getVal {n = 26} bd 23)
--                         (getVal {n = 26} bd 24) (getVal {n = 26} bd 25)
--             → Cube      (getVal {n = 26} bd 8) (getVal {n = 26} bd 17)
--                         (getVal {n = 26} bd 20) (getVal {n = 26} bd 23)
--                         (getVal {n = 26} bd 24) (getVal {n = 26} bd 25)
-- Pathⁿ-3-Cube x = x


-- -- -- this is also slow
-- -- Pathⁿ-Pathⁿ'-3 : ∀ {ℓ} → {A : Type ℓ} → {bd : Boundaryⁿ 3 A}
-- --             → (Pathⁿ 3 A (getVal {n = 26} bd 8) (getVal {n = 26} bd 17)
-- --                         (getVal {n = 26} bd 20) (getVal {n = 26} bd 23)
-- --                         (getVal {n = 26} bd 24) (getVal {n = 26} bd 25))
-- --             ≡ (Pathⁿ' 3 A (getVal {n = 26} bd 24) (getVal {n = 26} bd 25)
-- --                          (getVal {n = 26} bd 20) (getVal {n = 26} bd 23)
-- --                          (getVal {n = 26} bd 8) (getVal {n = 26} bd 17))
-- -- Pathⁿ-Pathⁿ'-3 = refl



-- type checking of this is much faster, not that much infering is needed :
-- providing 6 explicit arguments to Cube do not affects performance of typechecking noticably

InsideOfⁿ-3-Cube : ∀ {ℓ} → {A : Type ℓ} → {bd : Boundaryⁿ 3 A}
            → (InsideOfⁿ {n = 3} {A = A} bd)
                → Cube
                        _ _ _ _ _ _
                        -- (getVal {n = 26} bd 8) (getVal {n = 26} bd 17)
                        -- (getVal {n = 26} bd 20) (getVal {n = 26} bd 23)
                        -- (getVal {n = 26} bd 24) (getVal {n = 26} bd 25)
InsideOfⁿ-3-Cube x = x


-- -- this is slow, but fast function converting those will be created
-- InsideOfⁿ-InsideOfⁿ'-5 : ∀ {ℓ} → {A : Type ℓ} → {bd : Boundaryⁿ 5 A}
--             → (InsideOfⁿ {n = 5} {A = A} bd)
--             → (InsideOfⁿ' {n = 5} {A = A} _)
-- InsideOfⁿ-InsideOfⁿ'-5 x = x


I³-Pathⁿ-3 : ∀ {ℓ} → {A : Type ℓ}
            → (x : I → I → I → A)
            → Pathⁿ 3 A _ _ _ _ _ _
I³-Pathⁿ-3 x = (λ i i₁ i₂ → x i i₁ i₂)


I³-InsideOfⁿ'-3 : ∀ {ℓ} → {A : Type ℓ}
            → (x : I → I → I → A)
            → (InsideOfⁿ {n = 3} {A = A} _)

I³-InsideOfⁿ'-3 x = (λ i i₁ i₂ → x i i₁ i₂)


-- examples bellow do not ilustrate intended way of doing such conversions,
-- the purpose of those is to check if agda is able to accept this definitions without complaining

-- -- those are not fast, but they typecheck in finite time (3-5 s , for each one)
-- -- note that boundary, which is sigma nested 242 times is infered here without problems
--
-- -- those examples typechecks much slower when boundary is provided, even if boundary is
-- -- in  simpliest possible form , this can be observed by filling missing argument in signature
-- -- with C-c C-s, I am little suprised by this, typechecker can produce infered value very fast, but
-- -- after putting this value back in term, typechecking is very slow.

-- I⁵-InsideOfⁿ'-5 : ∀ {ℓ} → {A : Type ℓ}
--             → (x : I → I → I → I → I → A)
--             → (InsideOfⁿ' {n = 5} {A = A} _)
--                                       --  ↑ - try to expand it with C-c C-s,

-- I⁵-InsideOfⁿ'-5 x = (λ i i₁ i₂ i₃ i₄ → x i i₁ i₂ i₃ i₄)

-- I⁵-InsideOfⁿ-5 : ∀ {ℓ} → {A : Type ℓ}
--             → (x : I → I → I → I → I → A)
--             → (InsideOfⁿ {n = 5} {A = A} _)
-- I⁵-InsideOfⁿ-5 x = (λ i i₁ i₂ i₃ i₄ → x i i₁ i₂ i₃ i₄)


-- I⁵-Pathⁿ-5 : ∀ {ℓ} → {A : Type ℓ}
--             → (x : I → I → I → I → I → A)
--             → Pathⁿ 5 A _ _ _ _ _ _ _ _ _ _
-- I⁵-Pathⁿ-5 x = (λ i i₁ i₂ i₃ i₄ → x i i₁ i₂ i₃ i₄)


-- I⁵-Pathⁿ-5 : ∀ {ℓ} → {A : Type ℓ}
--             → (x : I → I → I → I → I → A)
--             → Pathⁿ' 5 A _ _ _ _ _ _ _ _ _ _
-- I⁵-Pathⁿ-5 x = (λ i i₁ i₂ i₃ i₄ → x i i₁ i₂ i₃ i₄)



-- -- typechecking this took ~50s

-- I⁶-InsideOfⁿ'-6 : ∀ {ℓ} → {A : Type ℓ}
--             → (x : I → I → I → I → I → I → A)
--             → (Pathⁿ 6 A _ _ _ _ _ _ _ _ _ _ _ _)
-- I⁶-InsideOfⁿ'-6 x = (λ i i₁ i₂ i₃ i₄ i₅ → x i i₁ i₂ i₃ i₄ i₅ )

