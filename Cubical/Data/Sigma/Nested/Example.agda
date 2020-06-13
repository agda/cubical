{-

This file is included only temporarly to test some features of this module,
and to show problems 

I plan to remove it before final pull request (or maybe move it to the experiments folder?)

-}

{-# OPTIONS --cubical --no-import-sorts --safe #-}

module Cubical.Data.Sigma.Nested.Example where

open import Cubical.Data.Nat

open import Cubical.Data.Bool
open import Cubical.Data.Sigma
open import Cubical.Data.Vec
open import Cubical.Data.List
open import Cubical.Data.Maybe

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
     --          (it is not suprising feature of this implementation,
     --            but my earlier faulty attempt was not able to do this
     --            so I decided to include this test here)
isPrec' {ob} {hom} = n-uncurryᵣ {n = 5} _ (isPrec {ob} {hom}) 


-- Types of holes in nestedΣ are not ugly, they do not mention snd, or fst
-- holes evaluates slighly beter for NestedΣ in default (rightMost) shape



test-isPrec' : IsPrecategory' {!!} {!!}
test-isPrec' = isPrec' ({!!} , {!!} , {!!} , {!!} , {!!})


-- here (C-u C-u C-c C-,) must be used to evaluate types of the holes
-- but after this all mentions of snd, fst , curry and uncurry disapears

test-isPrec'-leftMost : IsPrecategory' {!!} {!!}
test-isPrec'-leftMost = isPrec'
   (Iso.fun (NestedΣ-NestedΣᵣ-Iso (leftMost 4) _)
      ((((({!!}) , {!!}) , {!!}) , {!!}) , {!!}))



-- -- PROBLEM      

-- -- Cube, is chosen as example only becouse it have
-- --    lots of implicit and explicit arguments 


-- -- some problem with this implementations force us to write first
-- -- string of inplicit arguemnts in that way

-- -- note that after the initial string of implicit arguments,
-- -- strings of arguments are cheanged back and forth from implicit and explicit, and
-- -- everything works

extract-Test1 : Type₀ → Sig ℓ-zero 26
extract-Test1 A = extractSig (0 ∷ 8 ∷ 1 ∷ 8 ∷ 1 ∷ 2 ∷ 1 ∷ 2 ∷ 3 ∷ [])
                        (λ {y} {y1} {y2} {y3} {y4} {y5} {y6} {y7} →
                             Cube {A = A} {y} {y1} {y2} {y3} {y4} {y5} {y6} {y7}) 

-- -- In this definition of Cube, only te explicity of first argument is changed from explicit to
-- -- implicit, and now signature can be fully extracted by extractSig function

Cube-first-explicit : {A : Type₀} →
-- ↓ this argument is explicit in this example
  (a₀₀₀ : A) →  {a₀₀₁ : A} {a₀₀₋ : a₀₀₀ ≡ a₀₀₁}
  {a₀₁₀ a₀₁₁ : A} {a₀₁₋ : a₀₁₀ ≡ a₀₁₁}
  {a₀₋₀ : a₀₀₀ ≡ a₀₁₀} {a₀₋₁ : a₀₀₁ ≡ a₀₁₁}
  (a₀₋₋ : Square a₀₀₋ a₀₁₋ a₀₋₀ a₀₋₁)
  {a₁₀₀ a₁₀₁ : A} {a₁₀₋ : a₁₀₀ ≡ a₁₀₁}
  {a₁₁₀ a₁₁₁ : A} {a₁₁₋ : a₁₁₀ ≡ a₁₁₁}
  {a₁₋₀ : a₁₀₀ ≡ a₁₁₀} {a₁₋₁ : a₁₀₁ ≡ a₁₁₁}
  (a₁₋₋ : Square a₁₀₋ a₁₁₋ a₁₋₀ a₁₋₁)
  {a₋₀₀ : a₀₀₀ ≡ a₁₀₀} {a₋₀₁ : a₀₀₁ ≡ a₁₀₁}
  (a₋₀₋ : Square a₀₀₋ a₁₀₋ a₋₀₀ a₋₀₁)
  {a₋₁₀ : a₀₁₀ ≡ a₁₁₀} {a₋₁₁ : a₀₁₁ ≡ a₁₁₁}
  (a₋₁₋ : Square a₀₁₋ a₁₁₋ a₋₁₀ a₋₁₁)
  (a₋₋₀ : Square a₀₋₀ a₁₋₀ a₋₀₀ a₋₁₀)
  (a₋₋₁ : Square a₀₋₁ a₁₋₁ a₋₀₁ a₋₁₁)
  → Type _
Cube-first-explicit a₀₀₀ a₀₋₋ a₁₋₋ a₋₀₋ a₋₁₋ a₋₋₀ a₋₋₁ =
  PathP (λ i → Square (a₋₀₋ i) (a₋₁₋ i) (a₋₋₀ i) (a₋₋₁ i)) a₀₋₋ a₁₋₋

extract-Test2 : Type₀ → Sig ℓ-zero 26
extract-Test2 A = extractSig (1 ∷ 7 ∷ 1 ∷ 8 ∷ 1 ∷ 2 ∷ 1 ∷ 2 ∷ 3 ∷ [])
                        (Cube-first-explicit {A = A})

-- type of holes mentions fst, and snd a lot, but
-- C-u C-u C-c C-, is clearing everytihng

extracted-Test : ∀ A → NestedΣᵣ (extract-Test2 A)   
extracted-Test A = {!!} , {!!} , {!!} , {!!} , {!!} , {!!} , {!!} , {!!} , {!!}
                   , {!!} , {!!} , {!!} , {!!} , {!!} , {!!} , {!!} , {!!} , {!!}
                   , {!!} , {!!} , {!!} , {!!} , {!!} , {!!} , {!!} , {!!} 

-- to uncury Cube it is sufficient to provide the explicity of arguments (and indirectly their number)

uncurried-Cube : (A : Type₀) → _ → Type₀
                           --  ↑ this nested sigma do not containt any unwanted artefacts
                           -- it is large but clear  
uncurried-Cube A = n-uncurryᵣ-conf (impex (1 ∷ 7 ∷ 1 ∷ 8 ∷ 1 ∷ 2 ∷ 1 ∷ 2 ∷ 3 ∷ []))
                     _ ((Cube-first-explicit {A = A}))


-- holes in the argument of ncurried Cube, are in normal form even without using C-u C-u C-c C-,
-- i am not shure why it is not the case for NestedΣ in singature generated by extractSig

uncurried-Cube-test : (A : Type₀) → _
uncurried-Cube-test A = uncurried-Cube A
                          ( {!!} , {!!} , {!!} , {!!} , {!!} , {!!} , {!!} , {!!} , {!!}
                         , {!!} , {!!} , {!!} , {!!} , {!!} , {!!} , {!!} , {!!} , {!!}
                         , {!!} , {!!} , {!!} , {!!} , {!!} , {!!} , {!!} , {!!}) 

-- test of equivalence of function spaces of different explicity
-- both Sig, and uncurried description of the "Target" can be infered
-- (only if description of arguments is correct)

n-exp-imp-≃-test : ((z : ℕ) → (n k : ℕ) → (v₁ v₂ : Vec (Vec ℕ n × Vec ℕ k) z) → v₁ ≡ v₂)
                   ≃
                   ({z n k : ℕ} → (v₁ v₂ : Vec (Vec ℕ n × Vec ℕ k) z) → v₁ ≡ v₂)
n-exp-imp-≃-test = n-exp-imp-≃ (repeat false) (impex (0 ∷ 3 ∷ 2 ∷ [])) _
