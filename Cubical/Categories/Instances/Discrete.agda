-- Discrete category over a type
{-# OPTIONS --safe #-}

module Cubical.Categories.Instances.Discrete where

open import Cubical.Categories.Category.Base using (Precategory)
open import Cubical.Foundations.GroupoidLaws using (lUnit; rUnit; assoc)
open import Cubical.Foundations.Prelude using (Level; Type; _≡_; refl; _∙_; sym)

private
  variable
    ℓ : Level

open Precategory

Discrete : Type ℓ → Precategory ℓ ℓ
Discrete A .ob = A
Discrete A .Hom[_,_] a a' = a ≡ a'
Discrete A .id a = refl
Discrete A ._⋆_ = _∙_
Discrete A .⋆IdL f = sym (lUnit f)
Discrete A .⋆IdR f = sym (rUnit f)
Discrete A .⋆Assoc f g h = sym (assoc f g h)


-- TODO: define functors out of discrete categories
-- Should be equivalent to defining a function A → ob C
-- However I ran into serious unification problems when trying to prove
--   this preserves associativity


-- module _ {A : Type ℓ}
--          {C : Precategory ℓC ℓC'} where
--   open Functor

--   -- Functions f: A → ob C give functors F: Discrete A → C
--   DiscFunc : (A → ob C) → Functor (Discrete A) C
--   DiscFunc f .F-ob = f
--   DiscFunc f .F-hom {x} p = subst (λ z → C [ f x , f z ]) p (id C (f x))
--   DiscFunc f .F-id {x} = substRefl {B = λ z → C [ f x , f z ]} (id C (f x))
--   DiscFunc f .F-seq = {!   !}
--     -- substComposite (λ z → C [ f x , f z ]) p q (id C (f x))      Not right