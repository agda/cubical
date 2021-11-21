-- Discrete category over a type A
-- A must be an h-groupoid for the homs to be sets
{-# OPTIONS --safe #-}

module Cubical.Categories.Instances.Discrete where

open import Cubical.Categories.Category.Base
open import Cubical.Categories.Functor.Base
open import Cubical.Foundations.GroupoidLaws
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Prelude

private
  variable
    ℓ ℓC ℓC' : Level

open Category

Discrete : hGroupoid ℓ → Category ℓ ℓ
Discrete A .ob = A .fst
Discrete A .Hom[_,_] a a' = a ≡ a'
Discrete A .id = refl
Discrete A ._⋆_ = _∙_
Discrete A .⋆IdL f = sym (lUnit f)
Discrete A .⋆IdR f = sym (rUnit f)
Discrete A .⋆Assoc f g h = sym (assoc f g h)
Discrete A .isSetHom {x} {y} = A .snd x y


module _ {A : hGroupoid ℓ}
         {C : Category ℓC ℓC'} where
  open Functor
  
  -- Functions f: A → ob C give functors F: Discrete A → C
  DiscFunc : (fst A → ob C) → Functor (Discrete A) C
  DiscFunc f .F-ob = f
  DiscFunc f .F-hom {x} p = subst (λ z → C [ f x , f z ]) p (id C)
  DiscFunc f .F-id {x} = substRefl {B = λ z → C [ f x , f z ]} (id C)
  DiscFunc f .F-seq p q = {!   !}
