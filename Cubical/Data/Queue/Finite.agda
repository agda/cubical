{-# OPTIONS --no-exact-split #-}
module Cubical.Data.Queue.Finite where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function

open import Cubical.Foundations.SIP
open import Cubical.Structures.Queue

open import Cubical.Data.Maybe
open import Cubical.Data.List
open import Cubical.Data.Sigma
open import Cubical.HITs.PropositionalTruncation

open import Cubical.Data.Queue.1List

-- All finite queues are equal to 1List.Finite

private
  variable
    ℓ : Level

module _ (A : Type ℓ) (Aset : isSet A) where
 open Queues-on A Aset
 private
   module One = 1List A Aset
   open One renaming (Q to Q₁; emp to emp₁; enq to enq₁; deq to deq₁)

 isContrFiniteQueue : isContr FiniteQueue
 isContrFiniteQueue .fst = One.Finite
 isContrFiniteQueue .snd (Q , (S@(emp , enq , deq) , _ , deq-emp , deq-enq , _) , fin) =
   sip finiteQueueUnivalentStr _ _ ((f , fin) , f∘emp , f∘enq , sym ∘ f∘deq)
   where
   deq₁-enq₁ = str One.WithLaws .snd .snd .snd .fst

   f : Q₁ → Q
   f = foldr enq emp

   f∘emp : f emp₁ ≡ emp
   f∘emp = refl

   f∘enq : ∀ a xs → f (enq₁ a xs) ≡ enq a (f xs)
   f∘enq _ _ = refl

   fA : Q₁ × A → Q × A
   fA (q , a) = (f q , a)

   f∘returnOrEnq : (x : A) (xsr : Maybe (List A × A)) →
     returnOrEnq S x (deqMap f xsr) ≡ fA (returnOrEnq (str One.Raw) x xsr)
   f∘returnOrEnq _ nothing = refl
   f∘returnOrEnq _ (just _) = refl

   f∘deq : ∀ xs → deq (f xs) ≡ deqMap f (deq₁ xs)
   f∘deq [] = deq-emp
   f∘deq (x ∷ xs) =
     deq-enq x (f xs)
     ∙ cong (just ∘ returnOrEnq S x) (f∘deq xs)
     ∙ cong just (f∘returnOrEnq x (deq₁ xs))
     ∙ cong (deqMap f) (sym (deq₁-enq₁ x xs))
