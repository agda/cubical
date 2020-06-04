{-# OPTIONS --cubical --no-exact-split --safe #-}
module Cubical.Data.Queue.1List where

open import Cubical.Foundations.Everything

open import Cubical.Structures.Queue

open import Cubical.Data.Empty as ⊥
open import Cubical.Data.Unit
open import Cubical.Data.Sum
open import Cubical.Data.List
open import Cubical.Data.Sigma

module 1List (A : Type ℓ) (Aset : isSet A) where
 open Queues-on A Aset

 Q = List A

 emp : Q
 emp = []

 enq : A → Q → Q
 enq = _∷_

 deq : Q → Unit ⊎ (Q × A)
 deq [] = inl tt
 deq (x ∷ []) = inr ([] , x)
 deq (x ∷ x' ∷ xs) = deq-map-forward (enq x) (deq (x' ∷ xs))

 Raw : RawQueue
 Raw = (Q , emp , enq , deq)

 WithLaws : Queue
 WithLaws = (Q , S , isSetQ , refl , deq-enq , isInjEnq , isInjDeq)
  where
   S = str Raw

   isSetQ : isSet Q
   isSetQ = isOfHLevelList 0 Aset

   deq-enq : ∀ a q → deq (enq a q) ≡ inr (returnOrEnq S a (deq q))
   deq-enq a [] = refl
   deq-enq a (x ∷ []) = refl
   deq-enq a (x ∷ x' ∷ xs) =
     subst
       (λ t →
         deq-map-forward (enq a) (deq-map-forward (enq x) t)
         ≡ inr (returnOrEnq S a (deq-map-forward (enq x) t)))
       (deq-enq x' xs ⁻¹)
       refl

   isInjEnq : ∀ a a' q q' → enq a q ≡ enq a' q' → (a ≡ a') × (q ≡ q')
   isInjEnq _ _ _ _ p = fst c , ListPath.decode _ _ (snd c)
     where
     c = ListPath.encode _ _ p

   isInjReturnOrEnq : ∀ a a' qr qr'
     → returnOrEnq S a qr ≡ returnOrEnq S a' qr'
     → (a ≡ a') × (qr ≡ qr')
   isInjReturnOrEnq a a' (inl _) (inl _) p = cong snd p , refl
   isInjReturnOrEnq a a' (inl _) (inr (q' , b')) p =
     ⊥.rec (lower (ListPath.encode _ _ (cong fst p)))
   isInjReturnOrEnq a a' (inr (q , b)) (inl _) p =
     ⊥.rec (lower (ListPath.encode _ _ (cong fst p)))
   isInjReturnOrEnq a a' (inr (q , b)) (inr (q' , b')) p =
     fst c , cong inr (ΣPathP (ListPath.decode _ _ (snd c) , cong snd p))
     where
     c = ListPath.encode _ _ (cong fst p)

   isInjDeq-lemma : ∀ q q' → SumPath.Cover (deq q) (deq q') → q ≡ q'
   isInjDeq-lemma [] [] _ = refl
   isInjDeq-lemma [] (y ∷ q') c =
     ⊥.rec (lower (subst (SumPath.Cover (inl tt)) (deq-enq y q') c))
   isInjDeq-lemma (x ∷ q) [] c =
     ⊥.rec (lower (subst (λ r → SumPath.Cover r (inl tt)) (deq-enq x q) c))
   isInjDeq-lemma (x ∷ q) (y ∷ q') c =
     cong₂ _∷_ (fst p) (isInjDeq-lemma q q' (SumPath.encode _ _ (snd p)))
     where
     p : (x ≡ y) × (deq q ≡ deq q')
     p =
       isInjReturnOrEnq _ _ _ _
         (lower (subst (uncurry SumPath.Cover) (ΣPathP (deq-enq x q , deq-enq y q')) c))

   isInjDeq : ∀ q q' → deq q ≡ deq q' → q ≡ q'
   isInjDeq _ _ p = isInjDeq-lemma _ _ (SumPath.encode _ _ p)

 Finite : FiniteQueue
 Finite = (Q , str WithLaws , subst isEquiv (sym (funExt foldrCons)) (idIsEquiv _))
