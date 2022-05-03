{-# OPTIONS --no-exact-split --safe #-}
module Cubical.Data.Queue.1List where

open import Cubical.Foundations.Everything

open import Cubical.Structures.Queue

open import Cubical.Data.Empty as ⊥
open import Cubical.Data.Maybe
open import Cubical.Data.List
open import Cubical.Data.Sigma

module 1List {ℓ} (A : Type ℓ) (Aset : isSet A) where
 open Queues-on A Aset

 Q = List A

 emp : Q
 emp = []

 enq : A → Q → Q
 enq = _∷_

 deq : Q → Maybe (Q × A)
 deq [] = nothing
 deq (x ∷ []) = just ([] , x)
 deq (x ∷ x' ∷ xs) = deqMap (enq x) (deq (x' ∷ xs))

 Raw : RawQueue
 Raw = (Q , emp , enq , deq)

 WithLaws : Queue
 WithLaws = (Q , S , isSetQ , refl , deq-enq , isInjEnq , isInjDeq)
  where
   S = str Raw

   isSetQ : isSet Q
   isSetQ = isOfHLevelList 0 Aset

   deq-enq : ∀ a q → deq (enq a q) ≡ just (returnOrEnq S a (deq q))
   deq-enq a [] = refl
   deq-enq a (x ∷ []) = refl
   deq-enq a (x ∷ x' ∷ xs) =
     subst
       (λ t →
         deqMap (enq a) (deqMap (enq x) t)
         ≡ just (returnOrEnq S a (deqMap (enq x) t)))
       (deq-enq x' xs ⁻¹)
       refl

   isInjEnq : ∀ a a' q q' → enq a q ≡ enq a' q' → (a ≡ a') × (q ≡ q')
   isInjEnq _ _ _ _ p = fst c , ListPath.decode _ _ (snd c)
     where
     c = ListPath.encode _ _ p

   isInjReturnOrEnq : ∀ a a' qr qr'
     → returnOrEnq S a qr ≡ returnOrEnq S a' qr'
     → (a ≡ a') × (qr ≡ qr')
   isInjReturnOrEnq a a' nothing nothing p = cong snd p , refl
   isInjReturnOrEnq a a' nothing (just (q' , b')) p =
     ⊥.rec (lower (ListPath.encode _ _ (cong fst p)))
   isInjReturnOrEnq a a' (just (q , b)) nothing p =
     ⊥.rec (lower (ListPath.encode _ _ (cong fst p)))
   isInjReturnOrEnq a a' (just (q , b)) (just (q' , b')) p =
     fst c , cong just (ΣPathP (ListPath.decode _ _ (snd c) , cong snd p))
     where
     c = ListPath.encode _ _ (cong fst p)

   isInjDeq-lemma : ∀ q q' → MaybePath.Cover (deq q) (deq q') → q ≡ q'
   isInjDeq-lemma [] [] _ = refl
   isInjDeq-lemma [] (y ∷ q') c =
     ⊥.rec (lower (subst (MaybePath.Cover nothing) (deq-enq y q') c))
   isInjDeq-lemma (x ∷ q) [] c =
     ⊥.rec (lower (subst (λ r → MaybePath.Cover r nothing) (deq-enq x q) c))
   isInjDeq-lemma (x ∷ q) (y ∷ q') c =
     cong₂ _∷_ (fst p) (isInjDeq-lemma q q' (MaybePath.encode _ _ (snd p)))
     where
     p : (x ≡ y) × (deq q ≡ deq q')
     p =
       isInjReturnOrEnq _ _ _ _
         (subst (uncurry MaybePath.Cover) (ΣPathP (deq-enq x q , deq-enq y q')) c)

   isInjDeq : ∀ q q' → deq q ≡ deq q' → q ≡ q'
   isInjDeq _ _ p = isInjDeq-lemma _ _ (MaybePath.encode _ _ p)

 Finite : FiniteQueue
 Finite = (Q , str WithLaws , subst isEquiv (sym (funExt foldrCons)) (idIsEquiv _))
