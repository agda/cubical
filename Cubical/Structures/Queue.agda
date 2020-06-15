{-# OPTIONS --cubical --no-import-sorts --no-exact-split --safe #-}
module Cubical.Structures.Queue where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Functions.FunExtEquiv
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.SIP renaming (SNS-PathP to SNS)

open import Cubical.Structures.Pointed
open import Cubical.Structures.NAryOp
open import Cubical.Structures.Parameterized
open import Cubical.Structures.LeftAction
open import Cubical.Structures.Functorial

open import Cubical.Data.Unit
open import Cubical.Data.Sum as ⊎
open import Cubical.Data.Sigma
open import Cubical.Data.List


-- Developing Queues as a standard notion of structure, see
-- https://github.com/ecavallo/cubical/blob/queue/Cubical/Experiments/Queue.agda
-- for the original development

private
  variable
   ℓ ℓ' : Level

-- We start fixing a set A on which we define what it means for a type Q to have
-- a Queue structure (wrt. A)
module Queues-on (A : Type ℓ) (Aset : isSet A) where
 -- A Queue structure has three components, the empty Queue, an enqueue function and a dequeue function
 -- We first deal with enq and deq as separate structures

 -- deq-map as a structure
 -- First, a few preliminary results that we will need later
 deq-map : {X Y : Type ℓ} → (X → Y)
                  →  Unit ⊎ (X × A) → Unit ⊎ (Y × A)
 deq-map f (inl tt) = inl tt
 deq-map f (inr (x , a)) = inr (f x , a)

 deq-map-∘ :{B C D : Type ℓ}
  (g : C → D) (f : B → C)
  → ∀ r → deq-map {X = C} g (deq-map f r) ≡ deq-map (λ b → g (f b)) r
 deq-map-∘ g f (inl tt) = refl
 deq-map-∘ g f (inr (b , a)) = refl

 deq-map-id : {X : Type ℓ} → ∀ r → deq-map (idfun X) r ≡ r
 deq-map-id (inl _) = refl
 deq-map-id (inr _) = refl

 deq-structure : Type ℓ → Type ℓ
 deq-structure X = X → Unit ⊎ (X × A)

 Deq : Type (ℓ-suc ℓ)
 Deq = TypeWithStr ℓ deq-structure

 deq-iso : StrIso deq-structure ℓ
 deq-iso = unaryFunIso (functorial-iso deq-map)

 Deq-is-SNS : SNS {ℓ} deq-structure deq-iso
 Deq-is-SNS =
   unaryFunSNS
     (functorial-iso deq-map)
     (functorial-is-SNS deq-map deq-map-id)

 -- Now we can do Queues:
 raw-queue-structure : Type ℓ → Type ℓ
 raw-queue-structure Q = Q × (A → Q → Q) × (Q → Unit ⊎ (Q × A))

 RawQueue : Type (ℓ-suc ℓ)
 RawQueue = TypeWithStr ℓ raw-queue-structure

 raw-queue-iso : StrIso raw-queue-structure ℓ
 raw-queue-iso =
   join-iso pointed-iso (join-iso (left-action-iso A) deq-iso)

 RawQueue-is-SNS : SNS raw-queue-structure raw-queue-iso
 RawQueue-is-SNS =
   join-SNS pointed-iso pointed-is-SNS
            (join-iso (left-action-iso A) deq-iso)
            (join-SNS (left-action-iso A) (Left-Action-is-SNS A) deq-iso Deq-is-SNS)



 returnOrEnq : {Q : Type ℓ}
  → raw-queue-structure Q → A → Unit ⊎ (Q × A) → Q × A
 returnOrEnq (emp , enq , _) a qr =
   ⊎.rec (λ _ → emp , a) (λ {(q , b) → enq a q , b}) qr

 queue-axioms : (Q : Type ℓ) → raw-queue-structure Q → Type ℓ
 queue-axioms Q S@(emp , enq , deq) =
   (isSet Q)
   × (deq emp ≡ inl tt)
   × (∀ a q → deq (enq a q) ≡ inr (returnOrEnq S a (deq q)))
   × (∀ a a' q q' → enq a q ≡ enq a' q' → (a ≡ a') × (q ≡ q'))
   × (∀ q q' → deq q ≡ deq q' → q ≡ q')

 isProp-queue-axioms : ∀ Q S → isProp (queue-axioms Q S)
 isProp-queue-axioms Q S =
   isPropΣ isPropIsSet
           (λ Qset → isProp×3 (isOfHLevelDeq Qset _ _)
                              (isPropΠ2 λ _ _ → isOfHLevelDeq Qset _ _)
                              (isPropΠ3 λ _ _ _ → isPropΠ2 λ _ _ → isProp× (Aset _ _) (Qset _ _))
                              (isPropΠ3 λ _ _ _ → Qset _ _))
   where
   isOfHLevelDeq : isSet Q → isOfHLevel 2 (Unit ⊎ (Q × A))
   isOfHLevelDeq Qset = isSetSum isSetUnit (isSet× Qset Aset)

 queue-structure : Type ℓ → Type ℓ
 queue-structure = add-to-structure raw-queue-structure queue-axioms

 Queue : Type (ℓ-suc ℓ)
 Queue = TypeWithStr ℓ queue-structure

 queue-iso : StrIso queue-structure ℓ
 queue-iso = add-to-iso raw-queue-iso queue-axioms

 Queue-is-SNS : SNS queue-structure queue-iso
 Queue-is-SNS = add-axioms-SNS raw-queue-iso isProp-queue-axioms RawQueue-is-SNS


 finite-queue-axioms : (Q : Type ℓ) → queue-structure Q → Type ℓ
 finite-queue-axioms Q ((emp , enq , _) , _) = isEquiv (foldr enq emp)

 isProp-finite-queue-axioms : ∀ Q S → isProp (finite-queue-axioms Q S)
 isProp-finite-queue-axioms Q S = isPropIsEquiv _

 finite-queue-structure : Type ℓ → Type ℓ
 finite-queue-structure = add-to-structure queue-structure finite-queue-axioms

 FiniteQueue : Type (ℓ-suc ℓ)
 FiniteQueue = TypeWithStr ℓ finite-queue-structure

 finite-queue-iso : StrIso finite-queue-structure ℓ
 finite-queue-iso = add-to-iso queue-iso finite-queue-axioms

 FiniteQueue-is-SNS : SNS finite-queue-structure finite-queue-iso
 FiniteQueue-is-SNS = add-axioms-SNS queue-iso isProp-finite-queue-axioms Queue-is-SNS
