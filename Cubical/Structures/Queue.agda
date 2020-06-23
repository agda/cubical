{-# OPTIONS --cubical --no-import-sorts --no-exact-split --safe #-}
module Cubical.Structures.Queue where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Functions.FunExtEquiv
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.SIP

open import Cubical.Structures.Axiom
open import Cubical.Structures.Macro
open import Cubical.Structures.LeftAction
open import Cubical.Structures.Functorial
open import Cubical.Structures.NAryOp
open import Cubical.Structures.Auto

open import Cubical.Data.Unit
open import Cubical.Data.Maybe as Maybe
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

 -- deq as a structure
 -- First, a few preliminary results that we will need later
 deq-map : {X Y : Type ℓ} → (X → Y) → Maybe (X × A) → Maybe (Y × A)
 deq-map = autoFuncAction (λ (X : Type ℓ) → Maybe (X × A))

 deq-map-id : {X : Type ℓ} → ∀ r → deq-map (idfun X) r ≡ r
 deq-map-id = autoFuncId (λ (X : Type ℓ) → Maybe (X × A))

 deq-map-∘ :{B C D : Type ℓ}
  (g : C → D) (f : B → C)
  → ∀ r → deq-map {X = C} g (deq-map f r) ≡ deq-map (λ b → g (f b)) r
 deq-map-∘ g f nothing = refl
 deq-map-∘ g f (just (b , a)) = refl

 -- Now we can do Queues:
 raw-queue-desc =
   autoDesc (λ (X : Type ℓ) → X × (A → X → X) × (X → Funct[ Maybe (X × A) ]))

 open Macro ℓ raw-queue-desc public renaming
   ( structure to raw-queue-structure
   ; iso to raw-queue-iso
   ; isSNS to RawQueue-is-SNS
   )

 RawQueue : Type (ℓ-suc ℓ)
 RawQueue = TypeWithStr ℓ raw-queue-structure

 returnOrEnq : {Q : Type ℓ}
  → raw-queue-structure Q → A → Maybe (Q × A) → Q × A
 returnOrEnq (emp , enq , _) a qr =
   Maybe.rec (emp , a) (λ {(q , b) → enq a q , b}) qr

 queue-axioms : (Q : Type ℓ) → raw-queue-structure Q → Type ℓ
 queue-axioms Q S@(emp , enq , deq) =
   (isSet Q)
   × (deq emp ≡ nothing)
   × (∀ a q → deq (enq a q) ≡ just (returnOrEnq S a (deq q)))
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
   isOfHLevelDeq : isSet Q → isOfHLevel 2 (Maybe (Q × A))
   isOfHLevelDeq Qset = isOfHLevelMaybe 0 (isSet× Qset Aset)

 queue-structure : Type ℓ → Type ℓ
 queue-structure = AxiomStructure raw-queue-structure queue-axioms

 Queue : Type (ℓ-suc ℓ)
 Queue = TypeWithStr ℓ queue-structure

 queue-iso : StrEquiv queue-structure ℓ
 queue-iso = AxiomEquivStr raw-queue-iso queue-axioms

 Queue-is-SNS : UnivalentStr queue-structure queue-iso
 Queue-is-SNS = axiomUnivalentStr raw-queue-iso isProp-queue-axioms RawQueue-is-SNS


 finite-queue-axioms : (Q : Type ℓ) → queue-structure Q → Type ℓ
 finite-queue-axioms Q ((emp , enq , _) , _) = isEquiv (foldr enq emp)

 isProp-finite-queue-axioms : ∀ Q S → isProp (finite-queue-axioms Q S)
 isProp-finite-queue-axioms Q S = isPropIsEquiv _

 finite-queue-structure : Type ℓ → Type ℓ
 finite-queue-structure = AxiomStructure queue-structure finite-queue-axioms

 FiniteQueue : Type (ℓ-suc ℓ)
 FiniteQueue = TypeWithStr ℓ finite-queue-structure

 finite-queue-iso : StrEquiv finite-queue-structure ℓ
 finite-queue-iso = AxiomEquivStr queue-iso finite-queue-axioms

 FiniteQueue-is-SNS : UnivalentStr finite-queue-structure finite-queue-iso
 FiniteQueue-is-SNS = axiomUnivalentStr queue-iso isProp-finite-queue-axioms Queue-is-SNS
