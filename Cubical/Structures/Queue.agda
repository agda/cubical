{-# OPTIONS --no-exact-split #-}
module Cubical.Structures.Queue where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Functions.FunExtEquiv
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.SIP

open import Cubical.Structures.Axioms
open import Cubical.Structures.Macro
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
 deqMap : {X Y : Type ℓ} → (X → Y) → Maybe (X × A) → Maybe (Y × A)
 deqMap = map-Maybe ∘ map-fst

 deqMapId : {X : Type ℓ} → ∀ r → deqMap (idfun X) r ≡ r
 deqMapId = map-Maybe-id

 deqMap-∘ :{B C D : Type ℓ}
  (g : C → D) (f : B → C)
  → ∀ r → deqMap {X = C} g (deqMap f r) ≡ deqMap (λ b → g (f b)) r
 deqMap-∘ g f nothing = refl
 deqMap-∘ g f (just (b , a)) = refl

 -- Now we can do Queues:
 rawQueueDesc =
   autoDesc (λ (X : Type ℓ) → X × (A → X → X) × (X → Transp[ Maybe (X × A) ]))

 open Macro ℓ rawQueueDesc public renaming
   ( structure to RawQueueStructure
   ; equiv to RawQueueEquivStr
   ; univalent to rawQueueUnivalentStr
   )

 RawQueue : Type (ℓ-suc ℓ)
 RawQueue = TypeWithStr ℓ RawQueueStructure

 returnOrEnq : {Q : Type ℓ}
  → RawQueueStructure Q → A → Maybe (Q × A) → Q × A
 returnOrEnq (emp , enq , _) a qr =
   Maybe.rec (emp , a) (λ {(q , b) → enq a q , b}) qr

 QueueAxioms : (Q : Type ℓ) → RawQueueStructure Q → Type ℓ
 QueueAxioms Q S@(emp , enq , deq) =
   (isSet Q)
   × (deq emp ≡ nothing)
   × (∀ a q → deq (enq a q) ≡ just (returnOrEnq S a (deq q)))
   × (∀ a a' q q' → enq a q ≡ enq a' q' → (a ≡ a') × (q ≡ q'))
   × (∀ q q' → deq q ≡ deq q' → q ≡ q')

 isPropQueueAxioms : ∀ Q S → isProp (QueueAxioms Q S)
 isPropQueueAxioms Q S =
   isPropΣ isPropIsSet
           (λ Qset → isProp×3 (isOfHLevelDeq Qset _ _)
                              (isPropΠ2 λ _ _ → isOfHLevelDeq Qset _ _)
                              (isPropΠ3 λ _ _ _ → isPropΠ2 λ _ _ → isProp× (Aset _ _) (Qset _ _))
                              (isPropΠ3 λ _ _ _ → Qset _ _))
   where
   isOfHLevelDeq : isSet Q → isOfHLevel 2 (Maybe (Q × A))
   isOfHLevelDeq Qset = isOfHLevelMaybe 0 (isSet× Qset Aset)

 QueueStructure : Type ℓ → Type ℓ
 QueueStructure = AxiomsStructure RawQueueStructure QueueAxioms

 Queue : Type (ℓ-suc ℓ)
 Queue = TypeWithStr ℓ QueueStructure

 QueueEquivStr : StrEquiv QueueStructure ℓ
 QueueEquivStr = AxiomsEquivStr RawQueueEquivStr QueueAxioms

 queueUnivalentStr : UnivalentStr QueueStructure QueueEquivStr
 queueUnivalentStr = axiomsUnivalentStr RawQueueEquivStr isPropQueueAxioms rawQueueUnivalentStr


 FiniteQueueAxioms : (Q : Type ℓ) → QueueStructure Q → Type ℓ
 FiniteQueueAxioms Q ((emp , enq , _) , _) = isEquiv (foldr enq emp)

 isPropFiniteQueueAxioms : ∀ Q S → isProp (FiniteQueueAxioms Q S)
 isPropFiniteQueueAxioms Q S = isPropIsEquiv _

 FiniteQueueStructure : Type ℓ → Type ℓ
 FiniteQueueStructure = AxiomsStructure QueueStructure FiniteQueueAxioms

 FiniteQueue : Type (ℓ-suc ℓ)
 FiniteQueue = TypeWithStr ℓ FiniteQueueStructure

 FiniteQueueEquivStr : StrEquiv FiniteQueueStructure ℓ
 FiniteQueueEquivStr = AxiomsEquivStr QueueEquivStr FiniteQueueAxioms

 finiteQueueUnivalentStr : UnivalentStr FiniteQueueStructure FiniteQueueEquivStr
 finiteQueueUnivalentStr = axiomsUnivalentStr QueueEquivStr isPropFiniteQueueAxioms queueUnivalentStr
