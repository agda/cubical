{-# OPTIONS --cubical --no-exact-split --safe #-}
module Cubical.Structures.Queue where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Functions.FunExtEquiv
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.SIP renaming (SNS-PathP to SNS)
open import Cubical.Functions.Surjection

open import Cubical.Structures.Pointed

open import Cubical.Data.Unit
open import Cubical.Data.Sum as ⊎
open import Cubical.Data.Sigma
open import Cubical.Data.List


-- Developing Queues as a standard notion of structure, see
-- https://github.com/ecavallo/cubical/blob/queue/Cubical/Experiments/Queue.agda
-- for the original development

variable
 ℓ ℓ' : Level



-- We start fixing a set A on which we define what it means for a type Q to have
-- a Queue structure (wrt. A)
module Queues-on (A : Type ℓ) (Aset : isSet A) where
 -- A Queue structure has three components, the empty Queue, an enqueue function and a dequeue function
 -- We first deal with enq and deq as separate structures
 left-action-structure : Type ℓ → Type ℓ
 left-action-structure X = A → X → X

 Left-Action : Type (ℓ-suc ℓ)
 Left-Action = TypeWithStr ℓ left-action-structure

 left-action-iso : StrIso left-action-structure ℓ
 left-action-iso (X , l) (Y , m) e = ∀ a x → e .fst (l a x) ≡ m a (e .fst x)

 Left-Action-is-SNS : SNS {ℓ} left-action-structure left-action-iso
 Left-Action-is-SNS = SNS-≡→SNS-PathP left-action-iso (λ _ _ → funExt₂Equiv)


 -- Now for the deq-map as a structure
 -- First, a few preliminary results that we will need later
 deq-map-forward : {X Y : Type ℓ} → (X → Y)
                  →  Unit ⊎ (X × A) → Unit ⊎ (Y × A)
 deq-map-forward f (inl tt) = inl tt
 deq-map-forward f (inr (x , a)) = inr (f x , a)

 deq-map-forward-∘ :{B C D : Type ℓ}
  (g : C → D) (f : B → C)
  → ∀ r → deq-map-forward {X = C} g (deq-map-forward f r) ≡ deq-map-forward (λ b → g (f b)) r
 deq-map-forward-∘ g f (inl tt) = refl
 deq-map-forward-∘ g f (inr (b , a)) = refl


 deq-map-id : {X : Type ℓ} → idfun (Unit ⊎ (X × A)) ≡ deq-map-forward (idfun X)
 deq-map-id {X = X} = funExt γ
  where
   γ : ∀ z → z ≡ deq-map-forward (idfun X) z
   γ (inl tt) = refl
   γ (inr xa) = refl

 deq-structure : Type ℓ → Type ℓ
 deq-structure X = X → Unit ⊎ (X × A)

 Deq : Type (ℓ-suc ℓ)
 Deq = TypeWithStr ℓ deq-structure

 deq-iso : StrIso deq-structure ℓ
 deq-iso (X , p) (Y , q) e = ∀ x → deq-map-forward (e .fst) (p x) ≡ q (e .fst x)

 Deq-is-SNS : SNS {ℓ} deq-structure deq-iso
 Deq-is-SNS = SNS-≡→SNS-PathP deq-iso (λ p q → (subst (λ f → (∀ x → f (p x) ≡ q x) ≃ (p ≡ q)) deq-map-id funExtEquiv))



 -- Now we can do Queues:
 raw-queue-structure : Type ℓ → Type ℓ
 raw-queue-structure Q = Q × (A → Q → Q) × (Q → Unit ⊎ (Q × A))

 RawQueue : Type (ℓ-suc ℓ)
 RawQueue = TypeWithStr ℓ raw-queue-structure

 raw-queue-iso : StrIso raw-queue-structure ℓ
 raw-queue-iso (Q₁ , emp₁ , enq₁ , deq₁) (Q₂ , emp₂ , enq₂ , deq₂) e =
   (e .fst emp₁ ≡ emp₂)
   × (∀ a q → e .fst (enq₁ a q) ≡ enq₂ a (e .fst q))
   × (∀ q → deq-map-forward (e .fst) (deq₁ q) ≡ deq₂ (e .fst q))

 RawQueue-is-SNS : SNS raw-queue-structure raw-queue-iso
 RawQueue-is-SNS =
   join-SNS pointed-iso pointed-is-SNS
            {S₂ = λ X → (left-action-structure X) × (deq-structure X)}
            (λ B C e → (∀ a q → e .fst (B .snd .fst a q) ≡ C .snd .fst a (e .fst q))
                     × (∀ q → deq-map-forward (e .fst) (B .snd .snd q) ≡ C .snd .snd (e .fst q)))
            (join-SNS left-action-iso Left-Action-is-SNS deq-iso Deq-is-SNS)



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
   isPropΣ
     isPropIsSet
     (λ Qset →
       isProp×
       (isOfHLevelDeq Qset _ _)
       (isProp×
         (isPropΠ2 λ _ _ → isOfHLevelDeq Qset _ _)
         (isProp×
           (isPropΠ3 λ _ _ _ → isPropΠ2 λ _ _ → isProp× (Aset _ _) (Qset _ _))
           (isPropΠ3 λ _ _ _ → Qset _ _))))
   where
   isOfHLevelDeq : isOfHLevel 2 Q → isOfHLevel 2 (Unit ⊎ (Q × A))
   isOfHLevelDeq Qset = isOfHLevelSum 0 (isOfHLevelUnit 2) (isOfHLevel× 2 Qset Aset)

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
