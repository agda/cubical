{-# OPTIONS --cubical --no-exact-split --safe #-}
module Cubical.Structures.Queue where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Functions.FunExtEquiv
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.SIP renaming (SNS-PathP to SNS)

open import Cubical.Structures.Pointed

open import Cubical.Data.Unit
open import Cubical.Data.Sum
open import Cubical.Data.Sigma


-- Developing Queues as a standard notion of structure, see
-- https://github.com/ecavallo/cubical/blob/queue/Cubical/Experiments/Queue.agda
-- for the original development

variable
 ℓ ℓ' : Level



-- We start fixing a set A on which we define what it means for a type Q to have
-- a Queue structure (wrt. A)
module Queues-on (A : Type ℓ) (Aset : isSet A) where
 -- A Queue structure has three components, the empty Queue, a push function and a pop function
 -- We first deal with push and pop as separate structures
 left-action-structure : Type ℓ → Type ℓ
 left-action-structure X = A → X → X

 Left-Action : Type (ℓ-suc ℓ)
 Left-Action = TypeWithStr ℓ left-action-structure

 left-action-iso : StrIso left-action-structure ℓ
 left-action-iso (X , l) (Y , m) e = ∀ a x → e .fst (l a x) ≡ m a (e .fst x)

 Left-Action-is-SNS : SNS {ℓ} left-action-structure left-action-iso
 Left-Action-is-SNS = SNS-≡→SNS-PathP left-action-iso ((λ _ _ → funExt₂Equiv))


 -- Now for the pop-map as a structure
 -- First, a few preliminary results that we will need later
 pop-map-forward : {X Y : Type ℓ} → (X → Y)
                  →  Unit ⊎ (X × A) → Unit ⊎ (Y × A)
 pop-map-forward f (inl tt) = inl tt
 pop-map-forward f (inr (x , a)) = inr (f x , a)


 pop-map-forward-∘ :{B C D : Type ℓ}
  (g : C → D) (f : B → C)
  → ∀ r → pop-map-forward {X = C} g (pop-map-forward f r) ≡ pop-map-forward (λ b → g (f b)) r
 pop-map-forward-∘ g f (inl tt) = refl
 pop-map-forward-∘ g f (inr (b , a)) = refl


 pop-map-lemma : {X : Type ℓ} → idfun (Unit ⊎ (X × A)) ≡ pop-map-forward (idfun X)
 pop-map-lemma {X = X} = funExt γ
  where
   γ : ∀ z → z ≡ pop-map-forward (idfun X) z
   γ (inl tt) = refl
   γ (inr xa) = refl



 pop-structure : Type ℓ → Type ℓ
 pop-structure X = X → Unit ⊎ (X × A)

 Pop : Type (ℓ-suc ℓ)
 Pop = TypeWithStr ℓ pop-structure

 pop-iso : StrIso pop-structure ℓ
 pop-iso (X , p) (Y , q) e = ∀ x → pop-map-forward (e .fst) (p x) ≡ q (e .fst x)

 Pop-is-SNS : SNS {ℓ} pop-structure pop-iso
 Pop-is-SNS = SNS-≡→SNS-PathP pop-iso (λ p q → (subst (λ f → (∀ x → f (p x) ≡ q x) ≃ (p ≡ q)) pop-map-lemma funExtEquiv))



 -- Now we can do Queues:
 queue-structure : Type ℓ → Type ℓ
 queue-structure Q = Q × (A → Q → Q) × (Q → Unit ⊎ (Q × A))

 Queue : Type (ℓ-suc ℓ)
 Queue = TypeWithStr ℓ queue-structure

 queue-iso : StrIso queue-structure ℓ
 queue-iso (Q₁ , emp₁ , push₁ , pop₁) (Q₂ , emp₂ , push₂ , pop₂) e =
            (e .fst emp₁ ≡ emp₂)
          × (∀ a q → e .fst (push₁ a q) ≡ push₂ a (e .fst q))
          × (∀ q → pop-map-forward (e .fst) (pop₁ q) ≡ pop₂ (e .fst q))



 Queue-is-SNS : SNS {ℓ₁ = ℓ} queue-structure queue-iso
 Queue-is-SNS = join-SNS pointed-structure pointed-iso pointed-is-SNS
             (λ X → (left-action-structure X) × (pop-structure X))
             (λ B C e →  (∀ a q → e .fst (B .snd .fst a q) ≡ C .snd .fst a (e .fst q))
                       × (∀ q → pop-map-forward (e .fst) (B .snd .snd q) ≡ C .snd .snd (e .fst q)))
               (join-SNS left-action-structure left-action-iso Left-Action-is-SNS
                         pop-structure         pop-iso         Pop-is-SNS        )




 -- Should we add further axioms for Queues?
 -- Some suggestions:
 queue-axioms : (Q : Type ℓ) → queue-structure Q → Type ℓ
 queue-axioms Q (emp , push , pop) =   (isSet Q)
                                     × (pop emp ≡ inl tt)
                                     × ∀ a → pop (push a emp) ≡ inr (emp , a)
                                     -- etc.
