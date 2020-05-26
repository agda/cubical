{-# OPTIONS --cubical --no-exact-split --safe #-}
module Cubical.Structures.MultiSet where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.SIP renaming (SNS-PathP to SNS)
open import Cubical.Functions.FunExtEquiv

open import Cubical.Structures.Pointed
open import Cubical.Structures.Queue

open import Cubical.Data.Unit
open import Cubical.Data.Sum
open import Cubical.Data.Nat
open import Cubical.Data.Sigma


module _(A : Type ℓ)
        (Aset : isSet A) where

 open Queues-on A Aset

 count-structure : Type ℓ → Type ℓ
 count-structure X = A → X → ℕ

 Count : Type (ℓ-suc ℓ)
 Count = TypeWithStr ℓ count-structure

 count-iso : StrIso count-structure ℓ
 count-iso (X , f) (Y , g) e = ∀ a x → f a x ≡ g a (e .fst x)

 Count-is-SNS : SNS {ℓ} count-structure count-iso
 Count-is-SNS = SNS-≡→SNS-PathP count-iso ((λ _ _ → funExt₂Equiv))

 -- a multi set structure inspired bei Okasaki
 multi-set-structure : Type ℓ → Type ℓ
 multi-set-structure X = X × (A → X → X) × (A → X → ℕ)

 Multi-Set : Type (ℓ-suc ℓ)
 Multi-Set = TypeWithStr ℓ multi-set-structure

 multi-set-iso : StrIso multi-set-structure ℓ
 multi-set-iso (X , emp₁ , insert₁ , memb₁) (Y , emp₂ , insert₂ , memb₂) e =
            (e .fst emp₁ ≡ emp₂)
          × (∀ a q → e .fst (insert₁ a q) ≡ insert₂ a (e .fst q))
          × (∀ a x → memb₁ a x ≡ memb₂ a (e .fst x))


 Multi-Set-is-SNS : SNS {ℓ₁ = ℓ} multi-set-structure multi-set-iso
 Multi-Set-is-SNS =
   join-SNS pointed-iso pointed-is-SNS
            {S₂ = λ X → (left-action-structure X) × (count-structure X)}
            (λ B C e →  (∀ a q → e .fst (B .snd .fst a q) ≡ C .snd .fst a (e .fst q))
                      × (∀ a x → (B .snd .snd a x) ≡ (C .snd .snd a (e .fst x))))
            (join-SNS left-action-iso Left-Action-is-SNS count-iso Count-is-SNS)
