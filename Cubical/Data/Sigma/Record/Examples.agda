{-# OPTIONS --cubical --safe #-}
module Cubical.Data.Sigma.Record.Examples where

open import Cubical.Core.Everything

open import Cubical.Data.Nat
open import Cubical.Data.Fin

open import Cubical.Data.List
open import Cubical.Data.Vec
open import Cubical.Data.Bool
open import Cubical.Data.Sigma

open import Cubical.Foundations.Everything

open import Cubical.Foundations.CartesianKanOps

open import Cubical.HITs.Interval.Base renaming (elim to I-elim ; rec to I-rec)
open import Cubical.HITs.Interval.NCube

open import Cubical.Data.Sigma.Record.Base



someSig : Sig ℓ-zero 9
someSig = ℕ , λ n₁
          → ℕ , λ n₂
          → ((Vec (Fin n₂) n₁) → ℕ) , λ P
          → Vec (Fin n₂) n₁ , λ x
          → Fin n₁ , λ k
          → (P x ≡ toℕ k) , λ eq1
          → ℕ , (λ n₃ → ℕ , (λ n₄ → n₁ + n₂ ≡ n₃ + n₄))



someSigConstructor : _
someSigConstructor = mkConstructor 9 corner0 someSig

someSigConstructor-3-implicit-args : _
someSigConstructor-3-implicit-args = mkConstructor 9 (one ∷ one ∷ zero ∷ one ∷ corner0) someSig
   
rec-from-constructor : Rec 9 someSig
rec-from-constructor = someSigConstructor 1 2 (const 0) (fzero {1} ∷ []) (fzero {zero})
                                 refl 1 2 refl

rec-from-constructor-3-implicit-args : Rec 9 someSig
rec-from-constructor-3-implicit-args = someSigConstructor-3-implicit-args
                         {1} {2} (const 0) {fzero {1} ∷ []} (fzero {zero})
                                   refl 1 2 refl 

l-test : Rec 9 someSig
l-test = 1 , 2 , const 0 , fzero {1} ∷ []  , fzero {zero} , refl , 1 , 2 , refl

lr-test' : Recᵣ 9 someSig
lr-test' = (((((((1 , 2) , (const 0)) , fzero {1} ∷ []) , fzero {zero})
           , refl) , 1) , 2) , refl


Σ-assoc-7 : (x : Type)
              (x₁ : (x₂ : x) → Type)
              (x₂ : (x₃ : x) (x₄ : x₁ x₃) → Type)
              (x₃ : (x₄ : x) (x₅ : x₁ x₄) (x₆ : x₂ x₄ x₅) → Type)
              (x₄ : (x₅ : x) (x₆ : x₁ x₅) (x₇ : x₂ x₅ x₆) (x₈ : x₃ x₅ x₆ x₇) → Type)
              (x₅ : (x₆ : x) (x₇ : x₁ x₆) (x₈ : x₂ x₆ x₇)
                         (x₉ : x₃ x₆ x₇ x₈) (x₁₀ : x₄ x₆ x₇ x₈ x₉) → Type)
              (x₆ : (x₇ : x) (x₈ : x₁ x₇) (x₉ : x₂ x₇ x₈) (x₁₀ : x₃ x₇ x₈ x₉)
                         (x₁₁ : x₄ x₇ x₈ x₉ x₁₀) (x₁₂ : x₅ x₇ x₈ x₉ x₁₀ x₁₁) → Type)
           →
          Σ
           (Σ
            (Σ
             (Σ
              (Σ
               (Σ x
                (λ x₇ → x₁ x₇))
                (λ x₇ → x₂ (fst x₇) (snd x₇)))
                (λ x₇ → x₃ (fst (fst x₇)) (snd (fst x₇)) (snd x₇)))
                (λ x₇ → x₄ (fst (fst (x₇ .fst))) (snd (fst (x₇ .fst))) (snd (x₇ .fst)) (x₇ .snd)))
                (λ x₇ → x₅ (fst (fst (x₇ .fst .fst))) (snd (fst (x₇ .fst .fst)))
                          (snd (x₇ .fst .fst)) (x₇ .fst .snd) (x₇ .snd)))
                (λ x₇ → x₆ (fst (fst (x₇ .fst .fst .fst))) (snd (fst (x₇ .fst .fst .fst)))
                             (snd (x₇ .fst .fst .fst)) (x₇ .fst .fst .snd) (x₇ .fst .snd)
                (x₇ .snd))
       ≃
          Σ x
            (λ x₇ →
               Σ (x₁ x₇)
               (λ x₈ →
                  Σ (x₂ x₇ x₈)
                  (λ x₉ →
                     Σ (x₃ x₇ x₈ x₉)
                     (λ x₁₀ →
                        Σ (x₄ x₇ x₈ x₉ x₁₀)
                        (λ x₁₁ →
                           Σ (x₅ x₇ x₈ x₉ x₁₀ x₁₁) (λ x₁₂ → x₆ x₇ x₈ x₉ x₁₀ x₁₁ x₁₂))))))
Σ-assoc-7 = mk-Σ-assoc-n {ℓ-zero} 7
