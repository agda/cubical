{-# OPTIONS --safe #-}
module Cubical.Algebra.OrderedCommMonoid.Instances where

open import Cubical.Foundations.Prelude

open import Cubical.Algebra.OrderedCommMonoid.Base

open import Cubical.Data.Nat
open import Cubical.Data.Nat.Order

ℕ≤+ : OrderedCommMonoid ℓ-zero ℓ-zero
ℕ≤+ = ℕ ,
       record
         { _≤_ = _≤_;
           _·_ = _+_;
           1m = 0;
           isOrderedCommMonoid =
             makeIsOrderedCommMonoid
                isSetℕ
                +-assoc +-zero (λ _ → refl) +-comm
                (λ _ _ → isProp≤) (λ _ → ≤-refl) (λ _ _ _ → ≤-trans) (λ _ _ → ≤-antisym)
                (λ _ _ _ → ≤-+k) (λ _ _ _ → ≤-k+)
         }

ℕ≤· : OrderedCommMonoid ℓ-zero ℓ-zero
ℕ≤· = ℕ ,
       record
         { _≤_ = _≤_ ;
           _·_ = _·_ ;
           1m = 1 ;
           isOrderedCommMonoid =
             makeIsOrderedCommMonoid
               isSetℕ
               ·-assoc ·-identityʳ ·-identityˡ ·-comm
               (λ _ _ → isProp≤) (λ _ → ≤-refl) (λ _ _ _ → ≤-trans) (λ _ _ → ≤-antisym)
               (λ _ _ _ → ≤-·k) lmono
         }
         where lmono : (x y z : ℕ) → x ≤ y → z · x ≤ z · y
               lmono x y z x≤y = subst ((z · x) ≤_) (·-comm y z) (subst (_≤ (y · z)) (·-comm x z) (≤-·k x≤y))
