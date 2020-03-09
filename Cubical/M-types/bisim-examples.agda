{-# OPTIONS --cubical --guardedness #-} --safe

open import Cubical.M-types.itree
open import Cubical.M-types.M
open import Cubical.M-types.Coalg

open import Cubical.Data.Unit
open import Cubical.Data.Nat
open import Cubical.Data.Sum
open import Cubical.Data.Empty
open import Cubical.Data.Bool

open import Cubical.Codata.Stream

open import Cubical.Foundations.Function
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Univalence

open import Cubical.HITs.SetQuotients

module Cubical.M-types.bisim-examples where

-------------------------------
-- The identity bisimulation --
-------------------------------

Δ : ∀ {ℓ} {S : Container {ℓ}} -> bisimulation S M-coalg (_≡_)
αᵣ (Δ {S = S}) = λ a → fst (M-coalg .snd (a .fst)) , (λ b → snd (M-coalg .snd (a .fst)) b , (snd (M-coalg .snd (a .fst)) b , refl))
rel₁ (Δ {S = S}) = funExt λ x → refl
rel₂ (Δ {S = S}) = funExt λ x → λ i → M-coalg .snd (x .snd .snd (~ i))

---------------------------------
-- Quotienting the delay monad --
---------------------------------

mutual
  data delay≈ {R} : (delay R) -> (delay R) -> Set where
    EqNow : ∀ {r} -> ∀ {b} -> delay≈ (in-fun (inr r , b)) (in-fun (inr r , b))
    EqLater : ∀ {t} -> (∞delay≈ (in-fun (out-fun (t tt))) (in-fun (out-fun (t tt)))) -> delay≈ (in-fun (inl tt , t)) (in-fun (inl tt , t))

  record ∞delay≈ {R} (x : delay R) (y : delay R) : Set where
    coinductive
    field
      force : delay≈ x y

open ∞delay≈

data weak-delay≈ {R} : (delay R) -> (delay R) -> Set where
  EqNow : ∀ {r s} -> r ≡ s -> weak-delay≈ (delay-ret r) (delay-ret s)
  EqLater : ∀ {t u} -> weak-delay≈ t u -> weak-delay≈ (delay-tau t) (delay-tau u)
  EqLaterL : ∀ {t u} -> weak-delay≈ t u -> weak-delay≈ (delay-tau t) u
  EqLaterR : ∀ {t u} -> weak-delay≈ t u -> weak-delay≈ t (delay-tau u)

delay≈-in-out : ∀ {R} {x : delay R} -> delay≈ (in-fun (out-fun x)) (in-fun (out-fun x)) -> delay≈ x x
delay≈-in-out {x = x} = λ p → transp (λ i → delay≈ (funExt⁻ in-inverse-out x i) (funExt⁻ in-inverse-out x i)) i0 p

delay≈-in-out-L : ∀ {R} {x y : delay R} -> delay≈ (in-fun (out-fun x)) y -> delay≈ x y
delay≈-in-out-L {x = x} {y = y} = λ p → transp (λ i → delay≈ (funExt⁻ in-inverse-out x i) y) i0 p

delay≈-in-out-R : ∀ {R} {x y : delay R} -> delay≈ x (in-fun (out-fun y)) -> delay≈ x y
delay≈-in-out-R {x = x} {y = y} = λ p → transp (λ i → delay≈ x (funExt⁻ in-inverse-out y i)) i0 p

mutual
  ∞delay≈-refl-helper : ∀ {R} (x₁ : Σ (delay-S R .fst) (λ x₂ → delay-S R .snd x₂ → M (delay-S R))) → ∞delay≈ (in-fun x₁) (in-fun x₁)
  force (∞delay≈-refl-helper x) = delay≈-refl-helper x

  delay≈-refl-helper : ∀ {R} (x₁ : Σ (delay-S R .fst) (λ x₂ → delay-S R .snd x₂ → M (delay-S R))) → delay≈ (in-fun x₁) (in-fun x₁)
  delay≈-refl-helper (inr r , b) = EqNow
  delay≈-refl-helper (inl tt , b) = EqLater (∞delay≈-refl-helper (out-fun (b tt)))

delay≈-refl : ∀ {R} {x} -> delay≈ {R} x x
delay≈-refl {R = R} {x = x} = delay≈-in-out (case out-fun x return (λ x₁ → delay≈ (in-fun x₁) (in-fun x₁)) of delay≈-refl-helper)

-- delay≈-trans : ∀ {R} {x y z} -> delay≈ {R} x y -> delay≈ {R} y z -> delay≈ {R} x z
-- delay≈-trans {x = x} {y = y} {z = z} p q =
--   delay≈-in-out-L (case out-fun x return (λ x₁ → delay≈ (in-fun x₁) z) of λ { (inr r , b) ->
--   delay≈-in-out-R (case out-fun z return (λ z₁ → delay≈ (in-fun (inr r , b)) (in-fun z₁)) of λ { (inr s , b') →
--     case p of λ { EqNow → {!!} }
--   } ) } )

postulate
  delay≈-trans : ∀ {R} {x y z} -> delay≈ {R} x y -> delay≈ {R} y z -> delay≈ {R} x z
  delay≈-sym : ∀ {R} {x y} -> delay≈ {R} x y -> delay≈ {R} y x
  
delay≈-equality-relation : ∀ {R} -> equality-relation (delay≈ {R = R})
delay≈-equality-relation = record { eq-refl = delay≈-refl ; eq-sym = delay≈-sym ; eq-trans = delay≈-trans }

delay-bisimulation : ∀ {R : Set} -> bisimulation (delay-S R) M-coalg (delay≈ {R})
αᵣ (delay-bisimulation) = λ { (a₁ , a₂ , p ) → fst (out-fun a₁) , λ b → snd (out-fun a₁) b , snd (out-fun a₁) b , delay≈-refl }
rel₁ (delay-bisimulation) = funExt λ x → refl
rel₂ (delay-bisimulation {R = R}) = funExt λ x → λ i → out-fun (equality-relation-projection delay≈-equality-relation x (~ i))

delay≈≡≡ : ∀ {A} -> delay≈ {A} ≡ _≡_
delay≈≡≡ = coinduction-is-equality delay≈ delay-bisimulation delay≈-refl
