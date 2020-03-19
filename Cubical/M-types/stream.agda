{-# OPTIONS --cubical --guardedness #-} --safe


open import Cubical.Data.Unit
open import Cubical.Data.Sum
open import Cubical.Data.Prod
open import Cubical.Data.Nat
open import Cubical.Data.List
open import Cubical.Data.Sigma

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.Isomorphism

open import Cubical.Codata.Stream

open import Cubical.M-types.M-type
open import Cubical.M-types.helper
open import Cubical.M-types.Container
open import Cubical.M-types.Container-M-type

module Cubical.M-types.stream where

--------------------------------------
-- Stream definitions using M-types --
--------------------------------------

stream-S : ∀ A -> Container
stream-S A = (A , (λ _ → Unit))

stream : ∀ (A : Set₀) -> Set₀
stream A = M (stream-S A)

cons : ∀ {A} -> A -> stream A -> stream A
cons x xs = in-fun (x , λ { tt -> xs } )

hd : ∀ {A} -> stream A -> A
hd {A} S = out-fun S .fst

tl : ∀ {A} -> stream A -> stream A
tl {A} S = out-fun S .snd tt

-- --------------------------
-- -- Stream using M-types --
-- --------------------------

stream-pair-M : ∀ A B → stream A × stream B ≡ M (Container-product (stream-S A) (stream-S B))
stream-pair-M A B = M-product-equality (stream-S A) (stream-S B)

Container-product-streams : ∀ A B → Container-product (stream-S A) (stream-S B) ≡ stream-S (A × B)
Container-product-streams A B =
  Container-product (stream-S A) (stream-S B)
    ≡⟨ refl ⟩
  (A × B , λ x → Unit × Unit )
    ≡⟨ (λ i → (A × B) , λ _ → sym diagonal-unit i) ⟩
  (A × B , λ x → Unit )
    ≡⟨ refl ⟩
  stream-S (A × B) ∎

stream-pair : ∀ A B → stream A × stream B ≡ stream (A × B)
stream-pair A B = stream-pair-M A B □ λ i → M (Container-product-streams A B i)

zip : ∀ {A B} → stream A × stream B → stream (A × B)
zip {A} {B} = transport (stream-pair A B)

-------------------------
-- Stream using Limits --
-------------------------

lifting-cons-x : ∀ {A} → (c : ℕ) → (n : ℕ) → (f : ℕ → A) → X (sequence (stream-S A)) n
lifting-cons-x _ 0 _ = lift tt
lifting-cons-x c (suc n) f = f c , λ _ → lifting-cons-x (suc c) n f

lifting-cons-π :
  ∀ {A} (c : ℕ) (n : ℕ) (f : ℕ → A)
  ---------------------
  → π (sequence (stream-S A)) (lifting-cons-x c (suc n) f)
  ≡ (lifting-cons-x c n f)
lifting-cons-π _ 0 _ = refl
lifting-cons-π c (suc n) f i = f c , λ _ → lifting-cons-π (suc c) n f i

cons-2 : ∀ {A} -> ((n : ℕ) → A) -> stream A
cons-2 f = lift-to-M (lifting-cons-x 0) (lifting-cons-π 0) f

cons-2-inv : ∀ {A} -> stream A → (ℕ → A)
cons-2-inv x 0 = hd x
cons-2-inv x (suc n) = cons-2-inv (tl x) n

zip-2 : ∀ {A B} → stream A × stream B → stream (A × B)
zip-2 (x , y) = cons-2 λ n → cons-2-inv x n , cons-2-inv y n

zeros : stream ℕ
zeros = cons-2 λ _ → 0

postulate
  hd-of-cons-2 : ∀ {A} (f : ℕ → A) → hd (cons-2 f) ≡ f 0
