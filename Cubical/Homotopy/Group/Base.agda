{-# OPTIONS --safe --experimental-lossy-unification #-}
module Cubical.Homotopy.Group.Base where

open import Cubical.Homotopy.Loopspace

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Pointed
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.GroupoidLaws renaming (assoc to ∙assoc)
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Function
open import Cubical.Foundations.Path
open import Cubical.Foundations.Transport

open import Cubical.HITs.SetTruncation
  renaming (rec to sRec ; rec2 to sRec2 ; elim to sElim
          ; elim2 to sElim2 ; elim3 to sElim3 ; map to sMap)
open import Cubical.HITs.Sn
open import Cubical.Data.Bool
open import Cubical.HITs.Susp
open import Cubical.HITs.S1
open import Cubical.Data.Sigma
open import Cubical.Data.Nat

open import Cubical.Algebra.Group
open import Cubical.Algebra.Semigroup
open import Cubical.Algebra.Monoid

open Iso
open IsGroup
open IsSemigroup
open IsMonoid
open GroupStr


{- Homotopy group -}
π : ∀ {ℓ} (n : ℕ) (A : Pointed ℓ) → Type ℓ
π n A = ∥ typ ((Ω^ n) A) ∥₂

{- Alternative formulation. This will be given a group structure in
  the Properties file -}
π' : ∀ {ℓ} (n : ℕ) (A : Pointed ℓ) → Type ℓ
π' n A = ∥ S₊∙ n →∙ A ∥₂

{- π as a group -}
1π : ∀ {ℓ} (n : ℕ) {A : Pointed ℓ} → π n A
1π zero {A = A} = ∣ pt A ∣₂
1π (suc n) = ∣ refl ∣₂

·π : ∀ {ℓ} (n : ℕ) {A : Pointed ℓ} → π (suc n) A → π (suc n) A → π (suc n) A
·π n = sRec2 squash₂ λ p q → ∣ p ∙ q ∣₂

-π : ∀ {ℓ} (n : ℕ) {A : Pointed ℓ} → π (suc n) A → π (suc n) A
-π n = sMap sym

π-rUnit : ∀ {ℓ} (n : ℕ) {A : Pointed ℓ} (x : π (suc n) A)
        → (·π n x (1π (suc n))) ≡ x
π-rUnit n = sElim (λ _ → isSetPathImplicit) λ p i → ∣ rUnit p (~ i) ∣₂

π-lUnit : ∀ {ℓ} (n : ℕ) {A : Pointed ℓ} (x : π (suc n) A)
        → (·π n (1π (suc n)) x) ≡ x
π-lUnit n = sElim (λ _ → isSetPathImplicit) λ p i → ∣ lUnit p (~ i) ∣₂

π-rCancel : ∀ {ℓ} (n : ℕ) {A : Pointed ℓ} (x : π (suc n) A)
        → (·π n x (-π n x)) ≡ 1π (suc n)
π-rCancel n = sElim (λ _ → isSetPathImplicit) λ p i → ∣ rCancel p i ∣₂

π-lCancel : ∀ {ℓ} (n : ℕ) {A : Pointed ℓ} (x : π (suc n) A)
        → (·π n (-π n x) x) ≡ 1π (suc n)
π-lCancel n = sElim (λ _ → isSetPathImplicit) λ p i → ∣ lCancel p i ∣₂

π-assoc : ∀ {ℓ} (n : ℕ) {A : Pointed ℓ} (x y z : π (suc n) A)
        → ·π n x (·π n y z) ≡ ·π n (·π n x y) z
π-assoc n = sElim3 (λ _ _ _ → isSetPathImplicit) λ p q r i → ∣ ∙assoc p q r i ∣₂

π-comm : ∀ {ℓ} (n : ℕ) {A : Pointed ℓ} (x y : π (suc (suc n)) A)
        → ·π (suc n) x y ≡ ·π (suc n) y x
π-comm n = sElim2 (λ _ _ → isSetPathImplicit) λ p q i → ∣ EH n p q i ∣₂

πGr : ∀ {ℓ} (n : ℕ) (A : Pointed ℓ) → Group ℓ
fst (πGr n A) = π (suc n) A
1g (snd (πGr n A)) = 1π (suc n)
GroupStr._·_ (snd (πGr n A)) = ·π n
inv (snd (πGr n A)) = -π n
is-set (isSemigroup (isMonoid (isGroup (snd (πGr n A))))) = squash₂
assoc (isSemigroup (isMonoid (isGroup (snd (πGr n A))))) = π-assoc n
identity (isMonoid (isGroup (snd (πGr n A)))) x = (π-rUnit n x) , (π-lUnit n x)
inverse (isGroup (snd (πGr n A))) x = (π-rCancel n x) , (π-lCancel n x)

-- Group operations on π'.
-- We define the corresponding structure on the untruncated
-- (S₊∙ n →∙ A).

∙Π : ∀ {ℓ} {A : Pointed ℓ} {n : ℕ}
  → (S₊∙ n →∙ A)
  → (S₊∙ n →∙ A)
  → (S₊∙ n →∙ A)
∙Π {A = A} {n = zero} p q = (λ _ → pt A) , refl
fst (∙Π {A = A} {n = suc zero} (f , p) (g , q)) base = pt A
fst (∙Π {A = A} {n = suc zero} (f , p) (g , q)) (loop j) =
  ((sym p ∙∙ cong f loop ∙∙ p) ∙ (sym q ∙∙ cong g loop ∙∙ q)) j
snd (∙Π {A = A} {n = suc zero} (f , p) (g , q)) = refl
fst (∙Π {A = A} {n = suc (suc n)} (f , p) (g , q)) north = pt A
fst (∙Π {A = A} {n = suc (suc n)} (f , p) (g , q)) south = pt A
fst (∙Π {A = A} {n = suc (suc n)} (f , p) (g , q)) (merid a j) =
   ((sym p ∙∙ cong f (merid a ∙ sym (merid (ptSn (suc n)))) ∙∙ p)
  ∙ (sym q ∙∙ cong g (merid a ∙ sym (merid (ptSn (suc n)))) ∙∙ q)) j
snd (∙Π {A = A} {n = suc (suc n)} (f , p) (g , q)) = refl

-Π : ∀ {ℓ} {A : Pointed ℓ} {n : ℕ}
  → (S₊∙ n →∙ A)
  → (S₊∙ n →∙ A)
-Π {n = zero} f = f
fst (-Π {A = A} {n = suc zero} f) base = fst f base
fst (-Π {A = A} {n = suc zero} f) (loop j) = fst f (loop (~ j))
snd (-Π {A = A} {n = suc zero} f) = snd f
fst (-Π {A = A} {n = suc (suc n)} f) north = fst f north
fst (-Π {A = A} {n = suc (suc n)} f) south = fst f north
fst (-Π {A = A} {n = suc (suc n)} f) (merid a j) =
 fst f ((merid a ∙ sym (merid (ptSn _))) (~ j))
snd (-Π {A = A} {n = suc (suc n)} f) = snd f
