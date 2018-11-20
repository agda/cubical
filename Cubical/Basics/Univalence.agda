{-

Proof of the standard formulation of the univalence theorem and
various consequences of univalence

- Equivalence induction ([EquivJ])
- Univalence theorem ([univalence])

-}
{-# OPTIONS --cubical #-}
module Cubical.Basics.Univalence where

open import Cubical.Core.Everything

open import Cubical.Basics.NTypes
open import Cubical.Basics.Equiv

contrSinglEquiv : ∀ {ℓ} {A B : Set ℓ} (e : A ≃ B) → (B , idEquiv B) ≡ (A , e)
contrSinglEquiv {A = A} {B = B} e =
  isContr→isProp (EquivContr B) (B , idEquiv B) (A , e)

-- Equivalence induction
EquivJ : ∀ {ℓ ℓ′} (P : (A B : Set ℓ) → (e : B ≃ A) → Set ℓ′)
         → (r : (A : Set ℓ) → P A A (idEquiv A))
         → (A B : Set ℓ) → (e : B ≃ A) → P A B e
EquivJ P r A B e = subst (λ x → P A (x .fst) (x .snd)) (contrSinglEquiv e) (r A)

-- Eliminate equivalences by just looking at the underlying function
elimEquivFun : ∀ {ℓ} (B : Set ℓ) (P : (A : Set ℓ) → (A → B) → Set ℓ)
             → (r : P B (λ x → x))
             → (A : Set ℓ) → (e : A ≃ B) → P A (e .fst)
elimEquivFun B P r a e = subst (λ x → P (x .fst) (x .snd .fst)) (contrSinglEquiv e) r

-- ua is defined in Cubical/Core/Glue
uaIdEquiv : ∀ {ℓ} {A : Set ℓ} → ua (idEquiv A) ≡ refl
uaIdEquiv {A = A} i j = Glue A {φ = i ∨ ~ j ∨ j} (λ _ → A , idEquiv A)

pathToEquiv : ∀ {ℓ} {A B : Set ℓ} → A ≡ B → A ≃ B
pathToEquiv p = lineToEquiv (λ i → p i)

pathToEquivRefl : ∀ {ℓ} {A : Set ℓ} → pathToEquiv refl ≡ idEquiv A
pathToEquivRefl {A = A} = equivEq _ _ (λ i x → transp (λ j → A) i x)

uaPathToEquivRefl : ∀ {ℓ} {A : Set ℓ} → ua (pathToEquiv {A = A} refl) ≡ refl
uaPathToEquivRefl = compPath (cong ua pathToEquivRefl) uaIdEquiv

pathToEquivUAIdEquiv : ∀ {ℓ} (A : Set ℓ) → pathToEquiv (ua (idEquiv A)) ≡ idEquiv A
pathToEquivUAIdEquiv A = compPath (cong pathToEquiv uaIdEquiv) (equivEq _ _ (λ i x → transp (λ _ → A) i x))
  
univEquiv : ∀ {ℓ} (A B : Set ℓ) → isEquiv pathToEquiv
univEquiv A B =
  isoToIsEquiv pathToEquiv ua
               (EquivJ (λ _ _ e → pathToEquiv (ua e) ≡ e) pathToEquivUAIdEquiv B A)
               (J (λ _ p → ua (pathToEquiv p) ≡ p) uaPathToEquivRefl)

univalence : ∀ {ℓ} {A B : Set ℓ} → (A ≡ B) ≃ (A ≃ B)
univalence = ( pathToEquiv , univEquiv _ _ )

module test {ℓ} 
--            (au : (A B : Set ℓ) → A ≡ B → A ≃ B)
  where
  au' : (A B : Set ℓ) → A ≡ B → A ≃ B
  au' A  B e = J (λ (X : Set ℓ) (f : A ≡ X) → A ≃ X) (idEquiv A) e

  auid' : {A B : Set ℓ} → au' _ _ refl ≡ idEquiv A
  auid' {A} = JRefl (λ (X : Set ℓ) (f : A ≡ X) → A ≃ X) (idEquiv A)
  
  univ : {A B : Set ℓ} → isEquiv (au' A B)
  univ {A} {B} = isoToIsEquiv {A = A ≡ B} {B = A ≃ B} (au' A B) ua
     (EquivJ (λ _ _ e → au' _ _ (ua e) ≡ e) (λ X → compPath (cong (au' X X) uaIdEquiv) (auid' {B = B})) _ _)
     (J (λ X p → ua (au' _ _ p) ≡ p) (compPath (cong ua (auid' {B = B})) uaIdEquiv)) 
