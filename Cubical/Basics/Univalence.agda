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

-- Assuming that we have an inverse to ua we can easily prove univalence
module Univalence (au : ∀ {ℓ} {A B : Set ℓ} → A ≡ B → A ≃ B)
                  (auid : ∀ {ℓ} {A B : Set ℓ} → au refl ≡ idEquiv A) where
  thm : ∀ {ℓ} {A B : Set ℓ} → isEquiv au
  thm {A = A} {B = B} =
    isoToIsEquiv {B = A ≃ B} au ua
      (EquivJ (λ _ _ e → au (ua e) ≡ e) (λ X → compPath (cong au uaIdEquiv) (auid {B = B})) _ _)
      (J (λ X p → ua (au p) ≡ p) (compPath (cong ua (auid {B = B})) uaIdEquiv))

pathToEquiv : ∀ {ℓ} {A B : Set ℓ} → A ≡ B → A ≃ B
pathToEquiv p = lineToEquiv (λ i → p i)

pathToEquivRefl : ∀ {ℓ} {A : Set ℓ} → pathToEquiv refl ≡ idEquiv A
pathToEquivRefl {A = A} = equivEq _ _ (λ i x → transp (λ _ → A) i x)

-- Univalence
univalence : ∀ {ℓ} {A B : Set ℓ} → (A ≡ B) ≃ (A ≃ B)
univalence = ( pathToEquiv , Univalence.thm pathToEquiv pathToEquivRefl  )

-- The original map from UniMath/Foundations
eqweqmap : ∀ {ℓ} {A B : Set ℓ} → A ≡ B → A ≃ B
eqweqmap {A = A} e = J (λ X _ → A ≃ X) (idEquiv A) e

eqweqmapid : ∀ {ℓ} {A : Set ℓ} → eqweqmap refl ≡ idEquiv A
eqweqmapid {A = A} = JRefl (λ X _ → A ≃ X) (idEquiv A)

univalenceStatement : ∀ {ℓ} {A B : Set ℓ} → isEquiv (eqweqmap {ℓ} {A} {B})
univalenceStatement = Univalence.thm eqweqmap eqweqmapid

univalenceUAH : ∀ {ℓ} {A B : Set ℓ} → (A ≡ B) ≃ (A ≃ B)
univalenceUAH = ( _ , univalenceStatement )

-- TODO: upstream
record Lift {i j} (A : Set i) : Set (ℓ-max i j) where
  instance constructor lift
  field
    lower : A

open Lift public

LiftEquiv : ∀ {ℓ ℓ'} {A : Set ℓ} → A ≃ Lift {i = ℓ} {j = ℓ'} A
LiftEquiv = isoToEquiv lift lower (λ _ → refl) (λ _ → refl)

univalencePath : ∀ {ℓ} {A B : Set ℓ} → (A ≡ B) ≡ Lift (A ≃ B)
univalencePath = ua (compEquiv univalence LiftEquiv)
