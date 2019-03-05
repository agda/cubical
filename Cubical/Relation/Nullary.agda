{-# OPTIONS --cubical --safe #-}
module Cubical.Relation.Nullary where

open import Cubical.Core.Everything

open import Cubical.Data.Empty

-- Negation
infix 3 ¬_

¬_ : ∀ {ℓ} → Set ℓ → Set ℓ
¬ A = A → ⊥

isProp¬ : ∀ {ℓ} → (A : Set ℓ) → isProp (¬ A)
isProp¬ A p q i x = isProp⊥ (p x) (q x) i

-- Decidable types (inspired by standard library)
data Dec {ℓ} (P : Set ℓ) : Set ℓ where
  yes : ( p :   P) → Dec P
  no  : (¬p : ¬ P) → Dec P

Stable : ∀ {ℓ} → Set ℓ → Set ℓ
Stable A = ¬ ¬ A → A

Stable¬ : ∀ {ℓ} → {A : Set ℓ} → Stable (¬ A)
Stable¬ ¬¬¬a a = ¬¬¬a ¬¬a
  where
  ¬¬a = λ ¬a → ¬a a

Discrete : ∀ {ℓ} → Set ℓ → Set ℓ
Discrete A = (x y : A) → Dec (x ≡ y)

fromYes : ∀ {ℓ} → {A : Set ℓ} → A → Dec A → A
fromYes _ (yes a) = a
fromYes a (no _) = a

discreteDec : ∀ {ℓ} {A : Set ℓ} (Adis : Discrete A) → Discrete (Dec A)
discreteDec Adis (yes p) (yes p') = lift (Adis p p') -- TODO: monad would simply stuff
  where
    lift : Dec (p ≡ p') → Dec (yes p ≡ yes p')
    lift (yes eq) = yes (cong yes eq)
    lift (no ¬eq) = no λ eq → ¬eq (cong (fromYes p) eq)
discreteDec Adis (yes p) (no ¬p) = ⊥-elim (¬p p)
discreteDec Adis (no ¬p) (yes p) = ⊥-elim (¬p p)
discreteDec {A = A} Adis (no ¬p) (no ¬p') = yes (cong no (isProp¬ A ¬p ¬p'))

isPropDec : ∀ {ℓ} {A : Set ℓ} (Aprop : isProp A) → isProp (Dec A)
isPropDec Aprop (yes a) (yes a') = cong yes (Aprop a a')
isPropDec Aprop (yes a) (no ¬a) = ⊥-elim (¬a a)
isPropDec Aprop (no ¬a) (yes a) = ⊥-elim (¬a a)
isPropDec {A = A} Aprop (no ¬a) (no ¬a') = cong no (isProp¬ A ¬a ¬a')
