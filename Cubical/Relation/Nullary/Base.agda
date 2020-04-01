{-# OPTIONS --cubical --safe #-}
module Cubical.Relation.Nullary.Base where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function

open import Cubical.Data.Empty as ⊥
open import Cubical.HITs.PropositionalTruncation.Base

private
  variable
    ℓ  : Level
    A  : Type ℓ

-- Negation
infix 3 ¬_

¬_ : Type ℓ → Type ℓ
¬ A = A → ⊥

isProp¬ : (A : Type ℓ) → isProp (¬ A)
isProp¬ A p q i x = isProp⊥ (p x) (q x) i

-- Decidable types (inspired by standard library)
data Dec (P : Type ℓ) : Type ℓ where
  yes : ( p :   P) → Dec P
  no  : (¬p : ¬ P) → Dec P

NonEmpty : Type ℓ → Type ℓ
NonEmpty A = ¬ ¬ A

Stable : Type ℓ → Type ℓ
Stable A = NonEmpty A → A

-- reexport propositional truncation for uniformity
open Cubical.HITs.PropositionalTruncation.Base
  using (∥_∥) public

HStable : Type ℓ → Type ℓ
HStable A = ∥ A ∥ → A

Collapsible : Type ℓ → Type ℓ
Collapsible A = Σ[ f ∈ (A → A) ] 2-Constant f

Populated : Type ℓ → Type ℓ
Populated A = (f : Collapsible A) → Fixpoint (f .fst)

PStable : Type ℓ → Type ℓ
PStable A = Populated A → A

Stable≡ : Type ℓ → Type ℓ
Stable≡ A = (x y : A) → Stable (x ≡ y)

HStable≡ : Type ℓ → Type ℓ
HStable≡ A = (x y : A) → HStable (x ≡ y)

Collapsible≡ : Type ℓ → Type ℓ
Collapsible≡ A = (x y : A) → Collapsible (x ≡ y)

PStable≡ : Type ℓ → Type ℓ
PStable≡ A = (x y : A) → PStable (x ≡ y)

Discrete : Type ℓ → Type ℓ
Discrete A = (x y : A) → Dec (x ≡ y)

Stable¬ : Stable (¬ A)
Stable¬ ¬¬¬a a = ¬¬¬a ¬¬a
  where
  ¬¬a = λ ¬a → ¬a a

fromYes : A → Dec A → A
fromYes _ (yes a) = a
fromYes a (no _) = a

discreteDec : (Adis : Discrete A) → Discrete (Dec A)
discreteDec Adis (yes p) (yes p') = decideYes (Adis p p') -- TODO: monad would simply stuff
  where
    decideYes : Dec (p ≡ p') → Dec (yes p ≡ yes p')
    decideYes (yes eq) = yes (cong yes eq)
    decideYes (no ¬eq) = no λ eq → ¬eq (cong (fromYes p) eq)
discreteDec Adis (yes p) (no ¬p) = ⊥.rec (¬p p)
discreteDec Adis (no ¬p) (yes p) = ⊥.rec (¬p p)
discreteDec {A = A} Adis (no ¬p) (no ¬p') = yes (cong no (isProp¬ A ¬p ¬p'))

isPropDec : (Aprop : isProp A) → isProp (Dec A)
isPropDec Aprop (yes a) (yes a') = cong yes (Aprop a a')
isPropDec Aprop (yes a) (no ¬a) = ⊥.rec (¬a a)
isPropDec Aprop (no ¬a) (yes a) = ⊥.rec (¬a a)
isPropDec {A = A} Aprop (no ¬a) (no ¬a') = cong no (isProp¬ A ¬a ¬a')

mapDec : ∀ {B : Type ℓ} → (A → B) → (¬ A → ¬ B) → Dec A → Dec B
mapDec f _ (yes p) = yes (f p)
mapDec _ f (no ¬p) = no (f ¬p)
