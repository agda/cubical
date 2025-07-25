-- Various functions for manipulating hProps.
--
-- This file used to be part of Foundations, but it turned out to be
-- not very useful so moved here. Feel free to upstream content.
--
-- Note that it is often a bad idea to use hProp instead of having the
-- isProp proof separate. The reason is that Agda can rarely infer
-- isProp proofs making it easier to just give them explicitly instead
-- of having them bundled up with the type.
--
module Cubical.Functions.Logic where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Structure
open import Cubical.Foundations.Function
open import Cubical.Foundations.Univalence using (hPropExt)

import Cubical.Data.Empty as ⊥
open import Cubical.Data.Sum as ⊎ using (_⊎_)
open import Cubical.Data.Unit
open import Cubical.Data.Sigma

open import Cubical.HITs.PropositionalTruncation as PropTrunc

open import Cubical.Relation.Nullary hiding (¬_)


--------------------------------------------------------------------------------
-- The type hProp of mere propositions
-- the definition hProp is given in Foundations.HLevels
-- hProp ℓ = Σ (Type ℓ) isProp

private
  variable
    ℓ ℓ' ℓ'' : Level
    P Q R : hProp ℓ
    A B C : Type ℓ

infix 10 ¬_
infixr 8 _⊔_
infixr 8 _⊔′_
infixr 8 _⊓_
infixr 8 _⊓′_
infixr 6 _⇒_
infixr 4 _⇔_
infix 30 _≡ₚ_
infix 30 _≢ₚ_

infix 2 ∃[]-syntax
infix 2 ∃[∶]-syntax

infix 2 ∀[∶]-syntax
infix 2 ∀[]-syntax

infix 2 ⇒∶_⇐∶_
infix 2 ⇐∶_⇒∶_

∥_∥ₚ : Type ℓ → hProp ℓ
∥ A ∥ₚ = ∥ A ∥₁ , isPropPropTrunc

_≡ₚ_ : (x y : A) → hProp _
x ≡ₚ y = ∥ x ≡ y ∥ₚ

hProp≡ : ⟨ P ⟩ ≡ ⟨ Q ⟩ → P ≡ Q
hProp≡ = TypeOfHLevel≡ 1

isProp⟨⟩ : (A : hProp ℓ) → isProp ⟨ A ⟩
isProp⟨⟩ = snd

--------------------------------------------------------------------------------
-- Logical implication of mere propositions

_⇒_ : (A : hProp ℓ) → (B : hProp ℓ') → hProp _
A ⇒ B = (⟨ A ⟩ → ⟨ B ⟩) , isPropΠ λ _ → isProp⟨⟩ B

⇔toPath : ⟨ P ⇒ Q ⟩ → ⟨ Q ⇒ P ⟩ → P ≡ Q
⇔toPath {P = P} {Q = Q} P⇒Q Q⇒P = hProp≡ (hPropExt (isProp⟨⟩ P) (isProp⟨⟩ Q) P⇒Q Q⇒P)

pathTo⇒ : P ≡ Q → ⟨ P ⇒ Q ⟩
pathTo⇒ p x = subst fst  p x

pathTo⇐ : P ≡ Q → ⟨ Q ⇒ P ⟩
pathTo⇐ p x = subst fst (sym p) x

substₚ : {x y : A} (B : A → hProp ℓ) → ⟨ x ≡ₚ y ⇒ B x ⇒ B y ⟩
substₚ {x = x} {y = y} B = PropTrunc.elim (λ _ → isPropΠ λ _ → isProp⟨⟩ (B y)) (subst (fst ∘ B))

--------------------------------------------------------------------------------
-- Mixfix notations for ⇔-toPath
-- see ⊔-identityˡ and ⊔-identityʳ for the difference

⇒∶_⇐∶_ : ⟨ P ⇒ Q ⟩ → ⟨ Q ⇒ P ⟩ → P ≡ Q
⇒∶_⇐∶_ = ⇔toPath

⇐∶_⇒∶_ : ⟨ Q ⇒ P ⟩ → ⟨ P ⇒ Q ⟩ → P ≡ Q
⇐∶ g ⇒∶ f  = ⇔toPath f g
--------------------------------------------------------------------------------
-- False and True

⊥ : hProp _
⊥ = ⊥.⊥ , λ ()

⊤ : ∀ {ℓ} → hProp ℓ
⊤ = Unit* , (λ _ _ _ → tt*)

--------------------------------------------------------------------------------
-- Pseudo-complement of mere propositions

¬_ : hProp ℓ → hProp _
¬ A = (⟨ A ⟩ → ⊥.⊥) , isPropΠ λ _ → ⊥.isProp⊥

_≢ₚ_ : (x y : A) → hProp _
x ≢ₚ y = ¬ x ≡ₚ y

--------------------------------------------------------------------------------
-- Disjunction of mere propositions

_⊔′_ : Type ℓ → Type ℓ' → Type _
A ⊔′ B = ∥ A ⊎ B ∥₁

_⊔_ : hProp ℓ → hProp ℓ' → hProp _
P ⊔ Q = ∥ ⟨ P ⟩ ⊎ ⟨ Q ⟩ ∥ₚ

inl : A → A ⊔′ B
inl x = ∣ ⊎.inl x ∣₁

inr : B → A ⊔′ B
inr x = ∣ ⊎.inr x ∣₁

⊔-elim : (P : hProp ℓ) (Q : hProp ℓ') (R : ⟨ P ⊔ Q ⟩ → hProp ℓ'')
  → (∀ x → ⟨ R (inl x) ⟩) → (∀ y → ⟨ R (inr y) ⟩) → (∀ z → ⟨ R z ⟩)
⊔-elim _ _ R P⇒R Q⇒R = PropTrunc.elim (snd ∘ R) (⊎.elim P⇒R Q⇒R)

--------------------------------------------------------------------------------
-- Conjunction of mere propositions
_⊓′_ : Type ℓ → Type ℓ' → Type _
A ⊓′ B = A × B

_⊓_ : hProp ℓ → hProp ℓ' → hProp _
A ⊓ B = ⟨ A ⟩ ⊓′ ⟨ B ⟩ , isOfHLevelΣ 1 (isProp⟨⟩ A) (\ _ → isProp⟨⟩ B)

⊓-intro : (P : hProp ℓ) (Q : ⟨ P ⟩ → hProp ℓ') (R : ⟨ P ⟩ → hProp ℓ'')
       → (∀ a → ⟨ Q a ⟩) → (∀ a → ⟨ R a ⟩) → (∀ (a : ⟨ P ⟩) → ⟨ Q a ⊓ R a ⟩ )
⊓-intro _ _ _ = \ f g a → f a , g a

--------------------------------------------------------------------------------
-- Logical bi-implication of mere propositions

_⇔_ : hProp ℓ → hProp ℓ' → hProp _
A ⇔ B = (A ⇒ B) ⊓ (B ⇒ A)

⇔-id : (P : hProp ℓ) → ⟨ P ⇔ P ⟩
⇔-id P = (idfun ⟨ P ⟩) , (idfun ⟨ P ⟩)

--------------------------------------------------------------------------------
-- Universal Quantifier


∀[∶]-syntax : (A → hProp ℓ) → hProp _
∀[∶]-syntax {A = A} P = (∀ x → ⟨ P x ⟩) , isPropΠ (isProp⟨⟩ ∘ P)

∀[]-syntax : (A → hProp ℓ) → hProp _
∀[]-syntax {A = A} P = (∀ x → ⟨ P x ⟩) , isPropΠ (isProp⟨⟩ ∘ P)

syntax ∀[∶]-syntax {A = A} (λ a → P) = ∀[ a ∶ A ] P
syntax ∀[]-syntax (λ a → P)          = ∀[ a ] P

--------------------------------------------------------------------------------
-- Existential Quantifier

∃[]-syntax : (A → hProp ℓ) → hProp _
∃[]-syntax {A = A} P = ∥ Σ A (⟨_⟩ ∘ P) ∥ₚ

∃[∶]-syntax : (A → hProp ℓ) → hProp _
∃[∶]-syntax {A = A} P = ∥ Σ A (⟨_⟩ ∘ P) ∥ₚ

syntax ∃[∶]-syntax {A = A} (λ x → P) = ∃[ x ∶ A ] P
syntax ∃[]-syntax (λ x → P) = ∃[ x ] P

--------------------------------------------------------------------------------
-- Decidable mere proposition

Decₚ : (P : hProp ℓ) → hProp ℓ
Decₚ P = Dec ⟨ P ⟩ , isPropDec (isProp⟨⟩ P)

--------------------------------------------------------------------------------
-- Negation commutes with truncation

∥¬A∥≡¬∥A∥ : (A : Type ℓ) → ∥ (A → ⊥.⊥) ∥ₚ ≡ (¬ ∥ A ∥ₚ)
∥¬A∥≡¬∥A∥ _ =
  ⇒∶ (λ ¬A A → PropTrunc.elim (λ _ → ⊥.isProp⊥)
    (PropTrunc.elim (λ _ → isPropΠ λ _ → ⊥.isProp⊥) (λ ¬p p → ¬p p) ¬A) A)
  ⇐∶ λ ¬p → ∣ (λ p → ¬p ∣ p ∣₁) ∣₁

--------------------------------------------------------------------------------
-- (hProp, ⊔, ⊥) is a bounded ⊔-semilattice

⊔-assoc : (P : hProp ℓ) (Q : hProp ℓ') (R : hProp ℓ'')
  → P ⊔ (Q ⊔ R) ≡ (P ⊔ Q) ⊔ R
⊔-assoc P Q R =
  ⇒∶ ⊔-elim P (Q ⊔ R) (λ _ → (P ⊔ Q) ⊔ R)
    (inl ∘ inl)
    (⊔-elim Q R (λ _ → (P ⊔ Q) ⊔ R) (inl ∘ inr) inr)

  ⇐∶ assoc2
  where
    assoc2 : (A ⊔′ B) ⊔′ C → A ⊔′ (B ⊔′ C)
    assoc2 ∣ ⊎.inr a ∣₁              = ∣ ⊎.inr ∣ ⊎.inr a ∣₁ ∣₁
    assoc2 ∣ ⊎.inl ∣ ⊎.inr b ∣₁ ∣₁  = ∣ ⊎.inr ∣ ⊎.inl b ∣₁ ∣₁
    assoc2 ∣ ⊎.inl ∣ ⊎.inl c ∣₁ ∣₁  = ∣ ⊎.inl c ∣₁
    assoc2 ∣ ⊎.inl (squash₁ x y i) ∣₁ = isPropPropTrunc (assoc2 ∣ ⊎.inl x ∣₁) (assoc2 ∣ ⊎.inl y ∣₁) i
    assoc2 (squash₁ x y i)             = isPropPropTrunc (assoc2 x) (assoc2 y) i

⊔-idem : (P : hProp ℓ) → P ⊔ P ≡ P
⊔-idem P =
  ⇒∶ (⊔-elim P P (\ _ → P) (\ x → x) (\ x → x))
  ⇐∶ inl

⊔-comm : (P : hProp ℓ) (Q : hProp ℓ') → P ⊔ Q ≡ Q ⊔ P
⊔-comm P Q =
  ⇒∶ (⊔-elim P Q (\ _ → (Q ⊔ P)) inr inl)
  ⇐∶ (⊔-elim Q P (\ _ → (P ⊔ Q)) inr inl)

⊔-identityˡ : (P : hProp ℓ) → ⊥ ⊔ P ≡ P
⊔-identityˡ P =
  ⇒∶ (⊔-elim ⊥ P (λ _ → P) (λ ()) (λ x → x))
  ⇐∶ inr

⊔-identityʳ : (P : hProp ℓ) → P ⊔ ⊥ ≡ P
⊔-identityʳ P = ⇔toPath (⊔-elim P ⊥ (λ _ → P) (λ x → x) λ ()) inl

--------------------------------------------------------------------------------
-- (hProp, ⊓, ⊤) is a bounded ⊓-lattice

⊓-assoc : (P : hProp ℓ) (Q : hProp ℓ') (R : hProp ℓ'')
  → P ⊓ Q ⊓ R ≡ (P ⊓ Q) ⊓ R
⊓-assoc _ _ _ =
  ⇒∶ (λ {(x , (y , z)) →  (x , y) , z})
  ⇐∶ (λ {((x , y) , z) → x , (y , z) })

⊓-comm : (P : hProp ℓ) (Q : hProp ℓ') → P ⊓ Q ≡ Q ⊓ P
⊓-comm _ _ = ⇔toPath (\ p → p .snd , p .fst) (\ p → p .snd , p .fst)

⊓-idem : (P : hProp ℓ) → P ⊓ P ≡ P
⊓-idem _ = ⇔toPath fst (λ x → x , x)

⊓-identityˡ : (P : hProp ℓ) → ⊤ {ℓ} ⊓ P ≡ P
⊓-identityˡ _ = ⇔toPath snd λ x → tt* , x

⊓-identityʳ : (P : hProp ℓ) → P ⊓ ⊤ {ℓ} ≡ P
⊓-identityʳ _ = ⇔toPath fst λ x → x , tt*

--------------------------------------------------------------------------------
-- Distributive laws

⇒-⊓-distrib : (P : hProp ℓ) (Q : hProp ℓ')(R : hProp ℓ'')
  → P ⇒ (Q ⊓ R) ≡ (P ⇒ Q) ⊓ (P ⇒ R)
⇒-⊓-distrib _ _ _ =
  ⇒∶ (λ f → (fst ∘ f) , (snd ∘ f))
  ⇐∶ (λ { (f , g) x → f x , g x})

⊓-⊔-distribˡ : (P : hProp ℓ) (Q : hProp ℓ')(R : hProp ℓ'')
  → P ⊓ (Q ⊔ R) ≡ (P ⊓ Q) ⊔ (P ⊓ R)
⊓-⊔-distribˡ P Q R =
  ⇒∶ (λ { (x , a) → ⊔-elim Q R (λ _ → (P ⊓ Q) ⊔ (P ⊓ R))
        (λ y → ∣ ⊎.inl (x , y) ∣₁ )
        (λ z → ∣ ⊎.inr (x , z) ∣₁ ) a })

  ⇐∶ ⊔-elim (P ⊓ Q) (P ⊓ R) (λ _ → P ⊓ Q ⊔ R)
       (λ y → fst y , inl (snd y))
       (λ z → fst z , inr (snd z))

⊔-⊓-distribˡ : (P : hProp ℓ) (Q : hProp ℓ')(R : hProp ℓ'')
  → P ⊔ (Q ⊓ R) ≡ (P ⊔ Q) ⊓ (P ⊔ R)
⊔-⊓-distribˡ P Q R =
  ⇒∶ ⊔-elim P (Q ⊓ R) (λ _ → (P ⊔ Q) ⊓ (P ⊔ R) )
    (\ x → inl x , inl x) (\ p → inr (p .fst) , inr (p .snd))

  ⇐∶ (λ { (x , y) → ⊔-elim P R (λ _ → P ⊔ Q ⊓ R) inl
      (λ z → ⊔-elim P Q (λ _ → P ⊔ Q ⊓ R) inl (λ y → inr (y , z)) x) y })

⊓-∀-distrib :  (P : A → hProp ℓ) (Q : A → hProp ℓ')
  → (∀[ a ∶ A ] P a) ⊓ (∀[ a ∶ A ] Q a) ≡ (∀[ a ∶ A ] (P a ⊓ Q a))
⊓-∀-distrib P Q =
  ⇒∶ (λ {(p , q) a → p a , q a})
  ⇐∶ λ pq → (fst ∘ pq ) , (snd ∘ pq)
