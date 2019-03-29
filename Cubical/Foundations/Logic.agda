{-# OPTIONS --cubical --safe #-}
module Cubical.Foundations.Logic where

import Cubical.Data.Empty as D
import Cubical.Data.Prod  as D
import Cubical.Data.Sum   as D
import Cubical.Data.Unit  as D

open import Cubical.Core.Prelude
open import Cubical.Core.PropositionalTruncation

open import Cubical.Foundations.HLevels     using (hProp; ΣProp≡; isPropIsProp; propPi; isSetHProp) public
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Function

infixr 7 _⊔_
infixr 7 _⊔′_
infixr 7 _⊓_
infixr 7 _⊓′_
infixr 5 _⇒_
infixr 4 _⇔_

--------------------------------------------------------------------------------
-- The type hProp of mere propositions
-- the definition hProp is given in Foundations.HLevels
-- hProp {ℓ} = Σ (Set ℓ) isProp

private
  variable
    ℓ ℓ' ℓ'' : Level
    P Q R : hProp {ℓ}
    A B C : Set ℓ

[_] : hProp → Set ℓ
[_] = fst

infix 30 _≡ₘ_
infix 30 ∥_∥ₚ

∥_∥ₚ : Set ℓ → hProp
∥ A ∥ₚ = ∥ A ∥ , propTruncIsProp

_≡ₘ_ : (x y : A) → hProp
x ≡ₘ y = ∥ x ≡ y ∥ₚ

hProp≡ : [ P ] ≡ [ Q ] → P ≡ Q
hProp≡ p = ΣProp≡ (\ _ → isPropIsProp) p

--------------------------------------------------------------------------------
-- Logical implication of mere propositions

_⇒_ : (A : hProp {ℓ}) → (B : hProp {ℓ'}) → hProp
A ⇒ B = ([ A ] → [ B ]) , propPi λ _ → B .snd


⇔toPath : [ P ⇒ Q ] → [ Q ⇒ P ] → P ≡ Q
⇔toPath {P = P} {Q = Q} P⇒Q Q⇒P = hProp≡ (isoToPath
  (iso P⇒Q Q⇒P (λ b → Q .snd (P⇒Q (Q⇒P b)) b) λ a → P .snd (Q⇒P (P⇒Q a)) a))

--------------------------------------------------------------------------------
-- Mixfix notations for ⇔-toPath
-- see ⊔-identityˡ and ⊔-identityʳ for the difference

⇒∶_⇐∶_ : [ P ⇒ Q ] → [ Q ⇒ P ] → P ≡ Q
⇒∶_⇐∶_ = ⇔toPath
infix 2 ⇒∶_⇐∶_

⇐∶_⇒∶_ : [ Q ⇒ P ] → [ P ⇒ Q ] → P ≡ Q
⇐∶ g ⇒∶ f  = ⇔toPath f g
infix 2 ⇐∶_⇒∶_

--------------------------------------------------------------------------------
-- False and True

⊥ : hProp
⊥ = D.⊥ , λ ()

⊤ : hProp
⊤ = D.Unit , (λ _ _ _ → D.tt)

--------------------------------------------------------------------------------
-- Disjunction of mere propositions

_⊔′_ : Set ℓ → Set ℓ' → Set _
A ⊔′ B = ∥ A D.⊎ B ∥

_⊔_ : hProp {ℓ} → hProp {ℓ'} → hProp
P ⊔ Q = ∥ [ P ] D.⊎ [ Q ] ∥ₚ

inl : A → A ⊔′ B
inl x = ∣ D.inl x ∣

inr : B → A ⊔′ B
inr x = ∣ D.inr x ∣

⊔-elim : (P : hProp {ℓ}) (Q : hProp {ℓ'}) (R : [ P ⊔ Q ] → hProp {ℓ''})
  → (∀ x → [ R (inl x) ]) → (∀ y → [ R (inr y) ]) → (∀ z → [ R z ])
⊔-elim _ _ R P⇒R Q⇒R = elimPropTrunc (snd ∘ R) (D.elim-⊎ P⇒R Q⇒R)

--------------------------------------------------------------------------------
-- Conjunction of mere propositions
_⊓′_ : Set ℓ → Set ℓ' → Set _
A ⊓′ B = A D.× B

_⊓_ : hProp {ℓ} → hProp {ℓ'} → hProp
A ⊓ B = [ A ] ⊓′ [ B ] , D.hLevelProd 1 (A .snd) (B .snd)

⊓-intro : (P : hProp {ℓ}) (Q : [ P ] → hProp {ℓ'}) (R : [ P ] → hProp {ℓ''})
       → (∀ a → [ Q a ]) → (∀ a → [ R a ]) → (∀ (a : [ P ]) → [ Q a ⊓ R a ] )
⊓-intro _ _ _ = D.intro-×
--------------------------------------------------------------------------------
-- Pseudo-complement of mere propositions
¬_ : hProp {ℓ} → hProp
¬ A = ([ A ] → D.⊥) , propPi λ _ → D.isProp⊥

--------------------------------------------------------------------------------
-- Logical bi-implication of mere propositions

_⇔_ : hProp {ℓ} → hProp → hProp
A ⇔ B = (A ≡ B) , isSetHProp A B

--------------------------------------------------------------------------------
-- Universal Quantifier

infix 2 ∀-syntax

∀-syntax : (A → hProp {ℓ}) → hProp
∀-syntax {A = A} P = (∀ x → [ P x ]) , propPi (snd ∘ P)

syntax ∀-syntax {A = A} (λ a → P) = ∀[ a ∶ A ] P

--------------------------------------------------------------------------------
-- Existential Quantifier

infix 2 ∃-syntax

∃-syntax : (A → hProp {ℓ}) → hProp
∃-syntax {A = A} P = ∥ Σ A (fst ∘ P) ∥ₚ

syntax ∃-syntax {A = A} (λ x → P) = ∃[ x ∶ A ] P

--------------------------------------------------------------------------------
-- (hProp, ⊔, ⊥) is a bounded ⊔-semilattice

⊔-assoc : (P : hProp {ℓ}) (Q : hProp {ℓ'}) (R : hProp {ℓ''})
  → P ⊔ (Q ⊔ R) ≡ (P ⊔ Q) ⊔ R
⊔-assoc P Q R =
  ⇒∶ ⊔-elim P (Q ⊔ R) (λ _ → (P ⊔ Q) ⊔ R)
    (inl ∘ inl)
    (⊔-elim Q R (λ _ → (P ⊔ Q) ⊔ R) (inl ∘ inr) inr)

  ⇐∶ assoc2
  where
    assoc2 : (A ⊔′ B) ⊔′ C → A ⊔′ (B ⊔′ C)
    assoc2 ∣ D.inr a ∣ = ∣ D.inr ∣ D.inr a ∣ ∣
    assoc2 ∣ D.inl ∣ D.inr b ∣ ∣ = ∣ D.inr ∣ D.inl b ∣ ∣
    assoc2 ∣ D.inl ∣ D.inl c ∣ ∣ = ∣ D.inl c ∣
    assoc2 ∣ D.inl (squash x y i) ∣ = propTruncIsProp (assoc2 ∣ D.inl x ∣) (assoc2 ∣ D.inl y ∣) i
    assoc2 (squash x y i)           = propTruncIsProp (assoc2 x) (assoc2 y) i

⊔-idem : (P : hProp {ℓ}) → P ⊔ P ≡ P
⊔-idem P =
  ⇒∶ (⊔-elim P P (\ _ → P) (\ x → x) (\ x → x))
  ⇐∶ inl

⊔-comm : (P : hProp {ℓ}) (Q : hProp {ℓ'}) → P ⊔ Q ≡ Q ⊔ P
⊔-comm P Q =
  ⇒∶ (⊔-elim P Q (\ _ → (Q ⊔ P)) inr inl)
  ⇐∶ (⊔-elim Q P (\ _ → (P ⊔ Q)) inr inl)

⊔-identityˡ : (P : hProp {ℓ}) → ⊥ ⊔ P ≡ P
⊔-identityˡ P =
  ⇒∶ (⊔-elim ⊥ P (λ _ → P) (λ ()) (λ x → x))
  ⇐∶ inr

⊔-identityʳ : (P : hProp {ℓ}) → P ⊔ ⊥ ≡ P
⊔-identityʳ P = ⇔toPath (⊔-elim P ⊥ (λ _ → P) (λ x → x) λ ()) inl

--------------------------------------------------------------------------------
-- (hProp, ⊓, ⊤) is a bounded ⊓-lattice

⊓-assoc : (P : hProp {ℓ}) (Q : hProp {ℓ'}) (R : hProp {ℓ''})
  → P ⊓ Q ⊓ R ≡ (P ⊓ Q) ⊓ R
⊓-assoc _ _ _ =
  ⇒∶ (λ {(x D., (y D., z)) →  (x D., y) D., z})
  ⇐∶ (λ {((x D., y) D., z) → x D., (y D., z) })

⊓-comm : (P : hProp {ℓ}) (Q : hProp {ℓ'}) → P ⊓ Q ≡ Q ⊓ P
⊓-comm _ _ = ⇔toPath D.swap D.swap

⊓-idem : (P : hProp {ℓ}) → P ⊓ P ≡ P
⊓-idem _ = ⇔toPath D.proj₁ (λ x → x D., x)

⊓-identityˡ : (P : hProp {ℓ}) → ⊤ ⊓ P ≡ P
⊓-identityˡ _ = ⇔toPath D.proj₂ λ x → D.tt D., x

⊓-identityʳ : (P : hProp {ℓ}) → P ⊓ ⊤ ≡ P
⊓-identityʳ _ = ⇔toPath D.proj₁ λ x → x D., D.tt

--------------------------------------------------------------------------------
-- Distributive laws

⇒-⊓-distrib : (P : hProp {ℓ}) (Q : hProp {ℓ'})(R : hProp {ℓ''})
  → P ⇒ (Q ⊓ R) ≡ (P ⇒ Q) ⊓ (P ⇒ R)
⇒-⊓-distrib _ _ _ =
  ⇒∶ (λ f → (D.proj₁ ∘ f) D., (D.proj₂ ∘ f))
  ⇐∶ (λ { (f D., g) x → f x D., g x})

⊓-⊔-distribˡ : (P : hProp {ℓ}) (Q : hProp {ℓ'})(R : hProp {ℓ''})
  → P ⊓ (Q ⊔ R) ≡ (P ⊓ Q) ⊔ (P ⊓ R)
⊓-⊔-distribˡ P Q R =
  ⇒∶ (λ { (x D., a) → ⊔-elim Q R (λ _ → (P ⊓ Q) ⊔ (P ⊓ R))
        (λ y → ∣ D.inl (x D., y) ∣ )
        (λ z → ∣ D.inr (x D., z) ∣ ) a })

  ⇐∶ ⊔-elim (P ⊓ Q) (P ⊓ R) (λ _ → P ⊓ Q ⊔ R)
       (λ y → D.proj₁ y D., inl (D.proj₂ y))
       (λ z → D.proj₁ z D., inr (D.proj₂ z))

⊔-⊓-distribˡ : (P : hProp {ℓ}) (Q : hProp {ℓ'})(R : hProp {ℓ''})
  → P ⊔ (Q ⊓ R) ≡ (P ⊔ Q) ⊓ (P ⊔ R)
⊔-⊓-distribˡ P Q R =
  ⇒∶ ⊔-elim P (Q ⊓ R) (λ _ → (P ⊔ Q) ⊓ (P ⊔ R) )
    (D.intro-× inl inl) (D.map-× inr inr)

  ⇐∶ (λ { (x D., y) → ⊔-elim P R (λ _ → P ⊔ Q ⊓ R) inl
      (λ z → ⊔-elim P Q (λ _ → P ⊔ Q ⊓ R) inl (λ y → inr (y D., z)) x) y })
