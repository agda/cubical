{-# OPTIONS --cubical --safe #-}
module Cubical.Foundations.Logic where

import Cubical.Data.Everything as D
open import Cubical.Core.Everything
open import Cubical.Foundations.HLevels     using (ΣProp≡; isPropIsProp; propPi)
open import Cubical.Foundations.Isomorphism


infixr 7 _⊔_
infixr 7 _⊔′_
infixr 7 _⊓_
infixr 7 _⊓′_
infixr 5 _⇒_
infixr 4 _⇔_

--------------------------------------------------------------------------------
-- The type hProp of mere propositions 

Ω : Set₁
Ω = Σ Set isProp

[_] : Ω → Set
[_] = fst

--------------------------------------------------------------------------------
-- Logical equivalence of mere propositions

Ω≡ : {a b : Ω} → [ a ] ≡ [ b ] → a ≡ b
Ω≡ p = ΣProp≡ (\ _ → isPropIsProp) p

pequivToIso : (a b : Ω) → ([ a ] → [ b ]) → ([ b ] → [ a ]) → Iso [ a ] [ b ]
pequivToIso a b f g = iso f g (λ b₁ → b .snd (f (g b₁)) b₁) λ a₁ → a .snd (g (f a₁)) a₁

pequivToPath : (a b : Ω) → ([ a ] → [ b ]) → ([ b ] → [ a ]) → [ a ] ≡ [ b ]
pequivToPath a b f g = isoToPath (pequivToIso a b f g)

--------------------------------------------------------------------------------
-- True and False types

⊥ : Ω
⊥ = D.⊥ , D.isProp⊥

⊤ : Ω
⊤ = D.Unit , D.isPropUnit

--------------------------------------------------------------------------------
-- Disjunction of mere propositions

_⊔′_ : Set → Set → Set
A ⊔′ B = ∥ A D.⊎ B ∥

_⊔_ : Ω → Ω → Ω
A ⊔ B = [ A ] ⊔′ [ B ] , propTruncIsProp

inl : ∀ {A B} → A → A ⊔′ B
inl x = ∣ D.inl x ∣

inr : ∀ {A B} → B → A ⊔′ B
inr x = ∣ D.inr x ∣

⊔-elim : ∀ A B (C : [ A ⊔ B ] → Ω) → (∀ a → [ C (inl a) ]) → (∀ b → [ C (inr b) ]) → (∀ x → [ C x ])
⊔-elim A B C f g = elimPropTrunc (\ x → C _ .snd) (D.elim-⊎ f g)

--------------------------------------------------------------------------------
-- Conjunction of mere propositions
_⊓′_ : Set → Set → Set
A ⊓′ B = A D.× B

_⊓_ : Ω → Ω → Ω
A ⊓ B = [ A ] ⊓′ [ B ] , D.hLevelProd 1 (A .snd) (B .snd)

⊓-elim : ∀ A (B : [ A ] → Ω) (C : [ A ] → Ω)
       → (∀ a → [ B a ]) → (∀ a → [ C a ]) → (∀ (a : [ A ]) → [ B a ⊓ C a ] )
⊓-elim A B C f g a = f a D., g a
--------------------------------------------------------------------------------
-- Pseudo-complement of mere propositions
¬_ : Ω → Ω
¬ A = ([ A ] → D.⊥) , propPi λ _ → D.isProp⊥

--------------------------------------------------------------------------------
-- Logical implication of mere propositions

_⇒_ : Ω → Ω → Ω
A ⇒ B = ([ A ] → [ B ]) , propPi λ _ → B .snd

--------------------------------------------------------------------------------
-- Logical bi-implication of mere propositions

_⇔_ : Ω → Ω → Ω
A ⇔ B = (A ⇒ B) ⊓ (B ⇒ A)

⇔toPath : ∀ {A B} → [ A ⇔ B ] → A ≡ B
⇔toPath {A = A} {B = B} (A⇒B D., B⇒A) = Ω≡ (pequivToPath A B A⇒B B⇒A)

--------------------------------------------------------------------------------
-- (Ω, ⊔, ⊥) is a bounded ⊔-semilattice

⊔-assoc : ∀ a b c → a ⊔ (b ⊔ c) ≡ (a ⊔ b) ⊔ c
⊔-assoc a b c = ⇔toPath (assoc1 D., assoc2)
 where
   module _ {a b c : Set} where
    assoc1 : a ⊔′ (b ⊔′ c) → (a ⊔′ b) ⊔′ c
    assoc1 ∣ D.inl a ∣ = ∣ D.inl ∣ D.inl a ∣ ∣
    assoc1 ∣ D.inr ∣ D.inl b ∣ ∣ = ∣ D.inl ∣ D.inr b ∣ ∣
    assoc1 ∣ D.inr ∣ D.inr c ∣ ∣ = ∣ D.inr c ∣
    assoc1 ∣ D.inr (squash x y i) ∣ = propTruncIsProp (assoc1 ∣ D.inr x ∣) (assoc1 ∣ D.inr y ∣) i
    assoc1 (squash x y i)           = propTruncIsProp (assoc1 x) (assoc1 y) i

    assoc2 : (a ⊔′ b) ⊔′ c → a ⊔′ (b ⊔′ c)
    assoc2 ∣ D.inr a ∣ = ∣ D.inr ∣ D.inr a ∣ ∣
    assoc2 ∣ D.inl ∣ D.inr b ∣ ∣ = ∣ D.inr ∣ D.inl b ∣ ∣
    assoc2 ∣ D.inl ∣ D.inl c ∣ ∣ = ∣ D.inl c ∣
    assoc2 ∣ D.inl (squash x y i) ∣ = propTruncIsProp (assoc2 ∣ D.inl x ∣) (assoc2 ∣ D.inl y ∣) i
    assoc2 (squash x y i)           = propTruncIsProp (assoc2 x) (assoc2 y) i

⊔-idem : ∀ a → a ⊔ a ≡ a
⊔-idem a = ⇔toPath (⊔-elim a a (\ _ → a) (\ x → x) (\ x → x) D., inl)

⊔-comm : ∀ a b → a ⊔ b ≡ b ⊔ a
⊔-comm a b = ⇔toPath (⊔-elim a b (\ _ → (b ⊔ a)) inr inl D.,  (⊔-elim b a (\ _ → (a ⊔ b)) inr inl))

⊔-identityˡ : ∀ a → ⊥ ⊔ a ≡ a
⊔-identityˡ a = ⇔toPath (⊔-elim ⊥ a (λ _ → a) D.⊥-elim (idfun _) D., inr)

⊔-identityʳ : ∀ a → a ⊔ ⊥ ≡ a
⊔-identityʳ a = ⇔toPath ((⊔-elim a ⊥ (λ _ → a) (λ x → x) D.⊥-elim) D., inl)
  
--------------------------------------------------------------------------------
-- (Ω, ⊓, ⊤) is a bounded ⊓-semilattice

⊓-assoc : ∀ a b c → a ⊓ b ⊓ c ≡ (a ⊓ b) ⊓ c
⊓-assoc a b c =
  ⇔toPath ((λ {(x D., (y D., z)) →  (x D., y) D., z}) D., λ {((x D., y) D., z) → x D., (y D., z) })

⊓-comm : ∀ a b → a ⊓ b ≡ b ⊓ a
⊓-comm a b = ⇔toPath (D.swap D., D.swap)

⊓-idem : ∀ a → a ⊓ a ≡ a
⊓-idem a = ⇔toPath (D.proj₁ D., (λ a → a D., a))

⊓-identityˡ : ∀ a → ⊤ ⊓ a ≡ a 
⊓-identityˡ a = ⇔toPath (D.proj₂ D., λ a → D.tt D., a)

⊓-identityʳ : ∀ a → a ⊓ ⊤ ≡ a
⊓-identityʳ a = ⇔toPath (D.proj₁ D., λ a → a D., D.tt)
