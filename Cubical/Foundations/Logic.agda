{-# OPTIONS --cubical --safe #-}
module Cubical.Foundations.Logic where

import Cubical.Data.Everything as D
open import Cubical.Core.Everything
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism

Ω = Σ Set isProp

[_] : Ω → Set
[ P ] = P .fst

⊥ : Ω
⊥ = D.⊥ , D.isProp⊥

⊤ : Ω
⊤ = D.Unit , λ x y i → D.tt

_⊔′_ : Set → Set → Set
A ⊔′ B = ∥ A D.⊎ B ∥

_⊔_ : Ω → Ω → Ω
A ⊔ B = (∥ [ A ] D.⊎ [ B ] ∥) , propTruncIsProp

inl : ∀ {A B} → A → A ⊔′ B
inl x = ∣ D.inl x ∣

inr : ∀ {A B} → B → A ⊔′ B
inr x = ∣ D.inr x ∣

⊔-elim : ∀ {A B} (C : [ A ⊔ B ] → Ω) → (∀ a → [ C (inl a) ]) → (∀ b → [ C (inr b) ]) → (∀ x → [ C x ])
⊔-elim C f g = (elimPropTrunc (\ x → C _ .snd)
                             \ { (D.inl x) → f x
                               ; (D.inr x) → g x
                               })

Ω≡ : ∀ {a b : Ω} → a .fst ≡ b .fst → a ≡ b
Ω≡ p = ΣProp≡ (\ _ → isPropIsProp) p

pequivToIso : ∀ {a b : Ω} → (a .fst → b .fst) → (b .fst → a .fst) → Iso (a .fst) (b .fst)
pequivToIso {a} {b} f g = iso f g (λ b₁ → b .snd (f (g b₁)) b₁) λ a₁ → a .snd (g (f a₁)) a₁

pequivToPath : ∀ {a b : Ω} → (a .fst → b .fst) → (b .fst → a .fst) → (a .fst) ≡ (b .fst)
pequivToPath {a} {b} f g = isoToPath (pequivToIso {a} {b} f g)

⊔-assoc : ∀ a b c → a ⊔ (b ⊔ c) ≡ (a ⊔ b) ⊔ c
⊔-assoc a b c = Ω≡ (pequivToPath {a ⊔ (b ⊔ c)} {(a ⊔ b) ⊔ c} assoc1 assoc2)
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
⊔-idem a = Ω≡ (pequivToPath {a ⊔ a} {a} (⊔-elim {a} {a} (\ _ → a) (\ x → x) (\ x → x)) inl)

⊔-comm : ∀ a b → a ⊔ b ≡ b ⊔ a
⊔-comm a b = Ω≡ (pequivToPath {a ⊔ b} {b ⊔ a} (⊔-elim {a} {b} (\ _ → (b ⊔ a)) inr inl) (⊔-elim {b} {a} (\ _ → (a ⊔ b)) inr inl))
