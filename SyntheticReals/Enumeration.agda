{-# OPTIONS --cubical --no-import-sorts --allow-unsolved-metas #-}

open import Cubical.Foundations.Everything renaming (_⁻¹ to _⁻¹ᵖ; assoc to ∙-assoc)

open import Cubical.Relation.Nullary.Base -- ¬_
open import Cubical.Relation.Binary.Base -- Rel
open import Cubical.Data.Sigma.Base renaming (_×_ to infixr 4 _×_)
open import Cubical.Data.Empty renaming (elim to ⊥-elim) -- `⊥` and `elim`
open import Function.Base using (_$_)

open import Cubical.Data.Nat hiding (min)
open import Cubical.Data.Nat.Order
-- open import Cubical.Data.Nat.Properties -- using (+-suc; injSuc; snotz; +-comm; +-assoc; +-zero; inj-m+)

open import SyntheticReals.MoreNatProperties

module SyntheticReals.Enumeration
  {ℓ}
  {A   : Type ℓ}
  (f   : A → ℕ)
  (f⁻¹ : ℕ → A)
  (isRetraction : ∀ x → f⁻¹ (f x) ≡ x)
  where

_≤'_ : Rel A A ℓ-zero
a ≤' b = (f a) ≤ (f b)

min' : A → A → A
min' a b = f⁻¹ (min (f a) (f b))

max' : A → A → A
max' a b = f⁻¹ (max (f a) (f b))

max'-sym : ∀ a b → max' a b ≡ max' b a
max'-sym a b with f a ≟ f b | f b ≟ f a
... | lt x | lt y = ⊥-elim {A = λ _ → f⁻¹ (f b) ≡ f⁻¹ (f a)} $  <-asymʷ _ _ x y
... | lt x | eq y = refl
... | lt x | gt y = refl
... | eq x | lt y = refl
... | eq x | eq y = cong f⁻¹ x
... | eq x | gt y = cong f⁻¹ x
... | gt x | lt y = refl
... | gt x | eq y = sym (cong f⁻¹ y)
... | gt x | gt y = ⊥-elim {A = λ _ → f⁻¹ (f a) ≡ f⁻¹ (f b)} $  <-asymʷ _ _ x y

max'-implies-≤'₁ : ∀ a b → a ≤' max' a b
max'-implies-≤'₁ a b with (f a) ≟ (f b)
... | lt (x , p) =  suc x ,  sym (+-suc _ _)  ∙ p ∙ cong f (sym (isRetraction b))
... | eq x = 0 , sym (cong f (isRetraction a) ∙ refl {x = f a})
... | gt x = 0 , sym (cong f (isRetraction a) ∙ refl {x = f a})

max-implies-≤' : ∀ a b → (a ≤' max' a b) × (b ≤' max' a b)
max-implies-≤' a b = max'-implies-≤'₁ a b , transport (λ i → b ≤' max'-sym b a i) (max'-implies-≤'₁ b a)

min'-sym : ∀ a b → min' a b ≡ min' b a
min'-sym a b with f a ≟ f b | f b ≟ f a
... | lt x | lt y = ⊥-elim {A = λ _ → f⁻¹ (f a) ≡ f⁻¹ (f b)} $  <-asymʷ _ _ x y
... | lt x | eq y = sym (cong f⁻¹ y)
... | lt x | gt y = refl
... | eq x | lt y = cong f⁻¹ x
... | eq x | eq y = cong f⁻¹ x
... | eq x | gt y = refl
... | gt x | lt y = refl
... | gt x | eq y = refl
... | gt x | gt y = ⊥-elim {A = λ _ → f⁻¹ (f b) ≡ f⁻¹ (f a)} $  <-asymʷ _ _ x y

min'-implies-≤'₁ : ∀ a b → min' a b ≤' a
min'-implies-≤'₁ a b with (f a) ≟ (f b)
... | lt x = 0 , cong f (isRetraction a) ∙ refl {x = f a}
... | eq x = 0 , cong f (isRetraction a) ∙ refl {x = f a}
... | gt (x , p) = suc x , (λ i → suc (x + cong f (sym (isRetraction b)) (~ i))) ∙ sym (+-suc _ _) ∙ p

min-implies-≤' : ∀ a b → (min' a b ≤' a) × (min' a b ≤' b)
min-implies-≤' a b = min'-implies-≤'₁ a b , transport (λ i → min'-sym b a i ≤' b) (min'-implies-≤'₁ b a)
