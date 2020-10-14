{-# OPTIONS --cubical --no-import-sorts #-}

module SyntheticReals.MoreLogic.Definitions where -- hProp logic

open import Cubical.Foundations.Everything renaming (_⁻¹ to _⁻¹ᵖ; assoc to ∙-assoc)
open import Cubical.Data.Sum.Base renaming (_⊎_ to infixr 4 _⊎_)
open import Cubical.Relation.Nullary.Base renaming (¬_ to ¬ᵗ_)
open import Cubical.Foundations.Logic renaming (inl to inlᵖ; inr to inrᵖ)
open import Cubical.Data.Empty renaming (elim to ⊥-elim) renaming (⊥ to ⊥⊥) -- `⊥` and `elim`

import Cubical.Data.Empty as Empty
open import Cubical.Data.Unit.Base

open import SyntheticReals.MoreLogic.Reasoning
open import SyntheticReals.Utils

-- lifted versions of ⊥ and ⊤

hPropRel : ∀ {ℓ} (A B : Type ℓ) (ℓ' : Level) → Type (ℓ-max ℓ (ℓ-suc ℓ'))
hPropRel A B ℓ' = A → B → hProp ℓ'

isSetIsProp : ∀{ℓ} {A : Type ℓ} → isProp (isSet A)
isSetIsProp is-set₀ is-set₁ = funExt (λ x → funExt λ y → isPropIsProp (is-set₀ x y) (is-set₁ x y))

isSetᵖ : ∀{ℓ} (A : Type ℓ) → hProp ℓ
isSetᵖ A = isSet A , isSetIsProp

-- hProp-syntax for Σ types of hProps to omit propositional truncation
-- this should be equivalent to ∃! from the standard library but ∃! is not an hProp
-- proof sketch:
--   `∃! A B = isContr (Σ A B) = Σ[ x ∈ Σ A B ] ∀(  y : Σ A B) → x ≡ y`
--   `Σᵖ[]-syntax A B          ≈ Σ[ c ∈ Σ A B ] ∀(x y : Σ A B) → x ≡ y`
-- NOTE: we also have isProp→Iso in `Cubical.Foundations.Isomorphism`

Σᵖ[]-syntax : ∀{ℓ ℓ'} → {A : hProp ℓ'} → ([ A ] → hProp ℓ) → hProp _
Σᵖ[]-syntax {A = A} P = Σ [ A ] ([_] ∘ P) , isPropΣ (isProp[] A) (isProp[] ∘ P)

syntax  Σᵖ[]-syntax (λ x → P) = Σᵖ[ x ] P
infix 2 Σᵖ[]-syntax

Σᵖ[∶]-syntax : ∀{ℓ ℓ'} → {A : hProp ℓ'} → ([ A ] → hProp ℓ) → hProp _
Σᵖ[∶]-syntax {A = A} P = Σ [ A ] ([_] ∘ P) , isPropΣ (isProp[] A) (isProp[] ∘ P)

syntax  Σᵖ[∶]-syntax {A = A} (λ x → P) = Σᵖ[ x ∶ A ] P
infix 2 Σᵖ[∶]-syntax

isProp⊎ˡ : ∀{ℓ ℓ'} {A : Type ℓ} {B : Type ℓ'} → isProp A → isProp B → (A → ¬ᵗ B) → isProp (A ⊎ B)
isProp⊎ˡ pA pB A⇒¬B (inl x) (inl y) = cong inl (pA x y)
isProp⊎ˡ pA pB A⇒¬B (inr x) (inr y) = cong inr (pB x y)
isProp⊎ˡ pA pB A⇒¬B (inl x) (inr y) = ⊥-elim (A⇒¬B x y)
isProp⊎ˡ pA pB A⇒¬B (inr x) (inl y) = ⊥-elim (A⇒¬B y x)

-- hProp-syntax for disjoint unions to omit propositional truncation
⊎ᵖ-syntax : ∀{ℓ ℓ'} (P : hProp ℓ) (Q : hProp ℓ') → {[ P ] → ¬ᵗ [ Q ]} → hProp _
⊎ᵖ-syntax P Q {P⇒¬Q} = ([ P ] ⊎ [ Q ]) , isProp⊎ˡ (isProp[] P) (isProp[] Q) P⇒¬Q

syntax ⊎ᵖ-syntax P Q {P⇒¬Q} = [ P⇒¬Q ] P ⊎ᵖ Q

{-# DISPLAY ⊎ᵖ-syntax a b = a ⊎ b #-}

-- hProp-syntax for equality on sets to omit propositional truncation
≡ˢ-syntax : {ℓ : Level} {A : Type ℓ} → A → A → {isset : isSet A} → hProp ℓ
≡ˢ-syntax a b {isset} = (a ≡ b) , isset a b

syntax ≡ˢ-syntax a b {isset} = [ isset ] a ≡ˢ b

infix 1 ⊎ᵖ-syntax
infix 1 ≡ˢ-syntax

{-# DISPLAY ≡ˢ-syntax a b = a ≡ b #-}

-- pretty print ∀-syntax from cubical standard library
{-# DISPLAY ∀[]-syntax {A = A} P = P #-}
-- {-# DISPLAY ∀[]-syntax {A = A} P = ∃ P #-}
-- {-# DISPLAY ∀[]-syntax (λ a → P) = ∀[ a ] P #-}
-- {-# DISPLAY ∃[]-syntax (λ x → P) = ∃[ x ] P #-}

-- ∀-syntax to quantify over hProps (without needing to `[_]` them)
∀ᵖ[∶]-syntax : ∀{ℓ ℓ'} {A : hProp ℓ'} → ([ A ] → hProp ℓ) → hProp (ℓ-max ℓ ℓ')
∀ᵖ[∶]-syntax {A = A} P = (∀ x → [ P x ]) , isPropΠ (isProp[] ∘ P)

syntax ∀ᵖ[∶]-syntax {A = A} (λ a → P) = ∀ᵖ[ a ∶ A ] P
infix 2 ∀ᵖ[∶]-syntax

{-# DISPLAY ∀ᵖ[∶]-syntax {A = A} P = P #-}

-- isPropΠ for a function with an instance argument
isPropΠⁱ : ∀{ℓ ℓ'} {A : Type ℓ} {B : {{p : A}} → Type ℓ'} (h : (x : A) → isProp (B {{x}})) → isProp ({{x : A}} → B {{x}})
isPropΠⁱ h f g i {{x}} = (h x) (f {{x}}) (g {{x}}) i

-- ∀-syntax to quantify over hProps (without needing to `[_]` them) which produces an intance argument
∀ᵖ〚∶〛-syntax : ∀{ℓ ℓ'} {A : hProp ℓ'} → ([ A ] → hProp ℓ) → hProp (ℓ-max ℓ ℓ')
∀ᵖ〚∶〛-syntax {A = A} P = (∀ {{x}} → [ P x ]) , isPropΠⁱ (isProp[] ∘ P)

syntax ∀ᵖ〚∶〛-syntax {A = A} (λ a → P) = ∀ᵖ〚 a ∶ A 〛 P
infix 2 ∀ᵖ〚∶〛-syntax

!isProp : ∀{ℓ} {P : Type ℓ} → isProp P → isProp (! P)
!isProp is-prop (!! x) (!! y) = subst (λ z → (!! x) ≡ (!! z)) (is-prop x y) refl

∀ᵖ!〚∶〛-syntax : ∀{ℓ ℓ'} {A : hProp ℓ'} → (! [ A ] → hProp ℓ) → hProp (ℓ-max ℓ ℓ')
∀ᵖ!〚∶〛-syntax {A = A} P = (∀ {{x}} → [ P x ]) , isPropΠⁱ (λ p → isProp[] (P (p))) -- isPropΠⁱ (isProp[] ∘ P) -- isPropΠⁱ (!isProp ∘ isProp[] ∘ P) --  --

syntax ∀ᵖ!〚∶〛-syntax {A = A} (λ a → P) = ∀ᵖ!〚 a ∶ A 〛 P
infix 2 ∀ᵖ!〚∶〛-syntax

{-# DISPLAY ∀ᵖ[∶]-syntax {A = A} P = P #-}

-- ∀-syntax which produces an intance argument
∀〚∶〛-syntax : ∀{ℓ ℓ'} {A : Type ℓ'} → (A → hProp ℓ) → hProp _
∀〚∶〛-syntax {A = A} P = (∀ {{x}} → [ P x ]) , isPropΠⁱ (isProp[] ∘ P)

syntax ∀〚∶〛-syntax {A = A} (λ a → P) = ∀〚 a ∶ A 〛 P
infix 2 ∀〚∶〛-syntax

{-# DISPLAY ∀〚∶〛-syntax {A = A} P = P #-}

⊎⇒⊔ : ∀ {ℓ ℓ'} (P : hProp ℓ) (Q : hProp ℓ') → [ P ] ⊎ [ Q ] → [ P ⊔ Q ]
⊎⇒⊔ P Q (inl x) = inlᵖ x
⊎⇒⊔ P Q (inr x) = inrᵖ x

-- pretty `⊔-elim`
case[⊔]-syntaxᵈ : ∀ {ℓ ℓ' ℓ''} (P : hProp ℓ) (Q : hProp ℓ')
                  → (z : [ P ⊔ Q ])
                  → (R : [ P ⊔ Q ] → hProp ℓ'')
                  → (S : (x : [ P ] ⊎ [ Q ]) → [ R (⊎⇒⊔ P Q x) ] )
                  → [ R z ]
case[⊔]-syntaxᵈ P Q z R S = ⊔-elim P Q R (λ p → S (inl p)) (λ q → S (inr q)) z

syntax case[⊔]-syntaxᵈ P Q z (λ x → R) S = case z as x ∶ P ⊔ Q ⇒ R of S

case[⊔]-syntax : ∀ {ℓ ℓ' ℓ''} (P : hProp ℓ) (Q : hProp ℓ')
                  → (z : [ P ⊔ Q ])
                  → (R : hProp ℓ'')
                  → (S : (x : [ P ] ⊎ [ Q ]) → [ R ] )
                  → [ R ]
case[⊔]-syntax P Q z R S = ⊔-elim P Q (λ _ → R) (λ p → S (inl p)) (λ q → S (inr q)) z

syntax case[⊔]-syntax P Q z R S = case z as P ⊔ Q ⇒ R of S

-- {-# DISPLAY case[⊔]-syntax P Q z R S = case z of S #-}

-- for a function, to be an hProp, it suffices that the result is an hProp
-- so in principle we might inject any non-hProps as arguments with `_ᵗ⇒_`
_ᵗ⇒_ : ∀{ℓ ℓ'} (A : Type ℓ) → (B : hProp ℓ') → hProp _
A ᵗ⇒ B = (A → [ B ]) , isPropΠ λ _ → isProp[] B

infixr 6 _ᵗ⇒_

-- lifting of hProps to create "universe-homogeneous" pathes
--   this is not necessary when using _⇔_ which is universe-inhomogeneous
--   because `_⇔_` can "cross" universes, where `PathP` needs to stay in the same universe

Liftᵖ : ∀{i j : Level} → hProp i → hProp (ℓ-max i j)
Liftᵖ {i} {j} P = Lift {i} {j} [ P ] , λ{ (lift p) (lift q) → λ i → lift (isProp[] P p q i) }

liftᵖ : ∀{i j : Level} → (P : hProp i) → [ P ] → [ Liftᵖ {i} {j} P ]
liftᵖ P p = lift p

unliftᵖ : ∀{i j : Level} → (P : hProp i) → [ Liftᵖ {i} {j} P ] → [ P ]
unliftᵖ P (lift p) = p

⊥↑ : ∀{ℓ} → hProp ℓ
⊥↑ = Lift Empty.⊥ , λ ()

⊤↑ : ∀{ℓ} → hProp ℓ
⊤↑ = Lift Unit , isOfHLevelLift 1 (λ _ _ _ → tt)

infix 10 ¬↑_
¬↑_ : ∀{ℓ} → hProp ℓ → hProp ℓ
¬↑_ {ℓ} A = ([ A ] → Lift {j = ℓ} Empty.⊥) , isPropΠ λ _ → isOfHLevelLift 1 Empty.isProp⊥

-- negation with an instance argument
¬ⁱ_ : ∀{ℓ} → hProp ℓ → hProp ℓ
¬ⁱ A = ({{p : [ A ]}} → ⊥⊥) , isPropΠⁱ {A = [ A ]} λ _ → isProp⊥

¬'_ : ∀{ℓ} → Type ℓ → hProp ℓ
¬' A = (A → ⊥⊥) , isPropΠ λ _ → isProp⊥

¬-≡-¬ⁱ : ∀{ℓ} (P : hProp ℓ) → ¬ P ≡ ¬ⁱ P
¬-≡-¬ⁱ P =
  ⇒∶ (λ f {{p}} → f   p  )
  ⇐∶ (λ f   p   → f {{p}})
