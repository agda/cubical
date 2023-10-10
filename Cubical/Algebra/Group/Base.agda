{-# OPTIONS --safe #-}
module Cubical.Algebra.Group.Base where
{-
  Defines groups and adds the smart constructors [makeGroup-right] and [makeGroup-left]
  for constructing groups from less data than the standard [makeGroup] constructor.
-}

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Structure
open import Cubical.Data.Sigma
open import Cubical.Algebra.Monoid
open import Cubical.Algebra.Semigroup

open import Cubical.Reflection.RecordEquiv


private
  variable
    ℓ : Level

record IsGroup {G : Type ℓ}
               (1g : G) (_·_ : G → G → G) (inv : G → G) : Type ℓ where

  constructor isgroup

  field
    isMonoid  : IsMonoid 1g _·_
    ·InvR : (x : G) → x · inv x ≡ 1g
    ·InvL : (x : G) → inv x · x ≡ 1g

  open IsMonoid isMonoid public

unquoteDecl IsGroupIsoΣ = declareRecordIsoΣ IsGroupIsoΣ (quote IsGroup)

record GroupStr (G : Type ℓ) : Type ℓ where

  constructor groupstr

  field
    1g      : G
    _·_     : G → G → G
    inv     : G → G
    isGroup : IsGroup 1g _·_ inv

  infixr 7 _·_

  open IsGroup isGroup public

Group : ∀ ℓ → Type (ℓ-suc ℓ)
Group ℓ = TypeWithStr ℓ GroupStr

Group₀ : Type₁
Group₀ = Group ℓ-zero

group : (G : Type ℓ) (1g : G) (_·_ : G → G → G) (inv : G → G) (h : IsGroup 1g _·_ inv) → Group ℓ
group G 1g _·_ inv h = G , groupstr 1g _·_ inv h

makeIsGroup : {G : Type ℓ} {e : G} {_·_ : G → G → G} { inv : G → G}
              (is-setG : isSet G)
              (·Assoc : (x y z : G) → x · (y · z) ≡ (x · y) · z)
              (·IdR : (x : G) → x · e ≡ x)
              (·IdL : (x : G) → e · x ≡ x)
              (·InvR : (x : G) → x · inv x ≡ e)
              (·InvL : (x : G) → inv x · x ≡ e)
            → IsGroup e _·_ inv
IsGroup.isMonoid (makeIsGroup is-setG ·Assoc ·IdR ·IdL ·InvR ·InvL) = makeIsMonoid is-setG ·Assoc ·IdR ·IdL
IsGroup.·InvR (makeIsGroup is-setG ·Assoc ·IdR ·IdL ·InvR ·InvL) = ·InvR
IsGroup.·InvL (makeIsGroup is-setG ·Assoc ·IdR ·IdL ·InvR ·InvL) = ·InvL

makeGroup : {G : Type ℓ} (1g : G) (_·_ : G → G → G) (inv : G → G)
            (is-setG : isSet G)
            (·Assoc : (x y z : G) → x · (y · z) ≡ (x · y) · z)
            (·IdR : (x : G) → x · 1g ≡ x)
            (·IdL : (x : G) → 1g · x ≡ x)
            (·InvR : (x : G) → x · inv x ≡ 1g)
            (·InvL : (x : G) → inv x · x ≡ 1g)
          → Group ℓ
makeGroup 1g _·_ inv is-setG ·Assoc ·IdR ·IdL ·InvR ·InvL = _ , helper
  where
  helper : GroupStr _
  GroupStr.1g helper = 1g
  GroupStr._·_ helper = _·_
  GroupStr.inv helper = inv
  GroupStr.isGroup helper = makeIsGroup is-setG ·Assoc ·IdR ·IdL ·InvR ·InvL

Group→Monoid : Group ℓ → Monoid ℓ
Group→Monoid (A , groupstr  _ _ _ G) = A , monoidstr _ _ (IsGroup.isMonoid G)

makeGroup-right : {A : Type ℓ}
  → (1g : A)
  → (_·_ : A → A → A)
  → (inv : A → A)
  → (set : isSet A)
  → (·Assoc : ∀ a b c → a · (b · c) ≡ (a · b) · c)
  → (·IdR : ∀ a → a · 1g ≡ a)
  → (·InvR : ∀ a → a · inv a ≡ 1g)
  → Group ℓ
makeGroup-right 1g _·_ inv set ·Assoc ·IdR ·InvR =
  makeGroup 1g _·_ inv set ·Assoc ·IdR ·IdL ·InvR ·InvL
  where
    abstract
      ·InvL : ∀ a → inv a · a ≡ 1g
      ·InvL a =
        inv a · a
          ≡⟨ sym (·IdR _)  ⟩
        (inv a · a) · 1g
          ≡⟨ cong (_·_ _) (sym (·InvR (inv a))) ⟩
        (inv a · a) · (inv a · (inv (inv a)))
          ≡⟨ ·Assoc _ _ _ ⟩
        ((inv a · a) · (inv a)) · (inv (inv a))
          ≡⟨ cong (λ □ → □ · _) (sym (·Assoc _ _ _)) ⟩
        (inv a · (a · inv a)) · (inv (inv a))
          ≡⟨ cong (λ □ → (inv a · □) · (inv (inv a))) (·InvR a) ⟩
        (inv a · 1g) · (inv (inv a))
          ≡⟨ cong (λ □ → □ · (inv (inv a))) (·IdR (inv a)) ⟩
        inv a · (inv (inv a))
          ≡⟨ ·InvR (inv a) ⟩
        1g
          ∎

      ·IdL : ∀ a → 1g · a ≡ a
      ·IdL a =
        1g · a
          ≡⟨ cong (λ b → b · a) (sym (·InvR a)) ⟩
        (a · inv a) · a
          ≡⟨ sym (·Assoc _ _ _) ⟩
        a · (inv a · a)
          ≡⟨ cong (a ·_) (·InvL a) ⟩
        a · 1g
          ≡⟨ ·IdR a ⟩
        a
          ∎

makeGroup-left : {A : Type ℓ}
  → (1g : A)
  → (_·_ : A → A → A)
  → (inv : A → A)
  → (set : isSet A)
  → (·Assoc : ∀ a b c → a · (b · c) ≡ (a · b) · c)
  → (·IdL : ∀ a → 1g · a ≡ a)
  → (·InvL : ∀ a → (inv a) · a ≡ 1g)
  → Group ℓ
makeGroup-left 1g _·_ inv set ·Assoc ·IdL ·InvL =
  makeGroup 1g _·_ inv set ·Assoc ·IdR ·IdL ·InvR ·InvL
  where
    abstract
      ·InvR : ∀ a → a · inv a ≡ 1g
      ·InvR a =
        a · inv a
          ≡⟨ sym (·IdL _)  ⟩
        1g · (a · inv a)
          ≡⟨ cong (λ b → b · (a · inv a)) (sym (·InvL (inv a))) ⟩
        (inv (inv a) · inv a) · (a · inv a)
          ≡⟨ sym (·Assoc (inv (inv a)) (inv a) _) ⟩
        inv (inv a) · (inv a · (a · inv a))
          ≡⟨ cong (inv (inv a) ·_) (·Assoc (inv a) a (inv a)) ⟩
        (inv (inv a)) · ((inv a · a) · (inv a))
          ≡⟨ cong (λ b → (inv (inv a)) · (b · (inv a))) (·InvL a) ⟩
        inv (inv a) · (1g · inv a)
          ≡⟨ cong (inv (inv a) ·_) (·IdL (inv a)) ⟩
        inv (inv a) · inv a
          ≡⟨ ·InvL (inv a) ⟩
        1g
          ∎

      ·IdR : ∀ a → a · 1g ≡ a
      ·IdR a =
        a · 1g
          ≡⟨ cong (a ·_) (sym (·InvL a)) ⟩
        a · (inv a · a)
          ≡⟨ ·Assoc a (inv a) a ⟩
        (a · inv a) · a
          ≡⟨ cong (λ b → b · a) (·InvR a) ⟩
        1g · a
          ≡⟨ ·IdL a ⟩
        a
          ∎
