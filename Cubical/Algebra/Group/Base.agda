{-

Defines groups and adds some smart constructors

-}
{-# OPTIONS --safe #-}
module Cubical.Algebra.Group.Base where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Structure
open import Cubical.Data.Sigma
open import Cubical.Algebra.Monoid
open import Cubical.Algebra.Semigroup

private
  variable
    ℓ : Level

record IsGroup {G : Type ℓ}
               (1g : G) (_·_ : G → G → G) (inv : G → G) : Type ℓ where

  constructor isgroup

  field
    isMonoid  : IsMonoid 1g _·_
    inverse   : (x : G) → (x · inv x ≡ 1g) × (inv x · x ≡ 1g)

  open IsMonoid isMonoid public

  infixl 6 _-_

  -- Useful notation for additive groups
  _-_ : G → G → G
  x - y = x · inv y

  invl : (x : G) → inv x · x ≡ 1g
  invl x = inverse x .snd

  invr : (x : G) → x · inv x ≡ 1g
  invr x = inverse x .fst

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

isSetGroup : (G : Group ℓ) → isSet ⟨ G ⟩
isSetGroup G = GroupStr.isGroup (snd G) .IsGroup.isMonoid .IsMonoid.isSemigroup .IsSemigroup.is-set

makeIsGroup : {G : Type ℓ} {e : G} {_·_ : G → G → G} { inv : G → G}
              (is-setG : isSet G)
              (assoc : (x y z : G) → x · (y · z) ≡ (x · y) · z)
              (rid : (x : G) → x · e ≡ x)
              (lid : (x : G) → e · x ≡ x)
              (rinv : (x : G) → x · inv x ≡ e)
              (linv : (x : G) → inv x · x ≡ e)
            → IsGroup e _·_ inv
IsGroup.isMonoid (makeIsGroup is-setG assoc rid lid rinv linv) = makeIsMonoid is-setG assoc rid lid
IsGroup.inverse (makeIsGroup is-setG assoc rid lid rinv linv) = λ x → rinv x , linv x

makeGroup : {G : Type ℓ} (e : G) (_·_ : G → G → G) (inv : G → G)
            (is-setG : isSet G)
            (assoc : (x y z : G) → x · (y · z) ≡ (x · y) · z)
            (rid : (x : G) → x · e ≡ x)
            (lid : (x : G) → e · x ≡ x)
            (rinv : (x : G) → x · inv x ≡ e)
            (linv : (x : G) → inv x · x ≡ e)
          → Group ℓ
makeGroup e _·_ inv is-setG assoc rid lid rinv linv = _ , helper
  where
  helper : GroupStr _
  GroupStr.1g helper = e
  GroupStr._·_ helper = _·_
  GroupStr.inv helper = inv
  GroupStr.isGroup helper = makeIsGroup is-setG assoc rid lid rinv linv

Group→Monoid : Group ℓ → Monoid ℓ
Group→Monoid (A , groupstr  _ _ _ G) = A , monoidstr _ _ (IsGroup.isMonoid G)

makeGroup-right : {A : Type ℓ}
  → (1g : A)
  → (_·_ : A → A → A)
  → (inv : A → A)
  → (set : isSet A)
  → (assoc : ∀ a b c → a · (b · c) ≡ (a · b) · c)
  → (rUnit : ∀ a → a · 1g ≡ a)
  → (rCancel : ∀ a → a · inv a ≡ 1g)
  → Group ℓ
makeGroup-right 1g _·_ inv set assoc rUnit rCancel =
  makeGroup 1g _·_ inv set assoc rUnit lUnit rCancel lCancel
  where
    abstract
      lCancel : ∀ a → inv a · a ≡ 1g
      lCancel a =
        inv a · a
          ≡⟨ sym (rUnit _)  ⟩
        (inv a · a) · 1g
          ≡⟨ cong (_·_ _) (sym (rCancel (inv a))) ⟩
        (inv a · a) · (inv a · (inv (inv a)))
          ≡⟨ assoc _ _ _ ⟩
        ((inv a · a) · (inv a)) · (inv (inv a))
          ≡⟨ cong (λ □ → □ · _) (sym (assoc _ _ _)) ⟩
        (inv a · (a · inv a)) · (inv (inv a))
          ≡⟨ cong (λ □ → (inv a · □) · (inv (inv a))) (rCancel a) ⟩
        (inv a · 1g) · (inv (inv a))
          ≡⟨ cong (λ □ → □ · (inv (inv a))) (rUnit (inv a)) ⟩
        inv a · (inv (inv a))
          ≡⟨ rCancel (inv a) ⟩
        1g
          ∎

      lUnit : ∀ a → 1g · a ≡ a
      lUnit a =
        1g · a
          ≡⟨ cong (λ b → b · a) (sym (rCancel a)) ⟩
        (a · inv a) · a
          ≡⟨ sym (assoc _ _ _) ⟩
        a · (inv a · a)
          ≡⟨ cong (a ·_) (lCancel a) ⟩
        a · 1g
          ≡⟨ rUnit a ⟩
        a
          ∎

makeGroup-left : {A : Type ℓ}
  → (1g : A)
  → (_·_ : A → A → A)
  → (inv : A → A)
  → (set : isSet A)
  → (assoc : ∀ a b c → a · (b · c) ≡ (a · b) · c)
  → (lUnit : ∀ a → 1g · a ≡ a)
  → (lCancel : ∀ a → (inv a) · a ≡ 1g)
  → Group ℓ
makeGroup-left 1g _·_ inv set assoc lUnit lCancel =
  makeGroup 1g _·_ inv set assoc rUnit lUnit rCancel lCancel
  where
    abstract
      rCancel : ∀ a → a · inv a ≡ 1g
      rCancel a =
        a · inv a
          ≡⟨ sym (lUnit _)  ⟩
        1g · (a · inv a)
          ≡⟨ cong (λ b → b · (a · inv a)) (sym (lCancel (inv a))) ⟩
        (inv (inv a) · inv a) · (a · inv a)
          ≡⟨ sym (assoc (inv (inv a)) (inv a) _) ⟩
        inv (inv a) · (inv a · (a · inv a))
          ≡⟨ cong (inv (inv a) ·_) (assoc (inv a) a (inv a)) ⟩
        (inv (inv a)) · ((inv a · a) · (inv a))
          ≡⟨ cong (λ b → (inv (inv a)) · (b · (inv a))) (lCancel a) ⟩
        inv (inv a) · (1g · inv a)
          ≡⟨ cong (inv (inv a) ·_) (lUnit (inv a)) ⟩
        inv (inv a) · inv a
          ≡⟨ lCancel (inv a) ⟩
        1g
          ∎

      rUnit : ∀ a → a · 1g ≡ a
      rUnit a =
        a · 1g
          ≡⟨ cong (a ·_) (sym (lCancel a)) ⟩
        a · (inv a · a)
          ≡⟨ assoc a (inv a) a ⟩
        (a · inv a) · a
          ≡⟨ cong (λ b → b · a) (rCancel a) ⟩
        1g · a
          ≡⟨ lUnit a ⟩
        a
          ∎
