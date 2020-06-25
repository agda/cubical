{-# OPTIONS --cubical --no-import-sorts --safe #-}
module Cubical.Structures.Group.Base where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Equiv.HalfAdjoint
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.Transport

open import Cubical.Data.Sigma

open import Cubical.Structures.Macro
open import Cubical.Structures.NAryOp
open import Cubical.Structures.Pointed
open import Cubical.Structures.Semigroup hiding (⟨_⟩)
open import Cubical.Structures.Monoid hiding (⟨_⟩)

open Iso

private
  variable
    ℓ : Level

record IsGroup {G : Type ℓ}
               (0g : G) (_+_ : G → G → G) (-_ : G → G) : Type ℓ where

  constructor isgroup

  field
    isMonoid  : IsMonoid 0g _+_
    inverse   : (x : G) → (x + (- x) ≡ 0g) × ((- x) + x ≡ 0g)

  open IsMonoid isMonoid public

  infixl 6 _-_

  _-_ : G → G → G
  x - y = x + (- y)

  invl : (x : G) → (- x) + x ≡ 0g
  invl x = inverse x .snd

  invr : (x : G) → x + (- x) ≡ 0g
  invr x = inverse x .fst

record Group : Type (ℓ-suc ℓ) where

  constructor group

  field
    Carrier : Type ℓ
    0g      : Carrier
    _+_     : Carrier → Carrier → Carrier
    -_      : Carrier → Carrier
    isGroup : IsGroup 0g _+_ -_

  infix  8 -_
  infixr 7 _+_

  open IsGroup isGroup public

-- Extractor for the carrier type
⟨_⟩ : Group → Type ℓ
⟨_⟩ = Group.Carrier

makeIsGroup : {G : Type ℓ} {0g : G} {_+_ : G → G → G} { -_ : G → G}
              (is-setG : isSet G)
              (assoc : (x y z : G) → x + (y + z) ≡ (x + y) + z)
              (rid : (x : G) → x + 0g ≡ x)
              (lid : (x : G) → 0g + x ≡ x)
              (rinv : (x : G) → x + (- x) ≡ 0g)
              (linv : (x : G) → (- x) + x ≡ 0g)
            → IsGroup 0g _+_ -_
makeIsGroup is-setG assoc rid lid rinv linv =
   isgroup (makeIsMonoid is-setG assoc rid lid) λ x → rinv x , linv x

makeGroup : {G : Type ℓ} (0g : G) (_+_ : G → G → G) (-_ : G → G)
            (is-setG : isSet G)
            (assoc : (x y z : G) → x + (y + z) ≡ (x + y) + z)
            (rid : (x : G) → x + 0g ≡ x)
            (lid : (x : G) → 0g + x ≡ x)
            (rinv : (x : G) → x + (- x) ≡ 0g)
            (linv : (x : G) → (- x) + x ≡ 0g)
          → Group
makeGroup 0g _+_ -_ is-setG assoc rid lid rinv linv =
  group _ 0g _+_ -_ (makeIsGroup is-setG assoc rid lid rinv linv)

makeGroup-right : ∀ {ℓ} {A : Type ℓ}
  → (id : A)
  → (comp : A → A → A)
  → (inv : A → A)
  → (set : isSet A)
  → (assoc : ∀ a b c → comp a (comp b c) ≡ comp (comp a b) c)
  → (rUnit : ∀ a → comp a id ≡ a)
  → (rCancel : ∀ a → comp a (inv a) ≡ id)
  → Group
makeGroup-right {A = A} id comp inv set assoc rUnit rCancel =
  makeGroup id comp inv set assoc rUnit lUnit rCancel lCancel
  where
    _⨀_ = comp
    abstract
      lCancel : ∀ a → comp (inv a) a ≡ id
      lCancel a =
        inv a ⨀ a
          ≡⟨ sym (rUnit (comp (inv a) a))  ⟩
        (inv a ⨀ a) ⨀ id
          ≡⟨ cong (comp (comp (inv a) a)) (sym (rCancel (inv a))) ⟩
        (inv a ⨀ a) ⨀ (inv a ⨀ (inv (inv a)))
          ≡⟨ assoc _ _ _ ⟩
        ((inv a ⨀ a) ⨀ (inv a)) ⨀ (inv (inv a))
          ≡⟨ cong (λ □ → □ ⨀ _) (sym (assoc _ _ _)) ⟩
        (inv a ⨀ (a ⨀ inv a)) ⨀ (inv (inv a))
          ≡⟨ cong (λ □ → (inv a ⨀ □) ⨀ (inv (inv a))) (rCancel a) ⟩
        (inv a ⨀ id) ⨀ (inv (inv a))
          ≡⟨ cong (λ □ → □ ⨀ (inv (inv a))) (rUnit (inv a)) ⟩
        inv a ⨀ (inv (inv a))
          ≡⟨ rCancel (inv a) ⟩
        id
          ∎

      lUnit : ∀ a → comp id a ≡ a
      lUnit a =
        id ⨀ a
          ≡⟨ cong (λ b → comp b a) (sym (rCancel a)) ⟩
        (a ⨀ inv a) ⨀ a
          ≡⟨ sym (assoc _ _ _) ⟩
        a ⨀ (inv a ⨀ a)
          ≡⟨ cong (comp a) (lCancel a) ⟩
        a ⨀ id
          ≡⟨ rUnit a ⟩
        a
          ∎

makeGroup-left : ∀ {ℓ} {A : Type ℓ}
  → (id : A)
  → (comp : A → A → A)
  → (inv : A → A)
  → (set : isSet A)
  → (assoc : ∀ a b c → comp a (comp b c) ≡ comp (comp a b) c)
  → (lUnit : ∀ a → comp id a ≡ a)
  → (lCancel : ∀ a → comp (inv a) a ≡ id)
  → Group
makeGroup-left {A = A} id comp inv set assoc lUnit lCancel =
  makeGroup id comp inv set assoc rUnit lUnit rCancel lCancel
  where
    abstract
      rCancel : ∀ a → comp a (inv a) ≡ id
      rCancel a =
        comp a (inv a)
          ≡⟨ sym (lUnit (comp a (inv a)))  ⟩
        comp id (comp a (inv a))
          ≡⟨ cong (λ b → comp b (comp a (inv a))) (sym (lCancel (inv a))) ⟩
        comp (comp (inv (inv a)) (inv a)) (comp a (inv a))
          ≡⟨ sym (assoc (inv (inv a)) (inv a) (comp a (inv a))) ⟩
        comp (inv (inv a)) (comp (inv a) (comp a (inv a)))
          ≡⟨ cong (comp (inv (inv a))) (assoc (inv a) a (inv a)) ⟩
        comp (inv (inv a)) (comp (comp (inv a) a) (inv a))
          ≡⟨ cong (λ b → comp (inv (inv a)) (comp b (inv a))) (lCancel a) ⟩
        comp (inv (inv a)) (comp id (inv a))
          ≡⟨ cong (comp (inv (inv a))) (lUnit (inv a)) ⟩
        comp (inv (inv a)) (inv a)
          ≡⟨ lCancel (inv a) ⟩
        id
          ∎

      rUnit : ∀ a → comp a id ≡ a
      rUnit a =
        comp a id
          ≡⟨ cong (comp a) (sym (lCancel a)) ⟩
        comp a (comp (inv a) a)
          ≡⟨ assoc a (inv a) a ⟩
        comp (comp a (inv a)) a
          ≡⟨ cong (λ b → comp b a) (rCancel a) ⟩
        comp id a
          ≡⟨ lUnit a ⟩
        a
          ∎

isPropIsGroup : {G : Type ℓ} (0g : G) (_+_ : G → G → G) (-_ : G → G)
              → isProp (IsGroup 0g _+_ -_)
isPropIsGroup 0g _+_ -_ (isgroup GM Ginv) (isgroup HM Hinv) =
  λ i → isgroup (isPropIsMonoid _ _ GM HM i) (isPropInv Ginv Hinv i)
  where
  isSetG : isSet _
  isSetG = IsSemigroup.is-set (IsMonoid.isSemigroup GM)

  isPropInv : isProp ((x : _) → ((x + (- x)) ≡ 0g) × (((- x) + x) ≡ 0g))
  isPropInv = isPropΠ λ _ → isProp× (isSetG _ _) (isSetG _ _)
