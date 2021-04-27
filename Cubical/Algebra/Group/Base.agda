{-# OPTIONS --cubical --no-import-sorts --safe #-}
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
               (0g : G) (_+_ : G → G → G) (inv : G → G) : Type ℓ where

  constructor isgroup

  field
    isMonoid  : IsMonoid 0g _+_
    inverse   : (x : G) → (x + inv x ≡ 0g) × (inv x + x ≡ 0g)

  open IsMonoid isMonoid public

  infixl 6 _-_

  -- Useful notation for additive groups
  _-_ : G → G → G
  x - y = x + (inv y)

  invl : (x : G) → (inv x) + x ≡ 0g
  invl x = inverse x .snd

  invr : (x : G) → x + (inv x) ≡ 0g
  invr x = inverse x .fst

record GroupStr (G : Type ℓ) : Type (ℓ-suc ℓ) where

  constructor groupstr

  field
    0g      : G
    _+_     : G → G → G
    inv     : G → G
    isGroup : IsGroup 0g _+_ inv

  infixr 7 _+_

  open IsGroup isGroup public

Group : Type (ℓ-suc ℓ)
Group = TypeWithStr _ GroupStr

Group₀ : Type₁
Group₀ = Group {ℓ-zero}

group : (G : Type ℓ) (0g : G) (_+_ : G → G → G) (inv : G → G) (h : IsGroup 0g _+_ inv) → Group
group G 0g _+_ inv h = G , groupstr 0g _+_ inv h

isSetGroup : (G : Group {ℓ}) → isSet ⟨ G ⟩
isSetGroup G = GroupStr.isGroup (snd G) .IsGroup.isMonoid .IsMonoid.isSemigroup .IsSemigroup.is-set

makeIsGroup : {G : Type ℓ} {0g : G} {_+_ : G → G → G} { inv : G → G}
              (is-setG : isSet G)
              (assoc : (x y z : G) → x + (y + z) ≡ (x + y) + z)
              (rid : (x : G) → x + 0g ≡ x)
              (lid : (x : G) → 0g + x ≡ x)
              (rinv : (x : G) → x + inv x ≡ 0g)
              (linv : (x : G) → inv x + x ≡ 0g)
            → IsGroup 0g _+_ inv
IsGroup.isMonoid (makeIsGroup is-setG assoc rid lid rinv linv) = makeIsMonoid is-setG assoc rid lid
IsGroup.inverse (makeIsGroup is-setG assoc rid lid rinv linv) = λ x → rinv x , linv x

makeGroup : {G : Type ℓ} (0g : G) (_+_ : G → G → G) (inv : G → G)
            (is-setG : isSet G)
            (assoc : (x y z : G) → x + (y + z) ≡ (x + y) + z)
            (rid : (x : G) → x + 0g ≡ x)
            (lid : (x : G) → 0g + x ≡ x)
            (rinv : (x : G) → x + inv x ≡ 0g)
            (linv : (x : G) → inv x + x ≡ 0g)
          → Group
makeGroup 0g _+_ inv is-setG assoc rid lid rinv linv = _ , helper
  where
  helper : GroupStr _
  GroupStr.0g helper = 0g
  GroupStr._+_ helper = _+_
  GroupStr.inv helper = inv
  GroupStr.isGroup helper = makeIsGroup is-setG assoc rid lid rinv linv

makeGroup-right : {A : Type ℓ}
  → (id : A)
  → (_+_ : A → A → A)
  → (inv : A → A)
  → (set : isSet A)
  → (assoc : ∀ a b c → a + (b + c) ≡ (a + b) + c)
  → (rUnit : ∀ a → a + id ≡ a)
  → (rCancel : ∀ a → a + (inv a) ≡ id)
  → Group
makeGroup-right id _+_ inv set assoc rUnit rCancel =
  makeGroup id _+_ inv set assoc rUnit lUnit rCancel lCancel
  where
    abstract
      lCancel : ∀ a → inv a + a ≡ id
      lCancel a =
        inv a + a
          ≡⟨ sym (rUnit _)  ⟩
        (inv a + a) + id
          ≡⟨ cong (_+_ _) (sym (rCancel (inv a))) ⟩
        (inv a + a) + (inv a + (inv (inv a)))
          ≡⟨ assoc _ _ _ ⟩
        ((inv a + a) + (inv a)) + (inv (inv a))
          ≡⟨ cong (λ □ → □ + _) (sym (assoc _ _ _)) ⟩
        (inv a + (a + inv a)) + (inv (inv a))
          ≡⟨ cong (λ □ → (inv a + □) + (inv (inv a))) (rCancel a) ⟩
        (inv a + id) + (inv (inv a))
          ≡⟨ cong (λ □ → □ + (inv (inv a))) (rUnit (inv a)) ⟩
        inv a + (inv (inv a))
          ≡⟨ rCancel (inv a) ⟩
        id
          ∎

      lUnit : ∀ a → id + a ≡ a
      lUnit a =
        id + a
          ≡⟨ cong (λ b → b + a) (sym (rCancel a)) ⟩
        (a + inv a) + a
          ≡⟨ sym (assoc _ _ _) ⟩
        a + (inv a + a)
          ≡⟨ cong (a +_) (lCancel a) ⟩
        a + id
          ≡⟨ rUnit a ⟩
        a
          ∎

makeGroup-left : {A : Type ℓ}
  → (id : A)
  → (_+_ : A → A → A)
  → (inv : A → A)
  → (set : isSet A)
  → (assoc : ∀ a b c → a + (b + c) ≡ (a + b) + c)
  → (lUnit : ∀ a → id + a ≡ a)
  → (lCancel : ∀ a → (inv a) + a ≡ id)
  → Group
makeGroup-left id _+_ inv set assoc lUnit lCancel =
  makeGroup id _+_ inv set assoc rUnit lUnit rCancel lCancel
  where
    abstract
      rCancel : ∀ a → a + inv a ≡ id
      rCancel a =
        a + inv a
          ≡⟨ sym (lUnit _)  ⟩
        id + (a + inv a)
          ≡⟨ cong (λ b → b + (a + inv a)) (sym (lCancel (inv a))) ⟩
        (inv (inv a) + inv a) + (a + inv a)
          ≡⟨ sym (assoc (inv (inv a)) (inv a) _) ⟩
        inv (inv a) + (inv a + (a + inv a))
          ≡⟨ cong (inv (inv a) +_) (assoc (inv a) a (inv a)) ⟩
        (inv (inv a)) + ((inv a + a) + (inv a))
          ≡⟨ cong (λ b → (inv (inv a)) + (b + (inv a))) (lCancel a) ⟩
        inv (inv a) + (id + inv a)
          ≡⟨ cong (inv (inv a) +_) (lUnit (inv a)) ⟩
        inv (inv a) + inv a
          ≡⟨ lCancel (inv a) ⟩
        id
          ∎

      rUnit : ∀ a → a + id ≡ a
      rUnit a =
        a + id
          ≡⟨ cong (a +_) (sym (lCancel a)) ⟩
        a + (inv a + a)
          ≡⟨ assoc a (inv a) a ⟩
        (a + inv a) + a
          ≡⟨ cong (λ b → b + a) (rCancel a) ⟩
        id + a
          ≡⟨ lUnit a ⟩
        a
          ∎

isSetCarrier : (G : Group {ℓ}) → isSet ⟨ G ⟩
isSetCarrier G = IsSemigroup.is-set (IsMonoid.isSemigroup (GroupStr.isMonoid (snd G)))
