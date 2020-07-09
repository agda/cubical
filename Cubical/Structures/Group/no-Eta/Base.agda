{-# OPTIONS --cubical --no-import-sorts --safe #-}
module Cubical.Structures.Group.no-Eta.Base where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Sigma
open import Cubical.Structures.Monoid hiding (⟨_⟩)
open import Cubical.Structures.Semigroup hiding (⟨_⟩)

private
  variable
    ℓ : Level

record IsGroup {G : Type ℓ}
               (0g : G) (_+_ : G → G → G) (-_ : G → G) : Type ℓ where
  no-eta-equality
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
  no-eta-equality
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

Group₀ : Type₁
Group₀ = Group {ℓ-zero}

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


open Group
open IsGroup

isSetCarrier : ∀ {ℓ} → (G : Group {ℓ}) → isSet ⟨ G ⟩
isSetCarrier G = IsSemigroup.is-set (IsMonoid.isSemigroup (isMonoid (isGroup G)))

open import Cubical.Foundations.HLevels
dirProd : ∀ {ℓ ℓ'} → Group {ℓ} → Group {ℓ'} → Group
dirProd A B =
  makeGroup ((0g A) , (0g B))
            (λ a b → (_+_ A (fst a) (fst b)) , _+_ B (snd a) (snd b))
            (λ a → (-_ A (fst a)) , (-_ B (snd a)))
            (isOfHLevelΣ 2 (isSetCarrier A) λ _ → isSetCarrier B)
            (λ x y z i → assoc (isGroup A) (fst x) (fst y) (fst z) i , assoc (isGroup B) (snd x) (snd y) (snd z) i)
            (λ x i → IsGroup.rid (isGroup A) (fst x) i , IsGroup.rid (isGroup B) (snd x) i)
            (λ x i → IsGroup.lid (isGroup A) (fst x) i , IsGroup.lid (isGroup B) (snd x) i)
            (λ x i → (fst (inverse (isGroup A) (fst x)) i) , (fst (inverse (isGroup B) (snd x)) i))
            (λ x i → (snd (inverse (isGroup A) (fst x)) i) , (snd (inverse (isGroup B) (snd x)) i))

open import Cubical.Data.Unit
trivialGroup : Group₀
trivialGroup =
  makeGroup _
            (λ _ _ → _)
            (λ _ → _)
            isSetUnit
            (λ _ _ _ → refl)
            (λ _ → refl)
            (λ _ → refl)
            (λ _ → refl)
            λ _ → refl

open import Cubical.Data.Int renaming (_+_ to _+Int_ ; _-_ to _-Int_)
intGroup : Group₀
intGroup =
  makeGroup {G = Int}
            0
            _+Int_
            (pos 0 -Int_)
            isSetInt
            +-assoc
            (λ _ → refl)
            (λ x → +-comm (pos 0) x)
            (λ x → +-comm x (pos 0 -Int x) ∙ minusPlus x 0)
            λ x → minusPlus x 0
