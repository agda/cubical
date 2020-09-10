{-# OPTIONS --cubical --no-import-sorts --safe #-}
module Cubical.Algebra.Group.Base where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Sigma
open import Cubical.Data.Prod renaming (_×_ to _×'_)
open import Cubical.Data.Int renaming (_+_ to _+Int_ ; _-_ to _-Int_)
open import Cubical.Data.Unit

open import Cubical.Algebra.Monoid hiding (⟨_⟩)
open import Cubical.Algebra.Semigroup hiding (⟨_⟩)
open import Cubical.Foundations.HLevels

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

η-isGroup : {G : Type ℓ} {0g 0g' : G} {_+_ _+'_  : G → G → G} { -_ -'_  : G → G}
         → 0g ≡ 0g'
         → _+_ ≡ _+'_
         → -_ ≡ -'_
         → IsGroup 0g _+_ -_ ≡ IsGroup 0g' _+'_ -'_
η-isGroup id1 id2 id3 i = IsGroup (id1 i) (id2 i) (id3 i)

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

isSetGroup : (G : Group {ℓ}) → isSet ⟨ G ⟩
isSetGroup G = Group.isGroup G .IsGroup.isMonoid .IsMonoid.isSemigroup .IsSemigroup.is-set

makeIsGroup : {G : Type ℓ} {0g : G} {_+_ : G → G → G} { -_ : G → G}
              (is-setG : isSet G)
              (assoc : (x y z : G) → x + (y + z) ≡ (x + y) + z)
              (rid : (x : G) → x + 0g ≡ x)
              (lid : (x : G) → 0g + x ≡ x)
              (rinv : (x : G) → x + (- x) ≡ 0g)
              (linv : (x : G) → (- x) + x ≡ 0g)
            → IsGroup 0g _+_ -_
IsGroup.isMonoid (makeIsGroup is-setG assoc rid lid rinv linv) = makeIsMonoid is-setG assoc rid lid
IsGroup.inverse (makeIsGroup is-setG assoc rid lid rinv linv) = λ x → rinv x , linv x

makeGroup : {G : Type ℓ} (0g : G) (_+_ : G → G → G) (-_ : G → G)
            (is-setG : isSet G)
            (assoc : (x y z : G) → x + (y + z) ≡ (x + y) + z)
            (rid : (x : G) → x + 0g ≡ x)
            (lid : (x : G) → 0g + x ≡ x)
            (rinv : (x : G) → x + (- x) ≡ 0g)
            (linv : (x : G) → (- x) + x ≡ 0g)
          → Group
Group.Carrier (makeGroup 0g _+_ -_ is-setG assoc rid lid rinv linv) = _
Group.0g (makeGroup 0g _+_ -_ is-setG assoc rid lid rinv linv) = 0g
Group._+_ (makeGroup 0g _+_ -_ is-setG assoc rid lid rinv linv) = _+_
Group.- makeGroup 0g _+_ -_ is-setG assoc rid lid rinv linv = -_
Group.isGroup (makeGroup 0g _+_ -_ is-setG assoc rid lid rinv linv) = makeIsGroup is-setG assoc rid lid rinv linv

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

η-Group : {G H : Group {ℓ}}
       → (p : ⟨ G ⟩ ≡ ⟨ H ⟩)
       → (q : PathP (λ i → p i) (0g G) (0g H))
       → (r : PathP (λ i → (p i) → (p i) → (p i)) (_+_ G) (_+_ H))
       → (s : PathP (λ i → p i → p i) (-_ G) (-_ H))
       → PathP (λ i → IsGroup (q i) (r i) (s i)) (isGroup G) (isGroup H)
       → G ≡ H
Carrier (η-Group p _ _ _ _ i) = p i
0g (η-Group _ q _ _ _ i) = q i
_+_ (η-Group _ _ r _ _ i) = r i
- η-Group _ _ _ s t i = s i
isGroup (η-Group _ _ _ _ t i) = t i

isSetCarrier : ∀ {ℓ} → (G : Group {ℓ}) → isSet ⟨ G ⟩
isSetCarrier G = IsSemigroup.is-set (IsMonoid.isSemigroup (isMonoid G))

open IsMonoid
open IsSemigroup
dirProd : ∀ {ℓ ℓ'} → Group {ℓ} → Group {ℓ'} → Group
Carrier (dirProd A B) = Carrier A × Carrier B
0g (dirProd A B) = (0g A) , (0g B)
_+_ (dirProd A B) a b = (_+_ A (fst a) (fst b)) , _+_ B (snd a) (snd b)
-_ (dirProd A B) a = (-_ A (fst a)) , (-_ B (snd a))
is-set (isSemigroup (isMonoid (isGroup (dirProd A B)))) =
  isOfHLevelΣ 2 (isSetCarrier A) λ _ → isSetCarrier B
assoc (isSemigroup (isMonoid (isGroup (dirProd A B)))) x y z i =
  assoc (isGroup A) (fst x) (fst y) (fst z) i , assoc (isGroup B) (snd x) (snd y) (snd z) i
identity (isMonoid (isGroup (dirProd A B))) x =
   (λ i → IsGroup.rid (isGroup A) (fst x) i , IsGroup.rid (isGroup B) (snd x) i)
 , λ i → IsGroup.lid (isGroup A) (fst x) i , IsGroup.lid (isGroup B) (snd x) i
inverse (isGroup (dirProd A B)) x =
    (λ i → (fst (inverse (isGroup A) (fst x)) i) , (fst (inverse (isGroup B) (snd x)) i))
  , λ i → (snd (inverse (isGroup A) (fst x)) i) , (snd (inverse (isGroup B) (snd x)) i)

trivialGroup : Group₀
Carrier trivialGroup = Unit
0g trivialGroup = _
_+_ trivialGroup _ _ = _
-_ trivialGroup _ = _
is-set (isSemigroup (isMonoid (isGroup trivialGroup))) = isSetUnit
assoc (isSemigroup (isMonoid (isGroup trivialGroup))) _ _ _ = refl
identity (isMonoid (isGroup trivialGroup)) _ = refl , refl
inverse (isGroup trivialGroup) _ = refl , refl

intGroup : Group₀
Carrier intGroup = Int
0g intGroup = 0
_+_ intGroup = _+Int_
- intGroup = 0 -Int_
is-set (isSemigroup (isMonoid (isGroup intGroup))) = isSetInt
assoc (isSemigroup (isMonoid (isGroup intGroup))) = +-assoc
identity (isMonoid (isGroup intGroup)) x = refl , (+-comm (pos 0) x)
inverse (isGroup intGroup) x = +-comm x (pos 0 -Int x) ∙ minusPlus x 0 , (minusPlus x 0)
