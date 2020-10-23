{-# OPTIONS --cubical --no-import-sorts --safe #-}
module Cubical.Algebra.Group.Base where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.SIP
open import Cubical.Data.Sigma
open import Cubical.Data.Int renaming (_+_ to _+Int_ ; _-_ to _-Int_)
open import Cubical.Data.Unit

open import Cubical.Algebra.Monoid
open import Cubical.Algebra.Semigroup
open import Cubical.Foundations.HLevels

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

record GroupStr (G : Type ℓ) : Type (ℓ-suc ℓ) where

  constructor groupstr

  field
    0g      : G
    _+_     : G → G → G
    -_      : G → G
    isGroup : IsGroup 0g _+_ -_

  infix  8 -_
  infixr 7 _+_

  open IsGroup isGroup public

Group : Type (ℓ-suc ℓ)
Group = TypeWithStr _ GroupStr

Group₀ : Type₁
Group₀ = Group {ℓ-zero}

group : (G : Type ℓ) (0g : G) (_+_ : G → G → G) (-_ : G → G) (h : IsGroup 0g _+_ -_) → Group
group G 0g _+_ -_ h = G , groupstr 0g _+_ -_ h

isSetGroup : (G : Group {ℓ}) → isSet ⟨ G ⟩
isSetGroup G = GroupStr.isGroup (snd G) .IsGroup.isMonoid .IsMonoid.isSemigroup .IsSemigroup.is-set

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
makeGroup 0g _+_ -_ is-setG assoc rid lid rinv linv = _ , helper
  where
  helper : GroupStr _
  GroupStr.0g helper = 0g
  GroupStr._+_ helper = _+_
  GroupStr.- helper = -_
  GroupStr.isGroup helper = makeIsGroup is-setG assoc rid lid rinv linv

makeGroup-right : ∀ {ℓ} {A : Type ℓ}
  → (id : A)
  → (comp : A → A → A)
  → (inv : A → A)
  → (set : isSet A)
  → (assoc : ∀ a b c → comp a (comp b c) ≡ comp (comp a b) c)
  → (rUnit : ∀ a → comp a id ≡ a)
  → (rCancel : ∀ a → comp a (inv a) ≡ id)
  → Group
makeGroup-right id comp inv set assoc rUnit rCancel =
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
makeGroup-left id comp inv set assoc lUnit lCancel =
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

open GroupStr hiding (0g ; _+_ ; -_)

isSetCarrier : ∀ {ℓ} → (G : Group {ℓ}) → isSet ⟨ G ⟩
isSetCarrier G = IsSemigroup.is-set (IsMonoid.isSemigroup (GroupStr.isMonoid (snd G)))

open GroupStr

dirProd : ∀ {ℓ ℓ'} → Group {ℓ} → Group {ℓ'} → Group
dirProd (GC , G) (HC , H) =
  makeGroup (0g G , 0g H)
            (λ { (x1 , x2) (y1 , y2) → _+_ G x1 y1 , _+_ H x2 y2 })
            (λ { (x1 , x2) → -_ G x1 , -_ H x2 })
            (isSet× (isSetCarrier (GC , G)) (isSetCarrier (HC , H)))
            (λ { (x1 , x2) (y1 , y2) (z1 , z2) i →
               assoc G x1 y1 z1 i , assoc H x2 y2 z2 i })
            (λ { (x1 , x2) i → GroupStr.rid G x1 i , GroupStr.rid H x2 i })
            (λ { (x1 , x2) i → GroupStr.lid G x1 i , GroupStr.lid H x2 i })
            (λ { (x1 , x2) i → GroupStr.invr G x1 i , GroupStr.invr H x2 i })
            (λ { (x1 , x2) i → GroupStr.invl G x1 i , GroupStr.invl H x2 i })

trivialGroup : Group₀
trivialGroup = Unit , groupstr tt (λ _ _ → tt) (λ _ → tt)
                      (makeIsGroup isSetUnit (λ _ _ _ → refl) (λ _ → refl) (λ _ → refl)
                                   (λ _ → refl) (λ _ → refl))

intGroup : Group₀
intGroup = Int , groupstr 0 _+Int_ (0 -Int_)
                 (makeIsGroup isSetInt +-assoc (λ x → refl) (λ x → +-comm 0 x)
                              (λ x → +-comm x (pos 0 -Int x) ∙ minusPlus x 0) (λ x → minusPlus x 0))
