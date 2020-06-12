{-# OPTIONS --cubical --no-import-sorts --safe #-}

module Cubical.Structures.Ring where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.HLevels
open import Cubical.Data.Sigma

open import Cubical.Foundations.SIP renaming (SNS-PathP to SNS)

open import Cubical.Structures.NAryOp
open import Cubical.Structures.Monoid hiding (⟨_⟩)
open import Cubical.Structures.AbGroup hiding (⟨_⟩)
open import Cubical.Structures.Pointed

private
  variable
    ℓ ℓ' : Level

raw-ring-structure : Type ℓ → Type ℓ
raw-ring-structure X = (X → X → X) × X × (X → X → X)

-- Maybe this is not the best way? (Suggestions welcome, maybe having raw-monoid-iso defined?)
raw-ring-is-SNS : SNS {ℓ} raw-ring-structure _
raw-ring-is-SNS = join-SNS binaryIso binarySNS
                           (join-iso pointed-iso binaryIso)
                           (join-SNS
                             pointed-iso pointed-is-SNS
                             binaryIso binarySNS)
  where
  binaryIso = binaryFunIso pointed-iso
  binarySNS = binaryFunSNS pointed-iso pointed-is-SNS

ring-axioms : (X : Type ℓ) (s : raw-ring-structure X) → Type ℓ
ring-axioms X (_+_ , 1r , _·_) = abelian-group-axioms X _+_ ×
                                monoid-axioms X (1r , _·_) ×
                                ((x y z : X) → x · (y + z) ≡ (x · y) + (x · z)) ×
                                ((x y z : X) → (x + y) · z ≡ (x · z) + (y · z))

ring-structure : Type ℓ → Type ℓ
ring-structure = add-to-structure raw-ring-structure ring-axioms

Ring : Type (ℓ-suc ℓ)
Ring {ℓ} = TypeWithStr ℓ ring-structure

ring-str-iso : StrIso raw-ring-structure ℓ
ring-str-iso = (join-iso (binaryFunIso pointed-iso) (join-iso pointed-iso (binaryFunIso pointed-iso)))

ring-iso : StrIso ring-structure ℓ
ring-iso =
  add-to-iso
    ring-str-iso
    ring-axioms

ring-axioms-isProp : (X : Type ℓ) (s : raw-ring-structure X) → isProp (ring-axioms X s)
ring-axioms-isProp X (_+_ , 1r , _·_) = isPropΣ (abelian-group-axioms-isProp X _+_)
                                      λ _ → isPropΣ (monoid-axioms-are-Props X (1r , _·_))
                                      λ { (isSetX , _) → isPropΣ (isPropΠ3 (λ _ _ _ → isSetX _ _))
                                      λ _ → isPropΠ3 (λ _ _ _ → isSetX _ _)}

ring-is-SNS : SNS {ℓ} ring-structure ring-iso
ring-is-SNS = add-axioms-SNS _ ring-axioms-isProp raw-ring-is-SNS

RingPath : (M N : Ring {ℓ}) → (M ≃[ ring-iso ] N) ≃ (M ≡ N)
RingPath = SIP ring-is-SNS

-- Rings have an abelian group

Ring→AbGroup : Ring {ℓ} → AbGroup {ℓ}
Ring→AbGroup (R , (_+_ , _) , +AbGroup , _) = R , _+_ , +AbGroup

-- Rings have a monoid

Ring→Monoid : Ring {ℓ} → Monoid {ℓ}
Ring→Monoid (R , (_ , 1r , _·_) , _ , ·Monoid , _) = R , (1r , _·_) , ·Monoid

-- Ring extractors

⟨_⟩ : Ring {ℓ} → Type ℓ
⟨ R , _ ⟩ = R

module partialRingAxioms (R : Ring {ℓ}) where
  ring+-operation = abgroup-operation (Ring→AbGroup R)

  ring-is-set = abgroup-is-set (Ring→AbGroup R)

  ring+-assoc = abgroup-assoc (Ring→AbGroup R)

  ring+-id = abgroup-id (Ring→AbGroup R)

  ring+-rid = abgroup-rid (Ring→AbGroup R)

  ring+-lid = abgroup-lid (Ring→AbGroup R)

  ring+-inv = abgroup-inv (Ring→AbGroup R)

  ring+-rinv = abgroup-rinv (Ring→AbGroup R)

  ring+-linv = abgroup-linv (Ring→AbGroup R)

  ring+-comm = abgroup-comm (Ring→AbGroup R)

  ring·-operation = monoid-operation (Ring→Monoid R)

  ring·-assoc = monoid-assoc (Ring→Monoid R)

  ring·-id = monoid-id (Ring→Monoid R)

  ring·-rid = monoid-rid (Ring→Monoid R)

  ring·-lid = monoid-lid (Ring→Monoid R)


module explicit-ring-syntax where
  open partialRingAxioms

  ring+-operation-syntax : (R : Ring {ℓ}) → ⟨ R ⟩ → ⟨ R ⟩ → ⟨ R ⟩
  ring+-operation-syntax R = ring+-operation R

  infixr 14 ring+-operation-syntax
  syntax ring+-operation-syntax R x y = x +⟨ R ⟩ y

  ring·-operation-syntax : (R : Ring {ℓ}) → ⟨ R ⟩ → ⟨ R ⟩ → ⟨ R ⟩
  ring·-operation-syntax R = ring·-operation R

  infixr 18 ring·-operation-syntax
  syntax ring·-operation-syntax R x y = x ·⟨ R ⟩ y

  ring₁-constant-syntax : (R : Ring {ℓ}) → ⟨ R ⟩
  ring₁-constant-syntax R = ring·-id R

  syntax ring₁-constant-syntax R = ₁⟨ R ⟩

module ring-axioms (R : Ring {ℓ}) where
  open explicit-ring-syntax
  open partialRingAxioms R public

  private
    ring-rdist′ : (R : Ring {ℓ}) (x y z : ⟨ R ⟩) → x ·⟨ R ⟩ (y +⟨ R ⟩ z) ≡ (x ·⟨ R ⟩ y) +⟨ R ⟩ (x ·⟨ R ⟩ z)
    ring-rdist′ (_ , _ , _ , _ , P , _) = P

    ring-ldist′ : (R : Ring {ℓ}) (x y z : ⟨ R ⟩) → (x +⟨ R ⟩ y) ·⟨ R ⟩ z ≡ (x ·⟨ R ⟩ z) +⟨ R ⟩ (y ·⟨ R ⟩ z)
    ring-ldist′ (_ , _ , _ , _ , _ , P) = P

  ring-rdist = ring-rdist′ R
  ring-ldist = ring-ldist′ R


ringIsSet : (R : Ring {ℓ}) → isSet (⟨ R ⟩)
ringIsSet R = abgroupIsSet (Ring→AbGroup R)

-- Ring syntax

module ring-syntax (R : Ring {ℓ}) where
  open partialRingAxioms

  infixr 14 _+_
  infixr 14 _-_
  infixr 18 _·_
  infix  15 -_

  _+_ = ring+-operation R

  _·_ = ring·-operation R

  0r = ring+-id R

  1r = ring·-id R

  -_ = ring+-inv R

  _-_ : ⟨ R ⟩ → ⟨ R ⟩ → ⟨ R ⟩
  x - y = x + - y


record expandedRingStructure {ℓ} (R : Type ℓ) : Type ℓ where
  field
    0r : R
    1r : R
    _+_ : R → R → R
    -_ : R → R
    _·_ : R → R → R

    +-assoc : (x y z : R) → x + (y + z) ≡ (x + y) + z
    +-rid : (x : R) → x + 0r ≡ x
    +-comm : (x y : R) → x + y ≡ y + x
    +-rinv : (x : R) → x + (- x) ≡ 0r

    ·-assoc : (x y z : R) → x · (y · z) ≡ (x · y) · z
    ·-lid : (x : R) → 1r · x ≡ x
    ·-rid : (x : R) → x · 1r ≡ x

    ldist : (x y z : R) → (x + y) · z ≡ (x · z) + (y · z)
    rdist : (x y z : R) → x · (y + z) ≡ (x · y) + (x · z)

  +-lid : (x : R) → 0r + x ≡ x
  +-lid x =         0r + x     ≡⟨ +-comm _ _ ⟩
                    x + 0r     ≡⟨ +-rid x ⟩
                    x         ∎

  +-linv : (x : R) → (- x) + x ≡ 0r
  +-linv x =         (- x) + x    ≡⟨ +-comm _ _ ⟩
                     x + (- x)    ≡⟨ +-rinv x ⟩
                     0r            ∎

createRing : (R : Type ℓ)
             → isSet R
             → expandedRingStructure R
             → Ring {ℓ}
createRing R isSet-R ringStr =
           let open expandedRingStructure ringStr
           in R , (_+_ , 1r , _·_) ,
              (((isSet-R , +-assoc)
                , 0r
                , ((λ x → +-rid x , +-lid x)
                  , λ x → (- x) , ((+-rinv x) , (+-linv x))))
                , +-comm)
              , (isSet-R
                , (·-assoc
                  , (·-rid
                    , ·-lid)))
              , rdist
                , ldist


{-
  some basic calculations (used for example in QuotientRing.agda),
  that might should become obsolete or subject to change once we
  have a ring solver (see https://github.com/agda/cubical/issues/297)
-}
module theory (R : Ring {ℓ}) where
  open ring-axioms R
  open ring-syntax R

  implicitInverse : (x y : ⟨ R ⟩)
                 → x + y ≡ 0r
                 → y ≡ - x
  implicitInverse x y p = y             ≡⟨ sym (ring+-lid y) ⟩
                       0r + y            ≡⟨ cong (λ u → u + y)
                                               (sym (ring+-linv x)) ⟩
                       (- x + x) + y   ≡⟨ sym (ring+-assoc _ _ _) ⟩
                       (- x) + (x + y) ≡⟨ cong (λ u → (- x) + u) p ⟩
                       (- x) + 0r       ≡⟨ ring+-rid _ ⟩
                       - x             ∎

  0-selfinverse : - 0r ≡ 0r
  0-selfinverse = sym (implicitInverse _ _ (ring+-rid 0r))

  0-idempotent : 0r + 0r ≡ 0r
  0-idempotent = ring+-lid 0r

  +-idempotency→0 : (x : ⟨ R ⟩) → x ≡ x + x → 0r ≡ x
  +-idempotency→0 x p = 0r               ≡⟨ sym (ring+-rinv _) ⟩
                        x + (- x)       ≡⟨ cong (λ u → u + (- x)) p ⟩
                        (x + x) + (- x)   ≡⟨ sym (ring+-assoc _ _ _) ⟩
                        x + (x + (- x)) ≡⟨ cong (λ u → x + u) (ring+-rinv _) ⟩
                        x + 0r           ≡⟨ ring+-rid x ⟩
                        x               ∎

  0-rightNullifies : (x : ⟨ R ⟩) → x · 0r ≡ 0r
  0-rightNullifies x =
              let x·0-is-idempotent : x · 0r ≡ x · 0r + x · 0r
                  x·0-is-idempotent =
                    x · 0r              ≡⟨ cong (λ u → x · u) (sym 0-idempotent) ⟩
                    x · (0r + 0r)        ≡⟨ (ring-rdist _ _ _) ⟩
                    (x · 0r) + (x · 0r)  ∎
              in sym (+-idempotency→0 _ x·0-is-idempotent)

  0-leftNullifies : (x : ⟨ R ⟩) → 0r · x ≡ 0r
  0-leftNullifies x =
              let 0·x-is-idempotent : 0r · x ≡ 0r · x + 0r · x
                  0·x-is-idempotent =
                    0r · x              ≡⟨ cong (λ u → u · x) (sym 0-idempotent) ⟩
                    (0r + 0r) · x        ≡⟨ (ring-ldist _ _ _) ⟩
                    (0r · x) + (0r · x)  ∎
              in sym (+-idempotency→0 _ 0·x-is-idempotent)

  -commutesWithRight-· : (x y : ⟨ R ⟩) →  x · (- y) ≡ - (x · y)
  -commutesWithRight-· x y = implicitInverse (x · y) (x · (- y))

                               (x · y + x · (- y)     ≡⟨ sym (ring-rdist _ _ _) ⟩
                               x · (y + (- y))        ≡⟨ cong (λ u → x · u) (ring+-rinv y) ⟩
                               x · 0r                  ≡⟨ 0-rightNullifies x ⟩
                               0r ∎)

  -commutesWithLeft-· : (x y : ⟨ R ⟩) →  (- x) · y ≡ - (x · y)
  -commutesWithLeft-· x y = implicitInverse (x · y) ((- x) · y)

                              (x · y + (- x) · y     ≡⟨ sym (ring-ldist _ _ _) ⟩
                              (x - x) · y            ≡⟨ cong (λ u → u · y) (ring+-rinv x) ⟩
                              0r · y                  ≡⟨ 0-leftNullifies y ⟩
                              0r ∎)

  -isDistributive : (x y : ⟨ R ⟩) →  (- x) + (- y) ≡ - (x + y)
  -isDistributive x y =
    implicitInverse _ _
         ((x + y) + ((- x) + (- y)) ≡⟨ sym (ring+-assoc _ _ _) ⟩
          x + (y + ((- x) + (- y))) ≡⟨ cong
                                         (λ u → x + (y + u))
                                         (ring+-comm _ _) ⟩
          x + (y + ((- y) + (- x))) ≡⟨ cong (λ u → x + u) (ring+-assoc _ _ _) ⟩
          x + ((y + (- y)) + (- x)) ≡⟨ cong (λ u → x + (u + (- x)))
                                            (ring+-rinv _) ⟩
          x + (0r + (- x))           ≡⟨ cong (λ u → x + u) (ring+-lid _) ⟩
          x + (- x)                 ≡⟨ ring+-rinv _ ⟩
          0r ∎)

  translatedDifference :
    ∀ (x a b : ⟨ R ⟩)
    → a - b ≡ (x + a) - (x + b)
  translatedDifference x a b =
              a - b                       ≡⟨ cong (λ u → a + u)
                                                  (sym (ring+-lid _)) ⟩
              (a + (0r + (- b)))          ≡⟨ cong (λ u → a + (u + (- b)))
                                                  (sym (ring+-rinv _)) ⟩
              (a + ((x + (- x)) + (- b))) ≡⟨ cong (λ u → a + u)
                                                  (sym (ring+-assoc _ _ _)) ⟩
              (a + (x + ((- x) + (- b)))) ≡⟨ (ring+-assoc _ _ _) ⟩
              ((a + x) + ((- x) + (- b))) ≡⟨ cong (λ u → u + ((- x) + (- b)))
                                                  (ring+-comm _ _) ⟩
              ((x + a) + ((- x) + (- b))) ≡⟨ cong (λ u → (x + a) + u)
                                                  (-isDistributive _ _) ⟩
              ((x + a) - (x + b)) ∎
