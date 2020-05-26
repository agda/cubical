{-# OPTIONS --cubical --safe #-}

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
raw-ring-is-SNS = join-SNS (nAryFunIso 2) (nAryFunSNS 2)
                           (join-iso pointed-iso (nAryFunIso 2))
                           (join-SNS pointed-iso pointed-is-SNS (nAryFunIso 2) (nAryFunSNS 2))

ring-axioms : (X : Type ℓ) (s : raw-ring-structure X) → Type ℓ
ring-axioms X (_+_ , ₁ , _·_) = abelian-group-axioms X _+_ ×
                                monoid-axioms X (₁ , _·_) ×
                                ((x y z : X) → x · (y + z) ≡ (x · y) + (x · z)) ×
                                ((x y z : X) → (x + y) · z ≡ (x · z) + (y · z))

ring-structure : Type ℓ → Type ℓ
ring-structure = add-to-structure raw-ring-structure ring-axioms

Ring : Type (ℓ-suc ℓ)
Ring {ℓ} = TypeWithStr ℓ ring-structure

ring-iso : StrIso ring-structure ℓ
ring-iso = add-to-iso (join-iso (nAryFunIso 2) (join-iso pointed-iso (nAryFunIso 2))) ring-axioms

ring-axioms-isProp : (X : Type ℓ) (s : raw-ring-structure X) → isProp (ring-axioms X s)
ring-axioms-isProp X (_+_ , ₁ , _·_) = isPropΣ (abelian-group-axioms-isProp X _+_)
                                      λ _ → isPropΣ (monoid-axioms-are-Props X (₁ , _·_))
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
Ring→Monoid (R , (_ , ₁ , _·_) , _ , ·Monoid , _) = R , (₁ , _·_) , ·Monoid

-- Ring extractors

⟨_⟩ : Ring {ℓ} → Type ℓ
⟨ R , _ ⟩ = R

module ringAxioms (R : Ring {ℓ}) where
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

module ring-syntax where
  open ringAxioms

  ring+-operation-syntax : (R : Ring {ℓ}) → ⟨ R ⟩ → ⟨ R ⟩ → ⟨ R ⟩
  ring+-operation-syntax R = ring+-operation R

  infixr 14 ring+-operation-syntax
  syntax ring+-operation-syntax R x y = x +⟨ R ⟩ y

  ring·-operation-syntax : (R : Ring {ℓ}) → ⟨ R ⟩ → ⟨ R ⟩ → ⟨ R ⟩
  ring·-operation-syntax R = ring·-operation R

  infixr 18 ring·-operation-syntax
  syntax ring·-operation-syntax R x y = x ·⟨ R ⟩ y

open ring-syntax

ring-rdist : (R : Ring {ℓ}) (x y z : ⟨ R ⟩) → x ·⟨ R ⟩ (y +⟨ R ⟩ z) ≡ (x ·⟨ R ⟩ y) +⟨ R ⟩ (x ·⟨ R ⟩ z)
ring-rdist (_ , _ , _ , _ , P , _) = P

ring-ldist : (R : Ring {ℓ}) (x y z : ⟨ R ⟩) → (x +⟨ R ⟩ y) ·⟨ R ⟩ z ≡ (x ·⟨ R ⟩ z) +⟨ R ⟩ (y ·⟨ R ⟩ z)
ring-ldist (_ , _ , _ , _ , _ , P) = P

-- Ring ·syntax

module ring-·syntax (R : Ring {ℓ}) where
  open ringAxioms
  
  infixr 14 _+_
  infixr 14 _-_
  infixr 18 _·_
  infix  15 -_

  _+_ = ring+-operation R

  _·_ = ring·-operation R

  ₀ = ring+-id R

  ₁ = ring·-id R

  -_ = ring+-inv R

  _-_ : ⟨ R ⟩ → ⟨ R ⟩ → ⟨ R ⟩
  x - y = x + - y


record ringStructure {ℓ} (R : Type ℓ) : Type ℓ where
  field
    ₀ : R
    ₁ : R
    _+_ : R → R → R
    -_ : R → R
    _·_ : R → R → R

    +-assoc : (x y z : R) → x + (y + z) ≡ (x + y) + z
    +-rid : (x : R) → x + ₀ ≡ x
    +-comm : (x y : R) → x + y ≡ y + x
    +-rinv : (x : R) → x + (- x) ≡ ₀

    ·-assoc : (x y z : R) → x · (y · z) ≡ (x · y) · z
    ·-lid : (x : R) → ₁ · x ≡ x
    ·-rid : (x : R) → x · ₁ ≡ x

    ldist : (x y z : R) → (x + y) · z ≡ (x · z) + (y · z)
    rdist : (x y z : R) → x · (y + z) ≡ (x · y) + (x · z)

  +-lid : (x : R) → ₀ + x ≡ x
  +-lid x =         ₀ + x     ≡⟨ +-comm _ _ ⟩
                    x + ₀     ≡⟨ +-rid x ⟩
                    x         ∎
  
  +-linv : (x : R) → (- x) + x ≡ ₀
  +-linv x =         (- x) + x    ≡⟨ +-comm _ _ ⟩
                     x + (- x)    ≡⟨ +-rinv x ⟩
                     ₀            ∎

createRing : (R : Type ℓ)
             → isSet R
             → ringStructure R
             → Ring {ℓ}
createRing R isSet-R ringStr =
           let open ringStructure ringStr 
           in R , (_+_ , ₁ , _·_) ,
              (((isSet-R , +-assoc)
                , ₀
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
module calculations (R : Ring {ℓ}) where
  open ringAxioms R
  open ring-·syntax R

  implicitInverse : (x y : ⟨ R ⟩)
                 → x + y ≡ ₀
                 → y ≡ - x
  implicitInverse x y p = y             ≡⟨ sym (ring+-lid y) ⟩
                       ₀ + y            ≡⟨ cong (λ u → u + y)
                                               (sym (ring+-linv x)) ⟩
                       (- x + x) + y   ≡⟨ sym (ring+-assoc _ _ _) ⟩
                       (- x) + (x + y) ≡⟨ cong (λ u → (- x) + u) p ⟩
                       (- x) + ₀       ≡⟨ ring+-rid _ ⟩
                       - x             ∎ 

  0-selfinverse : - ₀ ≡ ₀
  0-selfinverse = sym (implicitInverse _ _ (ring+-rid ₀))

  0-idempotent : ₀ + ₀ ≡ ₀
  0-idempotent = ring+-lid ₀

  +-idempotency→0 : (x : ⟨ R ⟩) → x ≡ x + x → ₀ ≡ x
  +-idempotency→0 x p = ₀               ≡⟨ sym (ring+-rinv _) ⟩
                        x + (- x)       ≡⟨ cong (λ u → u + (- x)) p ⟩
                        (x + x) + (- x)   ≡⟨ sym (ring+-assoc _ _ _) ⟩
                        x + (x + (- x)) ≡⟨ cong (λ u → x + u) (ring+-rinv _) ⟩
                        x + ₀           ≡⟨ ring+-rid x ⟩
                        x               ∎
  
  0-rightNullifies : (x : ⟨ R ⟩) → ₀ ≡ x · ₀
  0-rightNullifies x =
              let x·0-is-idempotent : x · ₀ ≡ x · ₀ + x · ₀
                  x·0-is-idempotent =
                    x · ₀              ≡⟨ cong (λ u → x · u) (sym 0-idempotent) ⟩
                    x · (₀ + ₀)        ≡⟨ (ring-rdist R _ _ _) ⟩ 
                    (x · ₀) + (x · ₀)  ∎
              in +-idempotency→0 _ x·0-is-idempotent
              
  0-leftNullifies : (x : ⟨ R ⟩) → ₀ ≡ ₀ · x
  0-leftNullifies x =
              let 0·x-is-idempotent : ₀ · x ≡ ₀ · x + ₀ · x
                  0·x-is-idempotent =
                    ₀ · x              ≡⟨ cong (λ u → u · x) (sym 0-idempotent) ⟩
                    (₀ + ₀) · x        ≡⟨ (ring-ldist R _ _ _) ⟩ 
                    (₀ · x) + (₀ · x)  ∎
              in +-idempotency→0 _ 0·x-is-idempotent
              
  -commutesWithRight-· : (x y : ⟨ R ⟩) →  x · (- y) ≡ - (x · y)
  -commutesWithRight-· x y = implicitInverse (x · y) (x · (- y))
  
                                        (x · y + x · (- y)     ≡⟨ sym (ring-rdist R _ _ _) ⟩
                                        x · (y + (- y))        ≡⟨ cong (λ u → x · u) (ring+-rinv y) ⟩
                                        x · ₀                  ≡⟨ sym (0-rightNullifies x) ⟩
                                        ₀ ∎) 

  -commutesWithLeft-· : (x y : ⟨ R ⟩) →  (- x) · y ≡ - (x · y)
  -commutesWithLeft-· x y = implicitInverse (x · y) ((- x) · y)
  
                                        (x · y + (- x) · y     ≡⟨ sym (ring-ldist R _ _ _) ⟩
                                        (x - x) · y            ≡⟨ cong (λ u → u · y) (ring+-rinv x) ⟩
                                        ₀ · y                  ≡⟨ sym (0-leftNullifies y) ⟩
                                        ₀ ∎) 
