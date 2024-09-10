{-# OPTIONS --safe #-}
module Cubical.Algebra.BooleanRing.Base where

open import Cubical.Foundations.Prelude hiding (_∧_;_∨_)
open import Cubical.Foundations.Structure
open import Cubical.Data.Empty as ⊥
open import Cubical.Algebra.Ring
open import Cubical.Algebra.AbGroup.Base
open import Cubical.Algebra.CommRing
open import Cubical.Tactics.CommRingSolver


private
  variable
   ℓ ℓ' : Level

record IsBooleanRing {B : Type ℓ}
  (𝟘 𝟙 : B) (_+_ _·_ : B → B → B) (-_ : B → B) : Type ℓ where
  no-eta-equality

  field
    isCommRing   : IsCommRing 𝟘 𝟙 _+_ _·_ -_
    ·Idem : (x : B) → x · x ≡ x

  open IsCommRing isCommRing public

record BooleanStr (A : Type ℓ) : Type (ℓ-suc ℓ) where
  field
    𝟘          : A
    𝟙          : A
    _+_        : A → A → A
    _·_        : A → A → A
    -_         : A → A
    isBooleanRing : IsBooleanRing 𝟘 𝟙 _+_ _·_ -_

  infix  8 -_
  infixl 7 _·_
  infixl 6 _+_

  open IsBooleanRing isBooleanRing public

BooleanRing : ∀ ℓ → Type (ℓ-suc ℓ)
BooleanRing ℓ = TypeWithStr ℓ BooleanStr

BooleanStr→CommRingStr : { A : Type ℓ } →  BooleanStr A  → CommRingStr A
BooleanStr→CommRingStr x = record { isCommRing = IsBooleanRing.isCommRing (BooleanStr.isBooleanRing x) }

BooleanRing→CommRing : BooleanRing ℓ → CommRing ℓ
BooleanRing→CommRing (carrier , structure ) = carrier , BooleanStr→CommRingStr structure

module BooleanAlgebraStr (A : BooleanRing ℓ)  where
  open BooleanStr (A . snd)
  _∨_ : ⟨ A ⟩ → ⟨ A ⟩ → ⟨ A ⟩
  a ∨ b = (a + b) + (a · b)
  _∧_ : ⟨ A ⟩ → ⟨ A ⟩ → ⟨ A ⟩
  a ∧ b = a · b
  ¬_ : ⟨ A ⟩ → ⟨ A ⟩
  ¬ a = 𝟙 + a

  infix  8 ¬_
  infixl 7 _∧_
  infixl 6 _∨_

  variable x y z : ⟨ A ⟩

  ∧Idem : x ∧ x ≡ x
  ∧Idem = ·Idem _

  ∧Assoc : x ∧ ( y ∧ z ) ≡ ( x ∧ y ) ∧ z
  ∧Assoc = ·Assoc _ _ _

  ∧Comm :  x ∧ y ≡ y ∧ x
  ∧Comm = ·Comm _ _

  ∨Assoc : (x ∨ ( y ∨ z ) ≡ ( x ∨ y ) ∨ z )
  ∨Assoc =  solve! (BooleanRing→CommRing A)

  ∨Comm : x ∨ y ≡ y ∨ x
  ∨Comm  = solve! (BooleanRing→CommRing A)

  ∨IdR : x ∨ 𝟘 ≡ x
  ∨IdR = solve! (BooleanRing→CommRing A)

  ∨IdL : 𝟘 ∨ x ≡ x
  ∨IdL = solve! (BooleanRing→CommRing A)

  ∧IdR : x ∧ 𝟙 ≡ x
  ∧IdR = ·IdR _

  ∧IdL : 𝟙 ∧ x ≡ x
  ∧IdL = ·IdL _

  ∧AnnihilR : x ∧ 𝟘 ≡ 𝟘
  ∧AnnihilR = RingTheory.0RightAnnihilates (CommRing→Ring (BooleanRing→CommRing A)) _

  ∧AnnihilL : 𝟘 ∧ x ≡ 𝟘
  ∧AnnihilL = RingTheory.0LeftAnnihilates (CommRing→Ring (BooleanRing→CommRing A)) _

  -IsId : x + x ≡ 𝟘
  -IsId {x = x} =  RingTheory.+Idempotency→0 (CommRing→Ring (BooleanRing→CommRing A)) (x + x) 2x≡4x
    where
      2x≡4x : x + x ≡ (x + x) + (x + x)
      2x≡4x =
        x + x
          ≡⟨ sym (·Idem (x + x)) ⟩
        (x + x) · (x + x)
          ≡⟨ solve! (BooleanRing→CommRing A) ⟩
        ((x · x) + (x · x)) + ((x · x) + (x · x))
          ≡⟨ cong₂ _+_ (cong₂ _+_ (·Idem x) (·Idem x)) (cong₂ _+_ (·Idem x) (·Idem x)) ⟩
        (x + x) + (x + x) ∎

  ∨Idem   : x ∨ x ≡ x
  ∨Idem { x = x } =
    x + x + x · x
      ≡⟨ cong (λ y → y + x · x) -IsId ⟩
    𝟘  + x · x
      ≡⟨ +IdL (x · x) ⟩
    x · x
      ≡⟨ ·Idem x ⟩
    x ∎

  1Absorbs∨R : x ∨ 𝟙 ≡ 𝟙
  1Absorbs∨R {x = x} =
    (x + 𝟙) + (x · 𝟙)
      ≡⟨ solve! (BooleanRing→CommRing A) ⟩
    𝟙 + (x + x)
      ≡⟨ cong (λ y → 𝟙 + y) -IsId ⟩
    𝟙 + 𝟘
      ≡⟨ +IdR 𝟙 ⟩
    𝟙 ∎

  1Absorbs∨L : 𝟙 ∨ x ≡ 𝟙
  1Absorbs∨L {x = x} = ∨Comm ∙ 1Absorbs∨R

  ∧DistR∨ : x ∧ ( y ∨ z) ≡ (x ∧ y) ∨ (x ∧ z)
  ∧DistR∨ {x = x} {y = y} { z = z} =
    x · ((y + z) + (y · z))
      ≡⟨ solve! (BooleanRing→CommRing A) ⟩
    x · y + x · z +   x   · (y · z)
      ≡⟨ cong (λ a → x · y + x · z + a · (y · z)) (sym (·Idem x)) ⟩
    x · y + x · z + x · x · (y · z)
      ≡⟨  solve! (BooleanRing→CommRing A) ⟩
    x · y + x · z + (x · y) · (x · z) ∎

  ∧DistL∨ : (x ∨ y) ∧ z ≡ (x ∧ z) ∨ (y ∧ z)
  ∧DistL∨ = ∧Comm ∙ ∧DistR∨ ∙ cong₂ _∨_ ∧Comm ∧Comm

  ∨DistR∧ :  x ∨ (y ∧ z) ≡ (x ∨ y) ∧ (x ∨ z)
  ∨DistR∧ {x = x} {y = y} {z = z} =
    x + (y · z) + x · (y · z)
      ≡⟨ solve! (BooleanRing→CommRing A) ⟩
    x + 𝟘 + 𝟘 + y · z + 𝟘 + x · y · z
      ≡⟨ cong (λ a → a + 𝟘 + 𝟘 + y · z + 𝟘 + a · y · z) (sym (·Idem x)) ⟩
    x · x + 𝟘  + 𝟘  + y · z + 𝟘 + x · x · y · z
      ≡⟨ cong (λ a → x · x + 𝟘 + 𝟘 + y · z + a + x · x · y · z) (sym (-IsId {x = (x · y) · z})) ⟩
    x · x + 𝟘 + 𝟘 + y · z + (x · y · z + x · y · z) + x · x · y · z
      ≡⟨ (cong₂ (λ a b → x · x + a + b + y · z + (x · y · z + x · y · z) + x · x · y · z)) (xa-xxa≡0 z) (xa-xxa≡0 y) ⟩
    x · x + (x · z + x · x · z) + (x · y + x · x · y) + y · z + (x · y · z + x · y · z) + x · x · y · z
      ≡⟨ solve! (BooleanRing→CommRing A) ⟩
    (x + y + x · y) · (x + z + x · z) ∎ where
      xa≡xxa : (a : ⟨ A ⟩) → x · a ≡ (x · x ) · a
      xa≡xxa a = cong (λ y → y · a) (sym (·Idem x))
      xa-xxa≡0 : (a : ⟨ A ⟩) → 𝟘 ≡ x · a + x · x · a
      xa-xxa≡0 a =
       𝟘
         ≡⟨ sym -IsId ⟩
       x · a + x · a
         ≡⟨ cong (λ y → x · a + y · a) (sym (·Idem x)) ⟩
       x · a + x · x · a ∎

  ∨Distr∧R :  (x ∧ y) ∨ z ≡ (x ∨ z) ∧ (y ∨ z)
  ∨Distr∧R = ∨Comm ∙ ∨DistR∧ ∙ cong₂ _∧_ ∨Comm ∨Comm

  ∧AbsorbL∨ : x ∧ (x ∨ y) ≡ x
  ∧AbsorbL∨ {x = x} {y = y} =
    x · ((x + y) + (x · y))
      ≡⟨ solve! (BooleanRing→CommRing A) ⟩
    x · x + (x · y + x · x · y)
      ≡⟨ cong (λ z → z + ((x · y) + (z · y))) (·Idem x) ⟩
    x + (x · y + x · y)
      ≡⟨ cong (_+_ x) -IsId ⟩
    x + 𝟘
      ≡⟨ +IdR x ⟩
    x ∎

  ∨AbsorbL∧ :  x ∨ (x ∧ y) ≡ x
  ∨AbsorbL∧ {x = x} { y = y}  =
    x + x · y + x · (x · y)
      ≡⟨ solve! (BooleanRing→CommRing A)  ⟩
    x + (x · y + x · x · y)
      ≡⟨ cong (λ z → x + (x · y + z · y)) (·Idem x) ⟩
    x + (x · y + x · y)
      ≡⟨ cong (_+_ x) -IsId ⟩
    x + 𝟘
      ≡⟨ +IdR x ⟩
    x ∎

  ¬Cancels∧R : x ∧ ¬ x ≡ 𝟘
  ¬Cancels∧R {x = x} =
    x · (𝟙 + x)
      ≡⟨ solve! (BooleanRing→CommRing A) ⟩
    x + x · x
      ≡⟨ cong (λ y → x + y) (·Idem x) ⟩
    x + x
      ≡⟨ -IsId ⟩
    𝟘 ∎

  ¬Cancels∧L : ¬ x ∧ x ≡ 𝟘
  ¬Cancels∧L = ∧Comm ∙ ¬Cancels∧R

  ¬Completes∨R : x ∨ ¬ x ≡ 𝟙
  ¬Completes∨R {x = x} =
    x + ¬ x + (x ∧ ¬ x)
      ≡⟨ cong (λ z → x + ¬ x + z) ¬Cancels∧R ⟩
    x + ¬ x + 𝟘
      ≡⟨ solve! (BooleanRing→CommRing A) ⟩
    x ∨ 𝟙
      ≡⟨ 1Absorbs∨R ⟩
    𝟙 ∎

  ¬Completes∨L : (¬ x) ∨ x ≡ 𝟙
  ¬Completes∨L = ∨Comm ∙ ¬Completes∨R

  ¬Invol : ¬ ¬ x ≡ x
  ¬Invol {x = x} =
    𝟙 + (𝟙 + x)
      ≡⟨ +Assoc 𝟙 𝟙 x ⟩
    (𝟙 + 𝟙) + x
      ≡⟨ cong (λ y → y + x) ( -IsId {x = 𝟙}) ⟩
    𝟘 + x
      ≡⟨ +IdL x ⟩
    x ∎

  ¬0≡1 : ¬ 𝟘 ≡ 𝟙
  ¬0≡1 = +IdR 𝟙

  ¬1≡0 : ¬ 𝟙 ≡ 𝟘
  ¬1≡0 = -IsId {x = 𝟙}

  DeMorgan¬∨ : ¬ (x ∨ y) ≡ ¬ x ∧ ¬ y
  DeMorgan¬∨ = solve! (BooleanRing→CommRing A)

  DeMorgan¬∧ : ¬ (x ∧ y) ≡ ¬ x ∨ ¬ y
  DeMorgan¬∧ {x = x} {y = y} =
    𝟙 + x · y
      ≡⟨ solve! (BooleanRing→CommRing A) ⟩
    𝟘 + 𝟘 + 𝟙 + x · y
      ≡⟨ cong₂ (λ a b → ((a + b) + 𝟙) + (x · y)) (sym (-IsId {x = 𝟙 + x})) (sym (-IsId {x = y})) ⟩
    ((𝟙 + x)  + (𝟙 + x)) + (y + y)  + 𝟙 + x · y
      ≡⟨ solve! (BooleanRing→CommRing A) ⟩
    ¬ x ∨ ¬ y ∎
