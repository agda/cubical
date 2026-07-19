
{-
  The suspension of a Cartesian product is given by a triple wedge sum
    Σ (X × Y) = Σ X ⋁ Σ Y ⋁ Σ (X ⋀ Y)
-}

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Path
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.GroupoidLaws
open import Cubical.Foundations.Pointed
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Univalence

open import Cubical.Data.Sigma
open import Cubical.Data.Unit

open import Cubical.HITs.Pushout
open import Cubical.HITs.Susp
open import Cubical.HITs.SmashProduct
open import Cubical.HITs.Join
open import Cubical.HITs.Wedge

module Cubical.HITs.Susp.SuspProduct where

module PushoutNull {ℓ ℓ'} (X : Type ℓ) (Y : Type ℓ') (y₀ : Y) where

  {- The pushout of a null map is equivalent to a wedge with the suspension
    X --> 1 --> Y
    ↓     ↓     ↓
    1 -> Σ X -> ? = B
  -}

  module _ where
    open PushoutPasteLeft
      (rotatePushoutSquare (_ , SuspPushoutSquare ℓ-zero ℓ-zero X))
      {B = (Susp X , north) ⋁ (Y , y₀)}
      (const y₀) inr inl (funExt (λ _ → push _))

    squareL : commSquare
    squareL = totSquare

    pushoutSquareL : PushoutSquare
    pushoutSquareL = squareL , isPushoutRightSquare→isPushoutTotSquare
      (snd (⋁-PushoutSquare _ _ ℓ-zero))

  module _ where
    open PushoutPasteDown
      (_ , SuspPushoutSquare ℓ-zero ℓ-zero X)
      {B = (Susp X , north) ⋁ (Y , y₀)}
      (const y₀) inr inl (funExt (λ _ → sym (push _)))

    squareR : commSquare
    squareR = totSquare

    pushoutSquareR : PushoutSquare
    pushoutSquareR = squareR , isPushoutBottomSquare→isPushoutTotSquare
      (snd (rotatePushoutSquare (⋁-PushoutSquare _ _ ℓ-zero)))

module WedgePushout {ℓ ℓ' ℓ''} (A : Pointed ℓ) (B : Pointed ℓ') (C : Pointed ℓ'') where

  open 3x3-span
  span : 3x3-span
  span .A40 = typ A
  span .A42 = typ A
  span .A44 = typ A
  span .A20 = Unit
  span .A22 = Unit
  span .A24 = Unit
  span .A00 = typ B
  span .A02 = Unit
  span .A04 = typ C
  span .f30 _ = pt A
  span .f32 _ = pt A
  span .f34 _ = pt A
  span .f10 _ = pt B
  span .f12 _ = _
  span .f14 _ = pt C
  span .f41 = idfun (typ A)
  span .f21 = _
  span .f01 _ = pt B
  span .f43 = idfun (typ A)
  span .f23 = _
  span .f03 _ = pt C
  span .H11 _ = refl
  span .H13 _ = refl
  span .H31 _ = refl
  span .H33 _ = refl

  A□2≃ : A□2 span ≃ typ A
  A□2≃ = invEquiv (pushoutIdfunEquiv' _)

  f : typ A → B ⋁ A
  f = inr

  g : typ A → C ⋁ A
  g = inr

  A□○≃ : A□○ span ≃ Pushout f g
  A□○≃ = pushoutEquiv _ _ _ _
    A□2≃ (idEquiv _) (idEquiv _)
    (funExt λ
      { (inl x) → push _
      ; (inr x) → refl
      ; (push a i) j → sq (~ i) (~ j) })
    (funExt λ
      { (inl x) → push _
      ; (inr x) → refl
      ; (push a i) j → sq (~ i) (~ j) })
    where
      sq : ∀ {ℓ} {C : Type ℓ} {c : C}
        → Square refl (sym (Pushout.push _))
          refl (sym (push {f = λ x → c} {g = λ _ → pt A}
            tt ∙ refl))
      sq = slideSquare (sym (rUnit _))

  A4□≃ : A4□ span ≃ typ A
  A4□≃ = invEquiv (pushoutIdfunEquiv _)

  A2□≃ : A2□ span ≃ Unit
  A2□≃ = invEquiv (pushoutIdfunEquiv _)

  A2□isContr : isContr (A2□ span)
  A2□isContr = isOfHLevelRespectEquiv 0 (pushoutIdfunEquiv _) isContrUnit

  A○□≃ : A○□ span ≃ (B ⋁∙ₗ C) ⋁ A
  A○□≃ = pushoutEquiv _ _ _ _
    A2□≃ (idEquiv _) A4□≃
    (lemma A2□isContr refl) (lemma A2□isContr refl)
    where
      -- functions on contractible domains are determined by the basepoint
      lemma : ∀ {ℓ ℓ'}
        → {A : Type ℓ} {B : Type ℓ'}
        → {f g : A → B}
        → (c : isContr A)
        → f (c .fst) ≡ g (c .fst)
        → f ≡ g
      lemma {f = f} {g} c p = funExt λ x
        → cong f (sym (c .snd x))
        ∙ p
        ∙ cong g (c .snd x)

  opaque
    extendWedgeEq : Pushout f g ≃ ((B ⋁∙ₗ C) ⋁ A)
    extendWedgeEq = invEquiv A□○≃ ∙ₑ pathToEquiv (3x3-lemma span) ∙ₑ A○□≃

  wedgePushout : PushoutSquare
  wedgePushout = extendPushoutSquare
    (pushoutToSquare record { f1 = f ; f3 = g })
    extendWedgeEq


module _ {ℓ ℓ'} (X : Pointed ℓ) (Y : Pointed ℓ') where
  open commSquare
  open 3-span

  {-
    X × Y ---> Y --------> 1
      ↓   A    ↓     C     ↓
      X ---> Σ(X∧Y) --> ΣY ∨ Σ(X∧Y)
      ↓   B    ↓     D     ↓
      1 -> ΣX ∨ Σ(X∧Y) --> ? = ΣX ∨ ΣY ∨ Σ(X∧Y)
  -}

  pushoutA₀ : PushoutSquare  -- inrP maps to south, but we want north
  pushoutA₀ = extendPushoutSquare
      (pushoutToSquare (3span fst snd))
      (pathToEquiv (joinPushout≡join _ _) ∙ₑ
        invEquiv (isoToEquiv (SmashJoinIso {A = X} {B = Y})))

  squareA : I → commSquare
  squareA i = record
    { commSquare (pushoutA₀ .fst)
    ; inrP = λ _ → merid (inl _) i
    ; comm = transp (λ j →
      Path (typ X × typ Y → Susp (X ⋀ Y))
        (λ _ → north) (λ _ → merid (inl _) (i ∨ ~ j)))
      i (pushoutA₀ .fst .commSquare.comm)
    }

  pushoutA : PushoutSquare
  pushoutA = squareA i0 ,
    subst isPushoutSquare (λ i → squareA (~ i)) (pushoutA₀ .snd)

  module _ where
    open PushoutNull (typ X) (Susp (X ⋀ Y)) north
    open PushoutPasteDown pushoutA
      (squareL .sp .f1)
      (squareL .inlP)
      (squareL .inrP)
      (squareL .commSquare.comm)

    pushoutB : PushoutSquare
    pushoutB = pushoutSquareL

    pushoutAB : PushoutSquare
    pushoutAB = _ , isPushoutBottomSquare→isPushoutTotSquare (pushoutB .snd)

    cofib-snd : cofib snd ≃ Susp∙ (typ X) ⋁ Susp∙ (X ⋀ Y)
    cofib-snd = pushoutEquiv _ _ _ _
        (idEquiv _) Unit≃Unit* (idEquiv _)
        refl refl
      ∙ₑ (_ , pushoutAB .snd)

  pushoutC : PushoutSquare
  pushoutC = PushoutNull.pushoutSquareR (typ Y) (Susp (X ⋀ Y)) north

  pushoutD : PushoutSquare
  pushoutD = WedgePushout.wedgePushout
    (Susp∙ (X ⋀ Y)) (Susp∙ (typ X)) (Susp∙ (typ Y))

  pushoutCD : PushoutSquare
  pushoutCD = _ , isPushoutBottomSquare→isPushoutTotSquare (pushoutD .snd)
    where
      open PushoutPasteDown pushoutC
        (pushoutD .fst .sp .f1)
        (pushoutD .fst .inlP)
        (pushoutD .fst .inrP)
        (pushoutD .fst .commSquare.comm)

  pushoutTot : PushoutSquare
  pushoutTot = _ , isPushoutRightSquare→isPushoutTotSquare (pushoutCD .snd)
    where
      open PushoutPasteLeft pushoutAB
        (pushoutCD .fst .sp .f3)
        (pushoutCD .fst .inrP)
        (pushoutCD .fst .inlP)
        (pushoutCD .fst .commSquare.comm)

  SuspProduct : (Susp∙ (typ X) ⋁∙ₗ Susp∙ (typ Y)) ⋁ Susp∙ (X ⋀ Y)
    ≃ Susp (typ X × typ Y)
  SuspProduct = invEquiv (_ , pushoutTot .snd)
    ∙ₑ (_ , SuspPushoutSquare ℓ-zero ℓ-zero (typ X × typ Y))
