{-

This file contains:
  - The equivalence "James X ≃ Ω Σ X" for any connected pointed type X.
    (KANG Rongji, Feb. 2022)

-}
module Cubical.HITs.James.LoopSuspEquiv where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.GroupoidLaws
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Equiv.Fiberwise
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Pointed

open import Cubical.Data.Unit
open import Cubical.Data.Sigma
open import Cubical.HITs.Pushout
open import Cubical.HITs.Pushout.Flattening
open import Cubical.HITs.Susp
open import Cubical.HITs.James.Base
  renaming (James to JamesContruction ; James∙ to JamesContruction∙)
open import Cubical.HITs.Truncation

open import Cubical.Homotopy.Connected
open import Cubical.Homotopy.Loopspace

private
  variable
    ℓ : Level

module _
  ((X , x₀) : Pointed ℓ) where

  private
    James  =  JamesContruction  (X , x₀)
    James∙ =  JamesContruction∙ (X , x₀)

  Total : Type ℓ
  Total = Pushout {A = X × James} snd (λ (x , xs) → x ∷ xs)

  private
    flipSquare : (xs : James)(i j : I) → James
    flipSquare xs i j =
      hcomp (λ k → λ
        { (i = i0) → unit xs (j ∨ k)
        ; (i = i1) → unit (x₀ ∷ xs) j
        ; (j = i0) → unit xs (i ∨ k)
        ; (j = i1) → x₀ ∷ (unit xs i) })
      (unit (unit xs i) j)

    square1 : (x : X)(xs : James)(i j : I) → Total
    square1 x xs i j =
      hfill (λ j → λ
        { (i = i0) → push (x , xs) (~ j)
        ; (i = i1) → push (x₀ , x ∷ xs) (~ j) })
      (inS (inr (unit (x ∷ xs) i))) j

    square2 : (xs : James)(i j : I) → Total
    square2 xs i j =
      hcomp (λ k → λ
        { (i = i0) → push (x₀ , xs) (~ k)
        ; (i = i1) → square1 x₀ xs j k
        ; (j = i0) → push (x₀ , xs) (~ k)
        ; (j = i1) → push (x₀ , unit xs i) (~ k) })
      (inr (flipSquare xs i j))

    center : Total
    center = inl []

    pathL : (xs : James) → center ≡ inl xs
    pathL [] = refl
    pathL (x ∷ xs) = pathL xs ∙ (λ i → square1 x xs i i1)
    pathL (unit xs i) j =
      hcomp (λ k → λ
        { (i = i0) → pathL xs j
        ; (i = i1) → compPath-filler (pathL xs) (λ i → square1 x₀ xs i i1) k j
        ; (j = i0) → inl []
        ; (j = i1) → square2 xs i k })
      (pathL xs j)

  isContrTotal : isContr Total
  isContrTotal .fst = center
  isContrTotal .snd (inl xs) = pathL xs
  isContrTotal .snd (inr xs) = pathL xs ∙∙ push (x₀ , xs) ∙∙ (λ i → inr (unit xs (~ i)))
  isContrTotal .snd (push (x , xs) i) j =
    hcomp (λ k → λ
      { (i = i0) → compPath-filler' (pathL xs) (λ i → square1 x xs i i1) (~ j) (~ k)
      ; (i = i1) → doubleCompPath-filler (pathL (x ∷ xs)) (push (x₀ , x ∷ xs)) (λ i → inr (unit (x ∷ xs) (~ i))) k j
      ; (j = i0) → pathL (x ∷ xs) (~ k)
      ; (j = i1) → square1 x xs (~ k) (~ i) })
    (push (x₀ , x ∷ xs) (i ∧ j))

  module _
    (conn : isConnected 2 X) where

    private
      isEquivx₀∷ : isEquiv {A = James} (x₀ ∷_)
      isEquivx₀∷ = subst isEquiv (λ i xs → unit xs i) (idIsEquiv _)

      ∣isEquiv∣ : hLevelTrunc 2 X → Type ℓ
      ∣isEquiv∣ x = rec isSetHProp (λ x → isEquiv {A = James} (x ∷_) , isPropIsEquiv _) x .fst

    isEquiv∷ : (x : X) → isEquiv {A = James} (x ∷_)
    isEquiv∷ x = subst ∣isEquiv∣ (sym (conn .snd ∣ x₀ ∣) ∙ (conn .snd ∣ x ∣)) isEquivx₀∷

    Code : Susp X → Type ℓ
    Code north = James
    Code south = James
    Code (merid x i) = ua (_ , isEquiv∷ x) i

    private
      open FlatteningLemma (λ _ → tt) (λ _ → tt) (λ tt → James) (λ tt → James) (λ x → _ , isEquiv∷ x)

      Total≃ : Pushout Σf Σg ≃ Total
      Total≃ = pushoutEquiv _ _ _ _ (idEquiv _) (ΣUnit _) (ΣUnit _) refl refl

      PushoutSuspCode : (x : PushoutSusp X) → E x ≃ Code (PushoutSusp→Susp x)
      PushoutSuspCode (inl tt) = idEquiv _
      PushoutSuspCode (inr tt) = idEquiv _
      PushoutSuspCode (push x i) = idEquiv _

      ΣCode≃' : _ ≃ Σ _ Code
      ΣCode≃' = Σ-cong-equiv PushoutSusp≃Susp PushoutSuspCode

    ΣCode≃ : Total ≃ Σ _ Code
    ΣCode≃ = compEquiv (invEquiv Total≃) (compEquiv (invEquiv flatten) ΣCode≃')

    isContrΣCode : isContr (Σ _ Code)
    isContrΣCode = isOfHLevelRespectEquiv _ ΣCode≃ isContrTotal

    ΩΣ≃J : Ω (Susp∙ X) .fst ≃ James
    ΩΣ≃J = recognizeId Code [] isContrΣCode _

    ΩΣ≃∙J : Ω (Susp∙ X) ≃∙ James∙
    ΩΣ≃∙J = ΩΣ≃J , refl

    J≃ΩΣ : James ≃ Ω (Susp∙ X) .fst
    J≃ΩΣ = invEquiv ΩΣ≃J

    J≃∙ΩΣ : James∙ ≃∙ Ω (Susp∙ X)
    J≃∙ΩΣ = invEquiv∙ ΩΣ≃∙J
