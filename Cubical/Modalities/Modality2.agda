{-# OPTIONS --safe #-}
module Cubical.Modalities.Modality2 where

open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Function
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Prelude


private
  variable
    ℓ : Level
    A B : Type ℓ

record ModalOperator : Typeω where
  field
    ◯ : Type ℓ → Type ℓ
    η : A → ◯ A

  isModal : Type ℓ → Type ℓ
  isModal A = isEquiv (η {A = A})

  η⁻¹ : {modalWitness : isModal A} → ◯ A → A
  η⁻¹ {modalWitness = modalWitness} = Iso.inv (equivToIso (η , modalWitness))
  
  ModalType : (ℓ : Level) → Type (ℓ-suc ℓ)
  ModalType ℓ = Σ (Type ℓ) (λ X → isModal X)


record Modality : Typeω where
  field
    M : ModalOperator
    ◯-ind : {P : ModalOperator.◯ M A → Type ℓ}
            → ((a : A) → ModalOperator.◯ M (P (ModalOperator.η M a)))
            → ((z : ModalOperator.◯ M A) → ModalOperator.◯ M (P z))
    ◯-comp : {P : ModalOperator.◯ M A → Type ℓ}
             → (s : (a : A) → ModalOperator.◯ M (P (ModalOperator.η M a)))
             → (x : A) → ◯-ind {P = P} s (ModalOperator.η M x) ≡ s x
    ◯=-isModal : {x y : ModalOperator.◯ M A} → isEquiv (ModalOperator.η M {A = x ≡ y})

  open ModalOperator M public

  ◯-rec : (A → ◯ B) → (◯ A → ◯ B)
  ◯-rec {A = A} {B = B} = ◯-ind {P = λ (z : ◯ A) → B}


  ◯-isModal : isModal (◯ A)
  ◯-isModal {A = A} = snd (isoToEquiv φ)
    where
      open Iso

      f = ◯-rec (idfun (◯ A))
      H = ◯-comp (idfun (◯ A))
      η≡⁻¹ : {B : Type ℓ} {x y : ◯ B} → ◯ (x ≡ y) → x ≡ y
      η≡⁻¹ = η⁻¹ {modalWitness = ◯≡-isModal}

      φ : Iso (◯ A) (◯ (◯ A))
      fun φ = η {A = ◯ A}
      inv φ = f
      leftInv φ = H
      rightInv φ = η≡⁻¹ ∘ (◯-ind {P = P} s)
        where
        P = λ (z : ◯ (◯ A)) → (η (f z) ≡ z)
        s = λ (a : ◯ A) → η (cong η (H a))



--record UniquelyEliminatingModality : Typeω where
--  open ModalOperator
--  field
--    M : ModalOperator
--    depUniversalProperty : {P : ◯ M A → Type ℓ}
--                         → isEquiv (λ (s : (z : ◯ M A) → ◯ M (P z)) → s ∘ η M)
--
--  open ModalOperator M public

--record ReflectiveSubuniverse : Typeω where
--  open ModalOperator
--  field
--    M : ModalOperator
--    isModal : Type ℓ → Type ℓ
--    isModalIsProp : isProp (isModal A)
--    ◯-isModal : isModal (◯ M A)
--    universalProperty : isEquiv (λ (f : ◯ M A → ◯ M B) → f ∘ η M)
--
--  open ModalOperator M public
--
--record Σ-closedReflectiveSubuniverse : Typeω where
--  open ReflectiveSubuniverse
--  field
--    U◯ : ReflectiveSubuniverse
--    Σ-closed : {P : A → Type ℓ}
--             → isModal U◯ A
--             → ((a : A) → isModal U◯ (P a))
--             → isModal U◯ (Σ A P)
--
--  open ReflectiveSubuniverse U◯ public
