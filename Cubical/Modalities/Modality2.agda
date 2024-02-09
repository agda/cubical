{-# OPTIONS --safe #-}
module Cubical.Modalities.Modality2 where

open import Cubical.Data.Unit
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Equiv.Properties
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

  η⁻¹ : {modal : isModal A} → ◯ A → A
  η⁻¹ {modal = modal} = Iso.inv (equivToIso (η , modal))
  
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
    ◯≡-isModal : {x y : ModalOperator.◯ M A} → ModalOperator.isModal M (x ≡ y)

  open ModalOperator M public

  ◯-rec : (A → ◯ B) → (◯ A → ◯ B)
  ◯-rec {A = A} {B = B} = ◯-ind {P = λ (z : ◯ A) → B}

  ◯-isModal : isModal (◯ A)
  ◯-isModal {A = A} = snd (isoToEquiv (iso (η {A = ◯ A}) f H K))
      where
        f = (◯-rec (idfun (◯ A)))
        K : (x : ◯ A) → ◯-ind (idfun (◯ A)) (η x) ≡ x
        K = ◯-comp (idfun (◯ A))
        H : (x : ◯ (◯ A)) → η (◯-ind (idfun (◯ A)) x) ≡ x
        H x = η⁻¹ {modal = ◯≡-isModal} ((◯-ind {P = P} s) x)
          where
          P =  λ (z : ◯ (◯ A)) → η (f z) ≡ z
          s = λ (a : ◯ A) → η (cong η (K a))

  -- eliminate into modal type
  ◯-ind' : {P : ◯ A → Type ℓ} {depModal : (z : ◯ A) → isModal (P z)}
         → ((a : A) → P (η a))
         → ((z : ◯ A) → P z)
  ◯-ind' {depModal = W} s z = η⁻¹ {modal = W z} (◯-ind (η ∘ s) z)

  ◯-isUniqElim : {P : ◯ A → Type ℓ} → isEquiv (λ (s : (z : ◯ A) → ◯ (P z)) → s ∘ η)
  ◯-isUniqElim {A = A} {P = P} = snd (isoToEquiv (
    iso
      (λ s → s ∘ η)
      ◯-ind
      (λ t → funExt (◯-comp t))
      (λ s → funExt (◯-ind' {depModal = λ _ → ◯≡-isModal} (◯-comp (λ x → s (η x)))))))


  Unit*IsModal : {ℓ : Level} → isModal (Unit* {ℓ = ℓ})
  Unit*IsModal = snd (isoToEquiv φ) where
    open Iso
    φ : Iso Unit* (◯ Unit*)
    fun φ = η
    inv φ x = tt*
    rightInv φ = ◯-ind' {depModal = λ y → ◯≡-isModal {x = η tt*} {y = y}} λ tt* → cong η refl
    leftInv φ = snd isContrUnit*

  isModalCong≃ : {A B : Type ℓ} → A ≃ B → isModal A ≃ isModal B
  isModalCong≃ = cong≃ isModal

  isContr→≃Unit* : ∀ {ℓ} {A : Type ℓ} → isContr A → A ≃ Unit*
  isContr→≃Unit* contr = isoToEquiv (iso (λ _ → tt*) (λ _ → fst contr) (λ _ → refl) (snd contr))

  isContr→isModal : isContr A → isModal A
  isContr→isModal contr = equivFun (isModalCong≃ (invEquiv (isContr→≃Unit* contr))) Unit*IsModal


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
