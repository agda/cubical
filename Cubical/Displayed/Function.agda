{-

  Functions building UARels and DUARels on function types

-}
{-# OPTIONS --cubical --no-import-sorts --no-exact-split --safe #-}
module Cubical.Displayed.Function where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Path
open import Cubical.Foundations.Univalence using (pathToEquiv)

open import Cubical.Functions.FunExtEquiv
open import Cubical.Functions.Implicit

open import Cubical.Displayed.Base
open import Cubical.Displayed.Subst
open import Cubical.Displayed.Properties

private
  variable
    ℓ ℓA ℓ≅A ℓB ℓ≅B ℓC ℓ≅C : Level

-- UARel on Π-type

module _ {A : Type ℓA} (𝒮-A : UARel A ℓ≅A) {B : A → Type ℓB} (𝒮ᴰ-B : DUARel 𝒮-A B ℓ≅B) where

  open UARel 𝒮-A
  open DUARel 𝒮ᴰ-B

  𝒮ᴰ→𝒮-Π : UARel ((a : A) → B a) (ℓ-max ℓA ℓ≅B)
  UARel._≅_ 𝒮ᴰ→𝒮-Π f f' = ∀ a → f a ≅ᴰ⟨ ρ a ⟩ f' a
  UARel.ua 𝒮ᴰ→𝒮-Π f f' =
    compEquiv
      (equivΠCod λ a → uaᴰρ (f a) (f' a))
      funExtEquiv

equivΠ : ∀ {ℓA ℓA' ℓB ℓB'} {A : Type ℓA} {A' : Type ℓA'}
  {B : A → Type ℓB} {B' : A' → Type ℓB'}
  (eA : A ≃ A')
  (eB : (a : A) → B a ≃ B' (eA .fst a))
  → ((a : A) → B a) ≃ ((a' : A') → B' a')
equivΠ {B' = B'} eA eB = isoToEquiv is
  where
  open Iso

  is : Iso _ _
  fun is f a' =
    subst B' (retEq eA a') (eB _ .fst (f (invEq eA a')))
  inv is f' a =
    invEq (eB _) (f' (eA .fst a))
  rightInv is f' =
    funExt λ a' →
    cong (subst B' (retEq eA a')) (retEq (eB _) _)
    ∙ fromPathP (cong f' (retEq eA a'))
  leftInv is f =
    funExt λ a →
    invEq (eB a) (subst B' (retEq eA _) (eB _ .fst (f (invEq eA (eA .fst a)))))
      ≡⟨ cong (λ t → invEq (eB a) (subst B' t (eB _ .fst (f (invEq eA (eA .fst a))))))
           (commPathIsEq (snd eA) a) ⟩
    invEq (eB a) (subst B' (cong (eA .fst) (secEq eA a)) (eB _ .fst (f (invEq eA (eA .fst a)))))
      ≡⟨ cong (invEq (eB a)) (fromPathP (λ i → eB _ .fst (f (secEq eA a i)))) ⟩
    invEq (eB a) (eB a .fst (f a))
      ≡⟨ secEq (eB _) (f a) ⟩
    f a
    ∎

module _ {A : Type ℓA} {𝒮-A : UARel A ℓ≅A}
  {B : A → Type ℓB} (𝒮ᴰ-B : DUARel 𝒮-A B ℓ≅B)
  {C : (a : A) → B a → Type ℓC} (𝒮ᴰ-C : DUARel (∫ 𝒮ᴰ-B) (uncurry C) ℓ≅C)
  where

  open UARel 𝒮-A
  open DUARel 𝒮ᴰ-B renaming (_≅ᴰ⟨_⟩_ to _≅B⟨_⟩_ ; uaᴰ to uaB)
  open DUARel 𝒮ᴰ-C renaming (_≅ᴰ⟨_⟩_ to _≅C⟨_⟩_ ; uaᴰ to uaC)

  𝒮ᴰ-Π : DUARel 𝒮-A (λ a → (b : B a) → C a b) (ℓ-max (ℓ-max ℓB ℓ≅B) ℓ≅C)
  DUARel._≅ᴰ⟨_⟩_ 𝒮ᴰ-Π f p f' =
    ∀ {b b'} (q : b ≅B⟨ p ⟩ b') → f b ≅C⟨ p , q ⟩ f' b'
  DUARel.uaᴰ 𝒮ᴰ-Π f p f' =
    compEquiv
      (equivImplicitΠCod λ {b} →
        (equivImplicitΠCod λ {b'} →
          (equivΠ (uaB b p b') (λ q → uaC (f b) (p , q) (f' b')))))
      funExtDepEquiv
    
_𝒮ᴰ→_ : {A : Type ℓA} {𝒮-A : UARel A ℓ≅A}
  {B : A → Type ℓB} (𝒮ᴰ-B : DUARel 𝒮-A B ℓ≅B)
  {C : A → Type ℓC} (𝒮ᴰ-C : DUARel 𝒮-A C ℓ≅C)
  → DUARel 𝒮-A (λ a → B a → C a) (ℓ-max (ℓ-max ℓB ℓ≅B) ℓ≅C)
𝒮ᴰ-B 𝒮ᴰ→ 𝒮ᴰ-C =
  𝒮ᴰ-Π 𝒮ᴰ-B (Lift-𝒮ᴰ _ 𝒮ᴰ-C 𝒮ᴰ-B)

module _ {A : Type ℓA} {𝒮-A : UARel A ℓ≅A}
  {B : A → Type ℓB} (𝒮ˢ-B : SubstRel 𝒮-A B)
  {C : (a : A) → B a → Type ℓC} (𝒮ᴰ-C : DUARel (∫ (Subst→DUA 𝒮ˢ-B)) (uncurry C) ℓ≅C)
  where

  open UARel 𝒮-A
  open SubstRel 𝒮ˢ-B
  open DUARel 𝒮ᴰ-C renaming (_≅ᴰ⟨_⟩_ to _≅C⟨_⟩_ ; uaᴰ to uaC)

  𝒮ᴰ-Πˢ : DUARel 𝒮-A (λ a → (b : B a) → C a b) (ℓ-max ℓB ℓ≅C)
  DUARel._≅ᴰ⟨_⟩_ 𝒮ᴰ-Πˢ f p f' =
    (b : B _) → f b ≅C⟨ p , refl ⟩ f' (act p .fst b)
  DUARel.uaᴰ 𝒮ᴰ-Πˢ f p f' =
    compEquiv
      (compEquiv
        (equivΠCod λ b → Jequiv (λ b' q → f b ≅C⟨ p , q ⟩ f' b'))
        (invEquiv implicit≃Explicit))
      (DUARel.uaᴰ (𝒮ᴰ-Π (Subst→DUA 𝒮ˢ-B) 𝒮ᴰ-C) f p f')
