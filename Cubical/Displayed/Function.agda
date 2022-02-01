{-

  Functions building UARels and DUARels on function types

-}
{-# OPTIONS --no-exact-split --safe #-}
module Cubical.Displayed.Function where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Function
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Path

open import Cubical.Functions.FunExtEquiv
open import Cubical.Functions.Implicit

open import Cubical.Displayed.Base
open import Cubical.Displayed.Constant
open import Cubical.Displayed.Morphism
open import Cubical.Displayed.Subst
open import Cubical.Displayed.Sigma

private
  variable
    ℓA ℓ≅A ℓB ℓ≅B ℓC ℓ≅C : Level

-- UARel on dependent function type
-- from UARel on domain and DUARel on codomain

module _ {A : Type ℓA} (𝒮-A : UARel A ℓ≅A) {B : A → Type ℓB} (𝒮ᴰ-B : DUARel 𝒮-A B ℓ≅B) where

  open UARel 𝒮-A
  open DUARel 𝒮ᴰ-B

  𝒮-Π : UARel ((a : A) → B a) (ℓ-max ℓA ℓ≅B)
  UARel._≅_ 𝒮-Π f f' = ∀ a → f a ≅ᴰ⟨ ρ a ⟩ f' a
  UARel.ua 𝒮-Π f f' =
    compEquiv
      (equivΠCod λ a → uaᴰρ (f a) (f' a))
      funExtEquiv

-- Parameterize UARel by type

_→𝒮_ : (A : Type ℓA) {B : Type ℓB} (𝒮-B : UARel B ℓ≅B) → UARel (A → B) (ℓ-max ℓA ℓ≅B)
(A →𝒮 𝒮-B) .UARel._≅_ f f' = ∀ a → 𝒮-B .UARel._≅_ (f a) (f' a)
(A →𝒮 𝒮-B) .UARel.ua f f' =
  compEquiv
    (equivΠCod λ a → 𝒮-B .UARel.ua (f a) (f' a))
    funExtEquiv

𝒮-app : {A : Type ℓA} {B : Type ℓB} {𝒮-B : UARel B ℓ≅B}
  → A → UARelHom (A →𝒮 𝒮-B) 𝒮-B
𝒮-app a .UARelHom.fun f = f a
𝒮-app a .UARelHom.rel h = h a
𝒮-app a .UARelHom.ua h = refl

-- DUARel on dependent function type
-- from DUARels on domain and codomain

module _ {A : Type ℓA} {𝒮-A : UARel A ℓ≅A}
  {B : A → Type ℓB} (𝒮ᴰ-B : DUARel 𝒮-A B ℓ≅B)
  {C : (a : A) → B a → Type ℓC} (𝒮ᴰ-C : DUARel (∫ 𝒮ᴰ-B) (uncurry C) ℓ≅C)
  where

  open UARel 𝒮-A
  private
    module B = DUARel 𝒮ᴰ-B
    module C = DUARel 𝒮ᴰ-C

  𝒮ᴰ-Π : DUARel 𝒮-A (λ a → (b : B a) → C a b) (ℓ-max (ℓ-max ℓB ℓ≅B) ℓ≅C)
  DUARel._≅ᴰ⟨_⟩_ 𝒮ᴰ-Π f p f' =
    ∀ {b b'} (q : b B.≅ᴰ⟨ p ⟩ b') → f b C.≅ᴰ⟨ p , q ⟩ f' b'
  DUARel.uaᴰ 𝒮ᴰ-Π f p f' =
    compEquiv
      (equivImplicitΠCod λ {b} →
        (equivImplicitΠCod λ {b'} →
          (equivΠ (B.uaᴰ b p b') (λ q → C.uaᴰ (f b) (p , q) (f' b')))))
      funExtDepEquiv

_→𝒮ᴰ_ : {A : Type ℓA} {𝒮-A : UARel A ℓ≅A}
  {B : A → Type ℓB} (𝒮ᴰ-B : DUARel 𝒮-A B ℓ≅B)
  {C : A → Type ℓC} (𝒮ᴰ-C : DUARel 𝒮-A C ℓ≅C)
  → DUARel 𝒮-A (λ a → B a → C a) (ℓ-max (ℓ-max ℓB ℓ≅B) ℓ≅C)
𝒮ᴰ-B →𝒮ᴰ 𝒮ᴰ-C =
  𝒮ᴰ-Π 𝒮ᴰ-B (𝒮ᴰ-Lift _ 𝒮ᴰ-C 𝒮ᴰ-B)

-- DUARel on dependent function type
-- from a SubstRel on the domain and DUARel on the codomain

module _ {A : Type ℓA} {𝒮-A : UARel A ℓ≅A}
  {B : A → Type ℓB} (𝒮ˢ-B : SubstRel 𝒮-A B)
  {C : (a : A) → B a → Type ℓC} (𝒮ᴰ-C : DUARel (∫ˢ 𝒮ˢ-B) (uncurry C) ℓ≅C)
  where

  open UARel 𝒮-A
  open SubstRel 𝒮ˢ-B
  open DUARel 𝒮ᴰ-C

  𝒮ᴰ-Πˢ : DUARel 𝒮-A (λ a → (b : B a) → C a b) (ℓ-max ℓB ℓ≅C)
  DUARel._≅ᴰ⟨_⟩_ 𝒮ᴰ-Πˢ f p f' =
    (b : B _) → f b ≅ᴰ⟨ p , refl ⟩ f' (act p .fst b)
  DUARel.uaᴰ 𝒮ᴰ-Πˢ f p f' =
    compEquiv
      (compEquiv
        (equivΠCod λ b → Jequiv (λ b' q → f b ≅ᴰ⟨ p , q ⟩ f' b'))
        (invEquiv implicit≃Explicit))
      (DUARel.uaᴰ (𝒮ᴰ-Π (Subst→DUA 𝒮ˢ-B) 𝒮ᴰ-C) f p f')

-- SubstRel on a dependent function type
-- from a SubstRel on the domain and SubstRel on the codomain

module _ {A : Type ℓA} {𝒮-A : UARel A ℓ≅A}
  {B : A → Type ℓB} (𝒮ˢ-B : SubstRel 𝒮-A B)
  {C : Σ A B → Type ℓC} (𝒮ˢ-C : SubstRel (∫ˢ 𝒮ˢ-B) C)
  where

  open UARel 𝒮-A
  open SubstRel
  private
    module B = SubstRel 𝒮ˢ-B
    module C = SubstRel 𝒮ˢ-C

  𝒮ˢ-Π : SubstRel 𝒮-A (λ a → (b : B a) → C (a , b))
  𝒮ˢ-Π .act p = equivΠ' (B.act p) (λ q → C.act (p , q))
  𝒮ˢ-Π .uaˢ p f =
    fromPathP
      (DUARel.uaᴰ (𝒮ᴰ-Π (Subst→DUA 𝒮ˢ-B) (Subst→DUA 𝒮ˢ-C)) f p (equivFun (𝒮ˢ-Π .act p) f) .fst
        (λ {b} →
          J (λ b' q →
                equivFun (C.act (p , q)) (f b)
                ≡ equivFun (equivΠ' (𝒮ˢ-B .act p) (λ q → C.act (p , q))) f b')
            (λ i →
              C.act (p , λ j → commSqIsEq (𝒮ˢ-B .act p .snd) b (~ i) j) .fst
                (f (retEq (𝒮ˢ-B .act p) b (~ i))))))
