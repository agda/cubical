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
open import Cubical.Foundations.Transport
open import Cubical.Foundations.Univalence using (pathToEquiv)

open import Cubical.Functions.FunExtEquiv
open import Cubical.Functions.Implicit

open import Cubical.Displayed.Base
open import Cubical.Displayed.Subst
open import Cubical.Displayed.Sigma

private
  variable
    ℓ ℓA ℓ≅A ℓB ℓ≅B ℓC ℓ≅C : Level

-- UARel on dependent function type
-- from UARel on domain and DUARel on codomain

module _ {A : Type ℓA} (𝒮-A : UARel A ℓ≅A) {B : A → Type ℓB} (𝒮ᴰ-B : DUARel 𝒮-A B ℓ≅B) where

  open UARel 𝒮-A
  open DUARel 𝒮ᴰ-B

  Π-𝒮 : UARel ((a : A) → B a) (ℓ-max ℓA ℓ≅B)
  UARel._≅_ Π-𝒮 f f' = ∀ a → f a ≅ᴰ⟨ ρ a ⟩ f' a
  UARel.ua Π-𝒮 f f' =
    compEquiv
      (equivΠCod λ a → uaᴰρ (f a) (f' a))
      funExtEquiv

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

  Π-𝒮ᴰ : DUARel 𝒮-A (λ a → (b : B a) → C a b) (ℓ-max (ℓ-max ℓB ℓ≅B) ℓ≅C)
  DUARel._≅ᴰ⟨_⟩_ Π-𝒮ᴰ f p f' =
    ∀ {b b'} (q : b B.≅ᴰ⟨ p ⟩ b') → f b C.≅ᴰ⟨ p , q ⟩ f' b'
  DUARel.uaᴰ Π-𝒮ᴰ f p f' =
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
  Π-𝒮ᴰ 𝒮ᴰ-B (Lift-𝒮ᴰ _ 𝒮ᴰ-C 𝒮ᴰ-B)

-- DUARel on dependent function type
-- from a SubstRel on the domain and DUARel on the codomain

module _ {A : Type ℓA} {𝒮-A : UARel A ℓ≅A}
  {B : A → Type ℓB} (𝒮ˢ-B : SubstRel 𝒮-A B)
  {C : (a : A) → B a → Type ℓC} (𝒮ᴰ-C : DUARel (∫ (Subst→DUA 𝒮ˢ-B)) (uncurry C) ℓ≅C)
  where

  open UARel 𝒮-A
  open SubstRel 𝒮ˢ-B
  open DUARel 𝒮ᴰ-C

  Πˢ-𝒮ᴰ : DUARel 𝒮-A (λ a → (b : B a) → C a b) (ℓ-max ℓB ℓ≅C)
  DUARel._≅ᴰ⟨_⟩_ Πˢ-𝒮ᴰ f p f' =
    (b : B _) → f b ≅ᴰ⟨ p , refl ⟩ f' (act p .fst b)
  DUARel.uaᴰ Πˢ-𝒮ᴰ f p f' =
    compEquiv
      (compEquiv
        (equivΠCod λ b → Jequiv (λ b' q → f b ≅ᴰ⟨ p , q ⟩ f' b'))
        (invEquiv implicit≃Explicit))
      (DUARel.uaᴰ (Π-𝒮ᴰ (Subst→DUA 𝒮ˢ-B) 𝒮ᴰ-C) f p f')

-- SubstRel on a non-dependent function type
-- from a SubstRel on the domain and SubstRel on the codomain
-- TODO: dependent version

module _ {A : Type ℓA} {𝒮-A : UARel A ℓ≅A}
  {B : A → Type ℓB} (𝒮ˢ-B : SubstRel 𝒮-A B)
  {C : A → Type ℓC} (𝒮ᴰ-C : SubstRel 𝒮-A C)
  where

  open UARel 𝒮-A
  private
    module B = SubstRel 𝒮ˢ-B
    module C = SubstRel 𝒮ᴰ-C

  Π-𝒮ˢ : SubstRel 𝒮-A (λ a → B a → C a)
  SubstRel.act Π-𝒮ˢ p =
    equiv→ (B.act p) (C.act p)
  SubstRel.uaˢ Π-𝒮ˢ {a} {a'} p f =
    funExt λ b →
    C.act p .fst (f (invEq (B.act p) b))
      ≡⟨ C.uaˢ p (f (invEq (B.act p) b)) ⟩
    subst C (≅→≡ p) (f (invEq (B.act p) b))
      ≡⟨ cong (subst C (≅→≡ p) ∘ f) (B.uaˢ⁻ p b) ⟩
    subst (λ a₁ → B a₁ → C a₁) (≅→≡ p) f b
    ∎
