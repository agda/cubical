{-# OPTIONS --cubical --no-import-sorts --safe #-}
module Cubical.Displayed.Subst where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Path
open import Cubical.Foundations.Univalence

open import Cubical.Displayed.Base

private
  variable
    ℓ ℓA ℓA' ℓ≅A ℓB ℓB' ℓ≅B ℓC ℓ≅C : Level

record SubstRel {A : Type ℓA} {ℓ≅A : Level} (𝒮-A : UARel A ℓ≅A) (B : A → Type ℓB)
  : Type (ℓ-max (ℓ-max ℓA ℓB) ℓ≅A)
  where

  no-eta-equality
  constructor substrel
  open UARel 𝒮-A

  field
    act : {a a' : A} → a ≅ a' → B a ≃ B a'
    isSubst : {a a' : A} (p : a ≅ a') (b : B a) → equivFun (act p) b ≡ subst B (≅→≡ p) b

Subst→DUA : {A : Type ℓA} {ℓ≅A : Level} {𝒮-A : UARel A ℓ≅A} {B : A → Type ℓB}
  → SubstRel 𝒮-A B → DUARel 𝒮-A B ℓB
DUARel._≅ᴰ⟨_⟩_ (Subst→DUA 𝒮ˢ-B) b p b' =
  equivFun (SubstRel.act 𝒮ˢ-B p) b ≡ b'
DUARel.uaᴰ (Subst→DUA {𝒮-A = 𝒮-A} {B = B} 𝒮ˢ-B) b p b' =
  equivFun (SubstRel.act 𝒮ˢ-B p) b ≡ b'
    ≃⟨ pathToEquiv (cong (_≡ b') (SubstRel.isSubst 𝒮ˢ-B p b)) ⟩
  subst B (≅→≡ p) b ≡ b'
    ≃⟨ invEquiv (PathP≃Path _ _ _) ⟩
  PathP (λ i → B (UARel.≅→≡ 𝒮-A p i)) b b'
  ■
  where
  open UARel 𝒮-A
