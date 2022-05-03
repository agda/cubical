{-
  Given a type A with a UARel and a family B over A,
  a SubstRel on B is a family of functions a ≅ a' → B a ≃ B a' path-equal to transport in that family.

  Any SubstRel gives rise to a DUARel in which b and b' are related over p when the transport of b along p is
  equial to b'.
-}

{-# OPTIONS --safe #-}
module Cubical.Displayed.Subst where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Path
open import Cubical.Foundations.Transport
open import Cubical.Foundations.Univalence

open import Cubical.Displayed.Base

private
  variable
    ℓA ℓ≅A ℓB : Level

record SubstRel {A : Type ℓA} {ℓ≅A : Level} (𝒮-A : UARel A ℓ≅A) (B : A → Type ℓB)
  : Type (ℓ-max (ℓ-max ℓA ℓB) ℓ≅A)
  where

  no-eta-equality
  constructor substrel
  open UARel 𝒮-A

  field
    act : {a a' : A} → a ≅ a' → B a ≃ B a'
    uaˢ : {a a' : A} (p : a ≅ a') (b : B a) → subst B (≅→≡ p) b ≡ equivFun (act p) b

  uaˢ⁻ : {a a' : A} (p : a ≅ a') (b : B a') → subst B (sym (≅→≡ p)) b ≡ invEq (act p) b
  uaˢ⁻ p b =
    subst B (sym (≅→≡ p)) b
      ≡⟨ cong (subst B (sym (≅→≡ p))) (sym (secEq (act p) b)) ⟩
    subst B (sym (≅→≡ p)) (equivFun (act p) (invEq (act p) b))
      ≡⟨ cong (subst B (sym (≅→≡ p))) (sym (uaˢ p (invEq (act p) b))) ⟩
    subst B (sym (≅→≡ p)) (subst B (≅→≡ p) (invEq (act p) b))
      ≡⟨ pathToIso (cong B (≅→≡ p)) .Iso.leftInv (invEq (act p) b) ⟩
    invEq (act p) b
    ∎

Subst→DUA : {A : Type ℓA} {ℓ≅A : Level} {𝒮-A : UARel A ℓ≅A} {B : A → Type ℓB}
  → SubstRel 𝒮-A B → DUARel 𝒮-A B ℓB
DUARel._≅ᴰ⟨_⟩_ (Subst→DUA 𝒮ˢ-B) b p b' =
  equivFun (SubstRel.act 𝒮ˢ-B p) b ≡ b'
DUARel.uaᴰ (Subst→DUA {𝒮-A = 𝒮-A} {B = B} 𝒮ˢ-B) b p b' =
  equivFun (SubstRel.act 𝒮ˢ-B p) b ≡ b'
    ≃⟨ invEquiv (compPathlEquiv (sym (SubstRel.uaˢ 𝒮ˢ-B p b))) ⟩
  subst B (≅→≡ p) b ≡ b'
    ≃⟨ invEquiv (PathP≃Path (λ i → B (≅→≡ p i)) b b') ⟩
  PathP (λ i → B (≅→≡ p i)) b b'
  ■
  where
  open UARel 𝒮-A
