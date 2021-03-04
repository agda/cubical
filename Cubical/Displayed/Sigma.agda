{-

  Functions building UARels and DUARels on Σ-types

-}
{-# OPTIONS --cubical --no-import-sorts --safe #-}
module Cubical.Displayed.Sigma where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv

open import Cubical.Data.Sigma

open import Cubical.Displayed.Base
open import Cubical.Displayed.Subst

private
  variable
    ℓ ℓA ℓA' ℓP ℓ≅A ℓ≅A' ℓB ℓB' ℓ≅B ℓ≅B' ℓC ℓ≅C : Level

-- UARel on a Σ-type

module _ {A : Type ℓA} {ℓ≅A : Level} {𝒮-A : UARel A ℓ≅A}
  {B : A → Type ℓB} {ℓ≅B : Level}
  (𝒮ᴰ-B : DUARel 𝒮-A B ℓ≅B)
  where

  open UARel 𝒮-A
  open DUARel 𝒮ᴰ-B

  ∫ : UARel (Σ A B) (ℓ-max ℓ≅A ℓ≅B)
  UARel._≅_ ∫ (a , b) (a' , b') = Σ[ p ∈ a ≅ a' ] (b ≅ᴰ⟨ p ⟩ b')
  UARel.ua ∫ (a , b) (a' , b') =
    compEquiv
      (Σ-cong-equiv (ua a a') (λ p → uaᴰ b p b'))
      ΣPath≃PathΣ

-- Lift a DUARel to live over a Σ-type

module _ {A : Type ℓA} (𝒮-A : UARel A ℓ≅A)
  {B : A → Type ℓB}
  {ℓ≅B : Level}
  (𝒮ᴰ-B : DUARel 𝒮-A B ℓ≅B)
  {C : A → Type ℓC}
  (𝒮ᴰ-C : DUARel 𝒮-A C ℓ≅C)
  where

  open DUARel 𝒮ᴰ-B

  𝒮ᴰ-Lift : DUARel (∫ 𝒮ᴰ-C) (λ (a , _) → B a) ℓ≅B
  DUARel._≅ᴰ⟨_⟩_ 𝒮ᴰ-Lift b p b' = b ≅ᴰ⟨ p .fst ⟩ b'
  DUARel.uaᴰ 𝒮ᴰ-Lift b p b' = uaᴰ b (p .fst) b'

-- DUARel on a Σ-type

module _ {A : Type ℓA} {𝒮-A : UARel A ℓ≅A}
  {B : A → Type ℓB} {ℓ≅B : Level} (𝒮ᴰ-B : DUARel 𝒮-A B ℓ≅B)
  {C : Σ A B → Type ℓC} {ℓ≅C : Level} (𝒮ᴰ-C : DUARel (∫ 𝒮ᴰ-B) C ℓ≅C)
  where

  open UARel 𝒮-A
  private
    module B = DUARel 𝒮ᴰ-B
    module C = DUARel 𝒮ᴰ-C

  𝒮ᴰ-Σ : DUARel 𝒮-A (λ a → Σ[ b ∈ B a ] C (a , b)) (ℓ-max ℓ≅B ℓ≅C)
  DUARel._≅ᴰ⟨_⟩_ 𝒮ᴰ-Σ (b , c) p (b' , c') =
    Σ[ q ∈ b B.≅ᴰ⟨ p ⟩ b' ]  (c C.≅ᴰ⟨ p , q ⟩ c')
  DUARel.uaᴰ 𝒮ᴰ-Σ (b ,  c) p (b' , c') =
    compEquiv
      (Σ-cong-equiv (B.uaᴰ b p b') (λ q → C.uaᴰ c (p , q) c'))
      ΣPath≃PathΣ

-- DUARel on a non-dependent Σ-type

module _ {A : Type ℓA} {𝒮-A : UARel A ℓ≅A}
  {B : A → Type ℓB} {ℓ≅B : Level} (𝒮ᴰ-B : DUARel 𝒮-A B ℓ≅B)
  {C : A → Type ℓC} {ℓ≅C : Level} (𝒮ᴰ-C : DUARel 𝒮-A C ℓ≅C)
  where

  _×𝒮ᴰ_ : DUARel 𝒮-A (λ a → B a × C a) (ℓ-max ℓ≅B ℓ≅C)
  _×𝒮ᴰ_ = 𝒮ᴰ-Σ 𝒮ᴰ-B (𝒮ᴰ-Lift 𝒮-A 𝒮ᴰ-C 𝒮ᴰ-B)

-- SubstRel on a Σ-type

module _ {A : Type ℓA} {𝒮-A : UARel A ℓ≅A}
  {B : A → Type ℓB} (𝒮ˢ-B : SubstRel 𝒮-A B)
  {C : Σ A B → Type ℓC} (𝒮ˢ-C : SubstRel (∫ (Subst→DUA 𝒮ˢ-B)) C)
  where

  open UARel 𝒮-A
  open SubstRel
  private
    module B = SubstRel 𝒮ˢ-B
    module C = SubstRel 𝒮ˢ-C

  𝒮ˢ-Σ : SubstRel 𝒮-A (λ a → Σ[ b ∈ B a ] C (a , b))
  𝒮ˢ-Σ .act p = Σ-cong-equiv (B.act p) (λ b → C.act (p , refl))
  𝒮ˢ-Σ .uaˢ p _ =
    fromPathP
      (DUARel.uaᴰ (𝒮ᴰ-Σ (Subst→DUA 𝒮ˢ-B) (Subst→DUA 𝒮ˢ-C))  _ p _ .fst (refl , refl))
