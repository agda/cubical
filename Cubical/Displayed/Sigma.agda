{-

  Functions building UARels and DUARels on Σ-types

-}
{-# OPTIONS --safe #-}
module Cubical.Displayed.Sigma where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv

open import Cubical.Data.Sigma

open import Cubical.Displayed.Base
open import Cubical.Displayed.Subst
open import Cubical.Displayed.Morphism
open import Cubical.Displayed.Constant

private
  variable
    ℓ ℓA ℓA' ℓP ℓ≅A ℓ≅A' ℓB ℓB' ℓ≅B ℓ≅B' ℓC ℓ≅C : Level

-- UARel on a Σ-type

∫ˢ : {A : Type ℓA} {𝒮-A : UARel A ℓ≅A} {B : A → Type ℓB} (𝒮ˢ-B : SubstRel 𝒮-A B)
  → UARel (Σ A B) (ℓ-max ℓ≅A ℓB)
∫ˢ 𝒮ˢ-B = ∫ (Subst→DUA 𝒮ˢ-B)

_×𝒮_ : {A : Type ℓA} (𝒮-A : UARel A ℓ≅A) {B : Type ℓB} (𝒮-B : UARel B ℓ≅B)
  → UARel (A × B) (ℓ-max ℓ≅A ℓ≅B)
𝒮-A ×𝒮 𝒮-B = ∫ (𝒮ᴰ-const 𝒮-A 𝒮-B)

-- Projection UARel morphisms

𝒮-fst : {A : Type ℓA} {𝒮-A : UARel A ℓ≅A} {B : A → Type ℓB} {𝒮ᴰ-B : DUARel 𝒮-A B ℓ≅B}
  → UARelHom (∫ 𝒮ᴰ-B) 𝒮-A
𝒮-fst .UARelHom.fun = fst
𝒮-fst .UARelHom.rel = fst
𝒮-fst .UARelHom.ua p = refl

𝒮-snd : {A : Type ℓA} {𝒮-A : UARel A ℓ≅A} {B : Type ℓB} {𝒮-B : UARel B ℓ≅B}
  → UARelHom (𝒮-A ×𝒮 𝒮-B) 𝒮-B
𝒮-snd .UARelHom.fun = snd
𝒮-snd .UARelHom.rel = snd
𝒮-snd .UARelHom.ua p = refl

-- Lift a DUARel to live over a Σ-type

𝒮ᴰ-Lift : {A : Type ℓA} (𝒮-A : UARel A ℓ≅A) {B : A → Type ℓB} (𝒮ᴰ-B : DUARel 𝒮-A B ℓ≅B)
  {C : A → Type ℓC} (𝒮ᴰ-C : DUARel 𝒮-A C ℓ≅C)
  → DUARel (∫ 𝒮ᴰ-C) (λ (a , _) → B a) ℓ≅B
𝒮ᴰ-Lift _  𝒮ᴰ-B _ = 𝒮ᴰ-reindex 𝒮-fst 𝒮ᴰ-B

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
  {C : Σ A B → Type ℓC} (𝒮ˢ-C : SubstRel (∫ˢ 𝒮ˢ-B) C)
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

-- SubstRel on a non-dependent product

module _ {A : Type ℓA} {𝒮-A : UARel A ℓ≅A}
  {B : A → Type ℓB} (𝒮ˢ-B : SubstRel 𝒮-A B)
  {C : A → Type ℓC} (𝒮ˢ-C : SubstRel 𝒮-A C)
  where

  open UARel 𝒮-A
  open SubstRel
  private
    module B = SubstRel 𝒮ˢ-B
    module C = SubstRel 𝒮ˢ-C

  _×𝒮ˢ_ : SubstRel 𝒮-A (λ a → B a × C a)
  _×𝒮ˢ_ .act p = ≃-× (B.act p) (C.act p)
  _×𝒮ˢ_ .uaˢ p (b , c) = ΣPathP (B.uaˢ p b , C.uaˢ p c)
