{-# OPTIONS --safe #-}
module Cubical.Displayed.Properties where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Univalence using (pathToEquiv; univalence; ua-ungluePath-Equiv)

open import Cubical.Data.Unit
open import Cubical.Data.Sigma

open import Cubical.Relation.Binary
open BinaryRelation

open import Cubical.Displayed.Base

private
  variable
    ℓ ℓA ℓA' ℓP ℓ≅A ℓ≅A' ℓB ℓB' ℓ≅B ℓ≅B' ℓC ℓ≅C : Level

-- induction principles

module _ {A : Type ℓA} (𝒮-A : UARel A ℓ≅A) where
  open UARel 𝒮-A
  𝒮-J : {a : A}
        (P : (a' : A) → (p : a ≡ a') → Type ℓ)
        (d : P a refl)
        {a' : A}
        (p : a ≅ a')
        → P a' (≅→≡ p)
  𝒮-J {a} P d {a'} p
    = J (λ y q → P y q)
        d
        (≅→≡ p)

  𝒮-J-2 : {a : A}
            (P : (a' : A) → (p : a ≅ a') → Type ℓ)
            (d : P a (ρ a))
            {a' : A}
            (p : a ≅ a')
            → P a' p
  𝒮-J-2 {a = a} P d {a'} p
    = subst (λ r → P a' r) (Iso.leftInv (uaIso a a') p) g
    where
      g : P a' (≡→≅ (≅→≡ p))
      g = 𝒮-J (λ y q → P y (≡→≅ q)) d p


-- constructors

module _ {A : Type ℓA} {𝒮-A : UARel A ℓ≅A}
  {B : A → Type ℓB}
  (_≅ᴰ⟨_⟩_ : {a a' : A} → B a → UARel._≅_ 𝒮-A a a' → B a' → Type ℓ≅B)
  where

    open UARel 𝒮-A

    -- constructor that reduces ua to the case where p = ρ a by induction on p
    private
      𝒮ᴰ-make-aux : (uni : {a : A} (b b' : B a) → b ≅ᴰ⟨ ρ a ⟩ b' ≃ (b ≡ b'))
                    → ({a a' : A} (b : B a) (p : a ≅ a') (b' : B a') → (b ≅ᴰ⟨ p ⟩ b') ≃ PathP (λ i → B (≅→≡ p i)) b b')
      𝒮ᴰ-make-aux uni {a} {a'} b p
        = 𝒮-J-2 𝒮-A
                    (λ y q → (b' : B y) → (b ≅ᴰ⟨ q ⟩ b') ≃ PathP (λ i → B (≅→≡ q i)) b b')
                    (λ b' → uni' b')
                    p
        where
          g : (b' : B a) → (b ≡ b') ≡ PathP (λ i → B (≅→≡ (ρ a) i)) b b'
          g b' = subst (λ r → (b ≡ b') ≡ PathP (λ i → B (r i)) b b')
                       (sym (Iso.rightInv (uaIso a a) refl))
                       refl
          uni' : (b' : B a) → b ≅ᴰ⟨ ρ a ⟩ b' ≃ PathP (λ i → B (≅→≡ (ρ a) i)) b b'
          uni' b' = compEquiv (uni b b') (pathToEquiv (g b'))

    𝒮ᴰ-make-1 : (uni : {a : A} (b b' : B a) → b ≅ᴰ⟨ ρ a ⟩ b' ≃ (b ≡ b'))
                → DUARel 𝒮-A B ℓ≅B
    DUARel._≅ᴰ⟨_⟩_ (𝒮ᴰ-make-1 uni) = _≅ᴰ⟨_⟩_
    DUARel.uaᴰ (𝒮ᴰ-make-1 uni) = 𝒮ᴰ-make-aux uni

    -- constructor that reduces univalence further to contractibility of relational singletons

    𝒮ᴰ-make-2 : (ρᴰ : {a : A} → isRefl _≅ᴰ⟨ ρ a ⟩_)
                (contrTotal : (a : A) → contrRelSingl _≅ᴰ⟨ ρ a ⟩_)
                → DUARel 𝒮-A B ℓ≅B
    𝒮ᴰ-make-2 ρᴰ contrTotal = 𝒮ᴰ-make-1 (contrRelSingl→isUnivalent _ ρᴰ (contrTotal _))

-- relational isomorphisms

𝒮-iso→iso : {A : Type ℓA} (𝒮-A : UARel A ℓ≅A)
               {B : Type ℓB} (𝒮-B : UARel B ℓ≅B)
               (F : RelIso (UARel._≅_ 𝒮-A) (UARel._≅_ 𝒮-B))
               → Iso A B
𝒮-iso→iso 𝒮-A 𝒮-B F
  = RelIso→Iso (UARel._≅_ 𝒮-A)
               (UARel._≅_ 𝒮-B)
               (UARel.≅→≡ 𝒮-A)
               (UARel.≅→≡ 𝒮-B)
               F

-- fiberwise relational isomorphisms

module _ {A : Type ℓA} {𝒮-A : UARel A ℓ≅A}
  {A' : Type ℓA'} {𝒮-A' : UARel A' ℓ≅A'}
  (F : Iso A A')
  {B : A → Type ℓB} (𝒮ᴰ-B : DUARel 𝒮-A B ℓ≅B)
  {B' : A' → Type ℓB'} (𝒮ᴰ-B' : DUARel 𝒮-A' B' ℓ≅B') where

  open UARel 𝒮-A
  open DUARel 𝒮ᴰ-B renaming (_≅ᴰ⟨_⟩_ to _≅B⟨_⟩_
                            ; uaᴰ to uaB
                            ; fiberRel to fiberRelB
                            ; uaᴰρ to uaᴰρB)
  open DUARel 𝒮ᴰ-B' renaming (_≅ᴰ⟨_⟩_ to _≅B'⟨_⟩_
                             ; uaᴰ to uaB'
                             ; fiberRel to fiberRelB'
                             ; uaᴰρ to uaᴰρB')

  private
    f = Iso.fun F

    -- the following can of course be done slightly more generally
    -- for fiberwise binary relations

    F*fiberRelB' : (a : A) → Rel (B' (f a)) (B' (f a)) ℓ≅B'
    F*fiberRelB' a = fiberRelB' (f a)

  module _ (G : (a : A) → RelIso (fiberRelB a) (F*fiberRelB' a)) where
    private
      fiberIsoOver : (a : A) → Iso (B a) (B' (f a))
      fiberIsoOver a
        = RelIso→Iso (fiberRelB a)
                     (F*fiberRelB' a)
                     (equivFun (uaᴰρB _ _))
                     (equivFun (uaᴰρB' _ _))
                     (G a)

    -- DUARelFiberIsoOver→TotalIso produces an isomorphism of total spaces
    -- from a relational isomorphism between B a and (F * B) a
    𝒮ᴰ-fiberIsoOver→totalIso : Iso (Σ A B) (Σ A' B')
    𝒮ᴰ-fiberIsoOver→totalIso = Σ-cong-iso F fiberIsoOver
