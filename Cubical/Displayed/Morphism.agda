{-
  A morphism of UARels is a function between the structures with an action on the relations that
  commutes with the equivalence to PathP.

  We can reindex a DUARel or SubstRel along one of these.
-}
{-# OPTIONS --safe #-}
module Cubical.Displayed.Morphism where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Function
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Transport

open import Cubical.Displayed.Base
open import Cubical.Displayed.Subst

private
  variable
    ℓ ℓA ℓA' ℓ≅A ℓB ℓB' ℓ≅B ℓC ℓ≅C : Level

record UARelHom {A : Type ℓA} {B : Type ℓB} (𝒮-A : UARel A ℓ≅A) (𝒮-B : UARel B ℓ≅B)
  : Type (ℓ-max (ℓ-max ℓA ℓ≅A) (ℓ-max ℓB ℓ≅B)) where
  no-eta-equality
  constructor uarelhom
  field
    fun : A → B
    rel : ∀ {a a'} → UARel._≅_ 𝒮-A a a' → UARel._≅_ 𝒮-B (fun a) (fun a')
    ua : ∀ {a a'} (p : UARel._≅_ 𝒮-A a a')
      → cong fun (UARel.≅→≡ 𝒮-A p) ≡ UARel.≅→≡ 𝒮-B (rel p)

open UARelHom

𝒮-id : {A : Type ℓA} (𝒮-A : UARel A ℓ≅A) → UARelHom 𝒮-A 𝒮-A
𝒮-id 𝒮-A .fun = idfun _
𝒮-id 𝒮-A .rel = idfun _
𝒮-id 𝒮-A .ua _ = refl

𝒮-∘ : {A : Type ℓA} {𝒮-A : UARel A ℓ≅A} {B : Type ℓB} {𝒮-B : UARel B ℓ≅B}
  {C : Type ℓC} {𝒮-C : UARel C ℓ≅C}
  → UARelHom 𝒮-B 𝒮-C
  → UARelHom 𝒮-A 𝒮-B
  → UARelHom 𝒮-A 𝒮-C
𝒮-∘ g f .fun = g .fun ∘ f .fun
𝒮-∘ g f .rel = g .rel ∘ f .rel
𝒮-∘ {𝒮-A = 𝒮-A} {𝒮-B = 𝒮-B} {𝒮-C = 𝒮-C} g f .ua p =
  cong (cong (g .fun)) (f .ua p) ∙ g .ua (f .rel p)

𝒮ᴰ-reindex : {A : Type ℓA} {𝒮-A : UARel A ℓ≅A} {B : Type ℓB} {𝒮-B : UARel B ℓ≅B} {C : B → Type ℓC}
  (f : UARelHom 𝒮-A 𝒮-B)
  → DUARel 𝒮-B C ℓ≅C
  → DUARel 𝒮-A (C ∘ fun f) ℓ≅C
𝒮ᴰ-reindex f 𝒮ᴰ-C .DUARel._≅ᴰ⟨_⟩_ c p c' = 𝒮ᴰ-C .DUARel._≅ᴰ⟨_⟩_ c (f .rel p) c'
𝒮ᴰ-reindex {C = C} f 𝒮ᴰ-C .DUARel.uaᴰ c p c' =
  compEquiv
    (𝒮ᴰ-C .DUARel.uaᴰ c (f .rel p) c')
    (substEquiv (λ q → PathP (λ i → C (q i)) c c') (sym (f .ua p)))

𝒮ˢ-reindex : {A : Type ℓA} {𝒮-A : UARel A ℓ≅A} {B : Type ℓB} {𝒮-B : UARel B ℓ≅B} {C : B → Type ℓC}
  (f : UARelHom 𝒮-A 𝒮-B)
  → SubstRel 𝒮-B C
  → SubstRel 𝒮-A (C ∘ fun f)
𝒮ˢ-reindex f 𝒮ˢ-C .SubstRel.act p = 𝒮ˢ-C .SubstRel.act (f .rel p)
𝒮ˢ-reindex {C = C} f 𝒮ˢ-C .SubstRel.uaˢ p c =
  cong (λ q → subst C q c) (f .ua p)
  ∙ 𝒮ˢ-C .SubstRel.uaˢ (f .rel p) c
