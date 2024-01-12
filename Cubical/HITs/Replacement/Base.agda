{-

Type-theoretic replacement: a construction taking a map F : A → B where
  - A : Type ℓA
  - B : Type ℓB,
  - the identity types of B essentially have universe level ℓ≅B,
and producing an image of F with universe level (ℓ-max ℓA ℓ≅B).

See Axiom 18.1.8 in

Egbert Rijke
Introduction to Homotopy Theory
https://arxiv.org/abs/2212.11082

for a definition of type-theoretic replacement.

This module constructs the replacement using higher induction-recursion. It is
possible to construct the replacement with much less powerful HITs, for which
see

Egbert Rijke
The join construction
https://arxiv.org/abs/1701.07538

but higher IR allows for a particularly simple construction.

---

The datatype defined in this module originally included a third constructor
forcing the path constructor to preserve reflexivity, but Amélia Liao and David
Wärn independently observed that this was unnecessary.

-}
{-# OPTIONS --safe #-}
module Cubical.HITs.Replacement.Base where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Functions.Embedding
open import Cubical.Functions.Image
open import Cubical.HITs.PropositionalTruncation as Prop
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Equiv.Fiberwise
open import Cubical.Functions.Surjection
open import Cubical.Data.Sigma
open import Cubical.Displayed.Base

module _ {ℓA ℓB ℓ≅B} {A : Type ℓA} {B : Type ℓB} (𝒮-B : UARel B ℓ≅B) (f : A → B)  where

  module B = UARel 𝒮-B

  data Replacement : Type (ℓ-max ℓA ℓ≅B)
  unrep : Replacement → B

  data Replacement where
    rep : A → Replacement
    quo : ∀ r r' → unrep r B.≅ unrep r' → r ≡ r'

  unrep (rep a) = f a
  unrep (quo r r' eqv i) = B.≅→≡ eqv i

  {-
    To eliminate into a proposition, we need only provide the point constructor
    case.
  -}

  elimProp : ∀ {ℓ} {P : Replacement → Type ℓ}
    → ((r : Replacement) → isProp (P r))
    → ((x : A) → P (rep x))
    → (r : Replacement) → P r
  elimProp prop g (rep x) = g x
  elimProp prop g (quo r r' eqv i) =
    isProp→PathP (λ i → prop (quo r r' eqv i))
      (elimProp prop g r)
      (elimProp prop g r')
      i

  {-
    Our image factorization is F ≡ unrep ∘ rep.
    Note that this equation holds judgmentally.
  -}

  -- Surjection half of the image factorization

  isSurjectiveRep : isSurjection rep
  isSurjectiveRep = elimProp (λ _ → squash₁) (λ x → ∣ x , refl ∣₁)

  -- Embedding half of the image factorization

  isEmbeddingUnrep : isEmbedding unrep
  isEmbeddingUnrep =
    hasPropFibersOfImage→isEmbedding λ r →
    isOfHLevelRetract 1
      (map-snd (λ p → sym (inv _ r p)))
      (map-snd (λ p → sym (cong unrep p)))
      (λ (r' , p) → ΣPathP (refl , unrepInv r' r p))
      isPropSingl
    where
    inv : ∀ r r' → unrep r ≡ unrep r' → r ≡ r'
    inv r r' Q = quo r r' (B.≡→≅ Q)

    unrepInv : ∀ r r' Q → cong unrep (inv r r' Q) ≡ Q
    unrepInv r r' Q = B.uaIso (unrep r) (unrep r') .Iso.rightInv Q

  -- Equivalence to the image with level (ℓ-max ℓA ℓB) that always exists

  replacement≃Image : Replacement ≃ Image f
  replacement≃Image =
    imagesEquiv
      (rep , isSurjectiveRep)
      (unrep , isEmbeddingUnrep)
      (restrictToImage f , isSurjectionImageRestriction f)
      (imageInclusion f)
      refl
