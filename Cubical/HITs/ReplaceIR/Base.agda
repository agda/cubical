{-

A construction of the type-theoretic replacement of a map F : A → Type ℓ from
A : Type ℓ using induction-recursion. The output is an image factorization of F
that lies in Type ℓ.

See Rijke's Introduction to Homotopy Theory, Axiom 18.1.8 for a definition of
type-theoretic replacement.

The construction in this file should someday be generalized to handle the case
where the codomain is an arbitrary locally ℓ-small type (not necessarily Type
ℓ).

-}
{-# OPTIONS --safe #-}
module Cubical.HITs.ReplaceIR.Base where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Functions.Embedding
open import Cubical.HITs.PropositionalTruncation as Prop
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Equiv
open import Cubical.Functions.Surjection

module _ {ℓ} {A : Type ℓ} (F : A → Type ℓ) where

  data Replace : Type ℓ
  ReplaceEl : Replace → Type ℓ

  data Replace where
    rep : A → Replace
    quo : ∀ r r' → ReplaceEl r ≃ ReplaceEl r' → r ≡ r'
    quoid : ∀ r → quo r r (idEquiv (ReplaceEl r)) ≡ refl

  ReplaceEl (rep a) = F a
  ReplaceEl (quo r r' eqv i) = ua eqv i
  ReplaceEl (quoid r j i) = uaIdEquiv {A = ReplaceEl r} j i

  {-
    To eliminate into a proposition, we need only provide the point constructor
    case.
  -}

  elimProp : {P : Replace → Type ℓ}
    → ((r : Replace) → isProp (P r))
    → ((x : A) → P (rep x))
    → (r : Replace) → P r
  elimProp prop f (rep x) = f x
  elimProp prop f (quo r r' eqv i) =
    isProp→PathP (λ i → prop (quo r r' eqv i))
      (elimProp prop f r)
      (elimProp prop f r')
      i
  elimProp prop f (quoid r i j) =
    isSet→SquareP (λ i j → isProp→isSet (prop (quoid r i j)))
      (isProp→PathP (λ i → prop (quo r r _ i)) _ _)
      (λ _ → elimProp prop f r)
      (λ _ → elimProp prop f r)
      (λ _ → elimProp prop f r)
      i j

  {-
    Our image factorization is F ≡ ReplaceEl ∘ rep.
    Note that this equation holds judgmentally.
  -}

  -- Surjection half of the image factorization

  isSurjectiveRep : isSurjection rep
  isSurjectiveRep = elimProp (λ _ → squash₁) (λ x → ∣ x , refl ∣₁)

  -- Embedding half of the image factorization

  isEmbeddingReplaceEl : isEmbedding ReplaceEl
  isEmbeddingReplaceEl r r' =
    isoToIsEquiv (iso _ (inv r r') (elInv r r') (invEl r r'))
    where
    inv : ∀ r r' → ReplaceEl r ≡ ReplaceEl r' → r ≡ r'
    inv r r' Q = quo r r' (pathToEquiv Q)

    elInv : ∀ r r' Q →  cong ReplaceEl (inv r r' Q) ≡ Q
    elInv r r' Q = uaη Q

    invEl : ∀ r r' p → inv r r' (cong ReplaceEl p) ≡ p
    invEl r = J> cong (quo r r) pathToEquivRefl ∙ quoid r
