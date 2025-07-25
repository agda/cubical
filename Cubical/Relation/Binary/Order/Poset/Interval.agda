{-# OPTIONS --safe #-}

module Cubical.Relation.Binary.Order.Poset.Interval where

open import Cubical.Foundations.Equiv
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Structure
open import Cubical.Foundations.Transport
open import Cubical.Foundations.Isomorphism

open import Cubical.Functions.Embedding
open import Cubical.Functions.Fibration

open import Cubical.Data.Bool as B using (Bool; true; false)
open import Cubical.Data.Sigma

open import Cubical.Relation.Binary.Order.Poset.Base
open import Cubical.Relation.Binary.Order.Poset.Properties
open import Cubical.Relation.Binary.Order.Poset.Subset

open import Cubical.Reflection.RecordEquiv

private variable
  ℓ ℓ' : Level

module _ (P' : Poset ℓ ℓ') where
  private P = ⟨ P' ⟩
  open PosetStr (snd P')

  module _ (x y : P) where
    -- the set of elements between x and y
    record Interval : Type (ℓ-max ℓ ℓ') where
      constructor interval
      field
        z : P
        x≤z : x ≤ z
        z≤y : z ≤ y

    unquoteDecl IntervalIsoΣ = declareRecordIsoΣ IntervalIsoΣ (quote Interval)

    isSetInterval : isSet Interval
    isSetInterval = isOfHLevelRetractFromIso 2 IntervalIsoΣ $
      isSetΣSndProp is-set λ _ → isProp× (is-prop-valued _ _) (is-prop-valued _ _)

    Interval↪ : Interval ↪ P
    Interval↪ = compEmbedding (EmbeddingΣProp λ _ → isProp× (is-prop-valued _ _) (is-prop-valued _ _)) (Iso→Embedding IntervalIsoΣ)

    IntervalEmbedding : Embedding P (ℓ-max ℓ ℓ')
    IntervalEmbedding = Interval , Interval↪

    IntervalPosetStr : PosetStr ℓ' Interval
    IntervalPosetStr = posetstr _ (isPosetInduced isPoset Interval Interval↪)

    IntervalPoset : Poset (ℓ-max ℓ ℓ') ℓ'
    IntervalPoset = Interval , IntervalPosetStr

    Interval≡ : ∀ i j → i .Interval.z ≡ j .Interval.z → i ≡ j
    Interval≡ _ _ = isoFunInjective IntervalIsoΣ _ _ ∘ Σ≡Prop (λ _ → isProp× (is-prop-valued _ _) (is-prop-valued _ _))

    module _ (x≤y : x ≤ y) where
      intervalTop : Interval
      intervalTop = interval y x≤y (is-refl y)

      intervalBot : Interval
      intervalBot = interval x (is-refl x) x≤y

      2→Interval : Bool → Interval
      2→Interval false = intervalBot
      2→Interval true  = intervalTop
