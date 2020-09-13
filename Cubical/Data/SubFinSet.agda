{-# OPTIONS --cubical --no-import-sorts --safe #-}

module Cubical.Data.SubFinSet where

open import Cubical.Data.Nat
open import Cubical.Data.Fin
open import Cubical.Data.Sigma
open import Cubical.Data.FinSet
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Functions.Embedding
open import Cubical.HITs.PropositionalTruncation as PT
open import Cubical.Relation.Nullary

private
  variable
    ℓ : Level
    A B : Type ℓ

isSubFinSet : Type ℓ → Type ℓ
isSubFinSet A = ∃[ n ∈ ℕ ] A ↪ Fin n

isFinSet→isSubFinSet : isFinSet A → isSubFinSet A
isFinSet→isSubFinSet = PT.map
  λ (n , f , isEquiv-f) →
    n , f , isEmbedding→hasPropFibers (isEquiv→isEmbedding isEquiv-f)

isSubFinSet→isSet : isSubFinSet A → isSet A
isSubFinSet→isSet = PT.rec
  isPropIsSet
  λ (n , emb) → Embedding-into-isSet→isSet emb isSetFin

isSubFinSet→Discrete : isSubFinSet A → Discrete A
isSubFinSet→Discrete isSubFinSet-A x y = PT.rec
  (isPropDec (isSubFinSet→isSet isSubFinSet-A x y))
  (λ (n , emb) → Embedding-into-Discrete→Discrete emb discreteFin x y)
  isSubFinSet-A
