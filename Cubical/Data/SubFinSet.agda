{-

Definition of subfinite sets

A set is subfinite if it is merely a subset of `Fin n` for some `n`. This
definition is weaker than `isFinSet` if we don't assume LEM, but they
are equivalent if we do.

Every subfinite set is guaranteed to be a set and discrete.

-}


module Cubical.Data.SubFinSet where

open import Cubical.Data.Nat
open import Cubical.Data.SumFin
open import Cubical.Data.Sigma
open import Cubical.Data.FinSet
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
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
  (λ (n , f , isEquiv-f) →
      n , f , isEquiv→isEmbedding isEquiv-f) ∘ isFinSet→isFinSet'

isSubFinSet→isSet : isSubFinSet A → isSet A
isSubFinSet→isSet = PT.rec
  isPropIsSet
  λ (n , emb) → Embedding-into-isSet→isSet emb isSetFin

isSubFinSet→Discrete : isSubFinSet A → Discrete A
isSubFinSet→Discrete isSubFinSet-A x y = PT.rec
  (isPropDec (isSubFinSet→isSet isSubFinSet-A x y))
  (λ (n , emb) → Embedding-into-Discrete→Discrete emb discreteFin x y)
  isSubFinSet-A
