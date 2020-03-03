{-# OPTIONS --cubical --safe #-}
module Cubical.Foundations.Structure where

open import Cubical.Core.Everything

private
  variable
    ℓ ℓ' ℓ'' : Level
    S : Type ℓ → Type ℓ'

-- A structure is a type-family S : Type ℓ → Type ℓ', i.e. for X : Type ℓ and s : S X,
-- the pair (X , s) : TypeWithStr ℓ S means that X is equipped with a S-structure, witnessed by s.

TypeWithStr : (ℓ : Level) (S : Type ℓ → Type ℓ') → Type (ℓ-max (ℓ-suc ℓ) ℓ')
TypeWithStr ℓ S = Σ[ X ∈ Type ℓ ] S X

typ : TypeWithStr ℓ S → Type ℓ
typ = fst

str : (A : TypeWithStr ℓ S) → S (typ A)
str = snd

-- An S-structure should have a notion of S-homomorphism, or rather S-isomorphism.
-- This will be implemented by a function ι : StrIso S ℓ'
-- that gives us for any two types with S-structure (X , s) and (Y , t) a family:
--    ι (X , s) (Y , t) : (X ≃ Y) → Type ℓ''
StrIso : (S : Type ℓ → Type ℓ'') (ℓ' : Level) → Type (ℓ-max (ℓ-suc (ℓ-max ℓ ℓ')) ℓ'')
StrIso {ℓ} S ℓ' = (A B : TypeWithStr ℓ S) → typ A ≃ typ B → Type ℓ'
