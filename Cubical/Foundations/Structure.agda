{-# OPTIONS --safe #-}
module Cubical.Foundations.Structure where

open import Cubical.Core.Everything
open import Cubical.Foundations.Prelude

private
  variable
    ℓ ℓ' ℓ'' : Level
    S : Type ℓ → Type ℓ'

-- A structure is a type-family S : Type ℓ → Type ℓ', i.e. for X : Type ℓ and s : S X,
-- the pair (X , s) : TypeWithStr ℓ S means that X is equipped with an S-structure, witnessed by s.

TypeWithStr : (ℓ : Level) (S : Type ℓ → Type ℓ') → Type (ℓ-max (ℓ-suc ℓ) ℓ')
TypeWithStr ℓ S = Σ[ X ∈ Type ℓ ] S X

typ : TypeWithStr ℓ S → Type ℓ
typ = fst

str : (A : TypeWithStr ℓ S) → S (typ A)
str = snd

-- Alternative notation for typ
⟨_⟩ : TypeWithStr ℓ S → Type ℓ
⟨_⟩ = typ

instance
  mkTypeWithStr : ∀ {ℓ} {S : Type ℓ → Type ℓ'} {X} → {{S X}} → TypeWithStr ℓ S
  mkTypeWithStr {{i}} = _ , i

-- An S-structure should have a notion of S-homomorphism, or rather S-isomorphism.
-- This will be implemented by a function ι : StrEquiv S ℓ'
-- that gives us for any two types with S-structure (X , s) and (Y , t) a family:
--    ι (X , s) (Y , t) : (X ≃ Y) → Type ℓ''
StrEquiv : (S : Type ℓ → Type ℓ'') (ℓ' : Level) → Type (ℓ-max (ℓ-suc (ℓ-max ℓ ℓ')) ℓ'')
StrEquiv {ℓ} S ℓ' = (A B : TypeWithStr ℓ S) → typ A ≃ typ B → Type ℓ'

-- An S-structure may instead be equipped with an action on equivalences, which will
-- induce a notion of S-homomorphism

EquivAction : (S : Type ℓ → Type ℓ'') → Type (ℓ-max (ℓ-suc ℓ) ℓ'')
EquivAction {ℓ} S = {X Y : Type ℓ} → X ≃ Y → S X ≃ S Y

EquivAction→StrEquiv : {S : Type ℓ → Type ℓ''}
  → EquivAction S → StrEquiv S ℓ''
EquivAction→StrEquiv α (X , s) (Y , t) e = equivFun (α e) s ≡ t
