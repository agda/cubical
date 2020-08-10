{-# OPTIONS --cubical --safe #-}

module Cubical.Data.Strict2Group.Categorical where

open import Cubical.Foundations.Prelude
open import Cubical.Categories.InternalCategory
open import Cubical.Categories.Groups

{-- Formalization of strict 2-groups as
internal categories of the 1-category Grp
of Groups. --}

Strict2GroupInternalCat : (ℓ : Level) → Type (ℓ-suc ℓ)
Strict2GroupInternalCat ℓ = InternalCategory (1BGROUP ℓ)
