{-# OPTIONS --safe #-}
{-
  This is based on the article by Sojakova, van Doorn and Rijke:
  https://florisvandoorn.com/papers/sequential_colimits_homotopy.pdf
-}
module Cubical.HITs.SequentialColimit.Base where

open import Cubical.Foundations.Prelude
open import Cubical.Structures.Successor

private
  variable
    ℓ ℓ′ : Level

open SuccStr

data GenericSequentialColimit (S : SuccStr ℓ) (s : TypeSeq ℓ′ S) : Type (ℓ-max ℓ ℓ′) where
    ι : (i : Index S) → fst s i → GenericSequentialColimit S s
    glue : (i : Index S) (x : fst s i) → ι i x ≡ ι (succ S i) (snd s i x)

SequentialColimit : (s : TypeSeq ℓ′ ℕ+) → Type _
SequentialColimit = GenericSequentialColimit ℕ+