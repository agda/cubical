{-

This file contains:

- The first Eilenberg–Mac Lane type as a HIT

-}
{-# OPTIONS --cubical --no-import-sorts --safe #-}
module Cubical.HITs.EilenbergMacLane1.Base where

open import Cubical.Foundations.Prelude
open import Cubical.Algebra.Group.Base

private
  variable ℓ : Level

module _ (Group@(G , str) : Group ℓ) where
  open GroupStr str

  data EM₁ : Type ℓ where
    embase : EM₁
    emloop : G → embase ≡ embase
    emcomp : (g h : G)
           → PathP (λ j → embase ≡ emloop h j) (emloop g) (emloop (g · h))
    emsquash : ∀ (x y : EM₁) (p q : x ≡ y) (r s : p ≡ q) → r ≡ s

  {- The emcomp constructor fills the square:
^
    emloop (g · h)
    [a]— — — >[c]
     ‖         ^
     ‖         | emloop h     ^
     ‖         |            j |
    [a]— — — >[b]          ∙ — >
       emloop g                i

    We use this to give another constructor-like construction:
  -}

  emloop-comp : (g h : G) → emloop (g · h) ≡ emloop g ∙ emloop h
  emloop-comp g h i = compPath-unique refl (emloop g) (emloop h)
    (emloop (g · h) , emcomp g h)
    (emloop g ∙ emloop h , compPath-filler (emloop g) (emloop h)) i .fst
