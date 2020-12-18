{-
This is copied from a PR of Ulrik Bucholtz
This file contains:

- The first Eilenberg–Mac Lane type as a HIT

-}
{-# OPTIONS --cubical --no-import-sorts --safe #-}
module Cubical.HITs.EilenbergMacLane1.Base where

open import Cubical.Foundations.Prelude
open import Cubical.Structures.Group.Base

private
  variable ℓ : Level

module _ (G : Group {ℓ}) where
  open Group G

  data EM₁ : Type ℓ where
    embase : EM₁
    emloop : Carrier → embase ≡ embase
    emcomp : (g h : Carrier)
           → PathP (λ j → embase ≡ emloop h j) (emloop g) (emloop (g + h))
    emsquash : ∀ (x y : EM₁) (p q : x ≡ y) (r s : p ≡ q) → r ≡ s

  {- The comp// constructor fills the square:

    emloop (g + h)
    [a]— — — >[c]
     ‖         ^
     ‖         | emloop h     ^
     ‖         |            j |
    [a]— — — >[b]          ∙ — >
       emloop g                i

    We use this to give another constructor-like construction:
  -}

  emloop-comp : (g h : Carrier) → emloop (g + h) ≡ emloop g ∙ emloop h
  emloop-comp g h i = compPath-unique refl (emloop g) (emloop h)
    (emloop (g + h) , emcomp g h)
    (emloop g ∙ emloop h , compPath-filler (emloop g) (emloop h)) i .fst
