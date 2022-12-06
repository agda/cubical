{-

This file contains:

- The first Eilenberg–Mac Lane type as a HIT

Remark: The proof that there is an isomorphism of types
between Ω EM₁ and G is in

Cubical.Homotopy.EilenbergMacLane.Properties

-}
{-# OPTIONS --cubical --no-import-sorts --safe #-}
module Cubical.HITs.EilenbergMacLane1.Base where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.GroupoidLaws
  renaming (assoc to assoc∙)
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

  emloop-1g : emloop 1g ≡ refl
  emloop-1g =
       lUnit (emloop 1g)
    ∙∙ cong (_∙ emloop 1g) (sym (lCancel (emloop 1g)) )
    ∙∙ sym (assoc∙ _ _ _)
    ∙∙ cong (sym (emloop 1g) ∙_) (sym (emloop-comp 1g 1g) ∙ cong emloop (·IdL 1g))
    ∙∙ rCancel _

  emloop-sym : (g : G) → emloop (inv g) ≡ sym (emloop g)
  emloop-sym g =
       rUnit _
    ∙∙ cong (emloop (inv g) ∙_) (sym (rCancel (emloop g)))
    ∙∙ assoc∙ _ _ _
    ∙∙ cong (_∙ sym (emloop g)) (sym (emloop-comp (inv g) g) ∙∙ cong emloop (·InvL g) ∙∙ emloop-1g)
    ∙∙ sym (lUnit _)

  data EM₁-raw : Type ℓ where
    embase-raw : EM₁-raw
    emloop-raw : (g : G) → embase-raw ≡ embase-raw

  EM₁-raw→EM₁ : EM₁-raw → EM₁
  EM₁-raw→EM₁ embase-raw = embase
  EM₁-raw→EM₁ (emloop-raw g i) = emloop g i
