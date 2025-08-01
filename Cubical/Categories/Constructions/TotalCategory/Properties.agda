module Cubical.Categories.Constructions.TotalCategory.Properties where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels

open import Cubical.Data.Sigma

open import Cubical.Categories.Category.Base
open import Cubical.Categories.Functor
open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Displayed.Functor
open import Cubical.Categories.Displayed.Section.Base
open import Cubical.Categories.Constructions.TotalCategory.Base
open import Cubical.Categories.Displayed.Instances.Terminal.Base
import      Cubical.Categories.Displayed.Reasoning as HomᴰReasoning

private
  variable
    ℓC ℓC' ℓD ℓD' ℓE ℓE' ℓCᴰ ℓCᴰ' ℓDᴰ ℓDᴰ' ℓEᴰ ℓEᴰ' : Level

-- Projections out of the total category
module _ {C : Category ℓC ℓC'} {Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ'} where
  open Functor
  open Functorᴰ
  open Section

  Fst : Functor (∫C Cᴰ) C
  Fst .F-ob = fst
  Fst .F-hom = fst
  Fst .F-id = refl
  Fst .F-seq =
    λ f g → cong {x = f ⋆⟨ ∫C Cᴰ ⟩ g} fst refl

  Snd : Section Fst Cᴰ
  Snd .F-obᴰ      = snd
  Snd .F-homᴰ     = snd
  Snd .F-idᴰ      = refl
  Snd .F-seqᴰ _ _ = refl

-- A section
{-
          Cᴰ
        ↗ |
       /  |
   s  /   |
     /    |
    /     ↓
   E ---→ C
       F
-}
--
-- is equivalent to a functor
--    intro' F s
-- E ------------→ ∫ C Cᴰ
--
  module _ {D : Category ℓD ℓD'}
           (F : Functor D C)
           (Fᴰ : Section F Cᴰ)
           where
    -- should this be "intro" or "corec"? style decision needed.
    intro : Functor D (∫C Cᴰ)
    intro .F-ob d = F ⟅ d ⟆ , Fᴰ .F-obᴰ _
    intro .F-hom f = (F ⟪ f ⟫) , (Fᴰ .F-homᴰ _)
    intro .F-id = ΣPathP (F .F-id , Fᴰ .F-idᴰ)
    intro .F-seq f g = ΣPathP (F .F-seq f g , Fᴰ .F-seqᴰ _ _)

  module _ {D : Category ℓD ℓD'}
           {F : Functor C D}
           {Dᴰ : Categoryᴰ D ℓDᴰ ℓDᴰ'}
           (Fᴰ : Functorᴰ F Cᴰ Dᴰ)
         where

-- A displayed functor
--
--     Fᴰ
-- Cᴰ -----→ Dᴰ
-- |         |
-- |         |
-- ↓         ↓
-- C ------→ D
--     F
--
-- is equivalent to a section
{-
               Dᴰ
             ↗ |
            /  |
   elim Fᴰ /   |
          /    |
         /     ↓
   ∫ Cᴰ  ----→ D
        F ∘F Fst
-}
    open Functorᴰ
    private
      module Dᴰ = Categoryᴰ Dᴰ
      module R = HomᴰReasoning Dᴰ
    elim : Section (F ∘F Fst) Dᴰ
    elim = compFunctorᴰSection Fᴰ Snd

  module _ {D : Category ℓD ℓD'}
           (F : Functor C D)
           (Dᴰ : Categoryᴰ D ℓDᴰ ℓDᴰ')
           (Fᴰ : Section (F ∘F Fst) Dᴰ)
         where
    open Functorᴰ
    private
      module Dᴰ = Categoryᴰ Dᴰ
      module R = HomᴰReasoning Dᴰ
    -- this is a recursion principle for an *arbitrary* displayed
    -- category Cᴰ.

    -- this is a dependent uncurry
    recᴰ : Functorᴰ F Cᴰ Dᴰ
    recᴰ .F-obᴰ {x} xᴰ = Fᴰ .F-obᴰ (x , xᴰ)
    recᴰ .F-homᴰ {f = f} fᴰ = Fᴰ .F-homᴰ (f , fᴰ)
    recᴰ .F-idᴰ = R.rectify (Fᴰ .F-idᴰ)
    recᴰ .F-seqᴰ {x} {y} {z} {f} {g} {xᴰ} {yᴰ} {zᴰ} fᴰ gᴰ =
      R.rectify (Fᴰ .F-seqᴰ (f , fᴰ) (g , gᴰ))

