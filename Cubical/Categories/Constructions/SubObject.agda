{-# OPTIONS --safe #-}
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Powerset
open import Cubical.Foundations.Prelude

open import Cubical.Data.Sigma

open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.Morphism

open Category

module Cubical.Categories.Constructions.SubObject
  {ℓ ℓ' : Level}
  (C : Category ℓ ℓ')
  (c : C .ob)
  where

open import Cubical.Categories.Constructions.Slice C c

isSubObj : ℙ (SliceCat .ob)
isSubObj (sliceob arr) = isMonic C arr , isPropIsMonic C arr

SubObjCat : Category (ℓ-max ℓ ℓ') ℓ'
SubObjCat = ΣPropCat SliceCat isSubObj

SubObjCat→SliceCat : Functor SubObjCat SliceCat
SubObjCat→SliceCat = forgetΣPropCat SliceCat isSubObj

subObjMorIsMonic : {s t : SubObjCat .ob} (f : SubObjCat [ s , t ])
  → isMonic C (S-hom f)
subObjMorIsMonic {s = s} {t = t} f = postcompCreatesMonic C
  (S-hom f) (S-arr (t .fst)) comp-is-monic
  where comp-is-monic = subst (isMonic C) (sym (S-comm f)) (s .snd)
