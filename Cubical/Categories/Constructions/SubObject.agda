{-# OPTIONS --safe #-}
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Powerset
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Path
open import Cubical.Foundations.Univalence

open import Cubical.Data.Sigma

open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.Morphism

open import Cubical.Relation.Binary.Order.Proset

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

isPropSubObjMor : (s t : SubObjCat .ob) → isProp (SubObjCat [ s , t ])
SliceHom.S-hom
  (isPropSubObjMor
    (sliceob incS , isMonicIncS)
    (sliceob incT , isMonicIncT)
    (slicehom x xComm)
    (slicehom y yComm) i) =
    isMonicIncT {a = x} {a' = y} (xComm ∙ sym  yComm) i
SliceHom.S-comm
  (isPropSubObjMor
    (sliceob incS , isMonicIncS)
    (sliceob incT , isMonicIncT)
    (slicehom x xComm)
    (slicehom y yComm) i) =
    isProp→PathP (λ i → C .isSetHom (seq' C (isMonicIncT (xComm ∙ sym yComm) i) incT) incS) xComm yComm i

isReflSubObjMor : (x : SubObjCat .ob) → SubObjCat [ x , x ]
SliceHom.S-hom (isReflSubObjMor (sliceob inc , isMonicInc)) = C .id
SliceHom.S-comm (isReflSubObjMor (sliceob inc , isMonicInc)) = C .⋆IdL inc

isTransSubObjMor : (x y z : SubObjCat .ob) → SubObjCat [ x , y ] → SubObjCat [ y , z ] → SubObjCat [ x , z ]
SliceHom.S-hom
  (isTransSubObjMor
    (sliceob incX , isMonicIncX)
    (sliceob incY , isMonicIncY)
    (sliceob incZ , isMonicIncZ)
    (slicehom f fComm)
    (slicehom g gComm)) = seq' C f g
SliceHom.S-comm
  (isTransSubObjMor
    (sliceob incX , isMonicIncX)
    (sliceob incY , isMonicIncY)
    (sliceob incZ , isMonicIncZ)
    (slicehom f fComm)
    (slicehom g gComm)) =
  seq' C (seq' C f g) incZ
    ≡⟨ C .⋆Assoc f g incZ ⟩
  seq' C f (seq' C g incZ)
    ≡⟨ cong (λ x → seq' C f x) gComm ⟩
  seq' C f incY
    ≡⟨ fComm ⟩
  incX
    ∎

module _ (isSetCOb : isSet (C .ob)) where
  subObjCatPreorderStr : ProsetStr _ (SubObjCat .ob)
  ProsetStr._≲_ subObjCatPreorderStr x y = SubObjCat [ x , y ]
  IsProset.is-set (ProsetStr.isProset subObjCatPreorderStr) = isSetΣ (isSetSliceOb isSetCOb) λ x → isProp→isSet (∈-isProp isSubObj x)
  IsProset.is-prop-valued (ProsetStr.isProset subObjCatPreorderStr) = isPropSubObjMor
  IsProset.is-refl (ProsetStr.isProset subObjCatPreorderStr) = isReflSubObjMor
  IsProset.is-trans (ProsetStr.isProset subObjCatPreorderStr) = isTransSubObjMor
