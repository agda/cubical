{-

Pointed structure: X ↦ X

-}
{-# OPTIONS --cubical --no-import-sorts --safe #-}
module Cubical.Structures.Relational.Pointed where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.RelationalStructure
open import Cubical.Foundations.Univalence
open import Cubical.Relation.ZigZag.Base
open import Cubical.HITs.SetQuotients

open import Cubical.Structures.Pointed

private
  variable
    ℓ : Level

-- Structured relations

PointedSetStructure : SetStructure ℓ ℓ
PointedSetStructure .struct = PointedStructure
PointedSetStructure .set setX = setX

PointedPropRel : StrRel PointedStructure ℓ
PointedPropRel .rel R = R
PointedPropRel .prop propR = propR

open isUnivalentRel
open BisimDescends
open isBisimulation

pointedUnivalentRel : isUnivalentRel {ℓ = ℓ} PointedSetStructure PointedPropRel
pointedUnivalentRel .propQuo _ = isContr→isProp (isContrSingl _)
pointedUnivalentRel .descends _ .fst _ .quoᴸ = (_ , refl)
pointedUnivalentRel .descends _ .fst _ .quoᴿ = (_ , refl)
pointedUnivalentRel .descends {A = _ , x} {_ , y} R .fst r .path =
  ua-gluePath (Bisim→Equiv.Thm R) (eq/ (S.fwd x) y (S.zigzag (S.bwdRel y) r (S.fwdRel x)))
  where
  module S = isBisimulation (R .snd)
pointedUnivalentRel .descends {A = _ , x} {_ , y} R .snd d =
  R .snd .zigzag
    (R .snd .fwdRel x)
    (isEquivRel→isEffective
      (λ _ _ → R .snd .prop _ _)
      (bisim→EquivRel (invBisim R) .snd)
      (R .snd .fwd x) y
      .equiv-proof
      (cong (E.Thm .fst) (d .quoᴸ .snd)
        ∙∙ ua-ungluePath E.Thm (d .path)
        ∙∙ sym (d .quoᴿ .snd))
      .fst .fst)
    (R .snd .bwdRel y)
  where
  module S = isBisimulation (R .snd)
  module E = Bisim→Equiv R
