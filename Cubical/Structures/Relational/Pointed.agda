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

pointed-setStructure : SetStructure ℓ ℓ
pointed-setStructure .struct = pointed-structure
pointed-setStructure .set setX = setX

pointed-rel : StrRel pointed-structure ℓ
pointed-rel .rel _ _ R = R
pointed-rel .prop propR = propR

open isSNRS
open BisimDescends
open isBisimulation

isSNRSPointed : isSNRS {ℓ = ℓ} pointed-setStructure pointed-rel
isSNRSPointed .propQuo _ = isContr→isProp (isContrSingl _)
isSNRSPointed .descends _ .fst _ .quoᴸ = (_ , refl)
isSNRSPointed .descends _ .fst _ .quoᴿ = (_ , refl)
isSNRSPointed .descends {A = _ , x} {_ , y} R .fst r .path =
  ua-gluePath (Bisim→Equiv.Thm R) (eq/ (S.fwd x) y (S.zigzag (S.bwdRel y) r (S.fwdRel x)))
  where
  module S = isBisimulation (R .snd)
isSNRSPointed .descends {A = _ , x} {_ , y} R .snd d =
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
