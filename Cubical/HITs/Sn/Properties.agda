{-# OPTIONS --cubical --safe #-}
module Cubical.HITs.Sn.Properties where

open import Cubical.Data.Int
open import Cubical.Data.Bool
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Univalence
open import Cubical.HITs.S1
open import Cubical.HITs.Sn.Base
open import Cubical.HITs.Susp




--- Some silly lemmas on S1 ---

S¹≡S1 : S₊ 1 ≡ S¹
S¹≡S1 = cong Susp (sym (ua Bool≃Susp⊥)) ∙ sym S¹≡SuspBool

isOfHLevelS1 : isOfHLevel 3 (S₊ 1)
isOfHLevelS1 = transport (λ i → isOfHLevel 3 (S¹≡S1 (~ i)))
                          λ x y → J (λ y p → (q : x ≡ y) → isProp (p ≡ q))
                                     (transport (λ i → isSet (basedΩS¹≡Int x (~ i))) isSetInt refl)

SuspBool→S1 : Susp Bool → S₊ 1
SuspBool→S1 north = north
SuspBool→S1 south = south
SuspBool→S1 (merid false i) = merid south i
SuspBool→S1 (merid true i) = merid north i

S1→SuspBool : S₊ 1 → Susp Bool
S1→SuspBool north = north
S1→SuspBool south = south
S1→SuspBool (merid north i) = merid true i
S1→SuspBool (merid south i) = merid false i

SuspBool≃S1 : Susp Bool ≃ S₊ 1
SuspBool≃S1 = isoToEquiv iso1
  where
  iso1 : Iso (Susp Bool) (S₊ 1)
  Iso.fun iso1 = SuspBool→S1
  Iso.inv iso1 = S1→SuspBool
  Iso.rightInv iso1 north = refl
  Iso.rightInv iso1 south = refl
  Iso.rightInv iso1 (merid north i) = refl
  Iso.rightInv iso1 (merid south i) = refl
  Iso.leftInv iso1 north = refl
  Iso.leftInv iso1 south = refl
  Iso.leftInv iso1 (merid false i) = refl
  Iso.leftInv iso1 (merid true i) = refl
