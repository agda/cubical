{-# OPTIONS --safe --lossy-unification #-}
module Cubical.Cohomology.EilenbergMacLane.Rings.Z2-properties where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.HLevels

open import Cubical.Data.Unit
open import Cubical.Data.Nat hiding (_+_)

open import Cubical.Algebra.Group
open import Cubical.Algebra.Group.Morphisms
open import Cubical.Algebra.Group.Instances.IntMod
open import Cubical.Algebra.AbGroup
open import Cubical.Algebra.AbGroup.Instances.Unit
open import Cubical.Algebra.DirectSum.DirectSumHIT.Base
open import Cubical.Algebra.Ring
open import Cubical.Algebra.CommRing
open import Cubical.Algebra.CommRing.Instances.IntMod
open import Cubical.Algebra.AbGroup.Instances.IntMod

open import Cubical.Homotopy.EilenbergMacLane.Order2

open import Cubical.Cohomology.EilenbergMacLane.Base
open import Cubical.Cohomology.EilenbergMacLane.CupProduct
open import Cubical.Cohomology.EilenbergMacLane.RingStructure

open Iso
open PlusBis
open RingTheory
open IsGroupHom


module _
  (X : Type ℓ-zero)
  where

  -- Pratical notations
  H*ℤ/2 : Type ℓ-zero
  H*ℤ/2 = H* ℤ/2Ring X

  H*Rℤ/2 : Ring ℓ-zero
  H*Rℤ/2 = H*R ℤ/2Ring X

open CommRingStr (snd ℤ/2CommRing) using ()
  renaming
  ( 0r        to 0ℤ/2
  ; 1r        to 1ℤ/2
  ; _+_       to _+ℤ/2_
  ; -_        to -ℤ/2_
  ; _·_       to _·ℤ/2_
  ; +Assoc    to +ℤ/2Assoc
  ; +IdL      to +ℤ/2IdL
  ; +IdR      to +ℤ/2IdR
  ; +Comm     to +ℤ/2Comm
  ; ·Assoc    to ·ℤ/2Assoc
  ; ·IdL      to ·ℤ/2IdL
  ; ·IdR      to ·ℤ/2IdR
  ; ·DistR+   to ·ℤ/2DistR+
  ; ·Comm     to ·ℤ/2Comm
  ; is-set    to isSetℤ/2     )

module _
  {X : Type ℓ-zero}
  where

  -- This notation is needed as G'' as Agda can't figure it out. TODO: add a x ⌣[ R ] y notation?
  _⌣ℤ/2_ : {n m : ℕ} → coHom n ℤ/2 X → coHom m ℤ/2 X → coHom (n +' m) ℤ/2 X
  _⌣ℤ/2_ x y = _⌣_ {G'' = ℤ/2Ring} x y

  unitGroupEq : {n : ℕ} → (e : AbGroupIso (coHomGr n ℤ/2 X) (UnitAbGroup {ℓ = ℓ-zero})) →
                   (x y : coHom n ℤ/2 X) → x ≡ y
  unitGroupEq {n} e x y = isOfHLevelRetractFromIso {ℓ' = ℓ-zero} 1 (fst e) isPropUnit* _ _


-- X have to explicit or it doesn't type check when used in another file
module CbnCupProduct
  (X : Type ℓ-zero)
  where

  module _
    {n m : ℕ}
    (ϕₙ : fst ℤ/2 → coHom n ℤ/2 X)
    (ϕₙstr : IsGroupHom (snd (ℤGroup/ 2) ) ϕₙ (snd (AbGroup→Group (coHomGr n ℤ/2 X))))
    (ϕₘ : fst ℤ/2 → coHom m ℤ/2 X)
    (ϕₘstr : IsGroupHom (snd (ℤGroup/ 2) ) ϕₘ (snd (AbGroup→Group (coHomGr m ℤ/2 X))))
    (ϕₙ₊ₘ : fst ℤ/2 → coHom (n +' m) ℤ/2 X)
    (ϕₙ₊ₘstr : IsGroupHom (snd (ℤGroup/ 2) ) ϕₙ₊ₘ (snd (AbGroup→Group (coHomGr (n +' m) ℤ/2 X))))
    (cup-comp : ϕₙ 1ℤ/2 ⌣ℤ/2 ϕₘ 1ℤ/2 ≡ ϕₙ₊ₘ 1ℤ/2 )
    where

    ϕₙ⌣ϕₘ-notTrivial : (a b : fst ℤ/2) → ϕₙ a ⌣ℤ/2 ϕₘ b ≡ ϕₙ₊ₘ (a ·ℤ/2 b)
    ϕₙ⌣ϕₘ-notTrivial a = ℤ/2-elim {A = λ a → (b : fst ℤ/2) → ϕₙ a ⌣ℤ/2 ϕₘ b ≡ ϕₙ₊ₘ (a ·ℤ/2 b)}
                            (λ b → cong (λ X → X ⌣ℤ/2 ϕₘ b) (pres1 ϕₙstr)
                                    ∙ 0ₕ-⌣ _ _ _
                                    ∙ sym (pres1 ϕₙ₊ₘstr)
                                    ∙ cong ϕₙ₊ₘ (sym (0LeftAnnihilates ℤ/2Ring _)))
                            (λ b → ℤ/2-elim {A = λ b → ϕₙ 1ℤ/2 ⌣ℤ/2 ϕₘ b ≡ ϕₙ₊ₘ (1ℤ/2 ·ℤ/2 b)}
                                    (cong (λ X → ϕₙ 1ℤ/2 ⌣ℤ/2 X) (pres1 ϕₘstr)
                                    ∙ ⌣-0ₕ {G'' = ℤ/2Ring} n m (ϕₙ 1ℤ/2)
                                    ∙ sym (pres1 ϕₙ₊ₘstr)
                                    ∙ cong ϕₙ₊ₘ (sym (0RightAnnihilates ℤ/2Ring _)))
                                    cup-comp
                                    b)
                            a


  module _
    {n m : ℕ}
    (ϕₙ : fst ℤ/2 → coHom n ℤ/2 X)
    (ϕₙstr : IsGroupHom (snd (ℤGroup/ 2) ) ϕₙ (snd (AbGroup→Group (coHomGr n ℤ/2 X))))
    (ϕₘ : fst ℤ/2 → coHom m ℤ/2 X)
    (ϕₘstr : IsGroupHom (snd (ℤGroup/ 2) ) ϕₘ (snd (AbGroup→Group (coHomGr m ℤ/2 X))))
    (cup-comp : ϕₙ 1ℤ/2 ⌣ℤ/2 ϕₘ 1ℤ/2 ≡ 0ₕ (n +' m))
    where

    ϕₙ⌣ϕₘ-Trivial : (a b : fst ℤ/2) → ϕₙ a ⌣ℤ/2 ϕₘ b ≡ 0ₕ (n +' m)
    ϕₙ⌣ϕₘ-Trivial a = ℤ/2-elim {A = λ a → (b : fst ℤ/2) → ϕₙ a ⌣ℤ/2 ϕₘ b ≡ 0ₕ (n +' m)}
                       (λ b → cong (λ X → X ⌣ℤ/2 ϕₘ b) (pres1 ϕₙstr)
                                    ∙ 0ₕ-⌣ _ _ _)
                       (λ b → ℤ/2-elim {A = λ b → ϕₙ 1ℤ/2 ⌣ℤ/2 ϕₘ b ≡ 0ₕ (n +' m)}
                              (cong (λ X → ϕₙ 1ℤ/2 ⌣ℤ/2 X) (pres1 ϕₘstr)
                                    ∙ ⌣-0ₕ {G'' = ℤ/2Ring} n m (ϕₙ 1ℤ/2))
                              cup-comp
                       b)
                       a
