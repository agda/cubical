
{-# OPTIONS --cubical --no-import-sorts --safe #-}

module Cubical.Structures.Group.Higher where

open import Cubical.Core.Everything
open import Cubical.Data.Nat
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Prelude hiding (comp)
open import Cubical.Foundations.Pointed
open import Cubical.Homotopy.Loopspace
open import Cubical.Homotopy.Connected
open import Cubical.Structures.Group.Base

import Cubical.Foundations.GroupoidLaws as GL

record HigherGroup ℓ : Type (ℓ-suc ℓ) where
  constructor highergroup
  field
    base : Pointed ℓ
    isConn : isConnected 2 (typ base)

record BGroup ℓ (n k : ℕ) : Type (ℓ-suc ℓ) where
  constructor bgroup
  field
    base : Pointed ℓ
    isKConn : isConnected (k + 2) (typ base)
    isNKTrun : isOfHLevel (n + k + 2) (typ base)


BGroupHom : {ℓ : Level} {n k : ℕ} (G H : BGroup ℓ n k) → Type ℓ
BGroupHom G H = (BGroup.base G) →∙ (BGroup.base H)

carrier : {ℓ : Level} {n k : ℕ} (G : BGroup ℓ n k) → Pointed ℓ
carrier {k = k} (bgroup base _ _) = (Ω^ k) base

1BGroup : (ℓ : Level) → Type (ℓ-suc ℓ)
1BGroup ℓ = BGroup ℓ 0 1

1BGroup→Group : {ℓ : Level} (G : 1BGroup ℓ) → Group {ℓ}
1BGroup→Group (bgroup (BG , pt) conn trun) =
  makeGroup {G = pt ≡ pt}
            refl
            _∙_
            sym
            (trun pt pt)
            GL.assoc
            (λ a → sym (GL.rUnit a))
            (λ g → sym (GL.lUnit g))
            GL.rCancel
            GL.lCancel


{-
module BGroupNotation {ℓ : Level} {n k : ℕ} (G : BGroup ℓ n k) where
  BGroupType : Type ℓ
  BGroupType = typ (BGroup.base G)

  BGroup∙ : BGroupType
  BGroup∙ = pt (BGroup.base G)


data 1-GroupHIT {ℓ : Level} (G : Group ℓ) : Type ℓ where
  basepoint : 1-GroupHIT G
  loops : (Group.type G) → basepoint ≡ basepoint
  isTrun : isOfHLevel 3 (1-GroupHIT G)
  loopsid : loops (isGroup.id (Group.groupStruc G)) ≡ refl
  loopshom : ∀ g g' → loops ((isGroup.comp (Group.groupStruc G)) g g') ≡  (loops g) ∙ (loops g')




-- nkBGroup→Higher : {ℓ : Level} {n k : ℕ} (_ : nkBGroup ℓ n k) → HigherGroup ℓ
-- nkBGroup→Higher (nkbgroup base iscon _) = highergroup base iscon -- needs (suc k)-connected implies k-connected

BGroup→Group : {ℓ : Level} (G : 1BGroup ℓ) → Group ℓ
BGroup→Group (bgroup base kcon nktrun) = group
                     (point ≡ point)
                     (nktrun point point)
                     (group-struct refl sym _∙_ (λ { a → sym (GL.lUnit a) }) (λ { a → sym (GL.rUnit a) })  GL.assoc' GL.lCancel GL.rCancel)
                     where
                       point = pt base

-}
