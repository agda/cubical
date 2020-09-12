
{-# OPTIONS --cubical --no-import-sorts --safe #-}

module Cubical.Algebra.Group.Higher where

open import Cubical.Core.Everything
open import Cubical.Data.Nat
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Prelude hiding (comp)
open import Cubical.Foundations.Pointed
open import Cubical.Foundations.Isomorphism
open import Cubical.Homotopy.Loopspace
open import Cubical.Homotopy.Connected
open import Cubical.Algebra.Group.Base
open import Cubical.Algebra.Group.EilenbergMacLane1
open import Cubical.HITs.EilenbergMacLane1


import Cubical.Foundations.GroupoidLaws as GL

private
  variable
    ℓ : Level


record HigherGroup ℓ : Type (ℓ-suc ℓ) where
  constructor highergroup
  field
    base : Pointed ℓ
    isConn : isConnected 2 (typ base)

record BGroup ℓ (n k : ℕ) : Type (ℓ-suc ℓ) where
  no-eta-equality
  constructor bgroup
  field
    base : Pointed ℓ
    isConn : isConnected (k + 1) (typ base)
    isTrun : isOfHLevel (n + k + 2) (typ base)

module _ where
  open BGroup
  η-BGroup : {n k : ℕ} {BG BH : BGroup ℓ n k}
             → (p : typ (base BG) ≡ typ (base BH))
             → (q : PathP (λ i → p i) (pt (base BG)) (pt (base BH)))
             → BG ≡ BH
  base (η-BGroup p q i) .fst = p i
  base (η-BGroup p q i) .snd = q i
  isConn (η-BGroup {k = k} {BG = BG} {BH = BH} p q i) = r i
    where
      r : PathP (λ i → isConnected (k + 1) (p i)) (isConn BG) (isConn BH)
      r = isProp→PathP (λ _ → isPropIsOfHLevel 0) (isConn BG) (isConn BH)
  isTrun (η-BGroup {n = n} {k = k} {BG = BG} {BH = BH} p q i) = s i
    where
      s : PathP (λ i → isOfHLevel (n + k + 2) (p i)) (isTrun BG) (isTrun BH)
      s = isProp→PathP (λ i → isPropIsOfHLevel (n + k + 2)) (isTrun BG) (isTrun BH)


BGroupHom : {ℓ : Level} {n k : ℕ} (G H : BGroup ℓ n k) → Type ℓ
BGroupHom G H = (BGroup.base G) →∙ (BGroup.base H)

carrier : {ℓ : Level} {n k : ℕ} (G : BGroup ℓ n k) → Pointed ℓ
carrier {k = k} BG = (Ω^ k) base
  where
    open BGroup BG

1BGroup : (ℓ : Level) → Type (ℓ-suc ℓ)
1BGroup ℓ = BGroup ℓ 0 1

1BGroup→Group : {ℓ : Level} (BG : 1BGroup ℓ) → Group {ℓ}
1BGroup→Group BG =
  makeGroup {G = (pt base) ≡ (pt base)}
            refl
            _∙_
            sym
            (isTrun (pt base) (pt base))
            GL.assoc
            (λ a → sym (GL.rUnit a))
            (λ g → sym (GL.lUnit g))
            GL.rCancel
            GL.lCancel
    where
      open BGroup BG

Group→1BGroup : (G : Group {ℓ}) → 1BGroup ℓ
BGroup.base (Group→1BGroup G) .fst = EM₁ G
BGroup.base (Group→1BGroup G) .snd = embase
BGroup.isConn (Group→1BGroup G) = EM₁Connected G
BGroup.isTrun (Group→1BGroup G) = EM₁Groupoid G

{-
IsoGroup1BGroup : (ℓ : Level) → Iso (Group {ℓ}) (1BGroup ℓ)
Iso.fun (IsoGroup1BGroup ℓ) = Group→1BGroup
Iso.inv (IsoGroup1BGroup ℓ) = 1BGroup→Group
Iso.leftInv (IsoGroup1BGroup ℓ) G = η-Group (ΩEM₁≡ G) {!!} {!!} {!!} {!!}
Iso.rightInv (IsoGroup1BGroup ℓ) BG = η-BGroup {!!} {!!}
-}
