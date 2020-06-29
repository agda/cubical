{-

Constant structure: _ ↦ A

-}
{-# OPTIONS --cubical --no-import-sorts --safe #-}
module Cubical.Structures.Relational.Constant where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Structure
open import Cubical.Foundations.RelationalStructure
open import Cubical.HITs.SetQuotients

open import Cubical.Structures.Constant

private
  variable
    ℓ ℓ' : Level

-- Structured relations

module _ (A : hSet ℓ') where

  ConstantRelStr : StrRel {ℓ = ℓ} (ConstantStructure (A .fst)) ℓ'
  ConstantRelStr _ a₀ a₁ = a₀ ≡ a₁

  open SuitableStrRel

  constantSuitableRel : SuitableStrRel {ℓ = ℓ} (ConstantStructure (A .fst)) ConstantRelStr
  constantSuitableRel .quo _ _ _ = isContrSingl _
  constantSuitableRel .symmetric _ = sym
  constantSuitableRel .transitive _ _ = _∙_
  constantSuitableRel .set _ = A .snd
  constantSuitableRel .prop _ = A .snd

  constantRelMatchesEquiv : StrRelMatchesEquiv {ℓ = ℓ} ConstantRelStr (ConstantEquivStr (A .fst))
  constantRelMatchesEquiv _ _ _ = idEquiv _

  constantSimpleRel : SimpleStrRel {ℓ = ℓ} ConstantRelStr
  constantSimpleRel R = isoToEquiv isom
    where
    fwd : A .fst / ConstantRelStr (R .fst .fst) → A .fst
    fwd [ a ] = a
    fwd (eq/ a b r i) = r i
    fwd (squash/ _ _ p q i j) = A .snd _ _ (λ i → fwd (p i)) (λ i → fwd (q i)) i j

    bwdFwd : ∀ t → [ fwd t ] ≡ t
    bwdFwd [ a ] = refl
    bwdFwd (eq/ a b r i) k = squash/ _ _ (λ i → [ r i ]) (eq/ a b r) k i
    bwdFwd (squash/ t u p q i j) k =
      isGroupoid→isGroupoid' (isSet→isGroupoid squash/)
        (λ i j → [ fwd (squash/ _ _ p q i j) ])
        (squash/ _ _ p q)
        (λ k j → bwdFwd (p j) k)
        (λ k j → bwdFwd (q j) k)
        (λ k _ → bwdFwd t k)
        (λ k _ → bwdFwd u k)
        k i j

    open Iso
    isom : Iso _ _
    isom .fun = fwd
    isom .inv = [_]
    isom .rightInv _ = refl
    isom .leftInv = bwdFwd
