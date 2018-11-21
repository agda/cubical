{-# OPTIONS --cubical #-}
module Cubical.Basics.UnivalenceId where

open import Cubical.Core.Primitives public  hiding ( _≡_ )
open import Cubical.Core.Prelude public
  hiding ( _≡_ ; ≡-proof_ ; begin_ ; _≡⟨⟩_ ; _≡⟨_⟩_ ; _≡-qed ; _∎ )
open import Cubical.Core.Glue
  renaming ( fiber        to fiberPath
           ; isEquiv      to isEquivPath
           ; _≃_          to EquivPath
           ; equivFun     to equivFunPath
           ; equivIsEquiv to equivIsEquivPath
           ; equivCtr     to equivCtrPath
           ; EquivContr   to EquivContrPath )
open import Cubical.Core.Id

open import Cubical.Basics.Equiv
  renaming ( isPropIsEquiv to isPropIsEquivPath )
open import Cubical.Basics.Univalence

-- TODO: clean!

pathEqId : ∀ {ℓ} {A B : Set ℓ} → Path _ (Path _ A B) (Id A B)
pathEqId = isoToPath pathToId idToPath idToPathToId pathToIdToPath

equivPathToEquivPath : ∀ {ℓ} {A : Set ℓ} {B : Set ℓ} → (p : EquivPath A B) →
                       Path _ (equivToEquivPath (equivPathToEquiv p)) p
equivPathToEquivPath (f , p) i = ( f , isPropIsEquivPath f (λ { .equiv-proof y → helper2 fiberPathToFiber fiberToFiberPath fiberPathToFiberPath (helper1 fiberPathToFiber fiberToFiberPath fiberToFiber (p .equiv-proof y)) }) p i )

foo : ∀ {ℓ} {A B : Set ℓ} → Path (Set (ℓ-suc ℓ)) (Lift (EquivPath A B)) (Lift (A ≃ B))
foo = congPath Lift (isoToPath equivPathToEquiv equivToEquivPath equivToEquiv equivPathToEquivPath)

univalenceId : ∀ {ℓ} {A B : Set ℓ} → (A ≡ B) ≃ (A ≃ B)
univalenceId {ℓ} {A = A} {B = B} = equivPathToEquiv rem
  where
  rem1 : Path _ (Id A B) (Lift (A ≃ B))
  rem1 i = hcomp (λ j → λ { (i = i0) → pathEqId {A = A} {B = B} j
                          ; (i = i1) → foo {ℓ = ℓ} {A = A} {B = B} j })
                 (univalencePath {A = A} {B = B} i)
  rem : EquivPath (Id A B) (A ≃ B)
  rem = compEquiv (eqweqmap rem1) (invEquiv LiftEquiv)
