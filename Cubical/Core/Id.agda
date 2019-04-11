{- This file exports the primitives of cubical Id types -}
{-# OPTIONS --cubical --safe #-}
module Cubical.Core.Id where

open import Cubical.Core.Primitives hiding ( _≡_ )

open import Agda.Builtin.Cubical.Id public
  renaming ( conid to ⟨_,_⟩
           -- TODO: should the user really be able to access these two?
           ; primIdFace to faceId  -- ∀ {ℓ} {A : Type ℓ} {x y : A} → Id x y → I
           ; primIdPath to pathId  -- ∀ {ℓ} {A : Type ℓ} {x y : A} → Id x y → Path A x y

           ; primIdElim to elimId  -- ∀ {ℓ ℓ'} {A : Type ℓ} {x : A}
                                   -- (P : ∀ (y : A) → x ≡ y → Type ℓ')
                                   -- (h : ∀ (φ : I) (y : A [ φ ↦ (λ _ → x) ])
                                   --        (w : (Path _ x (outS y)) [ φ ↦ (λ { (φ = i1) → λ _ → x}) ] ) →
                                   --        P (outS y) ⟨ φ , outS w ⟩) →
                                   -- {y : A} (w' : x ≡ y) → P y w'
           )
  hiding ( primIdJ ) -- this should not be used as it is using compCCHM

{- BUILTIN ID Id -}
_≡_ : ∀ {ℓ} {A : Type ℓ} → A → A → Type ℓ
_≡_ = Id
